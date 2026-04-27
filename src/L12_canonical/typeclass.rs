
use std::collections::HashMap;

use smol_str::SmolStr;

use crate::list::List;
use crate::parser_lib::Span;

use super::{Val, Rc};

/// A type class applied to arguments.
#[derive(Debug, Clone)]
pub struct Assertion {
    pub name: SmolStr,
    pub arguments: Vec<Rc<Val>>,
}

/// A type class instance declaration.
#[derive(Debug, Clone)]
pub struct Instance {
    pub assertion: Assertion,
    pub dependencies: List<Assertion>,
    pub lvl: Span<SmolStr>,
}

/// A node in the "search tree" that stores information about
/// the `instances` available while attempting to solve a `goal`
/// and the `index` of the current instance being tried.
#[derive(Debug, Clone)]
pub struct GeneratorNode {
    goal: Assertion,
    instances: Vec<Instance>,
    index: usize,
}

/// A node in the "search tree" that stores information about
/// which `subgoals` need to be solved for a `goal` to solve.
#[derive(Debug, Clone)]
pub struct ConsumerNode {
    goal: Assertion,
    subgoals: List<Assertion>,
    lvl: Span<SmolStr>,
}

/// A "deferred" node in the "search tree" that represents a
/// `goal` waiting for its `subgoals` to be solved.
///
/// [`Waiter::Root`] represents the top-most `goal` being
/// solved, and as such, entails termination once called.
///
/// See also: [`TableEntry`].
#[derive(Debug, Clone)]
pub enum Waiter {
    Root,
    ConsumerNode(ConsumerNode),
}

/// The value type for the information table used in the
/// resolution algorithm.
///
/// Each `goal`, or more accurately, `subgoal` contains the
/// following information:
///
/// 1. A list of "waiters" that should respond to when a
///    `subgoal` gets solved.
///
/// 2. A list of "answers" or information that may be used
///    for code generation.
#[derive(Debug, Clone)]
pub struct TableEntry {
    waiters: Vec<Waiter>,
    answers: Vec<(Assertion, Span<SmolStr>)>,
}

/// The state of the algorithm.
#[derive(Debug, Clone, Default)]
pub struct Synth {
    /// A stack of [`GeneratorNode`]s.
    ///
    /// A more in-depth explanation can be found in [`Synth::synth`].
    generator_stack: Vec<GeneratorNode>,
    /// A stack of [`ConsumerNode`], [`Assertion`] pairs.
    ///
    /// A more in-depth explanation can be found in [`Synth::synth`].
    resume_stack: Vec<(ConsumerNode, Assertion)>,
    /// The instances available for a type class.
    pub class_instances: HashMap<SmolStr, Vec<Instance>>,
    /// Information about each `subgoal` being solved.
    assertion_table: Vec<(Assertion, TableEntry)>,
    /// The "final" answer for the algorithm.
    root_answer: Option<Span<SmolStr>>,
}

fn uncons<T: Clone>(xs: &List<T>) -> Option<(T, List<T>)> {
    xs.head().map(|x| (x.clone(), xs.tail()))
}

impl Synth {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn new_trait(&mut self, name: SmolStr) {
        self.class_instances.insert(name, vec![]);
    }

    pub fn impl_trait_for(&mut self, trait_name: SmolStr, instance: Instance) {
        self.class_instances
            .entry(trait_name)
            .or_default()
            .push(instance);
    }

    pub fn clean(&mut self) {
        self.generator_stack.clear();
        self.resume_stack.clear();
        self.assertion_table.clear();
        self.root_answer = None;
    }

    /// First-order structural matching: goal (ground) against instance pattern (may have Rigid vars).
    /// Rigid vars in the pattern are bound to the corresponding goal values via substitution.
    fn val_match(a: &Val, b: &Val, subst: &mut HashMap<u32, Val>) -> bool {
        match (a, b) {
            // Flex (unsolved meta) in either side matches anything
            (Val::Flex(..), _) | (_, Val::Flex(..)) => true,
            // Rigid var in instance pattern (empty spine) - bind to ground goal value
            (_, Val::Rigid(x, sp)) if sp.is_empty() => {
                if let Some(existing) = subst.get(&x.0) {
                    // Already bound - check structural equality with existing binding
                    Self::vals_eq_ground(a, existing)
                } else {
                    subst.insert(x.0, a.clone());
                    true
                }
            }
            // Rigid vars - must be same level with empty spines
            (Val::Rigid(x1, sp1), Val::Rigid(x2, sp2)) => {
                x1 == x2 && sp1.is_empty() && sp2.is_empty()
            }
            // Decl (named types) - must be same name, match spines
            (Val::Decl(x1, sp1), Val::Decl(x2, sp2)) => {
                x1.data == x2.data
                    && sp1.iter().count() == sp2.iter().count()
                    && sp1.iter().zip(sp2.iter()).all(|((v1, i1), (v2, i2))| {
                        i1 == i2 && Self::val_match(v1, v2, subst)
                    })
            }
            // Sum types - same name, match parameters
            (Val::Sum(n1, p1, _, _), Val::Sum(n2, p2, _, _)) => {
                n1.data == n2.data
                    && p1.len() == p2.len()
                    && p1.iter().zip(p2.iter()).all(|((_, v1, _, _), (_, v2, _, _))| {
                        Self::val_match(v1, v2, subst)
                    })
            }
            // SumCase - same name, match params
            (
                Val::SumCase { case_name: n1, datas: d1, .. },
                Val::SumCase { case_name: n2, datas: d2, .. },
            ) => {
                n1.data == n2.data
                    && d1.len() == d2.len()
                    && d1.iter().zip(d2.iter()).all(|((_, v1, _), (_, v2, _))| {
                        Self::val_match(v1, v2, subst)
                    })
            }
            // Universe level
            (Val::U(x1), Val::U(x2)) => x1 == x2,
            // LiteralType
            (Val::LiteralType, Val::LiteralType) => true,
            // Obj - same field name, match underlying val and spines
            (Val::Obj(a1, n1, sp1), Val::Obj(a2, n2, sp2)) => {
                n1.data == n2.data
                    && Self::val_match(a1, a2, subst)
                    && sp1.iter().count() == sp2.iter().count()
                    && sp1.iter().zip(sp2.iter()).all(|((v1, i1), (v2, i2))| {
                        i1 == i2 && Self::val_match(v1, v2, subst)
                    })
            }
            _ => false,
        }
    }

    /// Structural equality check on two ground Val values (no substitution needed).
    fn vals_eq_ground(a: &Val, b: &Val) -> bool {
        Self::vals_eq_ground_impl(a, b, &mut HashMap::new())
    }

    fn vals_eq_ground_impl(a: &Val, b: &Val, visited: &mut HashMap<u32, u32>) -> bool {
        match (a, b) {
            (Val::Flex(..), _) | (_, Val::Flex(..)) => true,
            (Val::Rigid(x1, sp1), Val::Rigid(x2, sp2)) => {
                x1 == x2 && sp1.is_empty() && sp2.is_empty()
            }
            (Val::Decl(x1, sp1), Val::Decl(x2, sp2)) => {
                x1.data == x2.data
                    && sp1.iter().count() == sp2.iter().count()
                    && sp1.iter().zip(sp2.iter()).all(|((v1, i1), (v2, i2))| {
                        i1 == i2 && Self::vals_eq_ground_impl(v1, v2, visited)
                    })
            }
            (Val::Sum(n1, p1, _, _), Val::Sum(n2, p2, _, _)) => {
                n1.data == n2.data
                    && p1.len() == p2.len()
                    && p1.iter().zip(p2.iter()).all(|((_, v1, _, _), (_, v2, _, _))| {
                        Self::vals_eq_ground_impl(v1, v2, visited)
                    })
            }
            (Val::U(x1), Val::U(x2)) => x1 == x2,
            (Val::LiteralType, Val::LiteralType) => true,
            _ => false,
        }
    }

    fn try_answer(&mut self, subgoal: &Assertion, answer: &Assertion) -> bool {
        if subgoal.name != answer.name {
            return false;
        }
        if subgoal.arguments.len() != answer.arguments.len() {
            return false;
        }
        subgoal.arguments.iter().zip(&answer.arguments).all(|(a, b)| Self::vals_eq_ground(a, b))
    }

    fn try_resolve(
        &mut self,
        goal: &Assertion,
        instance: &Instance,
    ) -> Option<(List<Assertion>, Span<SmolStr>)> {
        // Name must match
        if goal.name != instance.assertion.name {
            return None;
        }

        // Argument count must match
        if goal.arguments.len() != instance.assertion.arguments.len() {
            return None;
        }

        // Match goal arguments (ground) against instance assertion arguments (may have Rigid vars)
        let mut subst = HashMap::new();
        if !goal.arguments.iter()
            .zip(&instance.assertion.arguments)
            .all(|(g_arg, i_arg)| Self::val_match(g_arg, i_arg, &mut subst))
        {
            return None;
        }

        // Collect subgoals (dependencies currently always empty)
        let concrete_deps = instance.dependencies.clone();

        Some((concrete_deps, instance.lvl.clone()))
    }

    /// Find an assertion entry in the table by name and argument matching.
    fn find_assertion_entry(&self, target: &Assertion) -> Option<usize> {
        self.assertion_table.iter().position(|(a, _)| {
            if a.name != target.name || a.arguments.len() != target.arguments.len() {
                return false;
            }
            a.arguments.iter().zip(&target.arguments).all(|(x, y)| Self::vals_eq_ground(x, y))
        })
    }

    /// The entry point for the algorithm.
    pub fn synth(&mut self, assertion: Assertion) -> Option<Span<SmolStr>> {
        // Insert the "root" goal to be solved.
        self.new_subgoal(&assertion, &Waiter::Root);

        // Viciously terminate on cycles.
        let mut effort = 0;
        loop {
            effort += 1;
            if effort > 1000 {
                panic!("Too much effort :(");
            }

            // Terminate once we find an answer for the root goal.
            if let Some(root_answer) = &self.root_answer {
                break Some(root_answer.clone());
            }

            if let Some((consumer_node, answer)) = self.resume_stack.pop() {
                match uncons(&consumer_node.subgoals) {
                    Some((subgoal, remaining)) => {
                        if self.try_answer(&subgoal, &answer) {
                            self.consume(ConsumerNode {
                                goal: consumer_node.goal,
                                subgoals: remaining,
                                lvl: consumer_node.lvl,
                            });
                        } else {
                            continue;
                        }
                    }
                    None => panic!("Cannot resume with empty subgoals."),
                }
            } else if let Some(generator_node) = self.generator_stack.last_mut() {
                if generator_node.index >= generator_node.instances.len() {
                    self.generator_stack.pop();
                } else {
                    let goal = generator_node.goal.clone();
                    let instance = generator_node.instances[generator_node.index].clone();
                    generator_node.index += 1;
                    if let Some((subgoals, lvl)) = self.try_resolve(&goal, &instance) {
                        self.consume(ConsumerNode { goal, subgoals, lvl });
                    }
                }
            } else {
                break None;
            }
        }
    }

    fn new_subgoal(&mut self, subgoal: &Assertion, waiter: &Waiter) {
        // Create a table entry for this subgoal.
        self.assertion_table.push((
            subgoal.clone(),
            TableEntry {
                waiters: vec![waiter.clone()],
                answers: vec![],
            },
        ));
        // Find instances to try for this subgoal.
        let instances = self.class_instances.get(&subgoal.name).unwrap().clone();
        // Try instances from the beginning (more specific first).
        let index = 0usize;
        // Always push a generator node.
        self.generator_stack.push(GeneratorNode {
            goal: subgoal.clone(),
            instances,
            index,
        });
    }

    fn consume(&mut self, consumer_node: ConsumerNode) {
        match uncons(&consumer_node.subgoals) {
            None => {
                // Goal is solved - update the assertion table entry
                let answer = consumer_node.goal.clone();
                let answer_lvl = consumer_node.lvl.clone();
                // Find the entry for this goal
                if let Some(idx) = self.find_assertion_entry(&consumer_node.goal) {
                    let entry = &mut self.assertion_table[idx].1;
                    entry.answers.push((answer.clone(), answer_lvl.clone()));
                    let waiters = std::mem::take(&mut entry.waiters);
                    for waiter in &waiters {
                        match waiter {
                            Waiter::Root => self.root_answer = Some(answer_lvl.clone()),
                            Waiter::ConsumerNode(node) => self
                                .resume_stack
                                .push((node.clone(), answer.clone())),
                        }
                    }
                }
            }
            Some((subgoal, _)) => {
                // Look up the subgoal in the assertion table
                if let Some(idx) = self.find_assertion_entry(&subgoal) {
                    // Push existing answers to the resume stack
                    let entry = &mut self.assertion_table[idx].1;
                    let answers = entry.answers.clone();
                    for answer in &answers {
                        self.resume_stack
                            .push((consumer_node.clone(), answer.0.clone()));
                    }
                    entry.waiters.push(Waiter::ConsumerNode(consumer_node));
                } else {
                    self.new_subgoal(&subgoal, &Waiter::ConsumerNode(consumer_node));
                }
            }
        }
    }
}

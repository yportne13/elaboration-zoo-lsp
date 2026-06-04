
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
    assertion_idx: usize,
}

/// A node in the "search tree" that stores information about
/// which `subgoals` need to be solved for a `goal` to solve.
#[derive(Debug, Clone)]
pub struct ConsumerNode {
    goal: Assertion,
    subgoals: List<Assertion>,
    lvl: Span<SmolStr>,
    assertion_idx: usize,
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
    pub waiters: Vec<Waiter>,
    pub answers: Vec<(Assertion, Span<SmolStr>)>,
}

/// The state of the algorithm.
#[derive(Debug, Clone)]
pub struct Synth {
    /// A stack of [`GeneratorNode`]s.
    ///
    /// A more in-depth explanation can be found in [`Synth::synth`].
    pub generator_stack: Vec<GeneratorNode>,
    /// A stack of [`ConsumerNode`], [`Assertion`] pairs.
    ///
    /// A more in-depth explanation can be found in [`Synth::synth`].
    pub resume_stack: Vec<(ConsumerNode, Assertion)>,
    /// The instances available for a type class.
    pub class_instances: HashMap<SmolStr, Vec<Instance>>,
    /// Information about each `subgoal` being solved.
    pub assertion_table: Vec<(Assertion, TableEntry)>,
    /// The "final" answer for the algorithm.
    pub root_answer: Option<Span<SmolStr>>,
    /// Tracks which arguments of each trait are output params.
    pub trait_out_params: HashMap<SmolStr, Vec<bool>>,
    /// Index from (trait_name, head_constructor) to instance indices.
    /// Uses the first non-out-param's head as the key for O(1) lookup.
    pub head_index: HashMap<(SmolStr, SmolStr), Vec<usize>>,
}

impl Default for Synth {
    fn default() -> Self {
        Self {
            generator_stack: vec![],
            resume_stack: vec![],
            class_instances: HashMap::new(),
            assertion_table: vec![],
            root_answer: None,
            trait_out_params: HashMap::new(),
            head_index: HashMap::new(),
        }
    }
}

fn uncons<T: Clone>(xs: &List<T>) -> Option<(T, List<T>)> {
    xs.head().map(|x| (x.clone(), xs.tail()))
}

pub(crate) fn head_key(val: &Val) -> Option<SmolStr> {
    match val {
        Val::Decl(name, _) => Some(name.data.clone()),
        Val::Sum(name, _, _, _) => Some(name.data.clone()),
        _ => None,
    }
}

impl Synth {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn new_trait(&mut self, name: SmolStr) {
        self.class_instances.insert(name, vec![]);
    }

    pub fn set_trait_out_params(&mut self, name: SmolStr, out_params: Vec<bool>) {
        self.trait_out_params.insert(name, out_params);
    }

    pub fn impl_trait_for(&mut self, trait_name: SmolStr, instance: Instance) {
        let instances = self.class_instances
            .entry(trait_name.clone())
            .or_default();
        let idx = instances.len();

        // Index by first non-out param's head constructor
        if let Some(out_params) = self.trait_out_params.get(&trait_name) {
            for (i, arg) in instance.assertion.arguments.iter().enumerate() {
                if out_params.get(i).copied().unwrap_or(false) {
                    continue;
                }
                if let Some(head) = head_key(arg) {
                    self.head_index
                        .entry((trait_name.clone(), head))
                        .or_default()
                        .push(idx);
                }
                break;
            }
        }

        instances.push(instance);
    }

    /// Check if this trait has at least one instance whose Self-type head matches `self_type`.
    /// Uses head_index for O(1) lookup; falls back to val_match scan when the index misses.
    pub fn can_satisfy(&self, trait_name: &SmolStr, self_type: &Val) -> bool {
        if let Some(head) = head_key(self_type) {
            if let Some(indices) = self.head_index.get(&(trait_name.clone(), head)) {
                return !indices.is_empty();
            }
        }
        let instances = match self.class_instances.get(trait_name) {
            Some(insts) => insts,
            None => return false,
        };
        let out_params = self.trait_out_params.get(trait_name);
        for inst in instances {
            if inst.assertion.name != *trait_name {
                continue;
            }
            if inst.assertion.arguments.is_empty() {
                continue;
            }
            let first_is_out = out_params
                .and_then(|op| op.first().copied())
                .unwrap_or(false);
            if first_is_out {
                return true;
            }
            let mut subst = HashMap::new();
            if Self::val_match(self_type, &inst.assertion.arguments[0], &mut subst) {
                return true;
            }
        }
        false
    }

    pub fn clean(&mut self) {
        self.generator_stack.clear();
        self.resume_stack.clear();
        self.assertion_table.clear();
        self.root_answer = None;
    }

    /// First-order structural matching: goal (ground) against instance pattern (may have Rigid vars).
    /// Rigid vars in the pattern are bound to the corresponding goal values via substitution.
    pub fn val_match(a: &Val, b: &Val, subst: &mut HashMap<u32, Val>) -> bool {
        //println!("val_match: {:?} {:?}", a, b);
        //println!("------");
        //println!("{:?}", subst.get(&0));
        //println!("--------------------------");
        match (a, b) {
            // Flex (unsolved meta) in either side matches anything
            (Val::Flex(..), _) | (_, Val::Flex(..)) => true,
            // Rigid vars - must be same level with empty spines
            (Val::Rigid(x1, sp1), Val::Rigid(x2, sp2)) if x1 == x2 && sp1.is_empty() && sp2.is_empty() => {
                true
            }
            // Rigid var in instance pattern (empty spine) - bind to ground goal value
            (_, Val::Rigid(x, sp)) | (Val::Rigid(x, sp), _) if sp.is_empty() => {
                if let Some(existing) = subst.get(&x.0) {
                    // Already bound - check structural equality with existing binding
                    Self::vals_eq_ground(a, existing)
                } else {
                    subst.insert(x.0, a.clone());
                    true
                }
            }
            // Decl (named types) - must be same name, match spines
            (Val::Decl(x1, sp1), Val::Decl(x2, sp2)) => {
                x1.data == x2.data
                    && sp1.len() == sp2.len()
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
            // LiteralType (String) is equivalent to Decl("String")
            (Val::LiteralType, Val::Decl(x, sp)) | (Val::Decl(x, sp), Val::LiteralType) => {
                x.data == "String" && sp.is_empty()
            }
            // LiteralType
            (Val::LiteralType, Val::LiteralType) => true,
            // Obj - same field name, match underlying val and spines
            (Val::Obj(a1, n1, sp1), Val::Obj(a2, n2, sp2)) => {
                n1.data == n2.data
                    && Self::val_match(a1, a2, subst)
                    && sp1.len() == sp2.len()
                    && sp1.iter().zip(sp2.iter()).all(|((v1, i1), (v2, i2))| {
                        i1 == i2 && Self::val_match(v1, v2, subst)
                    })
            }
            _ => false,
        }
    }

    /// Structural equality check on two ground Val values (no substitution needed).
    pub fn vals_eq_ground(a: &Val, b: &Val) -> bool {
        Self::vals_eq_ground_impl(a, b, &mut HashMap::new())
    }

    fn vals_eq_ground_impl(a: &Val, b: &Val, visited: &mut HashMap<u32, u32>) -> bool {
        //println!("###### {a:?} ===== {b:?}");
        match (a, b) {
            (Val::Flex(..), _) | (_, Val::Flex(..)) => true,
            (Val::Rigid(x1, sp1), Val::Rigid(x2, sp2)) => {
                x1 == x2 && sp1.is_empty() && sp2.is_empty()
            }
            (Val::Decl(x1, sp1), Val::Decl(x2, sp2)) => {
                x1.data == x2.data
                    && sp1.len() == sp2.len()
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
            (
                Val::SumCase { case_name: n1, datas: d1, .. },
                Val::SumCase { case_name: n2, datas: d2, .. },
            ) => {
                n1.data == n2.data
                    && d1.len() == d2.len()
                    && d1.iter().zip(d2.iter()).all(|((_, v1, _), (_, v2, _))| {
                        Self::vals_eq_ground_impl(v1, v2, visited)
                    })
            }
            (Val::U(x1), Val::U(x2)) => x1 == x2,
            (Val::LiteralType, Val::Decl(x, sp)) | (Val::Decl(x, sp), Val::LiteralType) => {
                x.data == "String" && sp.is_empty()
            }
            (Val::LiteralType, Val::LiteralType) => true,
            (Val::Match(a1, b1, c1), Val::Match(a2, b2, c2)) => {
                Self::vals_eq_ground_impl(a1, a2, visited)
                    && b1.len() == b2.len()
                    //TODO:&& c1.iter().zip(c2.iter()).all(|()| )
            }
            (Val::Call(n1, args1, _), Val::Call(n2, args2, _)) => {
                n1 == n2
                    && args1.len() == args2.len()
                    && args1.iter().zip(args2.iter()).all(|((v1, i1), (v2, i2))| {
                        i1 == i2 && Self::vals_eq_ground_impl(v1, v2, visited)
                    })
            }
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

        // Determine which args are output params for this trait
        let out_params = self.trait_out_params.get(&goal.name);

        // Match goal arguments against instance assertion arguments.
        // For output params, Flex metas in the goal match anything (they get resolved later via unification).
        // For non-output params, use val_match as before.
        let mut subst = HashMap::new();
        for (i, (g_arg, i_arg)) in goal.arguments.iter().zip(&instance.assertion.arguments).enumerate() {
            let is_out = out_params.map(|op| op.get(i).copied().unwrap_or(false)).unwrap_or(false);
            if is_out && matches!(g_arg.as_ref(), Val::Flex(..)) {
                // Output param with flex meta in goal: accept any instance output
                continue;
            }
            if !Self::val_match(g_arg, i_arg, &mut subst) {
                return None;
            }
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
                                assertion_idx: consumer_node.assertion_idx,
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
                    let assertion_idx = generator_node.assertion_idx;
                    if let Some((subgoals, lvl)) = self.try_resolve(&goal, &instance) {
                        self.consume(ConsumerNode {
                            goal,
                            subgoals,
                            lvl,
                            assertion_idx,
                        });
                    }
                }
            } else {
                break None;
            }
        }
    }

    fn new_subgoal(&mut self, subgoal: &Assertion, waiter: &Waiter) {
        let assertion_idx = self.assertion_table.len();
        self.assertion_table.push((
            subgoal.clone(),
            TableEntry {
                waiters: vec![waiter.clone()],
                answers: vec![],
            },
        ));
        let instances = self.class_instances.get(&subgoal.name).unwrap().clone();
        let index = 0usize;
        self.generator_stack.push(GeneratorNode {
            goal: subgoal.clone(),
            instances,
            index,
            assertion_idx,
        });
    }

    fn consume(&mut self, consumer_node: ConsumerNode) {
        match uncons(&consumer_node.subgoals) {
            None => {
                let answer = consumer_node.goal.clone();
                let answer_lvl = consumer_node.lvl.clone();
                let entry = &mut self.assertion_table[consumer_node.assertion_idx].1;
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

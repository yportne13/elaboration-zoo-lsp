
use std::collections::HashMap;

use crate::{list::List, L10_typeclass::empty_span};

use super::{Val, Span};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Typ {
    Any,
    Val(Span<String>),
    Construct(Span<String>, Vec<Typ>),
    Fn(Box<Typ>, Box<Typ>),
    Trait(Span<String>),
}

impl Val {
    pub fn to_typ(&self) -> Option<Typ> {
        match self {
            Val::Flex(..) => None,
            Val::Rigid(lvl, list) => None,
            Val::Obj(val, span) => None,
            Val::Lam(..) => None,
            Val::Pi(span, icit, val, closure) => todo!(),
            Val::U(x) => Some(Typ::Val(empty_span(format!("Type {x}")))),
            Val::LiteralType => todo!(),
            Val::LiteralIntro(span) => todo!(),
            Val::Prim => todo!(),
            Val::Sum(span, items, _) => Some(
                if items.is_empty() {
                    Typ::Val(span.clone())
                } else {
                    Typ::Construct(
                        span.clone(),
                        items.iter().flat_map(|x| x.1.to_typ()).collect(),//TODO:
                    )
                }
            ),
            Val::SumCase { .. } => None,
            Val::Match(..) => None,
        }
    }
}

/// A type class applied to arguments.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assertion {
    pub name: String,
    pub arguments: Vec<Typ>,
}

/// A type class instance declaration.
#[derive(Debug, Clone)]
pub struct Instance {
    pub assertion: Assertion,
    pub dependencies: List<Assertion>,
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
    answers: Vec<Assertion>,
}

/// The state of the algorithm.
#[derive(Debug, Clone)]
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
    class_instances: HashMap<String, Vec<Instance>>,
    /// Information about each `subgoal` being solved.
    assertion_table: HashMap<Assertion, TableEntry>,
    /// The "final" answer for the algorithm.
    root_answer: Option<Assertion>,
}

impl Default for Synth {
    fn default() -> Self {
        Self {
            generator_stack: vec![],
            resume_stack: vec![],
            class_instances: HashMap::new(),
            assertion_table: HashMap::new(),
            root_answer: None,
        }
    }
}

fn uncons<T: Clone>(xs: &List<T>) -> Option<(T, List<T>)> {
    xs.head().map(|x| (x.clone(), xs.tail()))
}

impl Synth {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn new_trait(&mut self, name: String) {
        self.class_instances.insert(name, vec![]);
    }

    pub fn impl_trait_for(&mut self, trait_name: String, instance: Instance) {
        self.class_instances
            .entry(trait_name)
            .or_insert(vec![])
            .push(instance);
    }

    fn try_answer(&mut self, subgoal: &Assertion, answer: &Assertion) -> bool {
        todo!("try_answer")
    }

    fn try_resolve(&mut self, goal: &Assertion, instance: &Instance) -> Option<List<Assertion>> {
        todo!("try_resolve")
    }

    /// The entry point for the algorithm.
    pub fn synth(&mut self, assertion: Assertion) -> Option<Assertion> {
        // Insert the "root" goal to be solved.
        self.new_subgoal(&assertion, &Waiter::Root);

        // Visciously terminate on cycles.
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

            // In-depth explanation for `resume_stack`:
            //
            // We know that a `ConsumerNode` represents a `goal` and its `subgoals` that
            // need to be solved. The `resume_stack` is effectively pairs of consumer nodes
            // and potential "solutions" for the first subgoal of said nodes.
            //
            // If the solution works, we call the `consume` function to handle the remaining
            // subgoals for the current `consumer_node`.
            //
            // If the solution fails, we reject the answer and simply move along.
            //
            //
            // In-depth explanation for `generator_stack`:
            //
            // We know that a `GeneratorNode` represents a `goal`, a list of instances to
            // try, and the current instance being tried. The `generator_stack` effectively
            // mirrors a depth-first search for a solution.
            //
            // For the top-most generator node in the stack, we determine if the current
            // instance can be used to "solve" the goal. If it is, we return the subgoals,
            // which is then used to construct the consumer node to be passed to `consume`.
            //
            // If we run out of instances to try, that is, if the index falls to zero, we
            // simply pop the generator node as we're no longer interested in it.
            if let Some((consumer_node, answer)) = self.resume_stack.pop() {
                match uncons(&consumer_node.subgoals) {
                    Some((subgoal, remaining)) => {
                        if self.try_answer(&subgoal, &answer) {
                            self.consume(ConsumerNode {
                                goal: consumer_node.goal,
                                subgoals: remaining,
                            });
                        } else {
                            continue;
                        }
                    }
                    None => panic!("Cannot resume with empty subgoals."),
                }
            } else if let Some(generator_node) = self.generator_stack.last_mut() {
                if generator_node.index == 0 {
                    self.generator_stack.pop();
                } else {
                    generator_node.index -= 1;
                    let goal = generator_node.goal.clone();
                    let instance = generator_node.instances[generator_node.index].clone();
                    if let Some(subgoals) = self.try_resolve(&goal, &instance) {
                        self.consume(ConsumerNode { goal, subgoals });
                    }
                }
            } else {
                break None;
            }
        }
    }

    fn new_subgoal(&mut self, subgoal: &Assertion, waiter: &Waiter) {
        // Create a table entry for this subgoal.
        self.assertion_table.insert(
            subgoal.clone(),
            TableEntry {
                waiters: vec![waiter.clone()],
                answers: vec![],
            },
        );
        // Find instances to try for this subgoal.
        //
        // TODO: local instances should work too!
        let instances = self.class_instances.get(&subgoal.name).unwrap().clone();
        // Try instances from the end, counting down to zero.
        let index = instances.len();
        // Finally, push a generator node to the stack.
        self.generator_stack.push(GeneratorNode {
            goal: subgoal.clone(),
            instances,
            index,
        });
    }

    fn consume(&mut self, consumer_node: ConsumerNode) {
        // If there are no more subgoals, we consider the `consumer_node.goal` to be solved,
        // and then proceed to queue its waiters to the `resume_stack`. For example, when
        // solving `Eq Int`, `Eq [Int]` may have been registered as a waiter. Once we're back
        // at the `synth` loop, `Eq [Int]` tries the answer `Eq Int` with its subgoal `Eq Int`
        // and succeeds. Finally, `consume` gets called again for `Eq [Int]` with no more subgoals,
        // and maybe this time its waiter is `root`, so we terminate.
        //
        // If there's at least one subgoal, we consider the `consumer_node.goal` to be unsolved.
        // If a table entry exists for the subgoal, we take the `answers` and push them to the
        // `resume_stack` with the `consumer_node`; similarly, we say that the `consumer_node`
        // is a waiter for this subgoal. This is likely to be the case when we've solved this
        // subgoal in the past, serving as a caching mechanism.
        match uncons(&consumer_node.subgoals) {
            None => {
                self.assertion_table
                    .entry(consumer_node.goal.clone())
                    .and_modify(|TableEntry { waiters, answers }| {
                        let answer = consumer_node.goal;
                        answers.push(answer.clone());
                        for waiter in waiters {
                            match waiter {
                                Waiter::Root => self.root_answer = Some(answer.clone()),
                                Waiter::ConsumerNode(consumer_node) => self
                                    .resume_stack
                                    .push((consumer_node.clone(), answer.clone())),
                            }
                        }
                    });
            }
            Some((subgoal, _)) => {
                if let Some(TableEntry { waiters, answers }) =
                    self.assertion_table.get_mut(&subgoal)
                {
                    for answer in answers {
                        self.resume_stack
                            .push((consumer_node.clone(), answer.clone()));
                    }
                    waiters.push(Waiter::ConsumerNode(consumer_node));
                } else {
                    self.new_subgoal(&subgoal, &Waiter::ConsumerNode(consumer_node));
                }
            }
        }
    }
}

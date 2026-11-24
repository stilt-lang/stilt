//! The last step of name resolution: modules can't depend on one another in a cycle
//! (program.no-cycles). The references between a program's modules form a graph, and each of its
//! strongly connected components that holds a cycle is one error, at the last reference inside it
//! (errors.primary-spans). The components are found with Tarjan's algorithm.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use stilt_db::{Db, Program, SourceFile};

use crate::hir::Name;
use crate::lower::resolve_module;
use crate::scope::def_map;

/// The modules that a file's module names, in source order, without the positions, so that an
/// edit that names no other module leaves them unchanged.
#[salsa::tracked(returns(ref))]
pub(crate) fn references(db: &dyn Db, program: Program, file: SourceFile) -> Vec<Name> {
    resolve_module(db, program, file)
        .references
        .iter()
        .map(|(target, _)| *target)
        .collect()
}

/// A cycle of modules, reported at the reference of this index among its file's references.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Cycle {
    pub(crate) file: SourceFile,
    pub(crate) reference: usize,
    pub(crate) message: String,
}

/// A reference from one module to another, by its place among its file's references.
struct Reference {
    from: Name,
    target: Name,
    path: String,
    file: SourceFile,
    index: usize,
}

#[salsa::tracked(returns(ref))]
pub(crate) fn import_cycles(db: &dyn Db, program: Program) -> Vec<Cycle> {
    let map = def_map(db, program);
    let modules: Vec<_> = map.modules.iter().filter(|m| m.valid && !m.std).collect();
    let named: BTreeSet<Name> = modules.iter().map(|m| m.name).collect();
    let references: Vec<Reference> = modules
        .iter()
        .flat_map(|m| {
            references(db, program, m.file)
                .iter()
                .enumerate()
                .filter(|(_, target)| named.contains(*target))
                .map(|(index, target)| Reference {
                    from: m.name,
                    target: *target,
                    path: m.file.path(db).clone(),
                    file: m.file,
                    index,
                })
        })
        .collect();
    let mut targets: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();
    for r in &references {
        targets.entry(r.from).or_default().insert(r.target);
    }
    let graph = Graph { targets };
    let components = graph.components(&named);
    let of: HashMap<&Name, usize> = components
        .iter()
        .enumerate()
        .flat_map(|(i, component)| component.iter().map(move |m| (m, i)))
        .collect();
    // The last reference inside each component, found in one pass over the references.
    let mut last: Vec<Option<&Reference>> = vec![None; components.len()];
    for r in &references {
        let i = of[&r.from];
        if of[&r.target] == i && last[i].is_none_or(|l| (&l.path, l.index) < (&r.path, r.index)) {
            last[i] = Some(r);
        }
    }
    components
        .iter()
        .zip(last)
        .filter_map(|(component, last)| {
            let last = last?;
            let mut cycle = vec![last.from];
            cycle.extend(graph.route(component, last.target, last.from));
            Some(Cycle {
                file: last.file,
                reference: last.index,
                message: format!(
                    "modules depend on one another in a cycle: {}",
                    cycle.iter().map(|m| &**m).collect::<Vec<_>>().join(" -> ")
                ),
            })
        })
        .collect()
}

struct Graph {
    targets: BTreeMap<Name, BTreeSet<Name>>,
}

impl Graph {
    fn targets(&self, m: Name) -> impl Iterator<Item = Name> {
        self.targets.get(&m).into_iter().flatten().copied()
    }

    /// The strongly connected components of the graph over `nodes`.
    fn components(&self, nodes: &BTreeSet<Name>) -> Vec<HashSet<Name>> {
        let mut tarjan = Tarjan {
            graph: self,
            index: HashMap::new(),
            low: HashMap::new(),
            stack: Vec::new(),
            on_stack: HashSet::new(),
            components: Vec::new(),
        };
        for m in nodes {
            if !tarjan.index.contains_key(m) {
                tarjan.connect(*m);
            }
        }
        tarjan.components
    }

    /// The shortest route of references from `a` to `b` inside `component`, where every module
    /// reaches every other.
    fn route(&self, component: &HashSet<Name>, a: Name, b: Name) -> Vec<Name> {
        if a == b {
            return vec![a];
        }
        let mut previous: HashMap<Name, Name> = HashMap::new();
        let mut queue = VecDeque::from([a]);
        while !previous.contains_key(&b) {
            let Some(n) = queue.pop_front() else { break };
            for t in self.targets(n) {
                if component.contains(&t) && t != a && !previous.contains_key(&t) {
                    previous.insert(t, n);
                    queue.push_back(t);
                }
            }
        }
        let mut route = vec![b];
        let mut n = b;
        while n != a {
            let Some(&p) = previous.get(&n) else { break };
            route.push(p);
            n = p;
        }
        route.reverse();
        route
    }
}

struct Tarjan<'a> {
    graph: &'a Graph,
    index: HashMap<Name, usize>,
    low: HashMap<Name, usize>,
    stack: Vec<Name>,
    on_stack: HashSet<Name>,
    components: Vec<HashSet<Name>>,
}

impl Tarjan<'_> {
    fn connect(&mut self, m: Name) {
        let i = self.index.len();
        self.index.insert(m, i);
        self.low.insert(m, i);
        self.stack.push(m);
        self.on_stack.insert(m);
        for t in self.graph.targets(m) {
            if !self.index.contains_key(&t) {
                self.connect(t);
                let low = self.low[&m].min(self.low[&t]);
                self.low.insert(m, low);
            } else if self.on_stack.contains(&t) {
                let low = self.low[&m].min(self.index[&t]);
                self.low.insert(m, low);
            }
        }
        if self.low[&m] == i {
            let mut component = HashSet::new();
            while let Some(n) = self.stack.pop() {
                self.on_stack.remove(&n);
                let done = n == m;
                component.insert(n);
                if done {
                    break;
                }
            }
            self.components.push(component);
        }
    }
}

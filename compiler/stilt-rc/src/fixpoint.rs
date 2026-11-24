//! The parameters each function consumes, given every function's [`Summary`]: a least fixed
//! point, solved one strongly connected component of the call graph at a time, the callees'
//! components before their callers', so that recursion is the only reason to iterate.

use std::collections::HashMap;

use stilt_mir::FnRef;

use crate::consume::Summary;

/// The parameters, by position, that each function consumes: those its body consumes, and
/// those it passes to a parameter that its callee consumes. A callee without a summary, such as
/// a native, consumes none.
pub(crate) fn solve(summaries: &[(FnRef, &Summary)]) -> HashMap<FnRef, Vec<usize>> {
    let index: HashMap<&FnRef, usize> = summaries
        .iter()
        .enumerate()
        .map(|(i, (f, _))| (f, i))
        .collect();
    let edges: Vec<Vec<usize>> = summaries
        .iter()
        .map(|(_, s)| {
            s.passed
                .iter()
                .filter_map(|(_, g, _)| index.get(g).copied())
                .collect()
        })
        .collect();
    let mut consumed: Vec<Vec<usize>> = summaries.iter().map(|(_, s)| s.consumed.clone()).collect();
    for component in components(&edges) {
        let mut changed = true;
        while changed {
            changed = false;
            for &u in &component {
                for (p, g, i) in &summaries[u].1.passed {
                    let Some(&v) = index.get(g) else { continue };
                    if consumed[v].contains(i) && !consumed[u].contains(p) {
                        consumed[u].push(*p);
                        changed = true;
                    }
                }
            }
        }
    }
    summaries
        .iter()
        .zip(consumed)
        .map(|((f, _), mut c)| {
            c.sort_unstable();
            (f.clone(), c)
        })
        .collect()
}

/// The strongly connected components of a graph, by Tarjan's algorithm without recursion, so
/// that a long chain of calls can't exhaust the stack. Each component comes after every
/// component that its nodes reach.
pub(crate) fn components(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    const UNSEEN: usize = usize::MAX;
    let n = edges.len();
    let (mut order, mut low) = (vec![UNSEEN; n], vec![0; n]);
    let mut on_stack = vec![false; n];
    let (mut stack, mut out, mut next) = (Vec::new(), Vec::new(), 0);
    for root in 0..n {
        if order[root] != UNSEEN {
            continue;
        }
        // Each node being visited, with how many of its edges it has followed.
        let mut work = vec![(root, 0)];
        (order[root], low[root], next) = (next, next, next + 1);
        stack.push(root);
        on_stack[root] = true;
        while let Some(&(u, e)) = work.last() {
            if let Some(&v) = edges[u].get(e) {
                work.last_mut().expect("a node is being visited").1 += 1;
                if order[v] == UNSEEN {
                    (order[v], low[v], next) = (next, next, next + 1);
                    stack.push(v);
                    on_stack[v] = true;
                    work.push((v, 0));
                } else if on_stack[v] {
                    low[u] = low[u].min(order[v]);
                }
                continue;
            }
            work.pop();
            if let Some(&(parent, _)) = work.last() {
                low[parent] = low[parent].min(low[u]);
            }
            if low[u] == order[u] {
                let mut component = Vec::new();
                while let Some(w) = stack.pop() {
                    on_stack[w] = false;
                    component.push(w);
                    if w == u {
                        break;
                    }
                }
                out.push(component);
            }
        }
    }
    out
}

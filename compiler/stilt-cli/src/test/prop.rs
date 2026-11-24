//! Running a property (tests.property-cases, tests.running-cases and tests.shrinking): its cases,
//! in order, until one fails, whose values are then shrunk, each run of its closure a run of its
//! entry on a thread of its own (`stilt_runtime::property`), on values it reads from a tape.
//! Generation and shrinking are fixed by the record, so the reference interpreter finds the same
//! cases and the same counterexample.

mod draw;
mod shown;
mod shrink;
mod tape;
#[cfg(test)]
mod tests;
mod values;

use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use stilt_runtime::{Entry, Outcome};
use stilt_types::generable::Graph;

pub(crate) use draw::seed;
use shrink::Failure;
use values::Val;

/// The number of cases a property runs (tests.property-cases).
const CASES: u32 = 100;

/// What running a property needs: the types its parameters' types hold, the node of each
/// parameter's type, and its text, which seeds its cases.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct Spec {
    pub(crate) graph: Graph,
    pub(crate) params: Vec<usize>,
    pub(crate) text: String,
    /// The names of its parameters, for the counterexample.
    pub(crate) names: Vec<String>,
}

/// A property's verdict (tests.property-verdict).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Verdict {
    pub(crate) seed: u64,
    pub(crate) cases: u32,
    pub(crate) failed: Option<Failed>,
}

/// The failing case of a property, and its counterexample.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Failed {
    case: u32,
    counterexample: Vec<String>,
    failure: Failure,
    shrinks: u32,
}

/// Runs the property of `spec`, whose entry is `entry`.
pub(crate) fn run(entry: Entry, spec: &Spec) -> Verdict {
    let (g, params) = (&spec.graph, spec.params.as_slice());
    let seed = seed(&spec.text);
    let attempt = |values: &[Val]| {
        let mut t = tape::write(g, params, values);
        let failure = match stilt_runtime::property(entry, &mut t) {
            Outcome::Passed => None,
            Outcome::False => Some(Failure::False),
            Outcome::Raised(shown) => Some(Failure::Raise(shown)),
            Outcome::Panicked { kind, detail } => Some(Failure::Panic(kind, detail)),
        };
        (failure, t.notes().to_vec())
    };
    for case in 0..CASES {
        let values = values::case(g, seed, params, u64::from(case));
        let (Some(failure), notes) = attempt(&values) else {
            continue;
        };
        let values = tape::settle(g, params, &values, &notes);
        let mut run = |values: &[Val]| attempt(values).0;
        let shrunk = shrink::shrink(g, params, values, failure, &mut run);
        let counterexample = params
            .iter()
            .zip(&shrunk.values)
            .map(|(&k, v)| shown::shown(g, k, v))
            .collect();
        let failed = Failed {
            case,
            counterexample,
            failure: shrunk.failure,
            shrinks: shrunk.shrinks,
        };
        return Verdict {
            seed,
            cases: case + 1,
            failed: Some(failed),
        };
    }
    Verdict {
        seed,
        cases: CASES,
        failed: None,
    }
}

impl Verdict {
    /// The lines that tell a person why the property failed, none when it passed: how it
    /// failed, at which case and with which seed, and the shrunk counterexample, one value for
    /// each of the parameters `names`.
    pub(crate) fn lines(&self, names: &[String]) -> Vec<String> {
        let Some(f) = &self.failed else {
            return Vec::new();
        };
        let how = match &f.failure {
            Failure::False => "returned false".to_owned(),
            Failure::Raise(shown) => format!("raised {shown}"),
            Failure::Panic(kind, detail) => format!("panicked: {kind}: {detail}"),
        };
        let mut lines = vec![
            format!(
                "it {how} at case {}, with seed {:016x}",
                f.case + 1,
                self.seed
            ),
            match f.shrinks {
                0 => "counterexample:".to_owned(),
                1 => "counterexample, shrunk once:".to_owned(),
                n => format!("counterexample, shrunk {n} times:"),
            },
        ];
        let values = f.counterexample.iter().enumerate();
        lines.extend(values.map(|(i, v)| {
            let name = names.get(i).map_or("_", String::as_str);
            format!("  {name} = {v}")
        }));
        lines
    }

    /// The `property` object of `test --json`.
    pub(crate) fn json(&self) -> Value {
        let mut object = json!({ "seed": format!("{:016x}", self.seed), "cases": self.cases });
        if let Some(f) = &self.failed {
            let (failure, detail) = match &f.failure {
                Failure::False => ("false".to_owned(), None),
                Failure::Raise(d) => ("raise".to_owned(), Some(d)),
                Failure::Panic(k, d) => (format!("panic: {k}"), Some(d)),
            };
            object["case"] = json!(f.case);
            object["counterexample"] = json!(f.counterexample);
            object["failure"] = json!(failure);
            if let Some(d) = detail {
                object["detail"] = json!(d);
            }
            object["shrinks"] = json!(f.shrinks);
        }
        object
    }
}

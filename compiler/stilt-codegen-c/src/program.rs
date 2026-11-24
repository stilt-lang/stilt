//! What the files of a program's C share: a name for each compiled function, the cell of each
//! constant, and the declarations of the runtime's functions and natives it calls. Each
//! function's body records what it names in its [`Refs`], so that a file declares only what
//! its functions name, and a function that only its own file names is `static`.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use stilt_mir::FnRef;
use stilt_mir::mir::{Function, Operand, Repr};

use crate::Options;
use crate::names::c_name;
use crate::proved::Proved;

/// What a body names: compiled functions, by index, called or taken as values, cells, by
/// index, and runtime functions, by name.
#[derive(Clone, Debug, Default)]
pub(crate) struct Refs {
    pub(crate) functions: BTreeSet<usize>,
    pub(crate) slots: BTreeSet<usize>,
    pub(crate) cells: BTreeSet<usize>,
    pub(crate) externs: BTreeSet<String>,
}

impl Refs {
    pub(crate) fn extend(&mut self, other: &Refs) {
        self.functions.extend(&other.functions);
        self.slots.extend(&other.slots);
        self.cells.extend(&other.cells);
        self.externs.extend(other.externs.iter().cloned());
    }
}

/// A constant's cell: the code that computes it, and the words of its value.
#[derive(Debug)]
pub(crate) struct Cell {
    pub(crate) f: FnRef,
    pub(crate) words: Box<[Repr]>,
    pub(crate) name: String,
}

/// The names of a program's functions, cells and externs.
#[derive(Debug)]
pub(crate) struct Program<'f> {
    pub(crate) functions: &'f [Arc<Function>],
    /// The paths of the program's files, by index, as its panics and `#line` give them.
    pub(crate) files: &'f [String],
    /// What the program's profile tells clang.
    pub(crate) hints: &'f crate::Hints,
    index: HashMap<FnRef, usize>,
    names: Vec<String>,
    pub(crate) cells: Vec<Cell>,
    /// The C declaration of each runtime function or native the program calls.
    pub(crate) externs: BTreeMap<String, String>,
    pub(crate) options: Options,
}

/// The header's own declarations, which no extern repeats.
const IN_HEADER: &[&str] = &[
    "stilt_rt_dup",
    "stilt_rt_drop",
    "stilt_rt_unique",
    "stilt_rt_panic",
    "stilt_rt_list_index",
    "stilt_rt_list_get",
    "stilt_rt_list_slot",
    "stilt_rt_list_push",
    "stilt_rt_list_append_value",
    "stilt_rt_list_push_words",
    "stilt_rt_list_append_words",
    "stilt_rt_alloc_data",
    "stilt_rt_large_shape",
    "stilt_rt_shape_parts",
    "stilt_rt_constant_claim",
    "stilt_rt_constant_share",
    "stilt_rt_constant_done",
    "stilt_rt_fmod",
    "stilt_rt_float_compare",
    "stilt_rt_round",
    "stilt_rt_start",
];

impl<'f> Program<'f> {
    pub(crate) fn new(
        functions: &'f [Arc<Function>],
        files: &'f [String],
        hints: &'f crate::Hints,
        options: Options,
    ) -> Self {
        let index = functions
            .iter()
            .enumerate()
            .map(|(i, f)| (f.name.clone(), i))
            .collect();
        let names = functions
            .iter()
            .map(|f| c_name("f_", &f.name.symbol()))
            .collect();
        Self {
            functions,
            files,
            hints,
            index,
            names,
            cells: Vec::new(),
            externs: BTreeMap::new(),
            options,
        }
    }

    /// Which checks of the operation at `loc` the C drops: those verification proves, in a
    /// build that drops them.
    pub(crate) fn proved(&self, loc: &Operand) -> Proved {
        if self.options.proved {
            Proved::of(loc)
        } else {
            Proved::default()
        }
    }

    /// The index of a compiled function, if the program compiles it.
    pub(crate) fn compiled(&self, f: &FnRef) -> Option<usize> {
        self.index.get(f).copied()
    }

    /// The C name of compiled function `i`, made from its MIR name, which profiles show.
    pub(crate) fn name(&self, i: usize) -> &str {
        &self.names[i]
    }

    /// Declares the runtime function or native `name`, taking `params` words, of the C
    /// result type `result`.
    pub(crate) fn declare_extern(&mut self, name: &str, params: usize, result: &str) -> String {
        if !IN_HEADER.contains(&name) && !self.externs.contains_key(name) {
            let list = if params == 0 {
                "void".to_owned()
            } else {
                vec!["u64"; params].join(", ")
            };
            let decl = format!("extern {result} {name}({list});");
            self.externs.insert(name.to_owned(), decl);
        }
        name.to_owned()
    }

    /// The index of a constant's cell, for its value of the words `words`.
    pub(crate) fn cell(&mut self, f: &FnRef, words: &[Repr]) -> usize {
        if let Some(i) = (self.cells.iter()).position(|c| c.f == *f && *c.words == *words) {
            return i;
        }
        let same = self.cells.iter().filter(|c| c.f == *f).count();
        let mut name = c_name("", &f.symbol());
        if same > 0 {
            name = format!("{name}_{same}");
        }
        self.cells.push(Cell {
            f: f.clone(),
            words: words.into(),
            name,
        });
        self.cells.len() - 1
    }
}

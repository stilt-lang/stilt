//! Calls of foreign functions, which C gives (c.calls, c.finding-functions), as C calls them:
//! each argument converted from the word compiled code holds it in to its C type, and the result
//! back. Where the target's executables load libraries, the function is the one its name gives
//! among those loaded, which the runtime finds at its first call; elsewhere the program declares it
//! under a name of its own, bound by an `asm` label to its symbol, which the target's C library
//! gives (c.build-targets), so that no declaration of a system header can clash with it.

use std::fmt::Write as _;

use stilt_mir::mir::{Arg, Const, Operand};
use stilt_mir::{CType, Foreign};

use crate::CFunctions;
use crate::calls::{Results, Then};
use crate::exports::{c_type, to_word};
use crate::function::Emit;

/// The value of type `t` that the word `w` holds, as C takes it.
fn from_word(w: &str, t: CType) -> String {
    match t {
        CType::F64 => format!("({{ double x_; __builtin_memcpy(&x_, &(u64){{{w}}}, 8); x_; }})"),
        CType::F32 => format!(
            "({{ __UINT32_TYPE__ b_ = (__UINT32_TYPE__){w}; float x_; __builtin_memcpy(&x_, &b_, 4); x_; }})"
        ),
        CType::Bool => format!("({w} != 0)"),
        _ => format!("(({}){w})", c_type(t)),
    }
}

impl Emit<'_, '_> {
    /// Calls the foreign function `c` with `args`, the location first, and gives `dest` its
    /// result.
    pub(crate) fn call_foreign(
        &mut self,
        c: &Foreign,
        args: &[Arg],
        (dest, next, raised): Then,
    ) -> Result<(), String> {
        let mut words = Vec::with_capacity(args.len());
        for a in args {
            let (Arg::Borrow(o) | Arg::Own(o) | Arg::Ref(o)) = a else {
                return Err(format!("a call of {} lends a value", c.name));
            };
            words.push(self.word(o)?);
        }
        let Some((loc, words)) = words.split_first() else {
            return Err(format!("a call of {} has no location", c.name));
        };
        let params: Vec<&str> = c.params.iter().map(|&t| c_type(t)).collect();
        let list = if params.is_empty() {
            "void".to_owned()
        } else {
            params.join(", ")
        };
        let result = c.result.map_or("void", c_type);
        let callee = if self.prog.options.c_functions == CFunctions::Found {
            let find = self.prog.declare_extern("stilt_rt_c_function", 2, "u64");
            self.refs.externs.insert(find.clone());
            let name = self.word(&Operand::Const(Const::Str(c.name.as_str().into())))?;
            format!("(({result} (*)({list})){find}({loc}, {name}))")
        } else {
            let alias = format!("lt_c_{}", c.name);
            let decl = format!("extern {result} {alias}({list}) __asm__(\"{}\");", c.name);
            self.prog.externs.entry(alias.clone()).or_insert(decl);
            self.refs.externs.insert(alias.clone());
            alias
        };
        let values: Vec<String> = (words.iter().zip(&c.params))
            .map(|(w, &t)| from_word(w, t))
            .collect();
        let call = format!("{callee}({})", values.join(", "));
        let results = if let Some(t) = c.result {
            let _ = writeln!(self.out, "{result} c_ = {call};");
            to_word(&mut self.out, "w_", "c_", t);
            vec!["w_".to_owned()]
        } else {
            let _ = writeln!(self.out, "{call};");
            Vec::new()
        };
        self.returned(&Results::Words(results), None, dest, next, raised);
        self.out.push_str("}\n");
        Ok(())
    }
}

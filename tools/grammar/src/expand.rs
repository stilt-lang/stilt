//! Expands the macros of the notation (`list`, `list1` and rules with parameters), and names the
//! classes of tokens, so that every rule is plain EBNF.

use std::collections::{BTreeMap, BTreeSet};

use crate::ebnf::{Expr, RuleDef};
use crate::lexicon;

/// The rules of the grammar in order, each with its body.
#[derive(Debug, Default)]
pub(crate) struct Grammar {
    pub(crate) rules: Vec<(String, Expr)>,
}

impl Grammar {
    pub(crate) fn get(&self, name: &str) -> Option<&Expr> {
        self.rules.iter().find(|(n, _)| n == name).map(|(_, e)| e)
    }

    pub(crate) fn set(&mut self, name: &str, body: Expr) {
        match self.rules.iter_mut().find(|(n, _)| n == name) {
            Some(rule) => rule.1 = body,
            None => self.rules.push((name.to_owned(), body)),
        }
    }
}

struct Expander<'a> {
    params: BTreeMap<&'a str, &'a RuleDef>,
    made: BTreeSet<String>,
    instances: Vec<(String, Expr)>,
}

/// The grammar of the rules without parameters, with the uses of macros replaced by rules of
/// their own.
pub(crate) fn expand(defs: &[RuleDef]) -> Result<Grammar, String> {
    let mut expander = Expander {
        params: defs
            .iter()
            .filter(|d| !d.params.is_empty())
            .map(|d| (d.name.as_str(), d))
            .collect(),
        made: BTreeSet::new(),
        instances: Vec::new(),
    };
    let mut grammar = Grammar::default();
    for def in defs.iter().filter(|d| d.params.is_empty()) {
        let body = expander.resolve(&def.body)?;
        grammar.rules.push((def.name.clone(), body));
    }
    grammar.rules.append(&mut expander.instances);
    Ok(grammar)
}

impl Expander<'_> {
    fn resolve(&mut self, expr: &Expr) -> Result<Expr, String> {
        Ok(match expr {
            Expr::Ref(name) => token_class(name).unwrap_or_else(|| expr.clone()),
            Expr::Call(name, args) => self.instance(name, args)?,
            Expr::Seq(items) => Expr::Seq(self.all(items)?),
            Expr::Alt(items) => Expr::Alt(self.all(items)?),
            Expr::Opt(inner) => Expr::Opt(Box::new(self.resolve(inner)?)),
            Expr::Star(inner) => Expr::Star(Box::new(self.resolve(inner)?)),
            Expr::Lit(_) | Expr::Empty => expr.clone(),
        })
    }

    fn all(&mut self, items: &[Expr]) -> Result<Vec<Expr>, String> {
        items.iter().map(|e| self.resolve(e)).collect()
    }

    /// The rule that stands for `name(args)`, made the first time it is used.
    fn instance(&mut self, name: &str, args: &[Expr]) -> Result<Expr, String> {
        let [Expr::Ref(arg)] = args else {
            return Err(format!("`{name}` takes the name of one rule"));
        };
        let arg = token_class(arg).unwrap_or_else(|| Expr::Ref(arg.clone()));
        let Expr::Ref(arg_name) = &arg else {
            return Err(format!("`{name}` takes the name of one rule"));
        };
        let rule = format!("{name}_{arg_name}");
        if self.made.insert(rule.clone()) {
            let body = match name {
                "list" => Expr::Opt(Box::new(Expr::Ref(format!("list1_{arg_name}")))),
                "list1" => list1(&arg),
                _ => {
                    let def = self
                        .params
                        .get(name)
                        .ok_or(format!("unknown macro `{name}`"))?;
                    let body = substitute(&def.body, &def.params[0], &arg);
                    self.resolve(&body)?
                }
            };
            self.instances.push((rule.clone(), body));
            if name == "list" {
                self.instance("list1", args)?;
            }
        }
        Ok(Expr::Ref(rule))
    }
}

/// `a { "," a } [ "," ]` (expressions.trailing-commas).
fn list1(item: &Expr) -> Expr {
    let comma = || Expr::Lit(",".into());
    Expr::Seq(vec![
        item.clone(),
        Expr::Star(Box::new(Expr::Seq(vec![comma(), item.clone()]))),
        Expr::Opt(Box::new(comma())),
    ])
}

fn substitute(expr: &Expr, param: &str, arg: &Expr) -> Expr {
    let again = |items: &[Expr]| items.iter().map(|e| substitute(e, param, arg)).collect();
    match expr {
        Expr::Ref(name) if name == param => arg.clone(),
        Expr::Call(name, args) => Expr::Call(name.clone(), again(args)),
        Expr::Seq(items) => Expr::Seq(again(items)),
        Expr::Alt(items) => Expr::Alt(again(items)),
        Expr::Opt(inner) => Expr::Opt(Box::new(substitute(inner, param, arg))),
        Expr::Star(inner) => Expr::Star(Box::new(substitute(inner, param, arg))),
        _ => expr.clone(),
    }
}

/// What a name stands for when it names a class of tokens: the rule of the class, or nothing
/// for `DOC`, which is read as a comment.
fn token_class(name: &str) -> Option<Expr> {
    if name == "DOC" {
        Some(Expr::Empty)
    } else if lexicon::is_class(name) {
        Some(Expr::Ref(name.to_lowercase()))
    } else {
        None
    }
}

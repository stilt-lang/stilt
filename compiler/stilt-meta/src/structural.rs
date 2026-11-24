//! The prelude's traits on the values of a run (traits.structural-impls, traits.prelude-traits and
//! traits.show): a type's written impl where it has one, and otherwise the structural impl, which
//! compares, hashes and shows a value by its components, each through its own type's impl; and the
//! text of a splice of an interpolation formatted by its spec (std.width-fill-and-alignment,
//! std.precision and std.invalid-specs).

use std::cmp::Ordering;

use stilt_hir::hir::Name;

use crate::eval::{Flow, Machine, R};
use crate::value::{Value, prelude};

impl<'a> Machine<'a> {
    /// Whether the value's type has a written impl of the prelude trait `name`.
    fn has_impl(&self, v: &Value<'a>, trait_name: &str) -> bool {
        let owner = match v {
            Value::Record(r) => r.0.clone(),
            Value::Variant(x) => match self.image.variant(&x.0) {
                Some((ty, _)) => ty.clone(),
                None => return false,
            },
            _ => return false,
        };
        self.image.impl_of(&prelude(trait_name), &owner).is_some()
    }

    /// Calls the method `method` of the prelude trait `trait_name` on `values`.
    fn trait_call(&mut self, trait_name: &str, method: &str, mut values: Vec<Value<'a>>) -> R<'a> {
        let ty = self.type_of(&values[0]);
        let callee =
            stilt_types::tast::Callee::TraitMethod(prelude(trait_name), Name::from(method), ty);
        let target = self.target_in((&[], None), &callee, &[], &values)?;
        self.apply(target, &mut values)
    }

    /// `a == b`.
    pub(crate) fn equal(&mut self, a: &Value<'a>, b: &Value<'a>) -> Result<bool, Flow<'a>> {
        if let (Value::Window(_), _) | (_, Value::Window(_)) = (a, b) {
            let (a, b) = (self.thaw(a.clone())?, self.thaw(b.clone())?);
            return self.equal(&a, &b);
        }
        if self.has_impl(a, "Eq") {
            return Ok(self
                .trait_call("Eq", "eq", vec![a.clone(), b.clone()])?
                .as_bool());
        }
        Ok(match (a, b) {
            (Value::Bool(x), Value::Bool(y)) => x == y,
            (Value::Int(x, _), Value::Int(y, _)) => x == y,
            #[allow(clippy::float_cmp, reason = "the language compares floats exactly")]
            (Value::Float(x, _), Value::Float(y, _)) => x == y,
            (Value::Str(x), Value::Str(y)) => x.get() == y.get(),
            (Value::Meta(x), Value::Meta(y)) => crate::meta::same(x, y),
            (Value::Map(x), Value::Map(y)) => {
                let (left, right) = (x.entries.get().clone(), y.entries.get().clone());
                return self.entries_equal(&left, &right);
            }
            (Value::Variant(x), Value::Variant(y)) if x.0 != y.0 => false,
            _ => {
                let (xs, ys) = (components(a), components(b));
                if xs.len() != ys.len() {
                    return Ok(false);
                }
                for (x, y) in xs.iter().zip(&ys) {
                    if !self.equal(x, y)? {
                        return Ok(false);
                    }
                }
                true
            }
        })
    }

    /// Whether two maps' entries are the same, each key found in the other with an equal value.
    fn entries_equal(
        &mut self,
        left: &[(Value<'a>, Value<'a>)],
        right: &[(Value<'a>, Value<'a>)],
    ) -> Result<bool, Flow<'a>> {
        if left.len() != right.len() {
            return Ok(false);
        }
        for (key, val) in left {
            match self.find_key(right, key)? {
                Some(at) if self.equal(val, &right[at].1)? => {}
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    /// `Ord.compare(a, b)`.
    pub(crate) fn order(&mut self, a: &Value<'a>, b: &Value<'a>) -> Result<Ordering, Flow<'a>> {
        if let (Value::Window(_), _) | (_, Value::Window(_)) = (a, b) {
            let (a, b) = (self.thaw(a.clone())?, self.thaw(b.clone())?);
            return self.order(&a, &b);
        }
        if self.has_impl(a, "Ord") {
            let v = self.trait_call("Ord", "compare", vec![a.clone(), b.clone()])?;
            return Ok(match &v {
                Value::Variant(x) if &*x.0.name == "Less" => Ordering::Less,
                Value::Variant(x) if &*x.0.name == "Greater" => Ordering::Greater,
                _ => Ordering::Equal,
            });
        }
        Ok(match (a, b) {
            (Value::Bool(x), Value::Bool(y)) => x.cmp(y),
            (Value::Int(x, _), Value::Int(y, _)) => x.cmp(y),
            (Value::Float(x, _), Value::Float(y, _)) => x.total_cmp(y),
            (Value::Str(x), Value::Str(y)) => x.get().as_bytes().cmp(y.get().as_bytes()),
            (Value::Variant(x), Value::Variant(y)) if x.0 != y.0 => {
                let index = |item| self.image.variant(item).map_or(0, |v| v.1);
                index(&x.0).cmp(&index(&y.0))
            }
            _ => {
                let (xs, ys) = (components(a), components(b));
                for (x, y) in xs.iter().zip(&ys) {
                    let c = self.order(x, y)?;
                    if c != Ordering::Equal {
                        return Ok(c);
                    }
                }
                xs.len().cmp(&ys.len())
            }
        })
    }

    /// `Hash.hash(v)`: FNV-1a over the components, whose values programs can't observe.
    pub(crate) fn hash(&mut self, v: &Value<'a>) -> Result<u64, Flow<'a>> {
        if let Value::Window(_) = v {
            let part = self.thaw(v.clone())?;
            return self.hash(&part);
        }
        if self.has_impl(v, "Hash") {
            return Ok(u64::try_from(
                self.trait_call("Hash", "hash", vec![v.clone()])?.as_int() & i128::from(u64::MAX),
            )
            .unwrap_or(0));
        }
        let mix = |h: u64, x: u64| (h ^ x).wrapping_mul(0x100_0000_01b3);
        let start = 0xcbf2_9ce4_8422_2325_u64;
        Ok(match v {
            #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
            Value::Int(x, _) => mix(start, *x as u64),
            Value::Bool(b) => mix(start, u64::from(*b)),
            Value::Str(s) => s.get().bytes().fold(start, |h, c| mix(h, u64::from(c))),
            _ => {
                let mut h = start;
                for x in components(v) {
                    h = mix(h, self.hash(&x)?);
                }
                h
            }
        })
    }

    /// The text of a value, as `show` or `show_nested` gives it.
    pub(crate) fn show(&mut self, method: &str, v: Value<'a>) -> Result<String, Flow<'a>> {
        if self.has_impl(&v, "Show") {
            return Ok(self
                .trait_call("Show", method, vec![v])?
                .as_str()
                .to_owned());
        }
        let nested = |m: &mut Self, xs: &[Value<'a>]| -> Result<Vec<String>, Flow<'a>> {
            xs.iter()
                .map(|x| m.show("show_nested", x.clone()))
                .collect()
        };
        Ok(match &v {
            Value::Int(x, _) => x.to_string(),
            Value::Float(x, f32) => float_text(*x, *f32),
            Value::Bool(b) => b.to_string(),
            Value::Str(s) if method == "show_nested" => stilt_runtime::quoted(s.get()),
            Value::Str(s) => s.get().clone(),
            Value::Tuple(xs) if xs.len() == 1 => format!("({},)", nested(self, xs)?[0]),
            Value::Tuple(xs) => format!("({})", nested(self, xs)?.join(", ")),
            Value::List(xs) => format!("[{}]", nested(self, &xs.get().clone())?.join(", ")),
            Value::Map(m) => {
                let mut shown = Vec::new();
                for (k, x) in m.entries.get().clone() {
                    let k = self.show("show_nested", k)?;
                    shown.push(format!("{k}: {}", self.show("show_nested", x)?));
                }
                format!("{{{}}}", shown.join(", "))
            }
            Value::Variant(x) if x.1.is_empty() => x.0.name.to_string(),
            Value::Variant(x) => format!("{}({})", x.0.name, nested(self, &x.1)?.join(", ")),
            Value::Record(r) => self.show_record(r)?,
            Value::Window(_) => {
                let part = self.thaw(v.clone())?;
                self.show(method, part)?
            }
            Value::Meta(_) | Value::Closure(_) | Value::Func(_) => String::new(),
            Value::Handler(_) | Value::Shared(_) | Value::Iter(_) | Value::Deferred(_) => {
                unreachable!("handlers, shared values, iterators and lazy values have no `Show`")
            }
        })
    }

    fn show_record(
        &mut self,
        r: &(
            stilt_hir::hir::Item,
            crate::value::Counted<Vec<(Name, Value<'a>)>>,
        ),
    ) -> Result<String, Flow<'a>> {
        let mut fields = Vec::new();
        for (name, x) in r.1.iter() {
            fields.push(format!("{name}: {}", self.show("show_nested", x.clone())?));
        }
        Ok(if r.0.is_record() {
            format!("{{ {} }}", fields.join(", "))
        } else if fields.is_empty() {
            format!("{} {{}}", r.0.name)
        } else {
            format!("{} {{ {} }}", r.0.name, fields.join(", "))
        })
    }

    /// The structural impl of the method `name` of a prelude trait.
    pub(crate) fn structural(&mut self, name: &str, values: &[Value<'a>]) -> R<'a> {
        match (name, values) {
            ("eq", [a, b]) => Ok(Value::Bool(self.equal(a, b)?)),
            ("compare", [a, b]) => {
                let name = match self.order(a, b)? {
                    Ordering::Less => "Less",
                    Ordering::Equal => "Equal",
                    Ordering::Greater => "Greater",
                };
                Ok(Value::variant(prelude(name), Vec::new()))
            }
            ("hash", [v]) => Ok(Value::Int(
                i128::from(self.hash(v)?),
                crate::value::IntKind::U64,
            )),
            ("show" | "show_nested", [v]) => Ok(Value::str(self.show(name, v.clone())?)),
            _ => unreachable!(
                "a trait without a structural impl has a written one for every type it is called on, as checking found: `{name}`"
            ),
        }
    }
}

/// The components of a value that its structural impls go through.
fn components<'a>(v: &Value<'a>) -> Vec<Value<'a>> {
    match v {
        Value::Tuple(xs) => xs.to_vec(),
        Value::List(xs) => xs.get().clone(),
        Value::Variant(x) => x.1.to_vec(),
        Value::Record(r) => r.1.iter().map(|(_, x)| x.clone()).collect(),
        _ => Vec::new(),
    }
}

/// The text of a float, as numbers.printing-floats prints it.
pub(crate) fn float_text(x: f64, f32: bool) -> String {
    #[allow(clippy::cast_possible_truncation)]
    let bits = if f32 {
        u64::from((x as f32).to_bits())
    } else {
        x.to_bits()
    };
    stilt_runtime::shown_float(f32, bits)
}

/// The text of a splice of an interpolation, `shown` formatted by its spec, if it has one.
pub(crate) fn formatted(v: &Value<'_>, shown: String, spec: Option<&str>) -> String {
    let Some(words) = spec.and_then(stilt_mir::spec_words) else {
        return shown;
    };
    match v {
        Value::Int(x, k) => {
            #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
            let bits = *x as i64 as u64;
            stilt_runtime::formatted(u64::from(k.0), bits, "", words)
        }
        Value::Float(x, f32) => {
            #[allow(clippy::cast_possible_truncation)]
            let bits = if *f32 {
                u64::from((*x as f32).to_bits())
            } else {
                x.to_bits()
            };
            stilt_runtime::formatted(if *f32 { 8 } else { 9 }, bits, "", words)
        }
        _ => stilt_runtime::formatted(255, 0, &shown, words),
    }
}

//! The code of a descriptor's thunk (meta.shapes): it makes the descriptor of the
//! type its form describes, from the witness and the descriptor of each type parameter that the
//! closure holds: its case, name, witness, table of impls and the fields of its case, whose
//! parts it describes by thunks.

use stilt_hir::decls::{Lookup, TypeDefInfo};
use stilt_hir::hir::{Item, Name};
use stilt_types::ty::{FLOAT_TYPES, INTEGER_TYPES, SHAPE_CASES, Ty, instantiate, is_array};

use super::{DESC_LEN, IDENT, IMPLS, desc_ty};
use crate::described::{Access, Described, Piece};
use crate::lower::{Conv, Cx, Lower};
use crate::mir::{Function, Heapness, Local, Operand, ParamMode, Repr};
use crate::repr::num_kind;
use crate::{FnRef, Held};

/// The case of meta.shapes that a type's shape is, if it has one.
pub(crate) fn shape_case(decls: &dyn Lookup, ty: &Ty) -> Option<&'static str> {
    let declared = |item: &Item| match decls.type_info(item).map(|i| &i.def) {
        Some(TypeDefInfo::Record(_)) => Some("Record"),
        Some(TypeDefInfo::Variants(_)) => Some("Variants"),
        _ => None,
    };
    match ty {
        Ty::Tuple(ts) if ts.is_empty() => Some("Unit"),
        Ty::Tuple(_) => Some("Tuple"),
        Ty::Con(item, _) if item.is_record() => Some("Record"),
        Ty::Con(item, _) if is_array(item) => Some("Array"),
        Ty::Con(item, _) if &*item.home == "std.prelude" => {
            let name = &*item.name;
            if INTEGER_TYPES.contains(&name) {
                Some("Int")
            } else if FLOAT_TYPES.contains(&name) {
                Some("Float")
            } else {
                match name {
                    "bool" => Some("Bool"),
                    "str" => Some("Str"),
                    "Option" => Some("Option"),
                    "List" => Some("List"),
                    // A set is a record of the prelude, whose shape is its own (meta.shapes).
                    "Set" => Some("Set"),
                    "Map" => Some("Map"),
                    _ => declared(item),
                }
            }
        }
        Ty::Con(item, _) => declared(item),
        _ => None,
    }
}

/// The number of a case, its place in meta.shapes counted from 1; 0 for a type without a shape.
pub(crate) fn kind_number(case: Option<&str>) -> u64 {
    case.and_then(|c| SHAPE_CASES.iter().position(|s| *s == c))
        .map_or(0, |i| i as u64 + 1)
}

/// The number of type parameters a form holds.
fn params_count(d: &Described) -> u32 {
    match d {
        Described::Con(_, ds) | Described::Tuple(ds) => {
            ds.iter().map(params_count).max().unwrap_or(0)
        }
        Described::Param(i) => i + 1,
        Described::Other(pieces, _) => pieces
            .iter()
            .map(|p| match p {
                Piece::Param(i) => i + 1,
                Piece::Text(_) => 0,
            })
            .max()
            .unwrap_or(0),
        Described::Value(_) => 0,
    }
}

/// The code of the thunk of a descriptor of the form `d`, which gives it new.
pub(crate) fn describe(cx: &Cx<'_>, f: &FnRef, d: &Described) -> Option<Function> {
    let mut l = Lower::new(cx, f.clone(), true);
    l.ret = Conv::of(desc_ty());
    l.open_form(d);
    let desc = match d {
        Described::Param(i) => l.descriptor(&Lower::numbered_ty(*i)),
        // A type without a shape and without impls, whose name is its identity.
        Described::Other(pieces, witness) => {
            let name = l.type_name(pieces);
            let ident = l.joined(pieces, None, IDENT);
            let impls = l.no_impls();
            let fields = std::array::from_fn(|_| (Operand::word(0), Heapness::Static(false)));
            l.desc_object(0, (name, ident), Operand::word(*witness), impls, fields)
        }
        _ => {
            let ty = d.ty()?;
            l.describe_ty(&ty)
        }
    };
    l.return_(vec![desc]);
    Some(l.into_function())
}

impl Lower<'_> {
    /// Takes the closure of a form's code, and brings the type parameters it holds into scope,
    /// each held in a word, with its witness, its descriptor, and a dictionary of each trait of
    /// the table, from the descriptor's, 0 where it has none. The code takes and raises as a
    /// closure's does.
    pub(crate) fn open_form(&mut self, d: &Described) -> Local {
        let env = self.b.param(Repr::Heap, ParamMode::Borrowed, None);
        self.raises_to_slot = true;
        self.err = Conv::boxed(Ty::Error);
        let n = params_count(d);
        let len = 1 + 2 * n;
        let traits = self.table_traits();
        let tlen = u32::try_from(traits.len()).expect("under 4G traits");
        for i in 0..n {
            let w = self.borrowed_field(env, len, 1 + 2 * i, Repr::Scalar);
            let desc = Operand::Local(self.borrowed_field(env, len, 2 + 2 * i, Repr::Heap));
            let impls = self.read(desc.clone(), DESC_LEN, IMPLS, Repr::Heap);
            let dicts = (0..tlen)
                .zip(&traits)
                .map(|(j, t)| (t.clone(), self.read(impls.clone(), tlen, j, Repr::Heap)))
                .collect();
            let ty = Self::numbered_ty(i);
            self.push_generic(ty.clone(), w, dicts, Some(&Held::Word));
            self.set_descriptor(&ty, desc);
        }
        env
    }

    /// A descriptor's object, from its kind, its name and identity, its witness, its table of
    /// impls with their arguments, and the fields of its case.
    pub(crate) fn desc_object(
        &mut self,
        kind: u64,
        (name, ident): (Operand, Operand),
        witness: Operand,
        (impls, impl_args): (Operand, Operand),
        fields: [(Operand, Heapness); 4],
    ) -> Operand {
        let mut all = vec![
            (Operand::word(kind), Heapness::Static(false)),
            (name, Heapness::Static(true)),
            (witness, Heapness::Static(false)),
            (impls, Heapness::Static(true)),
        ];
        all.extend(fields);
        all.push((ident, Heapness::Static(true)));
        all.push((impl_args, Heapness::Static(true)));
        debug_assert_eq!(all.len(), DESC_LEN as usize);
        self.alloc(0, all)
    }

    /// The descriptor of a type with a shape, or of one without that has impls.
    fn describe_ty(&mut self, ty: &Ty) -> Operand {
        let case = shape_case(&self.decls(), ty);
        let name = {
            let pieces = Self::numbered_pieces(ty);
            self.type_name(&pieces)
        };
        let ident = {
            let pieces = Self::numbered_ident(std::slice::from_ref(ty));
            self.joined(&pieces, None, IDENT)
        };
        let witness = self.witness(ty);
        let fields = self.case_fields(case, ty);
        let parts = super::impls::Parts {
            case,
            witness: &witness,
            fields: &fields,
        };
        let impls = self.impls(ty, &parts);
        self.desc_object(kind_number(case), (name, ident), witness, impls, fields)
    }

    /// The fields of a descriptor that its case gives.
    fn case_fields(&mut self, case: Option<&str>, ty: &Ty) -> [(Operand, Heapness); 4] {
        let scalar = |w: u64| (Operand::word(w), Heapness::Static(false));
        let heap = |o: Operand| (o, Heapness::Static(true));
        let args = match ty {
            Ty::Con(_, args) => args.clone(),
            _ => Vec::new(),
        };
        let mut fields = [scalar(0), scalar(0), scalar(0), scalar(0)];
        match case {
            Some("Int") => fields[0] = scalar(num_kind(ty).map_or(0, crate::mir::NumKind::code)),
            Some("Float") => fields[0] = scalar(u64::from(ty.is_prelude("f64"))),
            Some("Option" | "List" | "Set" | "Map") => {
                for (i, a) in args.iter().take(2).enumerate() {
                    fields[i] = heap(self.thunk(a));
                }
                if case == Some("Option") {
                    fields[2] = heap(self.access(ty, Access::OptionGet));
                    fields[3] = heap(self.access(ty, Access::OptionMake));
                }
            }
            Some("Array") => {
                let (elem, n) = ty.arrayed().expect("an array type");
                let n = self.value_of(n).unwrap_or(0);
                fields[0] = heap(self.thunk(elem));
                fields[1] = scalar(u64::try_from(n.max(0)).unwrap_or(0));
                fields[2] = heap(self.access(ty, Access::ArrayGet));
                fields[3] = heap(self.access(ty, Access::ArrayMake));
            }
            Some("Tuple" | "Record") => {
                let parts = self.named_parts(ty);
                fields[0] = scalar(parts.len() as u64);
                fields[1] = heap(self.entries(ty, &parts, false));
                fields[2] = heap(self.access(ty, Access::Build));
            }
            Some("Variants") => {
                let cases = self.cases(ty);
                fields[0] = scalar(cases.len() as u64);
                fields[1] = heap(self.entries(ty, &cases, true));
            }
            _ => {}
        }
        fields
    }

    /// A closure of an accessor of a type's values.
    fn access(&mut self, ty: &Ty, op: Access) -> Operand {
        let t = self.template(ty);
        self.closure_of_form(FnRef::Access(Box::new(t.described), op), &t.params)
    }

    /// The fields of a record or a tuple type, by name, in the order of meta.shapes.
    pub(crate) fn named_parts(&self, ty: &Ty) -> Vec<(Name, Ty)> {
        match ty {
            Ty::Tuple(ts) => ts
                .iter()
                .enumerate()
                .map(|(i, t)| (Name::from(i.to_string().as_str()), t.clone()))
                .collect(),
            Ty::Con(item, args) if item.is_record() => item
                .record_fields()
                .into_iter()
                .zip(args.iter().cloned())
                .collect(),
            Ty::Con(item, args) => match self.decls().type_info(item) {
                Some(info) => match &info.def {
                    TypeDefInfo::Record(fs) => fs
                        .iter()
                        .map(|(f, t)| (*f, instantiate(t, &info.params, args)))
                        .collect(),
                    _ => Vec::new(),
                },
                None => Vec::new(),
            },
            _ => Vec::new(),
        }
    }

    /// The variants of a variant type, each with the tuple of its payload.
    pub(crate) fn cases(&self, ty: &Ty) -> Vec<(Name, Ty)> {
        let Ty::Con(item, args) = ty else {
            return Vec::new();
        };
        let decls = self.decls();
        let Some(info) = decls.type_info(item) else {
            return Vec::new();
        };
        match &info.def {
            TypeDefInfo::Variants(vs) => vs
                .iter()
                .map(|(v, payload)| {
                    let ts = payload.iter().map(|t| instantiate(t, &info.params, args));
                    (*v, Ty::Tuple(ts.collect()))
                })
                .collect(),
            _ => Vec::new(),
        }
    }

    /// The entries of a type's fields or variants, a list, which loops index: each a data
    /// object of its name, place, thunk, witness and accessors.
    fn entries(&mut self, ty: &Ty, parts: &[(Name, Ty)], variants: bool) -> Operand {
        let mut all = Vec::new();
        for (i, (name, part)) in parts.iter().enumerate() {
            let i32 = u32::try_from(i).expect("under 4G fields");
            let name = Operand::Const(crate::mir::Const::Str(name.as_ref().into()));
            let mut entry = vec![
                (name, Heapness::Static(true)),
                (Operand::word(i as u64), Heapness::Static(false)),
                (self.thunk(part), Heapness::Static(true)),
                (self.witness(part), Heapness::Static(false)),
            ];
            if variants {
                entry.push((
                    self.access(ty, Access::CaseGet(i32)),
                    Heapness::Static(true),
                ));
                entry.push((
                    self.access(ty, Access::CaseMake(i32)),
                    Heapness::Static(true),
                ));
            } else {
                entry.push((self.access(ty, Access::Field(i32)), Heapness::Static(true)));
            }
            all.push(vec![self.alloc(0, entry)]);
        }
        self.list_literal(all, &Ty::list(desc_ty()))
    }
}

//! The type constructors of the standard library that checking and lowering tell apart, and the
//! parts of their types: views and iterators (views.view-types and views.making-iterator), shared
//! values (shared.std-sync) and arrays (generics.arrays).

use stilt_hir::hir::Item;

use super::Ty;

/// Whether a type constructor is the prelude's `name`.
#[must_use]
pub fn is_prelude(item: &Item, name: &str) -> bool {
    &*item.home == "std.prelude" && &*item.name == name
}

/// Whether a type constructor is `std.array`'s `Array` (generics.arrays).
#[must_use]
pub fn is_array(item: &Item) -> bool {
    &*item.home == "std.array" && &*item.name == "Array"
}

/// Whether a type constructor is `std.sync`'s `Shared` (shared.std-sync).
#[must_use]
pub fn is_shared(item: &Item) -> bool {
    &*item.home == "std.sync" && &*item.name == "Shared"
}

/// Whether a type constructor is `std.view`'s `View` (`name` "View") or `Iter` ("Iter"), the
/// native types of views.std-view.
#[must_use]
pub fn is_view_type(item: &Item, name: &str) -> bool {
    &*item.home == "std.view" && &*item.name == name
}

impl Ty {
    /// The type `T` of the value a `Shared<T>` reaches (shared.std-sync).
    #[must_use]
    pub fn shared(&self) -> Option<&Ty> {
        let Self::Con(item, args) = self else {
            return None;
        };
        args.first().filter(|_| is_shared(item))
    }

    /// The viewed type `T` of a `View<T>`.
    #[must_use]
    pub fn viewed(&self) -> Option<&Ty> {
        match self {
            Self::Con(item, args) if is_view_type(item, "View") => args.first(),
            _ => None,
        }
    }

    /// The element type `U` of an `Iter<U>`.
    #[must_use]
    pub fn iterated(&self) -> Option<&Ty> {
        match self {
            Self::Con(item, args) if is_view_type(item, "Iter") => args.first(),
            _ => None,
        }
    }

    /// The element type `T` and the size of an `Array<T, n>` (generics.arrays).
    #[must_use]
    pub fn arrayed(&self) -> Option<(&Ty, &Ty)> {
        match self {
            Self::Con(item, args) if is_array(item) => match args.as_slice() {
                [elem, size] => Some((elem, size)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The element type `U` of a `List<U>`.
    #[must_use]
    pub fn listed(&self) -> Option<&Ty> {
        match self {
            Self::Con(item, args) if is_prelude(item, "List") => args.first(),
            _ => None,
        }
    }

    /// Whether the type is a view type: a `View`, an `Iter`, or an `Option` of one
    /// (views.view-types). A closure that captures a view is one too, which its type doesn't tell.
    #[must_use]
    pub fn is_view(&self) -> bool {
        match self {
            Self::Con(item, args) if is_prelude(item, "Option") => {
                args.first().is_some_and(Ty::is_view)
            }
            Self::Con(item, _) => is_view_type(item, "View") || is_view_type(item, "Iter"),
            _ => false,
        }
    }

    /// Whether the type is `View<T>` itself, which a `var` binding or an `inout` parameter of
    /// it writes through (projections.writable-bindings and projections.places-through-views).
    #[must_use]
    pub fn is_window(&self) -> bool {
        matches!(self, Self::Con(item, _) if is_view_type(item, "View"))
    }

    /// Whether a view can view a value of the type, a `str` or a `List` (views.viewable-types). The
    /// error type is taken to be (errors.error-type).
    #[must_use]
    pub fn is_viewable(&self) -> bool {
        self.is_prelude("str") || self.is_prelude("List") || *self == Ty::Error
    }

    /// Whether a value of the type stores a view, which only a local binding, a parameter, a
    /// result or a capture may hold (views.view-types): a view type in a list, a map, a tuple or a
    /// type argument of a declared type other than `Option`, `View` and `Iter`. A function
    /// type's parameters and result may be views, but not what they store.
    #[must_use]
    pub fn stores_view(&self) -> bool {
        match self {
            Self::Con(item, args) => {
                let free = is_prelude(item, "Option")
                    || is_view_type(item, "View")
                    || is_view_type(item, "Iter");
                args.iter()
                    .any(|a| a.stores_view() || (!free && a.is_view()))
            }
            Self::Tuple(ts) => ts.iter().any(|t| t.is_view() || t.stores_view()),
            Self::Spread(s) => s.elem.is_view() || s.elem.stores_view(),
            Self::Fn(f) => {
                f.params.iter().any(|(_, t)| t.stores_view())
                    || f.ret.stores_view()
                    || f.row
                        .raise
                        .as_deref()
                        .is_some_and(|t| t.is_view() || t.stores_view())
            }
            Self::App(_, args) => args.iter().any(|a| a.is_view() || a.stores_view()),
            Self::Param(_)
            | Self::SelfTy
            | Self::Var(_)
            | Self::Handler(_)
            | Self::Value(_)
            | Self::Error => false,
        }
    }
}

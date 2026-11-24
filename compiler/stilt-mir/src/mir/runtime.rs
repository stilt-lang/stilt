//! The functions of the runtime that compiled code calls directly, with how they treat their
//! arguments' references.

use serde::{Deserialize, Serialize};

/// A function of the runtime that compiled code calls directly. It can't raise, and it runs no
/// code of the program, except where it says so.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Runtime {
    /// `(len, tag)`: a data object whose fields the code then sets.
    AllocData,
    /// `(slot)`: the object the slot holds, made unique.
    Unique,
    /// `(object, len, taken, known)`: releases the reference the object's word holds, which it
    /// consumes, and gives the memory of the object for one of `len` words built in its place
    /// when that was the last reference to a data object of `len` words, and 0 otherwise
    /// (`stilt_runtime`'s `object::reuse`). The code takes a reference to each field that a bit
    /// of the constant `taken` names, through the word it read of it: the kept object's, or a new
    /// one; a kept object's other heap words are released. The constant `known` tells what the
    /// object is known to be ([`crate::mir::known_object`]): a variant's, of which only the count
    /// needs testing.
    Reclaim,
    /// `(memory)`: gives back memory that [`Runtime::Reclaim`] kept and nothing built in, if it
    /// isn't 0.
    Discard,
    /// `(cap, shape)`: an empty list with room for `cap` elements of the shape
    /// (`crate::shape`).
    ListNew,
    /// `(list, elem, words..)`: appends an element, whose words it consumes, to a list that
    /// nothing else references. `elem` is the elements' shape, a constant, or for a value of a
    /// type parameter, its witness, with the one word that holds it where a type parameter
    /// stands.
    ListPush,
    /// `(slot, elem, words..)`: appends an element, whose words it consumes, to the list a slot
    /// holds, made unique, `elem` being as for [`Runtime::ListPush`].
    ListAppend,
    /// `(list)`: the list's length.
    ListLen,
    /// `(list, i, elem, word)`: word `word` of element `i`, in bounds, of a list of elements of
    /// the constant shape `elem`, borrowed: a narrow scalar widened to a word.
    ListAt,
    /// `(loc, list, i, elem, word)`: word `word` of `xs[i]`, borrowed.
    ListIndex,
    /// `(loc, slot, i, elem)`: a pointer to `xs[i]` in a unique list, of elements of the
    /// constant shape `elem`.
    ListSlot,
    /// `(slot, i, elem)`: a pointer to element `i`, in bounds, of the list a slot holds, made
    /// unique, of elements of the constant shape `elem`.
    ListSlotAt,
    /// `(loc, slot, i, elem)`: a pointer to `xs[i]` in the list a slot holds, which nothing
    /// else references, of elements of the constant shape `elem`.
    ListElement,
    /// `(slot, i, elem)`: a pointer to element `i`, in bounds, of the list a slot holds, which
    /// nothing else references, of elements of the constant shape `elem`.
    ListElementAt,
    /// `(loc, list, i, shape)`: `xs[i]` of a list of values of a type parameter, whose witness
    /// is `shape`, in the one word that holds it where a type parameter stands, with
    /// references of its own.
    ListGet,
    /// `(loc, slot, i, x)`: `xs[i] = x` on the list a slot holds, made unique, of values of a
    /// type parameter, `x` in the one word that holds it, which it consumes.
    ListPut,
    /// `(pointer, x, elem)`: stores the scalar `x` in the element a pointer points to, of the
    /// constant shape `elem` of a scalar narrower than a word.
    StorePacked,
    /// `(words..)`: the shape of a value of these words, each 0 for a scalar, 1 for a heap
    /// word, or the witness of a type parameter.
    Shape,
    /// `(count, shape, ..)`: the shape of a value made of parts, each `count` values of a shape one
    /// after the other, as an array held in memory is its elements (generics.large-arrays).
    ShapeParts,
    /// `(loc, eq, hash, map, k)`: a pointer to the words of `m[k]`, which [`Runtime::MapWord`]
    /// reads. It calls the key type's `hash` and `eq`.
    MapIndex,
    /// `(map, position)`: the position of the first entry at or after `position`, or
    /// `u64::MAX`.
    MapNext,
    /// `(map, position)`: a pointer to the words of the key and of the value of an entry,
    /// which [`Runtime::MapWord`] reads.
    MapKeyAt,
    /// `(map, position)`: a pointer to the words of the value of the entry.
    MapValueAt,
    /// `(map, pointer, i)`: word `i` of the key or the value of `map` that `pointer` points to,
    /// borrowed from the map, which it names so that the map lives as long as the word.
    MapWord,
    /// `(map)`: a pointer to the words of the map's default, or 0 when it has none.
    MapDefault,
    /// `(slot, shape)`: a pointer to the words of the value that the slot holds in one word, of
    /// this shape: for a value of several words, the fields of its box, made unique, and
    /// otherwise the slot.
    InoutWords,
    /// `(shape, i)`: a word whose lowest bit tells whether word `i` of a value of this shape is
    /// a heap word, for a value of more words than a shape's mask tells (`crate::shape`).
    ShapeHeap,
    /// `(map, pointer, value)`: the key, or the value if `value` is set, of the map whose words
    /// `pointer` points to, in the one word that holds it where a type parameter stands, with
    /// references of its own: as code past the caps of instances holds a value of several words,
    /// a new box.
    MapHeld,
    /// `(loc, eq, hash, slot, k, v)`: `m[k] = v` on the map a slot holds, made unique. It
    /// borrows `k` and consumes `v`, and calls the key type's `hash` and `eq`.
    MapStore,
    /// `(list, start, end)`: the elements from `start` up to `end`, which are in bounds.
    ListSlice,
    /// `(a, b)`: whether two strings are equal.
    StrEq,
    /// `(a, b, heap)`: whether two values are the same by structure, for constant patterns
    /// (patterns.constants).
    Same,
    /// `(a, b)`: the order of two strings, as an `Ordering`.
    StrCompare,
    /// `()`: ends the program as running out of memory does, for a value larger than any
    /// that compiled code holds (generics.large-arrays).
    OutOfMemory,
    /// `()`: the hash a structural hash starts from.
    HashStart,
    /// `(h, x)`: the hash `h` with the word `x` mixed in.
    HashMix,
    /// `(x)`: the hash of an integer or a `bool`.
    HashWord,
    /// `(s)`: the hash of a string.
    HashStr,
    /// `(kind, value, shown, spec, spec)`: a splice formatted by its spec
    /// (std.width-fill-and-alignment, std.precision, std.integer-kinds, std.scientific-notation and
    /// std.format-special-values). `kind` is a number's kind, or 255 for a value whose text is
    /// `shown`.
    Format,
    /// The structural impls of lists and maps (traits.structural-impls), which take the location,
    /// the dictionaries of the element types, then the values, and call the elements' impls.
    ListEq,
    /// The structural `Ord` of lists.
    ListCompare,
    /// The structural `Hash` of lists.
    ListHash,
    /// The structural `Show` of lists.
    ListShow,
    /// The structural impls of tuples that spread a pack whose length is known at run time
    /// only, which take the location, the list of the elements' dictionaries,
    /// then the values, lists of their elements' boxes.
    PackEq,
    /// The structural `Ord` of such tuples.
    PackCompare,
    /// The structural `Hash` of such tuples.
    PackHash,
    /// The structural `Show` of such tuples.
    PackShow,
    /// `(loc, key eq, key hash, value eq, a, b)`.
    MapEq,
    /// `(loc, key show, value show, m)`.
    MapShow,
    /// `(parts)`: the concatenation of a list of strings.
    Concat,
    /// `(a, b)`, `(a, b, c)` and `(a, b, c, d)`: the concatenation of the strings, which it
    /// borrows.
    Concat2,
    /// `(a, b, c)`.
    Concat3,
    /// `(a, b, c, d)`.
    Concat4,
    /// `(a, b)`, `(a, b, c)` and `(a, b, c, d)`: the concatenation of the strings, which takes
    /// `a` and appends to it in place when nothing else references it, as a concatenation whose
    /// first part is released after it becomes ([`crate::opt::optimize_counted`]).
    ConcatOnto2,
    /// `(a, b, c)`.
    ConcatOnto3,
    /// `(a, b, c, d)`.
    ConcatOnto4,
    /// `(kind, n)`: the decimal text of an integer of the kind.
    ShowInt,
    /// `(kind, text)`: whether `text` is exactly the decimal text of an integer of the kind, and
    /// that integer, for `std.meta`'s `parse` (meta.shapes).
    IntValid,
    /// `(kind, text)`: the integer that [`Runtime::IntValid`] has found `text` to write.
    IntParse,
    /// `(kind, x)`: the text of a float of the kind.
    ShowFloat,
    /// `(b)`: `true` or `false`.
    ShowBool,
    /// `(s)`: a string quoted, as `show_nested` shows it.
    Quote,
    /// The values of a property's case, read from its tape (tests.property-cases;
    /// `stilt_runtime::Tape`). `(tape)`: the next word, a scalar, a length or a variant's
    /// number.
    PropWord,
    /// `(tape)`: the next string, new.
    PropStr,
    /// `(key, value)`: an empty map of keys and values of these shapes.
    PropMap,
    /// `(tape, loc, eq, hash, slot, k, v)`: [`Runtime::MapStore`], noting on the tape the
    /// position of the key's entry.
    PropStore,
    /// `(shown, other)`: what the current test says of its failure: the error it raised, as
    /// `Show` shows it, when `other` is 0, and otherwise the two sides of the comparison that
    /// gave `false`.
    TestNote,
    /// `(loc, callee)`: counts, in a profiled run, a call through a function value or a
    /// dictionary at `loc` that reaches the function whose address the static string `callee`
    /// holds (builds.profiles).
    ProfileCall,
    /// `(names)`: loads the C libraries that the program links, whose names the static string
    /// `names` gives, each ended by a newline, before any of its code runs (c.loading-libraries).
    CLoad,
    /// A function of the handlers of handlers.handler-literals.
    Effects(Effects),
    /// A function of the views and iterators of views.std-view.
    Views(Views),
    /// The functions of `when` (shared.when).
    Shared(Shared),
}

/// The functions of the runtime for views and iterators (views.std-view), which compiled code calls
/// directly: a view is its source's word, with a reference of its own, and two offsets; an
/// iterator is an object of the runtime.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Views {
    /// `(loc, source, start, end)`: the source's word, with a reference of
    /// its own, for a view of `start..end`, which it checks (views.making-view).
    Of,
    /// `(source)`: the length of a string, in bytes, or of a list.
    Len,
    /// `(loc, source, start, end, s, e)`: as [`Views::Of`], for the part `s..e` of the
    /// view `start..end`, counted from its start.
    Part,
    /// `(loc, start, end, i)`: the index into the source of `v[i]`, which it checks
    /// (views.functions-of-views).
    Index,
    /// `(loc, eq, a, a_start, a_end, b, b_start, b_end)`: whether two views' parts are equal,
    /// compared in place, through the elements' `Eq` dictionary `eq` for views of lists and
    /// byte by byte for views of strings, which pass 0 (views.functions-of-views).
    Eq,
    /// `(loc, ord, a, a_start, a_end, b, b_start, b_end)`: the order of two views' parts, as
    /// for [`Views::Eq`], through the elements' `Ord`.
    Compare,
    /// `(loc, hash, source, start, end)`: the hash of a view's part, in place, through the
    /// elements' `Hash` for a view of a list.
    Hash,
    /// `(loc, show, source, start, end, nested)`: the text of a view's part, a new string, as
    /// `show` gives it, or `show_nested` when `nested` isn't 0, through the elements' `Show` for
    /// a view of a list.
    Show,
    /// `(it)`: the state of a `for` loop over an iterator (views.for-over-view), a new object.
    State,
    /// `(loc, it, state)`: whether the loop has a next element, which it pulls into the state,
    /// calling the closures of the iterator's adapters.
    Next,
    /// `(state)`: the element pulled, in the one word that holds it where a type parameter
    /// stands, with references of its own.
    Take,
    /// `(loc, list, i, x)`: `v[i] = x` on the list a writable view holds, `i` its index into
    /// the list, in bounds, of values of a type parameter, `x` in the one word that holds it,
    /// which it consumes; the list's count isn't checked (projections.places-through-views).
    Put,
}

impl Runtime {
    /// The runtime's name for the function.
    #[must_use]
    pub fn symbol(self) -> &'static str {
        if let Some(name) = self.collection_symbol() {
            return name;
        }
        match self {
            Runtime::AllocData => "stilt_rt_alloc_data",
            Runtime::Unique => "stilt_rt_unique",
            Runtime::Reclaim => "stilt_rt_reclaim",
            Runtime::Discard => "stilt_rt_discard",
            Runtime::StorePacked => "store_packed",
            Runtime::Shape => "shape",
            Runtime::ShapeParts => "stilt_rt_shape_parts",
            Runtime::ShapeHeap => "stilt_rt_shape_heap",
            Runtime::InoutWords => "stilt_rt_inout_words",
            Runtime::StrEq => "stilt_rt_str_eq",
            Runtime::Same => "stilt_rt_same",
            Runtime::StrCompare => "stilt_rt_str_compare",
            Runtime::HashStart => "stilt_rt_hash_start",
            Runtime::OutOfMemory => "stilt_rt_out_of_memory",
            Runtime::HashMix => "stilt_rt_hash_mix",
            Runtime::HashWord => "stilt_rt_hash_word",
            Runtime::HashStr => "stilt_rt_hash_str",
            Runtime::Format => "stilt_rt_format",
            Runtime::ListEq => "stilt_rt_list_eq",
            Runtime::ListCompare => "stilt_rt_list_compare",
            Runtime::ListHash => "stilt_rt_list_hash",
            Runtime::ListShow => "stilt_rt_list_show",
            Runtime::PackEq => "stilt_rt_pack_eq",
            Runtime::PackCompare => "stilt_rt_pack_compare",
            Runtime::PackHash => "stilt_rt_pack_hash",
            Runtime::PackShow => "stilt_rt_pack_show",
            Runtime::MapEq => "stilt_rt_map_eq",
            Runtime::MapShow => "stilt_rt_map_show",
            Runtime::Concat => "stilt_rt_concat",
            Runtime::Concat2 => "stilt_rt_concat2",
            Runtime::Concat3 => "stilt_rt_concat3",
            Runtime::Concat4 => "stilt_rt_concat4",
            Runtime::ConcatOnto2 => "stilt_rt_concat_onto2",
            Runtime::ConcatOnto3 => "stilt_rt_concat_onto3",
            Runtime::ConcatOnto4 => "stilt_rt_concat_onto4",
            Runtime::ShowInt => "stilt_rt_show_int",
            Runtime::IntValid => "stilt_rt_int_valid",
            Runtime::IntParse => "stilt_rt_int_parse",
            Runtime::ShowFloat => "stilt_rt_show_float",
            Runtime::ShowBool => "stilt_rt_show_bool",
            Runtime::Quote => "stilt_rt_quote",
            Runtime::PropWord => "stilt_rt_prop_word",
            Runtime::PropStr => "stilt_rt_prop_str",
            Runtime::PropMap => "stilt_rt_prop_map",
            Runtime::PropStore => "stilt_rt_prop_store",
            Runtime::TestNote => "stilt_rt_test_note",
            Runtime::ProfileCall => "stilt_rt_profile_call",
            Runtime::CLoad => "stilt_rt_c_load",
            Runtime::Effects(e) => e.symbol(),
            Runtime::Views(v) => v.symbol(),
            Runtime::Shared(w) => w.symbol(),
            _ => unreachable!("`collection_symbol` names the functions of lists and maps"),
        }
    }

    /// The runtime's name for a function of lists and maps.
    fn collection_symbol(self) -> Option<&'static str> {
        let name = match self {
            Runtime::ListNew => "stilt_rt_list_new",
            Runtime::ListPush => "stilt_rt_list_push",
            Runtime::ListAppend => "list_append",
            Runtime::ListLen => "stilt_rt_list_len",
            Runtime::ListAt => "stilt_rt_list_at",
            Runtime::ListIndex => "stilt_rt_list_index",
            Runtime::ListSlot => "stilt_rt_list_slot",
            Runtime::ListSlotAt => "list_slot_at",
            Runtime::ListElement => "list_element",
            Runtime::ListElementAt => "list_element_at",
            Runtime::ListGet => "stilt_rt_list_get",
            Runtime::ListPut => "stilt_rt_list_put",
            Runtime::MapIndex => "stilt_rt_map_index",
            Runtime::MapNext => "stilt_rt_map_next",
            Runtime::MapKeyAt => "stilt_rt_map_key_at",
            Runtime::MapValueAt => "stilt_rt_map_value_at",
            Runtime::MapWord => "map_word",
            Runtime::MapDefault => "stilt_rt_map_default",
            Runtime::MapHeld => "stilt_rt_map_held",
            Runtime::MapStore => "stilt_rt_map_store",
            Runtime::ListSlice => "stilt_rt_list_slice",
            _ => return None,
        };
        Some(name)
    }

    /// Whether the function returns a word.
    #[must_use]
    pub fn returns(self) -> bool {
        !matches!(
            self,
            Runtime::ListPush
                | Runtime::ListAppend
                | Runtime::ListPut
                | Runtime::Discard
                | Runtime::OutOfMemory
                | Runtime::StorePacked
                | Runtime::MapStore
                | Runtime::PropStore
                | Runtime::TestNote
                | Runtime::ProfileCall
                | Runtime::CLoad
                | Runtime::Shared(Shared::Name | Shared::Hold | Shared::Leave | Shared::Direct)
                | Runtime::Effects(Effects::Leave)
                | Runtime::Views(Views::Put)
        )
    }

    /// Whether the word it returns is borrowed from an argument, rather than owned.
    #[must_use]
    pub fn borrows(self) -> bool {
        matches!(
            self,
            Runtime::ListAt | Runtime::ListIndex | Runtime::MapWord
        )
    }

    /// The arguments it consumes, by position.
    #[must_use]
    pub fn consumes(self, i: usize) -> bool {
        match self {
            Runtime::ListPush | Runtime::ListAppend => i >= 2,
            Runtime::Reclaim
            | Runtime::ConcatOnto2
            | Runtime::ConcatOnto3
            | Runtime::ConcatOnto4 => i == 0,
            Runtime::ListPut | Runtime::Views(Views::Put) => i == 3,
            Runtime::MapStore => i == 5,
            Runtime::PropStore => i == 6,
            _ => false,
        }
    }
}

/// The functions of the runtime for handlers (handlers.with and handlers.resuming;
/// `stilt_runtime`'s `effects`), which compiled code calls directly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Effects {
    /// `(effect, handler)`: installs a handler for the effect whose name hashes to `effect`,
    /// and gives its node.
    Enter,
    /// `(node)`: removes the handler of a `with` that its block leaves, cancelling the bodies
    /// that wait for its value.
    Leave,
    /// `()`: whether the raise going on is an abort, which every `catch` passes on.
    Aborting,
    /// `(node)`: whether the raise going on is an abort that ends the `with` of the node.
    AbortingTo,
    /// `()`: the value of the body that aborted, owned, which ends the abort.
    AbortTake,
    /// `(which)`: the static closure whose code performs an operation (0), resumes (1) or ends
    /// a `with` (2), which can raise and runs code of the program.
    Code,
}

impl Effects {
    /// The runtime's name for the function.
    #[must_use]
    pub fn symbol(self) -> &'static str {
        match self {
            Effects::Enter => "stilt_rt_with_enter",
            Effects::Leave => "stilt_rt_with_leave",
            Effects::Aborting => "stilt_rt_aborting",
            Effects::AbortingTo => "stilt_rt_aborting_to",
            Effects::AbortTake => "stilt_rt_abort_take",
            Effects::Code => "stilt_rt_effect_code",
        }
    }
}

impl Views {
    /// The runtime's name for the function.
    #[must_use]
    pub fn symbol(self) -> &'static str {
        match self {
            Views::Of => "stilt_rt_view_of",
            Views::Len => "stilt_rt_view_len",
            Views::Part => "stilt_rt_view_part",
            Views::Index => "stilt_rt_view_index",
            Views::Eq => "stilt_rt_view_eq",
            Views::Compare => "stilt_rt_view_compare",
            Views::Hash => "stilt_rt_view_hash",
            Views::Show => "stilt_rt_view_show",
            Views::State => "stilt_rt_iter_state",
            Views::Next => "stilt_rt_iter_next",
            Views::Take => "stilt_rt_iter_take",
            Views::Put => "stilt_rt_view_put",
        }
    }
}

/// The functions of the runtime for `when` and scopes (shared.when-order and
/// tasks.scope-failure; shared.when-on-value-already-held; `stilt_runtime`'s `std_sync`,
/// `std_scope` and `tasks`), which compiled code calls directly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Shared {
    /// `(loc, handle)`: a name of the `when` at `loc` being entered, which panics with
    /// `deadlock` there if a `when` that hasn't ended holds the value.
    Name,
    /// `()`: holds the values the `when` named, once it is their turn.
    Hold,
    /// `(handle)`: a pointer to the words of the value that a `Shared<T>` reaches, which a
    /// `when` holds, for its block to read and write in place.
    Place,
    /// `(handle)`: the end of a `when`'s hold on the value the handle reaches, however its block
    /// ends, which the handle keeps alive until then.
    Leave,
    /// `()`: tells the next `s.spawn` that its raise leaves the scope at once
    /// (tasks.scope-failure).
    Direct,
}

impl Shared {
    /// The runtime's name for the function.
    #[must_use]
    pub fn symbol(self) -> &'static str {
        match self {
            Shared::Name => "stilt_rt_when_name",
            Shared::Hold => "stilt_rt_when_hold",
            Shared::Place => "stilt_rt_shared_place",
            Shared::Leave => "stilt_rt_shared_leave",
            Shared::Direct => "stilt_rt_scope_direct",
        }
    }
}

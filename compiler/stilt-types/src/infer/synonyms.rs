//! The names that other languages give the members of their lists, maps, sets and strings,
//! with the names that Stilt's have (goal closest-candidates).

/// For a member's name in another language, the names that Stilt's members may have, the
/// first that the type has being the one meant.
const SYNONYMS: &[(&[&str], &[&str])] = &[
    (&["length", "size", "getLength", "count"], &["len"]),
    (
        &["append", "push_back", "pushBack", "add", "put", "set"],
        &["push", "insert"],
    ),
    (
        &[
            "toString",
            "to_string",
            "tostring",
            "ToString",
            "repr",
            "str",
        ],
        &["show"],
    ),
    (
        &["includes", "has", "contains_key", "has_key", "containsKey"],
        &["contains"],
    ),
    (
        &["indexOf", "index_of", "index", "position"],
        &["find", "find_index"],
    ),
    (
        &[
            "toUpperCase",
            "to_uppercase",
            "upper",
            "uppercase",
            "toUpper",
        ],
        &["ascii_upper"],
    ),
    (
        &[
            "toLowerCase",
            "to_lowercase",
            "lower",
            "lowercase",
            "toLower",
        ],
        &["ascii_lower"],
    ),
    (&["substring", "substr"], &["slice"]),
    (&["strip"], &["trim"]),
    (&["lstrip", "trimLeft", "trimStart"], &["trim_start"]),
    (&["rstrip", "trimRight", "trimEnd"], &["trim_end"]),
    (&["isEmpty", "empty"], &["is_empty"]),
    (&["reverse"], &["reversed"]),
    (&["sort"], &["sorted"]),
    (&["addAll", "concat", "append_all"], &["extend", "concat"]),
];

/// The names that other languages give a loop over a collection's elements, which Stilt
/// writes with `for`.
const LOOPS: &[&str] = &["forEach", "for_each", "each", "foreach"];

/// The names that other languages give the iterator of a collection, whose methods Stilt's
/// lists, maps and sets have themselves.
const ITERATORS: &[&str] = &["iter", "into_iter", "iter_mut", "stream"];

/// The member among `members` that `name`, another language's name for it, stands for.
pub(super) fn synonym<'m>(name: &str, members: &[&'m str]) -> Option<&'m str> {
    let (_, stilt) = SYNONYMS.iter().find(|(names, _)| names.contains(&name))?;
    stilt
        .iter()
        .find_map(|c| members.iter().copied().find(|m| m == c))
}

/// Whether `name` is another language's loop over the elements of a collection.
pub(super) fn is_loop(name: &str) -> bool {
    LOOPS.contains(&name)
}

/// Whether `name` is another language's iterator of a collection.
pub(super) fn is_iterator(name: &str) -> bool {
    ITERATORS.contains(&name)
}

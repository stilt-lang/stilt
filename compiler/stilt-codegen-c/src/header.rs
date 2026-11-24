//! The header that every C file of a release build starts with: the layout
//! constants of `stilt-runtime`, written from its own definitions so that the two can't
//! drift, then the fast paths of [`stilt.h`](stilt.h), then `_Static_assert`s of what the
//! fast paths take for granted of the constants and of C's types, so that a layout the header
//! can't read stops the build rather than the program.

use std::fmt::Write as _;

use stilt_runtime::layout;

/// The header's fast paths, which read the constants by name.
const FAST_PATHS: &str = include_str!("stilt.h");

/// What the fast paths take for granted: each a condition and the reason it must hold.
const ASSUMED: &[(&str, &str)] = &[
    (
        "sizeof(u64) == 8 && sizeof(void *) <= 8",
        "a word holds a pointer",
    ),
    (
        "sizeof(double) == 8 && sizeof(float) == 4",
        "floats are IEEE 754 binary64 and binary32",
    ),
    (
        "sizeof(lt_ret) == 16",
        "a lt_ret is the runtime's two words of a result",
    ),
    (
        "LT_RC == 0",
        "the count is the low half of an object's first word",
    ),
    (
        "(LT_SHARED_BIT >> 32) != 0",
        "the shared bit is apart from the count",
    ),
    (
        "LT_HEADER % 8 == 0 && LT_LIST_LEN % 8 == 0 && LT_LIST_CAP % 8 == 0 && LT_LIST_DATA % 8 == 0",
        "fields and a list's words are aligned words",
    ),
    (
        "LT_TAG % 2 == 0 && LT_TAG + 2 <= 8",
        "a tag is an aligned u16 of the first word",
    ),
    (
        "LT_ALIGN_BITS == 7",
        "objects are aligned to 8, so a pointer's low bits are 0",
    ),
    (
        "LT_KIND < 8 && LT_LAYOUT == 8 && LT_HEADER == 16",
        "a kind is a byte of the first word, and a data object's layout word the low half of the second",
    ),
    (
        "LT_HEADER + 8 * LT_INLINE_FIELDS <= LT_POOL_LARGEST && LT_INLINE_FIELDS < 31",
        "a small data object is a block of the pool, and its layout word holds its length's bit",
    ),
    (
        "__builtin_offsetof(lt_pool, owner) == LT_POOL_OWNER && __builtin_offsetof(lt_pool, room) == LT_POOL_ROOM && __builtin_offsetof(lt_pool, bytes) == LT_POOL_BYTES && __builtin_offsetof(lt_pool, objects) == LT_POOL_OBJECTS && __builtin_offsetof(lt_pool, next) == LT_POOL_NEXT && __builtin_offsetof(lt_pool, end) == LT_POOL_END && __builtin_offsetof(lt_pool, heads) == LT_POOL_HEADS",
        "the pool is laid out as the runtime's",
    ),
];

/// The header of a release build's C files.
#[must_use]
pub fn header() -> String {
    let mut out = String::from(
        "/* The layout constants of stilt-runtime (stilt_runtime::layout), as the runtime\n * defines them. */\n",
    );
    let constants: [(&str, String); 26] = [
        ("LT_RC", layout::RC.to_string()),
        ("LT_SHARED_BIT", format!("{:#x}ULL", layout::SHARED_BIT)),
        ("LT_ALIGN_BITS", layout::ALIGN_BITS.to_string()),
        ("LT_HEADER", layout::HEADER.to_string()),
        ("LT_KIND", layout::KIND.to_string()),
        ("LT_KIND_DATA", layout::KIND_DATA.to_string()),
        ("LT_TAG", layout::TAG.to_string()),
        ("LT_LAYOUT", layout::LAYOUT.to_string()),
        ("LT_INLINE_FIELDS", layout::INLINE_FIELDS.to_string()),
        ("LT_LAYOUT_LARGE", format!("{:#x}U", layout::LAYOUT_LARGE)),
        ("LT_POOL_OWNER", layout::POOL_OWNER.to_string()),
        ("LT_POOL_ROOM", layout::POOL_ROOM.to_string()),
        ("LT_POOL_BYTES", layout::POOL_BYTES.to_string()),
        ("LT_POOL_OBJECTS", layout::POOL_OBJECTS.to_string()),
        ("LT_POOL_NEXT", layout::POOL_NEXT.to_string()),
        ("LT_POOL_END", layout::POOL_END.to_string()),
        ("LT_POOL_HEADS", layout::POOL_HEADS.to_string()),
        ("LT_POOL_LARGEST", layout::POOL_LARGEST.to_string()),
        ("LT_POOL_LISTS", layout::POOL_LISTS.to_string()),
        ("LT_BOX", format!("{:#x}", layout::BOX)),
        ("LT_RUNTIME_TAGS", format!("{:#x}", layout::RUNTIME_TAGS)),
        ("LT_LIST_LEN", layout::LIST_LEN.to_string()),
        ("LT_LIST_CAP", layout::LIST_CAP.to_string()),
        ("LT_LIST_DATA", layout::LIST_DATA.to_string()),
        ("LT_SHAPE_SIZE_SHIFT", layout::SHAPE_SIZE_SHIFT.to_string()),
        (
            "LT_SHAPE_SIZE_BITS",
            format!("{:#x}", layout::SHAPE_SIZE_BITS),
        ),
    ];
    for (name, value) in constants {
        let _ = writeln!(out, "#define {name} {value}");
    }
    out.push_str(FAST_PATHS);
    for (condition, reason) in ASSUMED {
        let _ = writeln!(out, "_Static_assert({condition}, \"{reason}\");");
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn the_header_defines_what_it_asserts() {
        let header = super::header();
        for name in ["LT_RC", "LT_SHARED_BIT", "LT_TAG", "LT_LIST_DATA"] {
            assert!(header.contains(&format!("#define {name} ")), "{name}");
        }
        assert!(
            !header.contains("#include"),
            "the C includes no system header"
        );
    }
}

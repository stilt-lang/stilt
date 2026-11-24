//! A library's header (c.library-header): C11 and C++ alike, it declares each exported function in
//! the order of c.library-header, after the first paragraph of its doc comment, each parameter with
//! its name, but for a name that C or C++ code can already mean, as an exported function's own
//! can't be (c.exported-names), which would break the declaration: such a parameter is written by
//! its type alone.

use std::fmt::Write as _;

use stilt_mir::Export;

/// The header of the library `name` that exports `exports`.
pub(crate) fn header(name: &str, exports: &[Export]) -> String {
    let mut guard: String = name
        .bytes()
        .map(|b| {
            if b.is_ascii_alphanumeric() {
                char::from(b.to_ascii_uppercase())
            } else {
                '_'
            }
        })
        .collect();
    // A C name starts with no digit.
    if guard.starts_with(|c: char| c.is_ascii_digit()) {
        guard.insert(0, '_');
    }
    let mut out = format!(
        "#ifndef {guard}_H\n#define {guard}_H\n\n#include <stdbool.h>\n#include <stdint.h>\n\n\
         #ifdef __cplusplus\nextern \"C\" {{\n#endif\n\n"
    );
    for export in exports {
        for line in &export.doc {
            // A comment line that ends in a backslash would continue onto the declaration.
            let line = line.trim_end().trim_end_matches('\\').trim_end();
            if line.is_empty() {
                out.push_str("//\n");
            } else {
                let _ = writeln!(out, "// {line}");
            }
        }
        let _ = writeln!(out, "{};\n", declaration(export));
    }
    out.push_str("#ifdef __cplusplus\n}\n#endif\n\n#endif\n");
    out
}

/// An exported function's declaration: its result, its name, and each parameter's type, with
/// its name where C can take it.
fn declaration(export: &Export) -> String {
    let result = export.result.map_or("void", |t| t.c_name());
    let params: Vec<String> = export
        .params
        .iter()
        .enumerate()
        .map(|(i, t)| match export.names.get(i) {
            Some(name) if !name.is_empty() && !stilt_hir::exports::taken(name) => {
                format!("{} {name}", t.c_name())
            }
            _ => t.c_name().to_owned(),
        })
        .collect();
    let params = if params.is_empty() {
        "void".to_owned()
    } else {
        params.join(", ")
    };
    format!("{result} {}({params})", export.symbol)
}

#[cfg(test)]
mod tests {
    use super::header;

    #[test]
    fn a_guard_is_the_name_in_capitals_and_never_starts_with_a_digit() {
        // c.library-header: other bytes are written `_`, and a `_` comes before a digit.
        assert!(header("my-lib", &[]).starts_with("#ifndef MY_LIB_H\n#define MY_LIB_H\n"));
        assert!(header("9lib", &[]).starts_with("#ifndef _9LIB_H\n"));
    }
}

//! The names a position of a file may write: the variables in scope there, read off the syntax
//! tree so that a body with a syntax error still has them, and the items of the file's module, of
//! the prelude and of the modules it imports (program.what-use-binds and program.namespaces), each
//! with its signature or definition and its doc.

use stilt_db::{Database, Program, SourceFile};
use stilt_edit::{Kind, Place};
use stilt_lsp::{Completion, Sort};
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::{SyntaxNode, TextRange, TextSize};

use crate::show::parts::FileParts;

/// A variable in scope, bound by a pattern or a parameter.
#[derive(Clone, Debug)]
pub(super) struct Local {
    pub name: String,
    /// Its binding.
    pub at: TextRange,
    pub param: bool,
    /// The type its binding writes, if it writes one.
    pub written: Option<String>,
}

/// The variables in scope at `offset`, the innermost first, each name once.
pub(super) fn locals(root: &SyntaxNode, offset: TextSize) -> Vec<Local> {
    let Some(decl) = declaration_at(root, offset) else {
        return Vec::new();
    };
    let mut found = params(&decl);
    found.extend(value_params(&decl));
    for name in decl.descendants().filter(|n| n.kind() == NAME) {
        let Some(bind) = name.parent().filter(|p| p.kind() == BIND_PAT) else {
            continue;
        };
        if name.text_range().start() < offset && visible(&bind, offset) {
            found.push(local(&name, &bind));
        }
    }
    found.extend(broken_bindings(&decl, offset));
    found.sort_by_key(|l| std::cmp::Reverse(l.at.start()));
    let mut seen = Vec::new();
    found.retain(|l| {
        let first = !seen.contains(&l.name);
        seen.push(l.name.clone());
        first
    });
    found
}

/// The function, test or constant whose declaration holds `offset`.
pub(super) fn declaration_at(root: &SyntaxNode, offset: TextSize) -> Option<SyntaxNode> {
    let token = root.token_at_offset(offset).left_biased()?;
    token
        .parent_ancestors()
        .find(|n| matches!(n.kind(), FN | TEST | CONST))
}

/// The parameters of a function, `self` included, with their written types.
fn params(decl: &SyntaxNode) -> Vec<Local> {
    let Some(list) = decl.children().find(|c| c.kind() == PARAM_LIST) else {
        return Vec::new();
    };
    list.children()
        .filter_map(|p| {
            let (name, at) = match p.kind() {
                SELF_PARAM => ("self".to_owned(), p.text_range()),
                PARAM => {
                    let name = p.children().find(|c| c.kind() == NAME)?;
                    (name.text().to_string(), name.text_range())
                }
                _ => return None,
            };
            let written = p
                .text()
                .to_string()
                .split_once(':')
                .map(|(_, t)| t.trim().to_owned());
            Some(Local {
                name,
                at,
                param: true,
                written,
            })
        })
        .collect()
}

/// The value parameters in scope in a declaration's body: its own and its impl block's, each
/// an immutable value of its type (generics.value-parameters-in-body).
fn value_params(decl: &SyntaxNode) -> Vec<Local> {
    let block = decl.ancestors().skip(1).find(|n| n.kind() == IMPL);
    std::iter::once(decl.clone())
        .chain(block)
        .filter_map(|d| d.children().find(|c| c.kind() == GENERIC_LIST))
        .flat_map(|list| list.children().filter(|g| g.kind() == VALUE_PARAM))
        .filter_map(|p| {
            let name = p.children().find(|c| c.kind() == NAME)?;
            let written = p.text().to_string();
            Some(Local {
                name: name.text().to_string(),
                at: name.text_range(),
                param: true,
                written: written.split_once(':').map(|(_, t)| t.trim().to_owned()),
            })
        })
        .collect()
}

/// Whether the binding `bind` is in scope at `offset`: a `let`'s or a `var`'s after its
/// statement, to the end of its block; a closure's parameter in its closure; and an arm's or a
/// loop's pattern in its arm or loop.
fn visible(bind: &SyntaxNode, offset: TextSize) -> bool {
    for scope in bind.ancestors() {
        match scope.kind() {
            LET_STMT | VAR_STMT => {
                let after = scope.text_range().end() <= offset;
                let block = scope.parent().map(|b| b.text_range());
                return after && block.is_some_and(|b| b.contains_inclusive(offset));
            }
            CLOSURE_EXPR | ARM | FOR_EXPR | IF_EXPR | WHILE_EXPR => {
                return scope.text_range().contains_inclusive(offset);
            }
            FN | TEST | CONST => return true,
            _ => {}
        }
    }
    false
}

fn local(name: &SyntaxNode, bind: &SyntaxNode) -> Local {
    let stmt = bind
        .ancestors()
        .find(|n| matches!(n.kind(), LET_STMT | VAR_STMT | CLOSURE_PARAM));
    let written = stmt.as_ref().and_then(|s| {
        let ty = s.children().find(|c| {
            matches!(
                c.kind(),
                NAMED_TYPE | TUPLE_TYPE | FN_TYPE | RECORD_TYPE | PAREN_TYPE
            )
        })?;
        Some(ty.text().to_string())
    });
    Local {
        name: name.text().to_string(),
        at: name.text_range(),
        param: stmt.is_some_and(|s| s.kind() == CLOSURE_PARAM),
        written,
    }
}

/// The names that `let`, `var` and `for` bind before `offset` in the parts of a declaration
/// that the parser couldn't read, which keep their tokens.
fn broken_bindings(decl: &SyntaxNode, offset: TextSize) -> Vec<Local> {
    let mut found = Vec::new();
    for error in decl.descendants().filter(|n| n.kind() == ERROR) {
        let tokens: Vec<_> = error
            .children_with_tokens()
            .filter_map(stilt_syntax::SyntaxElement::into_token)
            .filter(|t| !t.kind().is_trivia())
            .collect();
        for pair in tokens.windows(2) {
            let binds = matches!(pair[0].kind(), LET_KW | VAR_KW | FOR_KW);
            if binds && pair[1].kind() == LOWER_IDENT && pair[1].text_range().end() < offset {
                found.push(Local {
                    name: pair[1].text().to_owned(),
                    at: pair[1].text_range(),
                    param: false,
                    written: None,
                });
            }
        }
    }
    found
}

/// The type of the variable `name` in scope at `offset`, as its binding writes it, or as the
/// value bound to it shows it: a record's type, a literal's, a list, or the result of the
/// function called. This reads code that doesn't parse whole, where checking found no types.
pub(super) fn written_type(
    db: &Database,
    program: Program,
    file: SourceFile,
    name: &str,
    offset: TextSize,
) -> Option<String> {
    let root = stilt_db::parse(db, file).syntax();
    if name == "self" {
        let token = root.token_at_offset(offset).left_biased()?;
        let imp = token.parent_ancestors().find(|n| n.kind() == IMPL)?;
        let ty = imp.children().filter(|c| c.kind() == NAMED_TYPE).last()?;
        return Some(ty.text().to_string());
    }
    let local = locals(&root, offset).into_iter().find(|l| l.name == name)?;
    if let Some(written) = local.written {
        return Some(written);
    }
    let bound = root.token_at_offset(local.at.start()).right_biased()?;
    let equals = next(&bound).filter(|t| t.kind() == EQ)?;
    let value = next(&equals)?;
    let after = next(&value).map(|t| t.kind());
    Some(match (value.kind(), after) {
        (UPPER_IDENT, Some(L_CURLY)) => value.text().to_owned(),
        (L_BRACK, _) => "List".to_owned(),
        (INT, _) => "i64".to_owned(),
        (FLOAT, _) => "f64".to_owned(),
        (STRING | STRING_HEAD, _) => "str".to_owned(),
        (TRUE_KW | FALSE_KW, _) => "bool".to_owned(),
        (LOWER_IDENT, Some(L_PAREN)) => {
            let module = stilt_hir::module_hir(db, program, file).name;
            let mut parts = crate::show::lookup::Parts::new(db, program);
            let (of, i) = [module.as_ref(), "std.prelude"]
                .iter()
                .find_map(|home| parts.declaration(&format!("{home}.{}", value.text())))?;
            let header = of.header(i);
            let result = header.rsplit_once("->")?.1;
            result.split(" /").next()?.trim().to_owned()
        }
        _ => return None,
    })
}

/// The token after `token` that isn't trivia.
fn next(token: &stilt_syntax::SyntaxToken) -> Option<stilt_syntax::SyntaxToken> {
    let mut t = token.next_token()?;
    while t.kind().is_trivia() {
        t = t.next_token()?;
    }
    Some(t)
}

/// The items of a file's module, every one of them, then the prelude's, then the modules that
/// it imports, by the name the file writes them with.
pub(super) fn items(db: &Database, program: Program, file: SourceFile) -> Vec<Completion> {
    let mut found = declared(&FileParts::of(db, program, file), false);
    if let Some(prelude) = module_file(db, program, "std.prelude") {
        found.extend(declared(&FileParts::of(db, program, prelude), true));
    }
    let module = stilt_hir::module_hir(db, program, file);
    for import in &module.imports {
        let short = import.rsplit('.').next().unwrap_or(import);
        found.push(Completion {
            label: short.to_owned(),
            sort: Sort::Module,
            detail: Some(format!("use {import}")),
            docs: None,
            insert: None,
        });
    }
    found
}

/// The `pub` items of the module named `module`.
pub(super) fn module_items(db: &Database, program: Program, module: &str) -> Vec<Completion> {
    module_file(db, program, module)
        .map(|f| declared(&FileParts::of(db, program, f), true))
        .unwrap_or_default()
}

/// The file of the module named `module`, the program's or the standard library's.
pub(super) fn module_file(db: &Database, program: Program, module: &str) -> Option<SourceFile> {
    (program.files(db).iter().chain(program.std(db)))
        .copied()
        .find(|&f| &*stilt_hir::module_hir(db, program, f).name == module)
}

/// The module-level declarations of a file, but its tests, or only its `pub` ones.
fn declared(of: &FileParts, only_pub: bool) -> Vec<Completion> {
    (0..of.parts.len())
        .filter(|&i| {
            let p = &of.parts[i];
            !p.body && p.place == Place::Item && p.kind != Kind::Test && (!only_pub || of.is_pub(i))
        })
        .map(|i| completion(of, i))
        .collect()
}

/// The completion of declaration `i` of a file: its name, its sort, its header and its doc. A
/// macro's is its name with its `!`.
pub(super) fn completion(of: &FileParts, i: usize) -> Completion {
    let part = &of.parts[i];
    let name = of.text[part.name.clone()].to_owned();
    let header = of.header(i);
    let (sort, label, detail) = match part.kind {
        Kind::Fn if part.place != Place::Item && header.contains("(self") => {
            (Sort::Method, name, header)
        }
        Kind::Fn => (Sort::Function, name, header),
        Kind::Type => (Sort::Type, name, format!("type {header}")),
        Kind::Trait => (Sort::Trait, name.clone(), format!("trait {name}")),
        // A constant's header ends at its `=`, which completion leaves out with its value.
        Kind::Const => {
            let declared = header.trim_end().trim_end_matches('=').trim_end();
            (Sort::Constant, name, format!("const {declared}"))
        }
        Kind::Test => (Sort::Test, name, format!("test {header}")),
        Kind::Macro => (Sort::Macro, format!("{name}!"), format!("syntax {name}")),
        Kind::Effect => (Sort::Effect, name.clone(), format!("effect {name}")),
    };
    let insert = match sort {
        Sort::Function | Sort::Method => super::snippets::call(&label, &detail),
        _ => None,
    };
    Completion {
        label,
        sort,
        detail: Some(detail),
        docs: of.docs(i),
        insert,
    }
}

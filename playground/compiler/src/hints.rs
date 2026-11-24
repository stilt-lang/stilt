//! The facts beside each function of the program, as the language server's inlay hints write
//! them into the editor (`compiler/stilt-ide/src/editor/hints.rs`): the facts of the bracket that
//! `stilt show` writes after the signature, as in `[panic, alloc]`, each with what it means and
//! the lines that cause it; what each line that causes a fact does there, as `show` writes it in
//! a comment at the line's end; and the type that inference gives each `let` and `var` that
//! writes none (types.inferred-per-body; facts.visibility; modes.show). The page writes each at
//! the end of its line.

use serde_json::{Value, json};
use stilt_db::{Database, Program};
use stilt_diag::LineIndex;
use stilt_syntax::SyntaxKind::{BLOCK, FN, NAME};
use stilt_syntax::{SyntaxNode, TextRange, TextSize};

use crate::report::text;
use stilt_ide::show::code::notes;
use stilt_ide::show::facts::{Function, declared};

/// A JSON record of each function of the program's files, in order: its address, the lines its
/// declaration spans, the line where its body starts, and whether its body has an error, which
/// leaves it no inferred fact (facts.bodies-with-errors); and otherwise its facts, the notes of
/// the lines that cause them, and the types of its patterns that write none, each with its line.
pub(crate) fn functions(db: &Database, program: Program) -> Vec<Value> {
    let mut found = Vec::new();
    for &file in program.files(db) {
        let root = stilt_db::parse(db, file).syntax();
        let text = text(db, file);
        let lines = LineIndex::new(&text);
        let line = |at: TextSize| lines.position(&text, at).line;
        for mut f in declared(db, program, file) {
            let Some((range, body)) = declaration(&root, f.name_at) else {
                continue;
            };
            f.infer(db, program);
            let mut record = json!({
                "address": f.address,
                "first": line(range.start()),
                "last": line(range.end() - TextSize::from(1)),
                "body": body.map(line),
                "broken": f.broken,
            });
            if !f.broken {
                record["facts"] = facts(&f);
                record["notes"] = (notes(&f).into_iter())
                    .filter(|(_, says)| !says.is_empty())
                    .map(|(line, says)| json!([line, says.join("; ")]))
                    .collect();
                record["types"] = (f.locals.iter())
                    .map(|l| json!([l.line, l.pattern, l.ty]))
                    .collect();
            }
            found.push(record);
        }
    }
    found
}

/// The facts of the function's bracket, in its order, each with its words, what it means, and
/// the lines that cause it with what each does there.
fn facts(f: &Function) -> Value {
    (f.listed().into_iter())
        .map(|fact| {
            let causes: Vec<Value> = (fact.causes.iter())
                .map(|c| json!([c.line, c.says]))
                .collect();
            json!({ "text": fact.text, "meaning": fact.meaning, "causes": causes })
        })
        .collect()
}

/// The text of the declaration of the function whose name starts at `name_at`, and where its
/// body starts, if it has one.
fn declaration(root: &SyntaxNode, name_at: usize) -> Option<(TextRange, Option<TextSize>)> {
    let name_at = TextSize::from(u32::try_from(name_at).ok()?);
    let decl = root.descendants().find(|n| {
        n.kind() == FN
            && n.children()
                .any(|c| c.kind() == NAME && c.text_range().start() == name_at)
    })?;
    let body = decl.children().find(|c| c.kind() == BLOCK);
    Some((decl.text_range(), body.map(|b| b.text_range().start())))
}

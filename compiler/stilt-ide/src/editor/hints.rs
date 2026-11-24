//! Inlay hints: what `stilt show` writes into a function, written in where the editor shows
//! the code (Inferred facts, "Seven commands"). Each `let` and `var` that writes no type has its
//! inferred type after its pattern (types.inferred-per-body), and so does each closure parameter
//! that writes none; each function of the program has its inferred facts before its body, as `show`
//! writes them after its signature, as in `[consumes xs, panic, alloc]`, each fact with what it
//! means and the lines that cause it; and each line that causes a fact has what it does there at
//! its end, as `show` writes it in a comment (values.consumed-parameters; facts.visibility;
//! modes.show).

use stilt_db::{Database, Program, SourceFile};
use stilt_diag::LineIndex;
use stilt_lsp::{Hint, HintPart, HintSort};
use stilt_syntax::SyntaxKind::*;
use stilt_syntax::{SyntaxNode, TextSize};

use crate::show::code::notes;
use crate::show::facts::{Function, declared};
use crate::show::position::local_type;

/// The inlay hints of `file`, in order.
pub fn hints(db: &Database, program: Program, file: SourceFile) -> Vec<Hint> {
    let root = stilt_db::parse(db, file).syntax();
    let text = crate::text(db, file);
    let lines = LineIndex::new(&text);
    let mut found = Vec::new();
    for mut f in declared(db, program, file) {
        f.infer(db, program);
        if f.broken {
            continue;
        }
        if let Some(body) = body_start(&root, f.name_at)
            && let Some(hint) = facts(&f, body)
        {
            found.push(hint);
        }
        found.extend(causes(&f, &text, &lines));
        found.extend(
            f.locals
                .iter()
                .map(|l| plain(l.end, format!(": {}", l.ty), HintSort::Type)),
        );
    }
    found.extend(closure_params(db, program, file, &root));
    found.sort_by_key(|h| h.at);
    found
}

/// A hint of one piece.
fn plain(at: TextSize, label: String, sort: HintSort) -> Hint {
    Hint {
        at: at.into(),
        label,
        sort,
        parts: Vec::new(),
    }
}

/// The facts of `f` before its body, which starts at `body`, as `[panic, alloc]`, each a piece
/// with its meaning and causes. None when it has no fact.
fn facts(f: &Function, body: TextSize) -> Option<Hint> {
    let listed = f.listed();
    if listed.is_empty() {
        return None;
    }
    let between = |text: &str| HintPart {
        text: text.to_owned(),
        meaning: None,
        causes: Vec::new(),
    };
    let mut parts = vec![between("[")];
    for (i, fact) in listed.iter().enumerate() {
        if i > 0 {
            parts.push(between(", "));
        }
        parts.push(HintPart {
            text: fact.text.clone(),
            meaning: Some(fact.meaning.clone()),
            causes: (fact.causes.iter())
                .map(|c| (c.line, c.says.clone()))
                .collect(),
        });
    }
    parts.push(between("]"));
    let label = parts.iter().map(|p| p.text.as_str()).collect();
    Some(Hint {
        at: body.into(),
        label,
        sort: HintSort::Facts,
        parts,
    })
}

/// What each line of `f` that causes a fact does there, at the line's end, as `show` writes it
/// after `// `.
fn causes(f: &Function, text: &str, lines: &LineIndex) -> Vec<Hint> {
    notes(f)
        .into_iter()
        .filter(|(_, says)| !says.is_empty())
        .map(|(line, says)| {
            let start = lines.line_start(text, line);
            let end = start + TextSize::of(lines.line(text, line).trim_end());
            plain(end, format!("// {}", says.join("; ")), HintSort::Causes)
        })
        .collect()
}

/// Where the body of the function whose name starts at `name_at` starts.
fn body_start(root: &SyntaxNode, name_at: usize) -> Option<TextSize> {
    let name_at = TextSize::from(u32::try_from(name_at).ok()?);
    let decl = root.descendants().find(|n| {
        n.kind() == FN
            && n.children()
                .any(|c| c.kind() == NAME && c.text_range().start() == name_at)
    })?;
    let body = decl.children().find(|c| c.kind() == BLOCK)?;
    Some(body.text_range().start())
}

/// The type hints of the closures' parameters that write no type.
fn closure_params(
    db: &Database,
    program: Program,
    file: SourceFile,
    root: &SyntaxNode,
) -> Vec<Hint> {
    root.descendants()
        .filter(|n| n.kind() == CLOSURE_PARAM && !n.children().any(|c| c.kind() == NAMED_TYPE))
        .filter(|n| !n.children_with_tokens().any(|c| c.kind() == COLON))
        .filter_map(|n| {
            let bind = n.children().find(|c| c.kind() == BIND_PAT)?;
            let ty = local_type(db, program, file, bind.text_range().start())?;
            Some(plain(
                bind.text_range().end(),
                format!(": {ty}"),
                HintSort::Type,
            ))
        })
        .collect()
}

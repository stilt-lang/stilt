//! The backend's answers as the protocol writes them.

use serde_json::{Value, json};

use crate::text::{position, range, utf16_len};
use crate::{
    Completion, Diagnostic, Edit, Fix, Fold, FoldSort, Hint, HintPart, HintSort, Signature, Sort,
    Symbol, codes, tokens,
};

/// The warnings about code that does nothing, which an editor fades: commented-out code
/// (lexical.commented-out-code), an unreachable arm (patterns.unreachable-arms) and a `try` with
/// nothing to mark (effects.empty-try).
const UNNECESSARY: [&str; 3] = ["W0001", "W0301", "W0500"];

/// A diagnostic, with its code and the page of the error index that describes it, its severity,
/// its notes as related information, and its tags.
/// An error is severity 1, and a warning 2, but for a hole (W0300), code not yet written, which is
/// information, 3 (declarations.typed-holes). A stale doc (W0002) is marked deprecated, since it
/// may describe a signature that changed (docs.stale), and a warning about code that does nothing
/// unnecessary.
pub(crate) fn diagnostic(text: &str, uri: &str, d: &Diagnostic) -> Value {
    let severity = match d.code.as_str() {
        _ if d.error => 1,
        "W0300" => 3,
        _ => 2,
    };
    let mut shown = json!({
        "range": range(text, d.start, d.end),
        "severity": severity,
        "code": d.code,
        "source": "stilt",
        "message": d.message,
    });
    if codes::CODES.binary_search(&d.code.as_str()).is_ok() {
        shown["codeDescription"] = json!({ "href": format!("{}{}.md", codes::INDEX, d.code) });
    }
    if UNNECESSARY.contains(&d.code.as_str()) {
        shown["tags"] = json!([1]);
    } else if d.code == "W0002" {
        shown["tags"] = json!([2]);
    }
    if !d.notes.is_empty() {
        let related: Vec<Value> = (d.notes.iter())
            .map(|n| {
                let location = json!({ "uri": uri, "range": range(text, n.start, n.end) });
                json!({ "location": location, "message": n.text })
            })
            .collect();
        shown["relatedInformation"] = Value::Array(related);
    }
    shown
}

/// The kind of the code action that applies every fix of a file at once, which an editor may
/// run on save.
pub(crate) const FIX_ALL: &str = "source.fixAll.stilt";

/// The code action of a fix of `d`, a quick fix that edits the file of `uri`. A diagnostic's
/// only fix is its preferred one, which an editor applies on its own when asked to fix.
pub(crate) fn action(text: &str, uri: &str, d: &Diagnostic, fix: &Fix) -> Value {
    json!({
        "title": fix.title,
        "kind": "quickfix",
        "diagnostics": [diagnostic(text, uri, d)],
        "isPreferred": d.fixes.len() == 1,
        "edit": { "changes": { uri: edits(text, &fix.edits) } },
    })
}

/// The action that applies, at once, the only fix of each diagnostic of a file that has one,
/// leaving out a fix whose edits overlap those of a fix before it. None when there is none.
pub(crate) fn fix_all(text: &str, uri: &str, diagnostics: &[Diagnostic]) -> Option<Value> {
    // The byte past an edit's span, which for an empty edit holds the byte it is written at,
    // counted wide enough for the last byte there can be.
    let past = |e: &Edit| u64::from(e.end).max(u64::from(e.start) + 1);
    let mut taken: Vec<&Edit> = Vec::new();
    let mut fixed = Vec::new();
    for d in diagnostics.iter().filter(|d| d.fixes.len() == 1) {
        let fix = &d.fixes[0];
        let clashes = fix.edits.iter().any(|e| {
            (taken.iter()).any(|t| u64::from(e.start) < past(t) && u64::from(t.start) < past(e))
        });
        if !clashes {
            taken.extend(&fix.edits);
            fixed.push(diagnostic(text, uri, d));
        }
    }
    if fixed.is_empty() {
        return None;
    }
    let all: Vec<Edit> = taken.into_iter().cloned().collect();
    Some(json!({
        "title": "Apply every fix in the file",
        "kind": FIX_ALL,
        "diagnostics": fixed,
        "edit": { "changes": { uri: edits(text, &all) } },
    }))
}

/// Edits as the protocol writes them.
fn edits(text: &str, edits: &[Edit]) -> Vec<Value> {
    edits
        .iter()
        .map(|e| json!({ "range": range(text, e.start, e.end), "newText": e.text }))
        .collect()
}

/// Hover contents in Markdown.
pub(crate) fn hover(markdown: &str) -> Value {
    json!({ "contents": { "kind": "markdown", "value": markdown } })
}

/// Markdown, as the protocol marks it.
fn markdown(text: &str) -> Value {
    json!({ "kind": "markdown", "value": text })
}

/// A completion item, with its kind, its signature or type, and its doc. Where the editor
/// expands snippets, a call is written with its parentheses and a placeholder for each
/// parameter, and in Visual Studio Code it then opens the call's signature help.
pub(crate) fn completion(c: &Completion, client: Client) -> Value {
    let kind = match c.sort {
        Sort::Method => 2,
        Sort::Function | Sort::Test => 3,
        Sort::Field => 5,
        Sort::Local | Sort::Parameter => 6,
        Sort::Type | Sort::Impl => 22,
        Sort::Trait | Sort::Effect => 8,
        Sort::Module => 9,
        Sort::Keyword => 14,
        Sort::Macro => 15,
        Sort::Variant => 20,
        Sort::Constant => 21,
    };
    let mut item = json!({ "label": c.label, "kind": kind });
    if let Some(detail) = &c.detail {
        item["detail"] = json!(detail);
    }
    if client.label_details
        && let Some(details) = label_details(c)
    {
        item["labelDetails"] = details;
    }
    if let Some(docs) = &c.docs {
        item["documentation"] = markdown(docs);
    }
    if let Some(insert) = c.insert.as_ref().filter(|_| client.snippets) {
        item["insertText"] = json!(insert);
        item["insertTextFormat"] = json!(2);
        let call = matches!(c.sort, Sort::Function | Sort::Method) && insert.ends_with(")$0");
        if client.vscode && call && !insert.ends_with("()$0") {
            let hints = "editor.action.triggerParameterHints";
            item["command"] = json!({ "title": "Show the signature", "command": hints });
        }
    }
    // Locals, then members and the module's own items, then the rest, then keywords.
    let rank = match c.sort {
        Sort::Local | Sort::Parameter | Sort::Field => 0,
        Sort::Method | Sort::Variant => 1,
        Sort::Keyword => 3,
        _ => 2,
    };
    item["sortText"] = json!(format!("{rank}{}", c.label));
    item
}

/// What the editor writes beside a completion's label: a function's parameters and result, or
/// a variant's payloads, right after it, and a variable's, a field's or a constant's type
/// apart from it.
fn label_details(c: &Completion) -> Option<Value> {
    let detail = c.detail.as_deref()?;
    match c.sort {
        Sort::Function | Sort::Method | Sort::Variant => {
            let rest = detail.strip_prefix(c.label.as_str())?;
            (!rest.is_empty()).then(|| json!({ "detail": rest }))
        }
        Sort::Local | Sort::Parameter => Some(json!({ "description": detail })),
        Sort::Field | Sort::Constant => {
            let (_, ty) = detail.split_once(": ")?;
            Some(json!({ "description": ty }))
        }
        _ => None,
    }
}

/// What the editor said it can do, at `initialize`, that changes how answers are written.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Client {
    /// It expands snippets in completions.
    pub(crate) snippets: bool,
    /// It writes a completion's label details beside its label.
    pub(crate) label_details: bool,
    /// It is Visual Studio Code, or a build of its sources, which has the command that opens
    /// signature help.
    pub(crate) vscode: bool,
}

impl Client {
    /// What the editor can do, from the parameters of its `initialize`.
    pub(crate) fn of(params: &Value) -> Client {
        let item = &params["capabilities"]["textDocument"]["completion"]["completionItem"];
        let name = params["clientInfo"]["name"].as_str().unwrap_or_default();
        Client {
            snippets: item["snippetSupport"] == true,
            label_details: item["labelDetailsSupport"] == true,
            vscode: ["Visual Studio Code", "Code - OSS", "VSCodium"]
                .iter()
                .any(|n| name.starts_with(n)),
        }
    }
}

/// Signature help: one signature, its parameters as spans of its label in UTF-16 units, a byte
/// inside a character counted from the character's start.
pub(crate) fn signature(s: &Signature) -> Value {
    let units = |n: u32| utf16_len(&s.label[..s.label.floor_char_boundary(n as usize)]);
    let params: Vec<Value> = (s.params.iter())
        .map(|&(a, b)| json!({ "label": [units(a), units(b)] }))
        .collect();
    let mut shown = json!({ "label": s.label, "parameters": params });
    if let Some(docs) = &s.docs {
        shown["documentation"] = markdown(docs);
    }
    json!({ "signatures": [shown], "activeSignature": 0, "activeParameter": s.active })
}

/// The protocol's kind of a symbol.
fn symbol_kind(sort: Sort) -> u32 {
    match sort {
        Sort::Module => 2,
        Sort::Impl => 5,
        Sort::Method => 6,
        Sort::Field => 8,
        Sort::Function | Sort::Test | Sort::Macro => 12,
        Sort::Local | Sort::Parameter | Sort::Keyword => 13,
        Sort::Constant => 14,
        Sort::Trait | Sort::Effect => 11,
        Sort::Variant => 22,
        Sort::Type => 23,
    }
}

/// The document symbols of a file, nested.
pub(crate) fn symbols(text: &str, symbols: &[Symbol]) -> Vec<Value> {
    symbols
        .iter()
        .map(|s| {
            let mut shown = json!({
                "name": s.name,
                "kind": symbol_kind(s.sort),
                "range": range(text, s.start, s.end),
                "selectionRange": range(text, s.name_start, s.name_end),
                "children": self::symbols(text, &s.children),
            });
            if let Some(detail) = &s.detail {
                shown["detail"] = json!(detail);
            }
            shown
        })
        .collect()
}

/// A symbol of the program, with where its name is.
pub(crate) fn workspace_symbol(uri: &str, text: &str, s: &Symbol) -> Value {
    let location = json!({ "uri": uri, "range": range(text, s.name_start, s.name_end) });
    let mut shown = json!({ "name": s.name, "kind": symbol_kind(s.sort), "location": location });
    if let Some(detail) = &s.detail {
        shown["containerName"] = json!(detail);
    }
    shown
}

/// An inlay hint: a type, of kind 1, written right after its binding; facts, with no kind,
/// written before a function's body with a space after them, each fact a part of the label
/// with its meaning and its causes as a tooltip and the line of its first cause as the place a
/// click goes to; or what a line does that causes facts, with no kind, after a space at the
/// line's end.
pub(crate) fn hint(text: &str, uri: &str, h: &Hint) -> Value {
    let at = position(text, h.at as usize);
    match h.sort {
        HintSort::Type => json!({ "position": at, "label": h.label, "kind": 1 }),
        HintSort::Causes => json!({ "position": at, "label": h.label, "paddingLeft": true }),
        HintSort::Facts if h.parts.is_empty() => {
            json!({ "position": at, "label": h.label, "paddingRight": true })
        }
        HintSort::Facts => {
            let parts: Vec<Value> = h.parts.iter().map(|p| hint_part(text, uri, p)).collect();
            json!({ "position": at, "label": parts, "paddingRight": true })
        }
    }
}

/// A part of a hint's label: its text, and for a fact, its meaning and each cause, by line,
/// in Markdown, with the place of its first cause.
fn hint_part(text: &str, uri: &str, part: &HintPart) -> Value {
    let mut shown = json!({ "value": part.text });
    let Some(meaning) = &part.meaning else {
        return shown;
    };
    let causes: Vec<String> = (part.causes.iter())
        .map(|(line, says)| format!("- [Line {line}]({uri}#L{line}): {says}"))
        .collect();
    let mut tooltip = format!("**`{}`**: {meaning}", part.text);
    if !causes.is_empty() {
        tooltip = format!("{tooltip}\n\n{}", causes.join("\n"));
    }
    shown["tooltip"] = markdown(&tooltip);
    if let Some((line, _)) = part.causes.first()
        && let Some((start, end)) = line_span(text, *line)
    {
        shown["location"] = json!({ "uri": uri, "range": range(text, start, end) });
    }
    shown
}

/// The bytes of line `line` of `text`, counted from 1, without the blanks around its code.
fn line_span(text: &str, line: u32) -> Option<(u32, u32)> {
    let mut start = 0;
    for _ in 1..line {
        start += text[start..].find('\n')? + 1;
    }
    let end = text[start..].find('\n').map_or(text.len(), |n| start + n);
    let code = &text[start..end];
    let lead = code.len() - code.trim_start().len();
    let byte = crate::server::byte;
    Some((byte(start + lead), byte(start + code.trim_end().len())))
}

/// A folding range by lines, of a span over more than one line. A span that ends with a
/// closing bracket on a line of its own keeps that line unfolded.
pub(crate) fn fold(text: &str, f: &Fold) -> Option<Value> {
    let line = |n: u32| position(text, n as usize)["line"].as_u64().unwrap_or(0);
    let start = line(f.start);
    let mut end = line(f.end);
    let before = text.get(..f.end as usize).unwrap_or(text);
    if f.sort == FoldSort::Code && before.ends_with(['}', ')', ']']) {
        end = end.saturating_sub(1);
    }
    if end <= start {
        return None;
    }
    let mut shown = json!({ "startLine": start, "endLine": end });
    match f.sort {
        FoldSort::Comment => shown["kind"] = json!("comment"),
        FoldSort::Imports => shown["kind"] = json!("imports"),
        FoldSort::Code => {}
    }
    Some(shown)
}

/// The edit that replaces all of `text` with `new`, none when they are the same.
pub(crate) fn whole_edit(text: &str, new: &str) -> Value {
    if text == new {
        return json!([]);
    }
    let end = crate::server::byte(text.len());
    json!([{ "range": range(text, 0, end), "newText": new }])
}

/// What the server can do: open, change and close buffers, sent whole; hovers; navigation,
/// where a declaration is its definition; completion after `.` too, with label details;
/// signature help, opened by `(` and moved on by `,`; renaming, prepared first; symbols;
/// formatting; inlay hints; semantic tokens of a whole file; folding and selection ranges;
/// quick fixes, each alone or all of a file's at once; and code lenses, but in Visual Studio
/// Code, whose extension has its own.
pub(crate) fn capabilities(client: Client) -> Value {
    let mut capabilities = json!({
        "capabilities": {
            "positionEncoding": "utf-16",
            "textDocumentSync": { "openClose": true, "change": 1 },
            "hoverProvider": true,
            "definitionProvider": true,
            "declarationProvider": true,
            "typeDefinitionProvider": true,
            "referencesProvider": true,
            "documentHighlightProvider": true,
            "renameProvider": { "prepareProvider": true },
            "completionProvider": {
                "triggerCharacters": ["."],
                "completionItem": { "labelDetailsSupport": true },
            },
            "signatureHelpProvider": { "triggerCharacters": ["(", ","] },
            "documentSymbolProvider": true,
            "workspaceSymbolProvider": true,
            "documentFormattingProvider": true,
            "inlayHintProvider": true,
            "semanticTokensProvider": { "legend": tokens::legend(), "full": true },
            "foldingRangeProvider": true,
            "selectionRangeProvider": true,
            "codeActionProvider": { "codeActionKinds": ["quickfix", FIX_ALL] },
        },
        "serverInfo": { "name": "stilt", "version": env!("CARGO_PKG_VERSION") },
    });
    if !client.vscode {
        let offered = &mut capabilities["capabilities"];
        offered["codeLensProvider"] = json!({ "resolveProvider": false });
        offered["executeCommandProvider"] = json!({ "commands": crate::jobs::COMMANDS });
    }
    capabilities
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::{diagnostic, fix_all, signature};
    use crate::{Diagnostic, Edit, Fix, Signature};

    fn warning(code: &str) -> Diagnostic {
        Diagnostic {
            start: 0,
            end: 3,
            error: false,
            code: code.to_owned(),
            message: "m".to_owned(),
            fixes: Vec::new(),
            notes: Vec::new(),
        }
    }

    #[test]
    fn a_stale_doc_is_deprecated_and_a_hole_is_information() {
        // docs.stale: a stale doc may describe a signature that changed; declarations.typed-holes:
        // a hole is code not written yet.
        let stale = diagnostic("/// a\n", "file:///a.lt", &warning("W0002"));
        assert_eq!(stale["severity"], json!(2));
        assert_eq!(stale["tags"], json!([2]));
        let hole = diagnostic("?\n", "file:///a.lt", &warning("W0300"));
        assert_eq!(hole["severity"], json!(3));
        assert_eq!(hole["tags"], json!(null));
    }

    #[test]
    fn a_code_links_to_its_page() {
        let shown = diagnostic("x\n", "file:///a.lt", &warning("W0300"));
        let href = shown["codeDescription"]["href"]
            .as_str()
            .unwrap_or_default();
        assert!(href.ends_with("/docs/errors/W0300.md"), "{href}");
        let unknown = diagnostic("x\n", "file:///a.lt", &warning("W9999"));
        assert_eq!(unknown["codeDescription"], json!(null));
    }

    #[test]
    fn a_parameter_counts_in_units_of_its_label_from_a_character_it_starts_inside() {
        let s = Signature {
            label: "f(\u{e9}: \u{1F600})".to_owned(),
            params: vec![(3, 99), (7, 10)],
            active: 0,
            docs: None,
        };
        let shown = signature(&s);
        let params = &shown["signatures"][0]["parameters"];
        assert_eq!(params[0]["label"], json!([2, 8]));
        assert_eq!(params[1]["label"], json!([5, 7]));
    }

    #[test]
    fn fixes_at_the_last_byte_there_can_be_clash() {
        let at_end = |code: &str| Diagnostic {
            fixes: vec![Fix {
                title: "f".to_owned(),
                edits: vec![Edit {
                    start: u32::MAX,
                    end: u32::MAX,
                    text: "x".to_owned(),
                }],
            }],
            ..warning(code)
        };
        let all = fix_all("x\n", "file:///a.lt", &[at_end("W0001"), at_end("W0002")]);
        let all = all.expect("the first fix is taken");
        assert_eq!(all["diagnostics"].as_array().map(Vec::len), Some(1));
    }
}

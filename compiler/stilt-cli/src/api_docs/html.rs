//! A package's pages as HTML (docs.stilt-doc): its index, a page for each module, and the
//! stylesheet they share.

use std::fmt::Write as _;

use super::markdown::{escape, html, inline};
use super::{Item, Module, Package};

/// The stylesheet of the pages, light or dark as the reader's system is.
pub(super) const STYLE: &str = include_str!("style.css");

/// The package's index: its name and each module, with its tier and the first line of its
/// description.
pub(super) fn index(package: &Package) -> String {
    let mut body = format!(
        "<h1>{}</h1>\n<ul class=\"modules\">\n",
        escape(&package.name)
    );
    for m in &package.modules {
        let summary = m.description.lines().next().unwrap_or_default();
        let _ = writeln!(
            body,
            "<li><a href=\"{0}.html\"><code>{0}</code></a> <span class=\"tier\">{1}</span>\
             <p>{2}</p></li>",
            escape(&m.address),
            escape(&m.tier),
            inline(summary)
        );
    }
    body.push_str("</ul>\n");
    page(&package.name, &package.name, &body)
}

/// A module's page: its address and tier, its description, a list of its declarations, then
/// each declaration.
pub(super) fn module(package: &Package, m: &Module) -> String {
    let mut body = format!(
        "<h1><code>{}</code> <span class=\"tier\">{}</span></h1>\n{}",
        escape(&m.address),
        escape(&m.tier),
        html(&m.description)
    );
    if !m.items.is_empty() {
        body.push_str("<nav class=\"contents\"><ul>\n");
        for i in &m.items {
            let _ = writeln!(
                body,
                "<li><a href=\"#{0}\"><span class=\"kind\">{1}</span> <code>{0}</code></a></li>",
                escape(&i.name),
                i.kind
            );
        }
        body.push_str("</ul></nav>\n");
    }
    for i in &m.items {
        item(&mut body, i, "", 2);
    }
    page(
        &format!("{} · {}", m.address, package.name),
        &package.name,
        &body,
    )
}

/// A declaration, its anchor `owner` and its name, then what goes under it, one level deeper.
fn item(out: &mut String, i: &Item, owner: &str, level: u8) {
    let anchor = if owner.is_empty() {
        i.name.clone()
    } else {
        format!("{owner}.{}", i.name)
    };
    let _ = write!(
        out,
        "<section class=\"item\" id=\"{0}\">\n<h{1}><span class=\"kind\">{2}</span> \
         <a href=\"#{0}\"><code>{3}</code></a></h{1}>\n<pre class=\"signature\"><code>{4}</code></pre>\n",
        escape(&anchor),
        level + 1,
        i.kind,
        escape(&i.name),
        escape(&i.signature)
    );
    if let Some(facts) = &i.facts {
        out.push_str(&facts_line(facts));
    }
    if !i.doc.is_empty() {
        let _ = write!(out, "<div class=\"doc\">\n{}</div>\n", html(&i.doc));
    }
    if !i.examples.is_empty() {
        out.push_str("<div class=\"examples\"><h5>Examples</h5>\n<pre><code>");
        out.push_str(&escape(&i.examples.join("\n")));
        out.push_str("</code></pre></div>\n");
    }
    for m in &i.members {
        if m.kind == "impl" {
            let _ = writeln!(
                out,
                "<pre class=\"signature impl\"><code>{}</code></pre>",
                escape(&m.signature)
            );
        } else {
            item(out, m, &anchor, level + 1);
        }
    }
    out.push_str("</section>\n");
}

/// A function's limitable facts, as `[panic, alloc]`, each its own span.
fn facts_line(facts: &[String]) -> String {
    let each: Vec<String> = facts
        .iter()
        .map(|f| format!("<span class=\"fact\">{}</span>", escape(f)))
        .collect();
    format!(
        "<p class=\"facts\" title=\"The facts the package's API holds for this function\">\
         [{}]</p>\n",
        each.join(", ")
    )
}

/// A whole page, titled `title`, with a link back to the package's index.
fn page(title: &str, package: &str, body: &str) -> String {
    format!(
        "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
         <title>{}</title>\n<link rel=\"stylesheet\" href=\"style.css\">\n</head>\n<body>\n\
         <header><a href=\"index.html\">{}</a></header>\n<main>\n{body}</main>\n</body>\n</html>\n",
        escape(title),
        escape(package)
    )
}

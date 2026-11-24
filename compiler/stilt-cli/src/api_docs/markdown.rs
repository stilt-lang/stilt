//! The Markdown of docs and descriptions, as a page renders it (docs.markdown): paragraphs,
//! lists whose items start with `-`, fenced code blocks, code spans, emphasis, strong emphasis
//! and links. Any other text is shown as it is, escaped.

use std::fmt::Write as _;

/// The HTML of Markdown text, whose blocks are separated by blank lines, and a list's items
/// each start with `- `.
pub(super) fn html(text: &str) -> String {
    let mut out = String::new();
    let mut paragraph: Vec<&str> = Vec::new();
    let mut list: Vec<String> = Vec::new();
    let mut lines = text.lines();
    while let Some(line) = lines.next() {
        let trimmed = line.trim();
        if trimmed.starts_with("```") {
            close(&mut out, &mut paragraph, &mut list);
            let code: Vec<&str> = lines
                .by_ref()
                .take_while(|l| !l.trim().starts_with("```"))
                .collect();
            let _ = writeln!(out, "<pre><code>{}</code></pre>", escape(&code.join("\n")));
        } else if let Some(item) = trimmed.strip_prefix("- ") {
            flush(&mut out, &mut paragraph);
            list.push(item.to_owned());
        } else if trimmed.is_empty() {
            close(&mut out, &mut paragraph, &mut list);
        } else if let Some(last) = list.last_mut().filter(|_| line.starts_with(' ')) {
            last.push(' ');
            last.push_str(trimmed);
        } else {
            end_list(&mut out, &mut list);
            paragraph.push(trimmed);
        }
    }
    close(&mut out, &mut paragraph, &mut list);
    out
}

fn close(out: &mut String, paragraph: &mut Vec<&str>, list: &mut Vec<String>) {
    flush(out, paragraph);
    end_list(out, list);
}

fn flush(out: &mut String, paragraph: &mut Vec<&str>) {
    if !paragraph.is_empty() {
        let _ = writeln!(out, "<p>{}</p>", inline(&paragraph.join(" ")));
        paragraph.clear();
    }
}

fn end_list(out: &mut String, list: &mut Vec<String>) {
    if !list.is_empty() {
        out.push_str("<ul>\n");
        for item in list.drain(..) {
            let _ = writeln!(out, "<li>{}</li>", inline(&item));
        }
        out.push_str("</ul>\n");
    }
}

/// The HTML of a line's inline Markdown: code spans first, whose contents are only escaped,
/// then links, strong emphasis and emphasis in the text between them.
pub(super) fn inline(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(start) = rest.find('`') {
        let Some(len) = rest[start + 1..].find('`') else {
            break;
        };
        out.push_str(&spans(&rest[..start]));
        let code = &rest[start + 1..start + 1 + len];
        let _ = write!(out, "<code>{}</code>", escape(code));
        rest = &rest[start + len + 2..];
    }
    out.push_str(&spans(rest));
    out
}

/// Links, strong emphasis and emphasis, in text without code spans.
fn spans(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while !rest.is_empty() {
        if let Some((label, url, after)) = link(rest) {
            let _ = write!(out, "<a href=\"{}\">{}</a>", escape(url), spans(label));
            rest = after;
        } else if let Some((inner, after)) = delimited(rest, "**") {
            let _ = write!(out, "<strong>{}</strong>", spans(inner));
            rest = after;
        } else if let Some((inner, after)) = delimited(rest, "*") {
            let _ = write!(out, "<em>{}</em>", spans(inner));
            rest = after;
        } else {
            let c = rest.chars().next().unwrap_or_default();
            out.push_str(&escape(&c.to_string()));
            rest = &rest[c.len_utf8()..];
        }
    }
    out
}

/// `[label](url)` at the start of `text`: the label, the URL and what follows.
fn link(text: &str) -> Option<(&str, &str, &str)> {
    let label_end = text.strip_prefix('[')?.find("](")? + 1;
    let url_len = text[label_end + 2..].find(')')?;
    let url = &text[label_end + 2..label_end + 2 + url_len];
    (!url.contains(' ')).then_some((&text[1..label_end], url, &text[label_end + 3 + url_len..]))
}

/// Text between two `mark`s at the start of `text`, not empty and not starting or ending with a
/// space: what they hold, and what follows.
fn delimited<'t>(text: &'t str, mark: &str) -> Option<(&'t str, &'t str)> {
    let body = text.strip_prefix(mark)?;
    let end = body.find(mark)?;
    let inner = &body[..end];
    let spaced = inner.starts_with(' ') || inner.ends_with(' ');
    (!inner.is_empty() && !spaced).then_some((inner, &body[end + mark.len()..]))
}

/// Text with `&`, `<`, `>` and `"` written as HTML's entities.
pub(super) fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            _ => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_and_spans() {
        let text = "A **strong** *word* and [a link](https://x.org).\n\n- one `a<b>`\n  more\n- two\n\n```\nlet x = 1 < 2\n```";
        assert_eq!(
            html(text),
            "<p>A <strong>strong</strong> <em>word</em> and <a href=\"https://x.org\">a link</a>.</p>\n\
             <ul>\n<li>one <code>a&lt;b&gt;</code> more</li>\n<li>two</li>\n</ul>\n\
             <pre><code>let x = 1 &lt; 2</code></pre>\n"
        );
    }

    #[test]
    fn text_that_is_no_span_stays_as_it_is() {
        assert_eq!(inline("2 * 3 * 4, `x"), "2 * 3 * 4, `x");
        assert_eq!(inline("[no](link with spaces)"), "[no](link with spaces)");
        assert_eq!(inline("a_b_c <i>"), "a_b_c &lt;i&gt;");
    }
}

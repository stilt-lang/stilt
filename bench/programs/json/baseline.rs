//! json: writes a JSON document of 20000 records, parses it back into a tree with a
//! recursive-descent parser, and sums what the tree holds.

enum Json {
    Null,
    Bool(bool),
    Num(i64),
    Text(String),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

fn document(n: i64) -> String {
    let mut parts = Vec::new();
    for i in 0..n {
        let active = if i % 3 == 0 { "true" } else { "false" };
        let note = if i % 5 == 0 { "null".to_string() } else { format!("\"line\\none \\\"{i}\\\"\"") };
        parts.push(format!(
            "{{\"id\": {i}, \"name\": \"item{i}\", \"active\": {active}, \"tags\": [\"a\", \"b{}\"], \"point\": {{\"x\": {}, \"y\": [1, 2, {}]}}, \"note\": {note}}}",
            i % 4,
            i % 7,
            i % 11
        ));
    }
    format!("[{}]", parts.join(", "))
}

fn skip_space(text: &[u8], pos: &mut usize) {
    while *pos < text.len() && (text[*pos] == 32 || text[*pos] == 10) {
        *pos += 1;
    }
}

fn string(source: &str, text: &[u8], pos: &mut usize) -> String {
    *pos += 1;
    let mut pieces = Vec::new();
    let mut start = *pos;
    while text[*pos] != 34 {
        if text[*pos] == 92 {
            pieces.push(&source[start..*pos]);
            let escaped = text[*pos + 1];
            pieces.push(if escaped == 110 { "\n" } else { &source[*pos + 1..*pos + 2] });
            *pos += 2;
            start = *pos;
        } else {
            *pos += 1;
        }
    }
    pieces.push(&source[start..*pos]);
    *pos += 1;
    pieces.join("")
}

fn number(text: &[u8], pos: &mut usize) -> i64 {
    let mut n = 0;
    while *pos < text.len() && text[*pos] >= 48 && text[*pos] <= 57 {
        n = n * 10 + i64::from(text[*pos] - 48);
        *pos += 1;
    }
    n
}

fn value(source: &str, text: &[u8], pos: &mut usize) -> Json {
    skip_space(text, pos);
    let c = text[*pos];
    if c == 123 {
        *pos += 1;
        let mut fields = Vec::new();
        skip_space(text, pos);
        while text[*pos] != 125 {
            skip_space(text, pos);
            let key = string(source, text, pos);
            skip_space(text, pos);
            *pos += 1;
            fields.push((key, value(source, text, pos)));
            skip_space(text, pos);
            if text[*pos] == 44 {
                *pos += 1;
            }
        }
        *pos += 1;
        Json::Object(fields)
    } else if c == 91 {
        *pos += 1;
        let mut items = Vec::new();
        skip_space(text, pos);
        while text[*pos] != 93 {
            items.push(value(source, text, pos));
            skip_space(text, pos);
            if text[*pos] == 44 {
                *pos += 1;
            }
        }
        *pos += 1;
        Json::Array(items)
    } else if c == 34 {
        Json::Text(string(source, text, pos))
    } else if c == 116 {
        *pos += 4;
        Json::Bool(true)
    } else if c == 102 {
        *pos += 5;
        Json::Bool(false)
    } else if c == 110 {
        *pos += 4;
        Json::Null
    } else {
        Json::Num(number(text, pos))
    }
}

struct Totals {
    numbers: i64,
    texts: i64,
    trues: i64,
    nulls: i64,
    nodes: i64,
}

fn add(totals: &mut Totals, json: &Json) {
    totals.nodes += 1;
    match json {
        Json::Null => totals.nulls += 1,
        Json::Bool(b) => {
            if *b {
                totals.trues += 1;
            }
        }
        Json::Num(n) => totals.numbers += n,
        Json::Text(s) => totals.texts += s.len() as i64,
        Json::Array(items) => {
            for item in items {
                add(totals, item);
            }
        }
        Json::Object(fields) => {
            for (key, item) in fields {
                totals.texts += key.len() as i64;
                add(totals, item);
            }
        }
    }
}

fn main() {
    let size = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(20000);
    let source = document(size);
    let text = source.as_bytes();
    let mut pos = 0;
    let json = value(&source, text, &mut pos);
    let mut totals = Totals { numbers: 0, texts: 0, trues: 0, nulls: 0, nodes: 0 };
    add(&mut totals, &json);
    println!("{} bytes, {} nodes", source.len(), totals.nodes);
    println!(
        "numbers {}, text {}, true {}, null {}",
        totals.numbers, totals.texts, totals.trues, totals.nulls
    );
}

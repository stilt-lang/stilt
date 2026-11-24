//! TOML 1.0 (<https://toml.io/en/v1.0.0>), which manifests are written in (packages.manifest).
//!
//! The parser keeps the place of every key and value, which manifest errors are reported at, and
//! the end of every value, after which `check` writes what it fills in (packages.filling-in). A
//! text that isn't TOML 1.0 is one error, at the first character from which no TOML document can
//! continue; a key or table defined twice, at the first character of the key that defines it again.

mod scan;
mod strings;

use scan::Cursor;

/// Why a text isn't TOML 1.0, and where: a byte offset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    /// The byte offset of the error.
    pub at: usize,
    /// What is wrong.
    pub message: String,
}

impl Error {
    fn at(at: usize, message: impl Into<String>) -> Self {
        Self {
            at,
            message: message.into(),
        }
    }
}

/// A value, from its first byte to the byte after its last.
#[derive(Clone, Debug, PartialEq)]
pub struct Value {
    /// The offset of its first byte.
    pub at: usize,
    /// The offset past its last byte.
    pub end: usize,
    /// What kind of value it is.
    pub kind: ValueKind,
}

/// The kinds of value (TOML 1.0).
#[derive(Clone, Debug, PartialEq)]
pub enum ValueKind {
    /// A string.
    String(String),
    /// An integer.
    Integer(i64),
    /// A float.
    Float,
    /// A boolean.
    Bool(bool),
    /// A date or time.
    Datetime,
    /// An array.
    Array(Vec<Value>),
    /// A table.
    Table(Table),
    /// An array of tables, `[[name]]`.
    Tables(Vec<Table>),
}

impl ValueKind {
    /// The kind of value, as errors name it.
    #[must_use]
    pub fn describe(&self) -> &'static str {
        match self {
            Self::String(_) => "a string",
            Self::Integer(_) => "an integer",
            Self::Float => "a float",
            Self::Bool(_) => "a boolean",
            Self::Datetime => "a date",
            Self::Array(_) => "an array",
            Self::Table(_) => "a table",
            Self::Tables(_) => "an array of tables",
        }
    }
}

/// How a table came to be, which decides how it may be added to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Defined {
    /// As the super-table of a header, `a` for `[a.b]`, which a header of its own may define.
    Implicitly,
    /// By a header `[a]`.
    Header,
    /// By dotted keys, `a.b = 1`.
    Dotted,
    /// As an inline table, `{ … }`, which nothing adds to.
    Inline,
}

/// A table: its entries in the order of their definitions.
#[derive(Clone, Debug, PartialEq)]
pub struct Table {
    /// How the table came to be.
    pub defined: Defined,
    /// The entries of the table.
    pub entries: Vec<Entry>,
    /// The end of the table's last key-value pair, or of its header when it has none.
    pub end: usize,
}

/// A key of a table, where it is first written, and its value.
#[derive(Clone, Debug, PartialEq)]
pub struct Entry {
    /// The key.
    pub key: String,
    /// The offset of the key.
    pub at: usize,
    /// The value of the key.
    pub value: Value,
}

impl Table {
    fn new(defined: Defined, end: usize) -> Self {
        Self {
            defined,
            entries: Vec::new(),
            end,
        }
    }

    /// The value of `key`, if the table has it.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.entries.iter().find(|e| e.key == key).map(|e| &e.value)
    }

    fn get_mut(&mut self, key: &str) -> Option<&mut Value> {
        self.entries
            .iter_mut()
            .find(|e| e.key == key)
            .map(|e| &mut e.value)
    }
}

/// A key as written: each of its dotted parts, with where it starts.
type Key = Vec<(String, usize)>;

/// Parses a TOML 1.0 document, whose root table it gives.
///
/// # Errors
///
/// The first place from which the text isn't TOML 1.0.
pub fn parse(bytes: &[u8]) -> Result<Table, Error> {
    let text = std::str::from_utf8(bytes)
        .map_err(|e| Error::at(e.valid_up_to(), "the file isn't UTF-8"))?;
    let mut parser = Parser {
        cursor: Cursor::new(text),
        root: Table::new(Defined::Header, 0),
        current: Vec::new(),
    };
    parser.document()?;
    Ok(parser.root)
}

struct Parser<'a> {
    cursor: Cursor<'a>,
    root: Table,
    /// The path of the table that the last header opened.
    current: Vec<String>,
}

impl Parser<'_> {
    fn document(&mut self) -> Result<(), Error> {
        loop {
            let c = &mut self.cursor;
            c.ws();
            match c.peek() {
                None => return Ok(()),
                Some('#') => c.comment()?,
                Some('\n' | '\r') => {}
                Some('[') => self.header()?,
                Some(_) => {
                    let (key, value) = self.key_value()?;
                    let current = self.current.clone();
                    let table = table_at(&mut self.root, &current);
                    table.end = value.end;
                    define(table, &key, value)?;
                }
            }
            let c = &mut self.cursor;
            c.ws();
            c.comment()?;
            if c.peek().is_some() && !c.newline()? {
                return Err(c.error("expected the end of the line"));
            }
        }
    }

    /// A table's header, `[a.b]`, or an array of tables', `[[a.b]]`.
    fn header(&mut self) -> Result<(), Error> {
        let c = &mut self.cursor;
        c.bump();
        let array = c.eat('[');
        c.ws();
        let key = self.key()?;
        let c = &mut self.cursor;
        c.expect(']', "`]`")?;
        if array {
            c.expect(']', "`]]`")?;
        }
        let end = c.pos;
        open(&mut self.root, &key, array, end)?;
        self.current = key.into_iter().map(|(k, _)| k).collect();
        Ok(())
    }

    /// A key, followed by the spaces after it.
    fn key(&mut self) -> Result<Key, Error> {
        let c = &mut self.cursor;
        let mut key = Vec::new();
        loop {
            let at = c.pos;
            let part = match c.peek() {
                Some('"' | '\'') if c.peek_at(1) == c.peek() && c.peek_at(2) == c.peek() => {
                    return Err(c.error("a key isn't a multi-line string"));
                }
                Some('"' | '\'') => c.string()?,
                _ => {
                    let bare = c.text[at..]
                        .chars()
                        .take_while(|&ch| ch.is_ascii_alphanumeric() || ch == '_' || ch == '-')
                        .count();
                    if bare == 0 {
                        return Err(c.error("expected a key"));
                    }
                    c.pos += bare;
                    c.text[at..c.pos].to_owned()
                }
            };
            key.push((part, at));
            c.ws();
            if !c.eat('.') {
                return Ok(key);
            }
            c.ws();
        }
    }

    fn key_value(&mut self) -> Result<(Key, Value), Error> {
        let key = self.key()?;
        let c = &mut self.cursor;
        c.expect('=', "`=`")?;
        c.ws();
        let value = self.value()?;
        Ok((key, value))
    }

    fn value(&mut self) -> Result<Value, Error> {
        let c = &mut self.cursor;
        let at = c.pos;
        let kind = match c.peek() {
            Some('"' | '\'') => ValueKind::String(c.string()?),
            Some('t') => c.word("true").map(|()| ValueKind::Bool(true))?,
            Some('f') => c.word("false").map(|()| ValueKind::Bool(false))?,
            Some('[') => self.array()?,
            Some('{') => self.inline_table()?,
            Some(ch) if ch.is_ascii_digit() || matches!(ch, '+' | '-' | 'i' | 'n') => c.number()?,
            _ => return Err(c.error("expected a value")),
        };
        Ok(Value {
            at,
            end: self.cursor.pos,
            kind,
        })
    }

    /// An array, whose values may be spread over lines, with comments between them.
    fn array(&mut self) -> Result<ValueKind, Error> {
        self.cursor.bump();
        let mut values = Vec::new();
        loop {
            self.blank()?;
            if self.cursor.eat(']') {
                return Ok(ValueKind::Array(values));
            }
            values.push(self.value()?);
            self.blank()?;
            if self.cursor.eat(']') {
                return Ok(ValueKind::Array(values));
            }
            self.cursor.expect(',', "`,` or `]`")?;
        }
    }

    /// Spaces, comments and newlines, as an array may hold between its values.
    fn blank(&mut self) -> Result<(), Error> {
        loop {
            let c = &mut self.cursor;
            c.ws();
            c.comment()?;
            if !c.newline()? {
                return Ok(());
            }
        }
    }

    /// An inline table, on one line, whose pairs are separated by commas without a trailing one.
    fn inline_table(&mut self) -> Result<ValueKind, Error> {
        let c = &mut self.cursor;
        c.bump();
        c.ws();
        let mut table = Table::new(Defined::Dotted, c.pos);
        if c.eat('}') {
            table.defined = Defined::Inline;
            return Ok(ValueKind::Table(table));
        }
        loop {
            let (key, value) = self.key_value()?;
            table.end = value.end;
            define(&mut table, &key, value)?;
            let c = &mut self.cursor;
            c.ws();
            if c.eat('}') {
                table.defined = Defined::Inline;
                return Ok(ValueKind::Table(table));
            }
            c.expect(',', "`,` or `}`")?;
            c.ws();
        }
    }
}

/// The table at `path`, which earlier headers made: through an array of tables, its last.
fn table_at<'t>(root: &'t mut Table, path: &[String]) -> &'t mut Table {
    path.iter().fold(root, |table, key| {
        match &mut table.get_mut(key).expect("a header made the table").kind {
            ValueKind::Table(t) => t,
            ValueKind::Tables(ts) => ts.last_mut().expect("an array of tables has one"),
            _ => unreachable!("a header's path holds tables"),
        }
    })
}

/// Defines `key` as `value` in `table`, through the tables its dotted parts name.
fn define(table: &mut Table, key: &Key, value: Value) -> Result<(), Error> {
    let start = key[0].1;
    let twice = || Error::at(start, "this key is already defined");
    let (last, parts) = key.split_last().expect("a key has a part");
    let mut table = table;
    for (part, at) in parts {
        if table.get(part).is_none() {
            let value = Value {
                at: *at,
                end: value.end,
                kind: ValueKind::Table(Table::new(Defined::Dotted, value.end)),
            };
            table.entries.push(Entry {
                key: part.clone(),
                at: *at,
                value,
            });
        }
        table = match &mut table.get_mut(part).expect("defined above").kind {
            ValueKind::Table(t) if matches!(t.defined, Defined::Dotted | Defined::Implicitly) => {
                t.defined = Defined::Dotted;
                t.end = value.end;
                t
            }
            _ => return Err(twice()),
        };
    }
    if table.get(&last.0).is_some() {
        return Err(twice());
    }
    table.entries.push(Entry {
        key: last.0.clone(),
        at: last.1,
        value,
    });
    Ok(())
}

/// Opens the table of a header, or a new table of an array of tables.
fn open(root: &mut Table, key: &Key, array: bool, end: usize) -> Result<(), Error> {
    let start = key[0].1;
    let twice = || Error::at(start, "this table is already defined");
    let (last, parts) = key.split_last().expect("a key has a part");
    let mut table = root;
    for (part, at) in parts {
        if table.get(part).is_none() {
            let value = Value {
                at: *at,
                end,
                kind: ValueKind::Table(Table::new(Defined::Implicitly, end)),
            };
            table.entries.push(Entry {
                key: part.clone(),
                at: *at,
                value,
            });
        }
        table = match &mut table.get_mut(part).expect("defined above").kind {
            ValueKind::Table(t) if t.defined != Defined::Inline => t,
            ValueKind::Tables(ts) => ts.last_mut().expect("an array of tables has one"),
            _ => return Err(twice()),
        };
    }
    let fresh = Table::new(Defined::Header, end);
    match table.get_mut(&last.0).map(|v| &mut v.kind) {
        None => {
            let kind = if array {
                ValueKind::Tables(vec![fresh])
            } else {
                ValueKind::Table(fresh)
            };
            table.entries.push(Entry {
                key: last.0.clone(),
                at: last.1,
                value: Value {
                    at: last.1,
                    end,
                    kind,
                },
            });
            Ok(())
        }
        Some(ValueKind::Table(t)) if !array && t.defined == Defined::Implicitly => {
            t.defined = Defined::Header;
            t.end = end;
            Ok(())
        }
        Some(ValueKind::Tables(ts)) if array => {
            ts.push(fresh);
            Ok(())
        }
        Some(_) => Err(twice()),
    }
}

#[cfg(test)]
mod tests;

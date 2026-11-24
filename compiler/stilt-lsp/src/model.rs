//! What the backend answers with, each span in bytes of a file's text, before the server writes
//! it in the protocol's positions.

use std::path::PathBuf;

use serde::{Deserialize, Serialize};

/// A diagnostic of a file, its spans in bytes of the file's text.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostic {
    /// The byte where the span starts.
    pub start: u32,
    /// The byte where the span ends, past its last.
    pub end: u32,
    /// Whether it is an error, rather than a warning.
    pub error: bool,
    /// The diagnostic's code, such as `E0001`.
    pub code: String,
    /// What the diagnostic says.
    pub message: String,
    /// The fixes the editor offers for it.
    pub fixes: Vec<Fix>,
    /// Other spans of the file that the diagnostic points at, each with what it shows, such
    /// as the template of a macro whose expansion has the error (macros.errors-in-expansions).
    pub notes: Vec<Note>,
}

/// A span of a diagnostic's file that it points at besides its own, and what it shows.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Note {
    /// The byte where the span starts.
    pub start: u32,
    /// The byte where the span ends, past its last.
    pub end: u32,
    /// What the span shows.
    pub text: String,
}

/// A fix of a diagnostic: edits of the diagnostic's file.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Fix {
    /// What the fix does, as the editor lists it.
    pub title: String,
    /// The edits that make the fix.
    pub edits: Vec<Edit>,
}

/// An edit: the bytes from `start` to `end` replaced by `text`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Edit {
    /// The byte where the span starts.
    pub start: u32,
    /// The byte where the replaced text ends, past its last.
    pub end: u32,
    /// The text written in place of the bytes.
    pub text: String,
}

/// The diagnostics of one file of the program.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FileDiagnostics {
    /// The file's canonical path.
    pub path: PathBuf,
    /// The diagnostics of the file.
    pub diagnostics: Vec<Diagnostic>,
}

/// A span of a file, as a definition is found at.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Place {
    /// The file's canonical path.
    pub path: PathBuf,
    /// The byte where the span starts.
    pub start: u32,
    /// The byte where the span ends, past its last.
    pub end: u32,
}

/// What a name stands for, which decides the icon of a completion or a symbol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Sort {
    /// A local binding.
    Local,
    /// A parameter of a function.
    Parameter,
    /// A function.
    Function,
    /// A method of a type or a trait.
    Method,
    /// A field of a record.
    Field,
    /// A variant of an enum.
    Variant,
    /// A type.
    Type,
    /// A trait.
    Trait,
    /// A constant.
    Constant,
    /// A test.
    Test,
    /// A macro.
    Macro,
    /// A user-defined effect (handlers.declaring-effect), whose operations are its members.
    Effect,
    /// A module.
    Module,
    /// A keyword.
    Keyword,
    /// An `impl`, which holds the members of a type or a trait's for it.
    Impl,
}

/// A name that completion offers, with its signature or type and its doc.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Completion {
    /// The name as it is written.
    pub label: String,
    /// What the name stands for.
    pub sort: Sort,
    /// The signature of a function, the type of a variable or a field, or a type's definition.
    pub detail: Option<String>,
    /// The doc comment, in Markdown.
    pub docs: Option<String>,
    /// What to write in place of the label, as a snippet whose `$1`, `${2:name}` and `$0` are
    /// the places the cursor visits in turn: a call's parentheses with a placeholder for each
    /// parameter, or a keyword's construct. `None` writes the label.
    pub insert: Option<String>,
}

/// The signature of the function a call calls, with the parameter being written.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Signature {
    /// The header, as code calls the function.
    pub label: String,
    /// Each parameter's span in the label, in bytes.
    pub params: Vec<(u32, u32)>,
    /// The parameter being written, among `params`.
    pub active: u32,
    /// The function's doc comment, in Markdown.
    pub docs: Option<String>,
}

/// A declaration of a file, with the declarations inside it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Symbol {
    /// The name of the declaration.
    pub name: String,
    /// What the declaration is.
    pub sort: Sort,
    /// Its signature or its type, on one line.
    pub detail: Option<String>,
    /// Its file's canonical path.
    pub path: PathBuf,
    /// The whole declaration.
    pub start: u32,
    /// The byte where the whole declaration ends.
    pub end: u32,
    /// Its name.
    pub name_start: u32,
    /// The byte where its name ends.
    pub name_end: u32,
    /// The declarations inside it.
    pub children: Vec<Symbol>,
}

/// What an inlay hint shows.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HintSort {
    /// The inferred type of a binding that writes none.
    Type,
    /// The inferred facts of a function, after its signature.
    Facts,
    /// What a line of a function does that causes its facts, at the line's end, as
    /// `stilt show` writes it there (modes.show).
    Causes,
}

/// A hint written in at a byte of a file.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hint {
    /// The byte the hint is written in at.
    pub at: u32,
    /// The text of the hint.
    pub label: String,
    /// What the hint shows.
    pub sort: HintSort,
    /// The pieces of the label, for facts: each fact with what it means and the lines that
    /// cause it, and the text between them. Empty for a label of one piece.
    pub parts: Vec<HintPart>,
}

/// A piece of a hint's label.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HintPart {
    /// The text of the piece.
    pub text: String,
    /// What it means, in Markdown, for a fact.
    pub meaning: Option<String>,
    /// The lines of the file that cause it, from 1, each with what it does there.
    pub causes: Vec<(u32, String)>,
}

/// What a token of a file is, for semantic highlighting.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TokenSort {
    /// A keyword, marked [`modifier::CONTROL_FLOW`] when it directs control.
    Keyword,
    /// `true` or `false`.
    Boolean,
    /// `self` or `Self`.
    SelfKeyword,
    /// An effect: a built-in label or limit where it acts as a keyword, in a row or after
    /// `without`, such as `io`, `raise`, `panic` or `fs`, marked [`modifier::LIBRARY`]; or an
    /// effect a program declares, where it is declared and where a row names it.
    Effect,
    /// A type.
    Type,
    /// A trait.
    Trait,
    /// A type parameter.
    TypeParameter,
    /// A row variable.
    RowVariable,
    /// A function.
    Function,
    /// A method.
    Method,
    /// A parameter.
    Parameter,
    /// A variable.
    Variable,
    /// A field.
    Field,
    /// A variant of an enum.
    Variant,
    /// A module.
    Module,
    /// A macro.
    Macro,
    /// A macro's fragment, `$cond`.
    Fragment,
    /// A comment.
    Comment,
    /// A string literal.
    String,
    /// An escape of a string literal, such as `\n` or `\u{1F600}` (lexical.escapes).
    EscapeSequence,
    /// The braces of a string's interpolation.
    Interpolation,
    /// The format spec of an interpolation, from its `:`, as in `{x:>8.2}` (lexical.format-specs).
    FormatSpecifier,
    /// A number literal.
    Number,
    /// An operator.
    Operator,
}

/// The modifiers of a token, each a bit.
pub mod modifier {
    /// Where the name is declared.
    pub const DECLARATION: u32 = 1;
    /// A binding that can't change, a constant's.
    pub const READONLY: u32 = 1 << 1;
    /// A doc comment, or a doc example's code.
    pub const DOCUMENTATION: u32 = 1 << 2;
    /// A `var`'s binding, or an `inout` parameter, which code may change.
    pub const MUTABLE: u32 = 1 << 3;
    /// A name of the standard library, or a built-in effect.
    pub const LIBRARY: u32 = 1 << 4;
    /// A keyword that directs control: a branch, a loop, a jump, a failure or a handler's, as
    /// `if`, `for`, `return`, `try` or `resume`.
    pub const CONTROL_FLOW: u32 = 1 << 5;
}

/// A place in a file where the name a highlight was asked about stands, and whether code writes
/// it there: where it is bound, or where an assignment changes it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Highlight {
    /// The byte where the span starts.
    pub start: u32,
    /// The byte where the span ends, past its last.
    pub end: u32,
    /// Whether code writes the name there.
    pub write: bool,
}

/// A token of a file, for semantic highlighting: on one line, in bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Token {
    /// The byte where the span starts.
    pub start: u32,
    /// The byte where the span ends, past its last.
    pub end: u32,
    /// What the token is.
    pub sort: TokenSort,
    /// Bits of [`modifier`].
    pub modifiers: u32,
}

/// What a folding range folds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FoldSort {
    /// Code between braces, such as a function body.
    Code,
    /// A run of comments.
    Comment,
    /// A run of imports.
    Imports,
}

/// A span of a file that the editor may fold.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Fold {
    /// The byte where the span starts.
    pub start: u32,
    /// The byte where the span ends, past its last.
    pub end: u32,
    /// What the range folds.
    pub sort: FoldSort,
}

/// Where a position of a file is in the program: its module, with the module's tier
/// (program.module-tier), and the function around it, by its address, as `stilt show` takes it
/// (edits.paths).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Whereabouts {
    /// The name of the file's module.
    pub module: String,
    /// The module's tier.
    pub tier: String,
    /// The address of the function around the position, if one is.
    pub function: Option<String>,
}

/// The edits of a rename, by each file's canonical path, or why it is refused.
pub type Renamed = Result<Vec<(PathBuf, Vec<Edit>)>, String>;

/// What a code lens runs, as `stilt test` and `stilt run` do.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Job {
    /// The program's tests, doc examples and properties, each of which shows its result.
    Tests,
    /// The program's `main`.
    Main,
}

/// A code lens: a job, run from the line of the byte `at`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Lens {
    /// The byte the lens's line holds: a test's `test`, a doc example's comment, `fn main`.
    pub at: u32,
    /// What the lens runs.
    pub job: Job,
}

/// What a job's process gave: its exit status, `None` when it was stopped, and its output.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Output {
    /// Its exit status.
    pub code: Option<i32>,
    /// Its standard output.
    pub stdout: String,
    /// Its standard error.
    pub stderr: String,
}

/// What a run of a job found.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Ran {
    /// Each result, which a lens shows at its line until a file changes.
    pub outcomes: Vec<Outcome>,
    /// A line on the run as a whole, as `3 passed, 1 failed`, which the editor shows.
    pub summary: String,
}

/// A result of a job: a case's, or the program's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outcome {
    /// The canonical path of the case's file and its line, from 1; `None` for the result of the
    /// whole job, shown at its own lens.
    pub at: Option<(PathBuf, u32)>,
    /// Whether it passed, or exited with 0.
    pub passed: bool,
    /// What the lens shows, on one line.
    pub label: String,
    /// What the editor shows when the lens is chosen: why it failed, or the program's output.
    pub detail: String,
}

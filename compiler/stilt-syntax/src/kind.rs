//! The kinds of the tokens and nodes of the lossless syntax tree.

/// Defines [`SyntaxKind`] and the table that turns a raw kind back into one.
macro_rules! syntax_kinds {
    ($($kind:ident,)*) => {
        /// The kind of a token or a node.
        ///
        /// Tokens come first: those the lexer produces, then the contextual keywords, which the
        /// parser gives to identifiers (lexical.contextual-keywords), then the tokens that only the
        /// parser reads, which stand for separators, doc comments and the end of the input. Nodes
        /// follow. Each is named for the token or the node it stands for, as `IF_KW` or
        /// `MATCH_EXPR`, and so has no doc of its own.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[repr(u16)]
        #[allow(non_camel_case_types, clippy::upper_case_acronyms, missing_docs)]
        pub enum SyntaxKind {
            $($kind,)*
        }

        const ALL: &[SyntaxKind] = &[$(SyntaxKind::$kind,)*];
    };
}

syntax_kinds! {
    // Trivia
    WHITESPACE,
    NEWLINE,
    COMMENT,
    DOC_COMMENT,

    // Names and literals
    LOWER_IDENT,
    UPPER_IDENT,
    UNDERSCORE,
    INT,
    FLOAT,
    STRING,
    STRING_HEAD,
    STRING_MID,
    STRING_TAIL,
    FORMAT,

    // Keywords (lexical.keywords and lexical.reserved-words)
    ASSERT_KW,
    YIELD_KW,
    BREAK_KW,
    CATCH_KW,
    CONST_KW,
    CONTINUE_KW,
    ELSE_KW,
    FALSE_KW,
    FN_KW,
    FOR_KW,
    IF_KW,
    IMPL_KW,
    IN_KW,
    INOUT_KW,
    LET_KW,
    LOOP_KW,
    MATCH_KW,
    MODULE_KW,
    PUB_KW,
    RAISE_KW,
    RETURN_KW,
    SELF_KW,
    SELF_TYPE_KW,
    TEST_KW,
    TRAIT_KW,
    TRUE_KW,
    TRY_KW,
    TYPE_KW,
    USE_KW,
    VAR_KW,
    WHILE_KW,
    WHERE_KW,
    SYNTAX_KW,
    EFFECT_KW,
    HANDLER_KW,
    WITH_KW,
    RESUME_KW,
    ASYNC_KW,
    AWAIT_KW,
    WHEN_KW,
    COMPTIME_KW,
    MACRO_KW,
    QUOTE_KW,
    EXTERN_KW,
    UNSAFE_KW,

    // Contextual keywords (lexical.contextual-keywords)
    WITHOUT_KW,
    // The limits that are contextual keywords, from `panic` to `locks`.
    PANIC_KW,
    OVERFLOW_KW,
    ALLOC_KW,
    DIV_KW,
    COPY_KW,
    FS_KW,
    NET_KW,
    CLOCK_KW,
    ENV_KW,
    CONSOLE_KW,
    RAND_KW,
    SPAWN_KW,
    EXEC_KW,
    LOCKS_KW,
    BECAUSE_KW,
    IO_KW,
    ESCAPING_KW,
    META_KW,
    PATTERN_KW,
    FIELD_KW,

    // Operators and punctuation (lexical.tokens)
    PLUS,
    MINUS,
    STAR,
    SLASH,
    PERCENT,
    PLUS_PERCENT,
    MINUS_PERCENT,
    STAR_PERCENT,
    EQ2,
    NEQ,
    L_ANGLE,
    LTEQ,
    R_ANGLE,
    GTEQ,
    AMP2,
    PIPE2,
    BANG,
    AMP,
    PIPE,
    CARET,
    SHL,
    SHR,
    EQ,
    PLUS_EQ,
    MINUS_EQ,
    STAR_EQ,
    SLASH_EQ,
    PERCENT_EQ,
    PLUS_PERCENT_EQ,
    MINUS_PERCENT_EQ,
    STAR_PERCENT_EQ,
    AMP_EQ,
    PIPE_EQ,
    CARET_EQ,
    SHL_EQ,
    SHR_EQ,
    THIN_ARROW,
    FAT_ARROW,
    DOT,
    DOT2,
    DOT2EQ,
    COMMA,
    COLON,
    SEMICOLON,
    L_PAREN,
    R_PAREN,
    L_BRACK,
    R_BRACK,
    L_CURLY,
    R_CURLY,
    QUESTION,
    AT,
    DOLLAR,
    QUOTE,
    POUND,

    // Tokens that only the parser reads: a separator, which is a `;` or a newline
    // (lexical.terminator-insertion and lexical.separators), a run of doc comments, a doc comment
    // in no place for one, and the end of the input.
    SEP,
    DOC,
    MISPLACED_DOC,
    EOF,

    // Programs
    SOURCE_FILE,
    EXAMPLE,
    HEADER,
    LIMITS,
    USE,
    PATH,
    NAME,
    DOCS,

    // Declarations
    FN,
    GENERIC_LIST,
    TYPE_PARAM,
    ROW_PARAM,
    VALUE_PARAM,
    BOUND_LIST,
    BOUND,
    WHERE_CLAUSE,
    WHERE_BOUND,
    PARAM_LIST,
    SELF_PARAM,
    PARAM,
    RET_TYPE,
    HOLE_BODY,
    TYPE_DECL,
    RECORD_DEF,
    FIELD_DEF,
    VARIANT_LIST,
    VARIANT,
    PAYLOAD_LIST,
    PAYLOAD,
    TRAIT,
    CONST,
    TEST,
    IMPL,

    // Macros (macros.syntax-declarations and macros.patterns): a declaration, its arms, the groups,
    // fragments and repetitions of its patterns and templates, and a template.
    SYNTAX,
    MACRO_ARM,
    MACRO_GROUP,
    MACRO_FRAG,
    MACRO_REP,
    MACRO_SEP,
    TEMPLATE,

    // Effects (handlers.declaring-effect; tasks.async): a declaration and its operations.
    EFFECT,
    OPERATION,

    // Types
    NAMED_TYPE,
    TYPE_ARG_LIST,
    VALUE_ARG,
    TUPLE_TYPE,
    PAREN_TYPE,
    RECORD_TYPE,
    SPREAD_TYPE,
    FN_TYPE,
    PARAM_TYPE_LIST,
    PARAM_TYPE,
    ROW,
    ROW_IO,
    ROW_RAISE,
    ROW_VAR,
    ROW_EFFECT,
    ROW_ASYNC,
    HANDLER_TYPE,
    // A use of a procedural macro whose result is a type (macros.procedural-uses), and a splice in
    // a quote where a type stands (macros.splices).
    MACRO_TYPE,
    SPLICE_TYPE,

    // Patterns
    WILDCARD_PAT,
    BIND_PAT,
    LITERAL_PAT,
    PATH_PAT,
    VARIANT_PAT,
    RECORD_PAT,
    FIELD_PAT,
    REST_PAT,
    TUPLE_PAT,
    PAREN_PAT,
    LIST_PAT,
    OR_PAT,
    MACRO_PAT,
    SPLICE_PAT,

    // Statements
    BLOCK,
    LET_STMT,
    VAR_STMT,
    ASSERT_STMT,
    YIELD_STMT,
    ASSIGN_STMT,
    EXPR_STMT,

    // Expressions
    LITERAL,
    INTERP,
    SPLICE,
    NAME_REF,
    SELF_EXPR,
    SELF_TYPE_EXPR,
    HOLE_EXPR,
    KEY_PATH_EXPR,
    PAREN_EXPR,
    TUPLE_EXPR,
    LIST_EXPR,
    FIELD_EXPR,
    CALL_EXPR,
    ARG_LIST,
    ARG,
    INDEX_EXPR,
    STRUCT_EXPR,
    RECORD_EXPR,
    SPREAD_EXPR,
    FIELD_INIT,
    PREFIX_EXPR,
    BINARY_EXPR,
    ELSE_EXPR,
    TRY_EXPR,
    CATCH_CLAUSE,
    ARM,
    GUARD,
    BECAUSE,
    RAISE_EXPR,
    RETURN_EXPR,
    BREAK_EXPR,
    CONTINUE_EXPR,
    CLOSURE_EXPR,
    CLOSURE_PARAM,
    IF_EXPR,
    BOUND_TEST,
    MATCH_EXPR,
    LOOP_EXPR,
    WHILE_EXPR,
    FOR_EXPR,
    RANGE,
    MACRO_USE,
    HANDLER_EXPR,
    WITH_EXPR,
    RESUME_EXPR,
    WHEN_EXPR,
    COMPTIME_EXPR,
    // `unsafe because "reason" { … }` (c.unsafe-because).
    UNSAFE_EXPR,
    // Quotes and their splices (macros.quote and macros.splices): a quote, a splice where an
    // expression stands, one where a name stands, and a spread among elements or fields.
    QUOTE_EXPR,
    SPLICE_EXPR,
    SPLICE_NAME,
    SPLICE_SPREAD,

    // Code that the parser couldn't read, kept so that the tree holds all of the text.
    ERROR,
}

impl SyntaxKind {
    /// Whether tokens of this kind are trivia, which the parser never reads.
    #[must_use]
    pub fn is_trivia(self) -> bool {
        matches!(
            self,
            Self::WHITESPACE | Self::NEWLINE | Self::COMMENT | Self::DOC_COMMENT
        )
    }

    /// The kind whose raw value is `raw`.
    ///
    /// # Panics
    ///
    /// If no kind has that raw value. Every raw kind in a tree comes from a [`SyntaxKind`].
    #[must_use]
    pub fn from_raw(raw: u16) -> Self {
        ALL[usize::from(raw)]
    }
}

/// The language of Stilt's syntax trees, for `rowan`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Stilt {}

impl rowan::Language for Stilt {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> SyntaxKind {
        SyntaxKind::from_raw(raw.0)
    }

    fn kind_to_raw(kind: SyntaxKind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind as u16)
    }
}

/// A node of a syntax tree.
pub type SyntaxNode = rowan::SyntaxNode<Stilt>;
/// A token of a syntax tree.
pub type SyntaxToken = rowan::SyntaxToken<Stilt>;
/// A node or a token of a syntax tree.
pub type SyntaxElement = rowan::SyntaxElement<Stilt>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_kinds_round_trip() {
        for (raw, &kind) in ALL.iter().enumerate() {
            assert_eq!(kind as usize, raw);
            assert_eq!(SyntaxKind::from_raw(kind as u16), kind);
        }
    }
}

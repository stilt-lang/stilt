//! The external scanner of the tree-sitter grammar, `editors/tree-sitter/src/scanner.c`, which
//! reads a newline as the separator `_line_end` where the grammar accepts a separator, as
//! lexical.terminator-insertion inserts one: unless the next line that holds a token continues
//! the line (lexical.continuation-lines), or begins with the `}` before which a separator is
//! ignored (lexical.separators). The grammar accepts a separator only after a token that can end an
//! expression, outside `(…)` and `[…]` (lexical.inside-brackets).

use crate::lexical::Lexical;

pub(crate) const PATH: &str = "editors/tree-sitter/src/scanner.c";

/// The text of the scanner, with the limits of the production `limit`, the words after which
/// `without` begins a clause on the next line.
pub(crate) fn emit(lexical: &Lexical) -> String {
    let limits: Vec<String> = lexical.limits.iter().map(|l| format!("{l:?}")).collect();
    format!(
        "{HEAD}static const char *LIMITS[] = {{{}, NULL}};\n{BODY}",
        limits.join(", ")
    )
}

const HEAD: &str = r#"// The external scanner of the tree-sitter grammar of Stilt. Generated from the limits of
// reference/03-syntax.md by `just grammar-generate`; `just grammar` checks it is current.

#include "tree_sitter/parser.h"

#include <stdbool.h>
#include <string.h>

enum TokenType { LINE_END };

"#;

const BODY: &str = r#"
void *tree_sitter_stilt_external_scanner_create(void) { return NULL; }
void tree_sitter_stilt_external_scanner_destroy(void *payload) { (void)payload; }

unsigned tree_sitter_stilt_external_scanner_serialize(void *payload, char *buffer) {
  (void)payload;
  (void)buffer;
  return 0;
}

void tree_sitter_stilt_external_scanner_deserialize(void *payload, const char *buffer,
                                                      unsigned length) {
  (void)payload;
  (void)buffer;
  (void)length;
}

static bool is_word_char(int32_t c) {
  return c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9');
}

static void skip_blanks(TSLexer *lexer) {
  while (lexer->lookahead == ' ' || lexer->lookahead == '\t' || lexer->lookahead == '\r') {
    lexer->advance(lexer, true);
  }
}

/// Reads the word at the lexer into `word`, of at most `size - 1` characters.
static void read_word(TSLexer *lexer, char *word, unsigned size) {
  unsigned length = 0;
  while (is_word_char(lexer->lookahead)) {
    if (length + 1 < size) word[length++] = (char)lexer->lookahead;
    lexer->advance(lexer, false);
  }
  word[length] = '\0';
}

static bool is_limit(const char *word) {
  for (const char **limit = LIMITS; *limit; limit++) {
    if (strcmp(*limit, word) == 0) return true;
  }
  return false;
}

/// Whether the line that begins at the lexer continues the line before it, or begins with `}`.
static bool continues(TSLexer *lexer) {
  int32_t first = lexer->lookahead;
  if (first == '}') return true;
  if (first == '.' || first == '|') {
    lexer->advance(lexer, false);
    return lexer->lookahead != first;
  }
  char word[16];
  read_word(lexer, word, sizeof word);
  if (strcmp(word, "else") == 0 || strcmp(word, "catch") == 0) return true;
  if (strcmp(word, "without") != 0) return false;
  skip_blanks(lexer);
  read_word(lexer, word, sizeof word);
  return is_limit(word);
}

enum Next { NONE, TOKEN, SLASH };

/// Skips the blank lines and the lines that hold only comments, to the next token, or past the
/// `/` that begins one.
static enum Next next_token(TSLexer *lexer) {
  for (;;) {
    while (lexer->lookahead == ' ' || lexer->lookahead == '\t' || lexer->lookahead == '\r' ||
           lexer->lookahead == '\n') {
      lexer->advance(lexer, false);
    }
    if (lexer->eof(lexer)) return NONE;
    if (lexer->lookahead != '/') return TOKEN;
    lexer->advance(lexer, false);
    if (lexer->lookahead != '/') return SLASH;
    while (lexer->lookahead != '\n' && !lexer->eof(lexer)) lexer->advance(lexer, false);
  }
}

bool tree_sitter_stilt_external_scanner_scan(void *payload, TSLexer *lexer,
                                              const bool *valid_symbols) {
  (void)payload;
  if (!valid_symbols[LINE_END]) return false;
  skip_blanks(lexer);
  if (lexer->lookahead != '\n') return false;
  lexer->advance(lexer, false);
  lexer->mark_end(lexer);
  enum Next next = next_token(lexer);
  if (next == NONE || (next == TOKEN && continues(lexer))) return false;
  lexer->result_symbol = LINE_END;
  return true;
}
"#;

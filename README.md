# welly-parser

An artisanal parser for the Welly programming language.

It's a recursive descent parser, hand-written (i.e. not using a parser library), with a separate lexer. It should be fast by design, but I haven't put any effort into optimising it.


## Usage

Clone this repo, and checkout the `main` branch.

`cargo run` will run the REPL (Read-Eval-Print-Loop), which currently just prints out the parse tree of the commands you enter, and reports syntax errors.

`rlwrap cargo run` runs the REPL with command-line history. `rlwrap` is a well-known program that you can install separately.


## Syntax examples

The directory `examples` includes some mock-ups of Welly programs. These predate the implementation, and occasionally include ideas that I have not implemented, but they should give you some idea of what Welly programs look like.


## Status

The API is nearly complete but still in flux. The syntax is in less flux, but could still change in the details. See the GitHub issues for missing features that are planned for this release. Missing features that I don't plan for the next release include floating point literals. These could be added later.


## How it works

Parsing happens in three phases: lexing, semi-structured parsing, and validating. The lexer and semi-structured parser are barely more complicated than Lisp's, yet provide enough structure for syntax colouring and code formatting tools, and for the REPL, and enough variety to be pleasant for human readers. The lexer and parser specifications probably won't change much from now on. The validator then defines a rich subset of the semi-syntax, which may well evolve in future.

Unusually, Welly's syntax is designed to be suitable for use in a REPL (Read-Eval-Print Loop). If you type in half a source file and press "Enter", the parser will not return an incorrect parse tree by mistake, but will instead wait for more input. A command is considered complete only if its last line ends with a semicolon or close curly bracket, and all brackets are matched. An example REPL is provided (use `cargo run`).


## Lexer

The lexer recognises only the following lexemes:

- Whitespace (removed)
- Block comments and line comments
- String and character literals
- Alphanumeric words, including underscore characters
- Separator and bracket characters
- Words composed of other punctuation characters


## Parser

The parser then recognises a simple semi-structured syntax, with only the following non-terminals:

- Block - Curly brackets around a sequence of items.
- Bracket - Round or square brackets around a sequence of items.
- Item - One of:
  - A separator character
  - A formula
  - Two formulae separated by an assignment operator
  - A keyword, then optionally a formula, then optionally a block
  - A block
- Formula - A maximal string of:
  - Alphanumeric words
  - Arithmetic operators
  - Brackets

Formulae are futher parsed into expression trees according to the associativity and binding precedence of the arithmetic operators, which are listed in a table.


## Validator

The validator then goes to work on the parse tree. A big part of its work is to distinguish "expressions", which have a value, from "statements", which don't. Formulae always turn into expressions, while items can turn into either, depending on their syntax. Groups must only contain expressions. Blocks must only contain statements, but any expression can be used as a statement.

The validator enforces various rules:

- In blocks:
  - Items must validate as statements (though any expression may be used as a statement).
  - Items that do not end with a block must be followed by a semicolon. There must be no other separators.
  - Every item beginning `else` becomes part of the previous item, provided it begins with `if`, `while` or `for`, otherwise it is an error.
  - An item that begins with a keyword can require that the expression and/or the block are present, depending on the keyword, and can impose further syntactic constraints on the expression.
- In brackets:
  - Items must validate as expressions, not statements.
  - Items must be separated by commas, with an optional trailing comma. There must be no other separators.

Alphanumeric words are split into three classes:
- A "number" is a word that start with a digit. It is an error if it can't be parsed as an integer.
- A "tag" consists only of capital letters and underscores, and must be at least two characters long.
- A "name" is any other alphanumeric word.

Brackets are split into two classes:
- A "group" contains exactly one expression and does not have trailing comma.
- A "tuple" is any other bracket.

A subset of expressions is further restricted to be "patterns", which describe how to unpack a value and name its pieces. The archetype is the left-hand side of an assignment statement. The parameter list of a function, macro or object definition, and the parameter list of a `case` statement, are also a patterns, with the extra rule that they must be brackets (of either kind), optionally preceded by a name or tag. Most arithmetic operators are forbidden in patterns. The exceptions are the mode prefix operators `$` and `&`, the type cast infix operator `:`, and the field access operator `.`.

An expression that is the right operand of `.` is restricted further still. Currently only numbers, names and tags are allowed.


## Futher information

- The file `enums.rs` lists all the keywords, and all the arithmetic operators with their binding precedece and associativity.
- The file `lexer.rs` defines the lexer.
- The file `parser.rs` defines the semi-structured parser.
- The file `ast/expr.rs` defines the rules for validating expressions.
- The file `ast/stmt.rs` defines the rules for validating statements.
- The file `ast/pattern.rs` defines the rules for validating patterns.

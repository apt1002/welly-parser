# welly-parser

An artisanal parser for the Welly programming language.

It's a recursive descent parser, hand-written (i.e. not using a parser library). It should be fast by design, but I haven't put any effort into optimising it.


## Status

The API is incomplete and in flux. The syntax is in less flux, but could still change in the details.

Missing features that I do plan to include in the first release include some type literals. Missing features that I don't plan for the first release include floating point literals. These will be added later.


## Syntax choices

It is a two-pass parser:
- The first pass accepts a significant superset of Welly syntax, while getting the correct structure for syntactically correct programs. Some trivial things are not fully disambiguated; for example numbers and identifiers both parse as type `word::AlphaNumeric`.
- The second pass rejects many incorrect programs, generating helpful errors, and fully disambiguates everything. It still accepts a superset of Welly syntax. For example, it will accept `fn(4+5) {}` and `4+5 = foo;` which are not legal in Welly. It also accepts some extra syntax that I plan to use in experimental versions of Welly, e.g. `$x`, `&x` and `x?`.

Whitespace and comments are removed. Comments in "doc string positions" will probably be preserved in a future version. If a parse error occurs, the parser does not make a parse tree. Because of these losses, this parser *is not* suitable for use in a code reformatter.

This parser *is* suitable for use in a REPL (Read-Eval-Print Loop). Specifically, if you type in half a source file and press "Enter", the parser will not return an incorrect parse tree by mistake, but will instead wait for more input. An example REPL is provided (use `cargo run`).

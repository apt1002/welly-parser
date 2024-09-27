# welly-parser

An artisanal parser for the Welly programming language.

It's a recursive descent parser, hand-written (i.e. not using a parser library). It should be fast by design, but I haven't put any effort into optimising it.


## Status

Unfinished. The API is incomplete and in flux. The syntax is in less flux, but could still change in the details.

Missing features that I do plan to include in the first release include e.g. statements and some type literals. Missing features that I don't plan for the first release include floating point literals. These will be added later.


## Syntax choices

It accepts a significant superset of Welly syntax. Most obviously, it accepts any expression in places where Welly would only accept a subset of expressions. For example, it will accept `fn(4+5) {}` and `4+5 = foo;` which are not legal in Welly. It also accepts some extra syntax that I plan to use in experimental versions of Welly, e.g. `$x`, `&x` and `x?`.

Some trivial things are not fully disambiguated; for example numbers and identifiers both parse as type `word::AlphaNumeric`. The caller is certainly going to want to make another pass over the parse tree before trying to compile it, so there is an opportunity to fix things up.

Whitespace is removed. Comments are removed, except in "doc string positions". If a parse error occurs, the parse tree is replaced with an error token. Because of these losses, this parser *is not* suitable for use in a code reformatter.

This parser *is* suitable for use in a REPL (Read-Eval-Print Loop). Specifically, if you type in half a source file and press "Enter", the parser will not return an incorrect parse tree by mistake, but will instead report a special error token (which the caller can test for) at the point where it reads beyond the available input. A different token `EndOfFile` informs the parser that there will be no more input.

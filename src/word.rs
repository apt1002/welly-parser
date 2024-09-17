use std::collections::{HashMap};
use std::{fmt};

use super::{Tree, Stream, Context, Parse};

#[derive(Debug, Clone, PartialEq)]
pub struct Whitespace;

impl Tree for Whitespace {}

#[derive(Debug, Clone, PartialEq)]
pub struct Symbol(String);

impl Tree for Symbol {}

#[derive(Debug, Clone, PartialEq)]
pub struct Alphanumeric(String);

impl Tree for Alphanumeric {}

// ----------------------------------------------------------------------------

/// Three classes of character combine with similar neighbours to make a word.
#[derive(Debug, Copy, Clone, PartialEq)]
enum CharacterClass {
    /// A whitespace character.
    WHITESPACE,

    /// A character that can appear in a multi-character operator.
    SYMBOL,

    /// An ASCII letter, digit or underscore.
    ALPHANUMERIC,
}

impl CharacterClass {
    /// Map `s` to a `Self`, if possible.
    fn classify(c: char) -> Option<Self> {
        use CharacterClass::*;
        match c {
            '\t' | '\n' | '\r' | ' ' =>
                Some(WHITESPACE),
            '!' | '$' | '%' | '^' | '&' | '*' | '-' | '+' | '=' | ':' | '@' | '~' | '<' | '>' | '?' | '.' | '/' =>
                Some(SYMBOL),
            '0'..='9' | 'A'..='Z' | 'a'..='z' | '_' =>
                Some(ALPHANUMERIC),
            _ => None,
        }
    }

    /// Combine `self` with `s` to make a [`dyn Tree`].
    fn wrap(self, s: String) -> Box<dyn Tree> {
        use CharacterClass::*;
        match self {
            WHITESPACE => Box::new(Whitespace),
            SYMBOL => Box::new(Symbol(s)),
            ALPHANUMERIC => Box::new(Alphanumeric(s)),
        }
    }
}

// ----------------------------------------------------------------------------

#[derive(Default)]
pub struct Parser(HashMap<&'static str, Box<dyn Fn() -> Box<dyn Tree>>>);

impl Parser {
    pub fn add_keyword(&mut self, name: &'static str, tree: impl 'static + Fn() -> Box<dyn Tree>) {
        let old = self.0.insert(name, Box::new(tree));
        assert!(old.is_none(), "Keywords must be distinct");
    }
}

impl fmt::Debug for Parser {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("Parser")
            .field(&Vec::from_iter(self.0.keys().copied()))
            .finish()
    }
}

impl Parse for Parser {
    fn parse(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String> {
        if let Some(c) = input.read::<char>()? {
            if let Some(cc) = CharacterClass::classify(*c) {
                let mut s = String::new();
                s.push(*c);
                while let Some(c) = input.read::<char>()? {
                    if CharacterClass::classify(*c) != Some(cc) {
                        input.unread(c);
                        break;
                    }
                    s.push(*c);
                }
                Ok(if let Some(f) = self.0.get(&s.as_ref()) { f() } else { cc.wrap(s) })
            } else {
                Ok(c)
            }
        } else {
            input.read_any()
        }
    }
}

// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::buffer::{Characters};

    #[derive(Debug, PartialEq)]
    enum Keyword {RETURN, EQUALS}
    use Keyword::*;

    impl Tree for Keyword {}

    #[test]
    fn keywords() {
        let mut parser = Parser::default();
        parser.add_keyword("return", || Box::new(RETURN));
        parser.add_keyword("==", || Box::new(EQUALS));
        let mut stream = crate::Parser::new(parser, Characters::new("return foo==69;"));
        assert_eq!(stream.read(), RETURN);
        assert_eq!(stream.read(), Whitespace);
        assert_eq!(stream.read(), Alphanumeric("foo".into()));
        assert_eq!(stream.read(), EQUALS);
        assert_eq!(stream.read(), Alphanumeric("69".into()));
        assert_eq!(stream.read(), ';');
        assert_eq!(stream.read(), crate::EndOfFile);
    }
}

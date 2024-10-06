use std::collections::{HashMap};
use std::{fmt};

use super::{Tree, Stream, Context, Parse};

#[derive(Debug, Clone, PartialEq)]
pub struct Whitespace;

impl Tree for Whitespace {}

#[derive(Debug, Clone, PartialEq)]
pub struct Symbol(pub String);

impl Tree for Symbol {}

#[derive(Debug, Clone, PartialEq)]
pub struct Alphanumeric(pub String);

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
    pub fn add_keywords<T: Tree + Clone>(&mut self) {
        T::declare_keywords(|name, tree| {
            let old = self.0.insert(name, Box::new(move || Box::new(tree.clone())));
            assert!(old.is_none(), "Keyword '{}' has multiple meanings", name);
        });
    }
}

impl fmt::Debug for Parser {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("Parser")
            .field(&Vec::from_iter(self.0.keys().copied()))
            .finish()
    }
}

impl<'a> Parse for &'a Parser {
    fn parse(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String> {
        if let Some(c) = input.read::<char>()? {
            if let Some(cc) = CharacterClass::classify(*c) {
                let mut s = String::new();
                s.push(*c);
                while let Some(c) = input.read_if(
                    |&c| CharacterClass::classify(c) == Some(cc)
                )? {
                    s.push(*c);
                }
                Ok(if let Some(f) = self.0.get(&s.as_ref()) {
                    f()
                } else {
                    s.shrink_to_fit();
                    cc.wrap(s)
                })
            } else {
                Ok(c)
            }
        } else {
            input.read_any()
        }
    }
}

impl Parse for Parser {
    fn parse(
        &self,
        input: &mut Context<impl Stream>,
    ) -> Result<Box<dyn Tree>, String> {
        (&self).parse(input)
    }
}

// ----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Characters};

    /// A minimal mock-up of some Welly keywords.
    #[derive(Debug, Copy, Clone, PartialEq)]
    enum Keyword {RETURN, EQUALS}
    use Keyword::*;

    impl Tree for Keyword {
        fn declare_keywords(mut declare: impl FnMut(&'static str, Self)) {
            declare("return", RETURN);
            declare("==", EQUALS);
        }
    }

    #[test]
    fn keywords() {
        let mut parser = Parser::default();
        parser.add_keywords::<Keyword>();
        let mut stream = parser.parse_stream(Characters::new("return foo==69;", true));
        assert_eq!(stream.read(), RETURN);
        assert_eq!(stream.read(), Whitespace);
        assert_eq!(stream.read(), Alphanumeric("foo".into()));
        assert_eq!(stream.read(), EQUALS);
        assert_eq!(stream.read(), Alphanumeric("69".into()));
        assert_eq!(stream.read(), ';');
        assert_eq!(stream.read(), crate::EndOfFile);
    }
}

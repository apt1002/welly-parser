use super::{Tree, Stream, Context, Parse};

#[derive(Debug, Clone, PartialEq)]
pub struct Whitespace(String);

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
            '\t' | '\n' | '\r' | ' ' => Some(WHITESPACE),
            '!' | '$' | '%' | '^' | '&' | '*' | ':' | '@' | '~' | '<' | '>' | '?' | '.' | '/' => Some(SYMBOL),
            '0'..='9' | 'A'..='Z' | 'a'..='z' | '_' => Some(ALPHANUMERIC),
            _ => None,
        }
    }

    /// Combine `self` with `s` to make a [`dyn Tree`].
    fn wrap(self, s: String) -> Box<dyn Tree> {
        use CharacterClass::*;
        match self {
            WHITESPACE => Box::new(Whitespace(s)),
            SYMBOL => Box::new(Symbol(s)),
            ALPHANUMERIC => Box::new(Alphanumeric(s)),
        }
    }
}

// ----------------------------------------------------------------------------

#[derive(Debug, Default)]
pub struct Parser;

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
                Ok(cc.wrap(s))
            } else {
                Ok(c)
            }
        } else {
            input.read_any()
        }
    }
}

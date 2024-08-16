use super::{lexer, TokenIterator, Failure, Context, Parse};

#[derive(Debug, Clone, PartialEq)]
pub enum AST {
    Char(char),
    Comment(String),
    CharacterLiteral(char),
    StringLiteral(String),
    Whitespace(String),
    Symbol(String),
    Alphanumeric(String),
}

impl From<lexer::AST> for AST {
    fn from(value: lexer::AST) -> AST {
        match value {
            lexer::AST::Char(c) => AST::Char(c),
            lexer::AST::Comment(s) => AST::Comment(s),
            lexer::AST::CharacterLiteral(c) => AST::CharacterLiteral(c),
            lexer::AST::StringLiteral(s) => AST::StringLiteral(s),
        }
    }
}

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

    /// Combine `self` with `s` to make an [`AST`].
    fn wrap(self, s: String) -> AST {
        use CharacterClass::*;
        match self {
            WHITESPACE => AST::Whitespace(s),
            SYMBOL => AST::Symbol(s),
            ALPHANUMERIC => AST::Alphanumeric(s),
        }
    }
}


// ----------------------------------------------------------------------------

#[derive(Debug, Default)]
pub struct Parser;

impl Parse for Parser {
    type Input = lexer::AST;

    type Output = AST;

    fn parse(
        &self,
        input: &mut Context<impl TokenIterator<T=Self::Input>>,
    ) -> Result<Self::Output, Failure> {
        match input.read()? {
            lexer::AST::Char(c) => if let Some(cc) = CharacterClass::classify(c) {
                let mut s = String::new();
                s.push(c);
                loop {
                    match input.read()? {
                        lexer::AST::Char(c) => {
                            if CharacterClass::classify(c) != Some(cc) { break; }
                            s.push(c);
                        },
                        a => { input.unread(a); break; }
                    }
                }
                Ok(cc.wrap(s))
            } else {
                Ok(AST::Char(c))
            },
            a => Ok(AST::from(a)),
        }
    }
}

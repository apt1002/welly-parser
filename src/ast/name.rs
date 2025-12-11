use std::{fmt};
use std::rc::{Rc};

// ----------------------------------------------------------------------------

/// An identifier for a value.
///
/// `Name`s are strings of letters, digits and underscores, starting with a
/// letter or underscore.
#[derive(Clone)]
pub struct Name(Rc<str>);

impl Name {
    pub fn new(s: &Rc<str>) -> Option<Self> {
        if !matches!(s.chars().next(), Some('A' .. 'Z' | 'a' .. 'z' | '_')) { return None; }
        if !s.chars().all(|c| matches!(c, '0' .. '9' | 'A' .. 'Z' | 'a' .. 'z' | '_')) { return None; }
        Some(Self(s.clone()))
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}

impl std::ops::Deref for Name {
    type Target = str;
    fn deref(&self) -> &Self::Target { &*self.0 }
}

// ----------------------------------------------------------------------------

/// A tag that can be attached to a tuple of values.
///
/// `Tag`s are strings of at least two capital letters, digits and underscores,
/// starting with a capital letter.
#[derive(Clone)]
pub struct Tag(Rc<str>);

impl Tag {
    /// Construct `Self` from `s` if it is of the required form.
    pub fn new(s: &Rc<str>) -> Option<Self> {
        if s.len() < 2 { return None; }
        if !matches!(s.chars().next(), Some('A' .. 'Z')) { return None; }
        if !s.chars().all(|c| matches!(c, 'A' .. 'Z' | '_')) { return None; }
        Some(Self(s.clone()))
    }
}

impl fmt::Debug for Tag {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
}

impl std::ops::Deref for Tag {
    type Target = str;
    fn deref(&self) -> &Self::Target { &*self.0 }
}

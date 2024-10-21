use super::{welly, Tree, Location, Loc, Token, Invalid, AST};
use welly::{Op, AssignOp, Verb};

/// Reports an error if `tree` is `None`.
fn compulsory<T>(
    tree: &Option<T>,
    missing: impl FnOnce(),
) -> Result<&T, Invalid> {
    Ok(tree.as_ref().ok_or_else(missing)?)
}

/// Returns the sole element of `array`, if its length is `1`.
fn only<T>(array: Box<[T]>) -> Result<T, Box<[T]>> {
    let array: Box<[T; 1]> = array.try_into()?;
    let [element] = *array;
    Ok(element)
}

// ----------------------------------------------------------------------------

/// Represents a comma-separated tuple of `A`s in round brackets.
///
/// The `bool` indicates if there is a trailing comma.
pub struct Tuple<A>(pub Box<[A]>, pub bool);

impl<A> Tuple<A> {
    /// If there's no trailing comma and exactly one element, return it.
    /// Otherwise apply `tuple`.
    fn bracket_or_tuple(self, tuple: impl FnOnce(Box<[A]>) -> A) -> A {
        let Tuple(asts, trailing_comma) = self;
        let asts = if !trailing_comma { only(asts) } else { Err(asts) };
        asts.unwrap_or_else(|asts| tuple(asts))
    }
}

impl<A: AST> AST for Tuple<A> where
    <A as AST>::Generous: Tree,
{
    type Generous = welly::Round;

    fn validate(report: &mut impl FnMut(Location, &str), round: &Self::Generous)
    -> Result<Self, Invalid> {
        struct State<'s, R, A> {
            asts: Vec<A>,
            report: &'s mut R,
            is_valid: bool,
            trailing_comma: bool,
        }
        
        impl<R: FnMut(Location, &str), A> State<'_, R, A> {
            /// Report an error.
            fn report(&mut self, loc: Location, msg: &str) {
                if self.is_valid { (self.report)(loc, msg); }
                self.is_valid = false;
            }

            /// Record an `A`.
            fn push(&mut self, loc: Location, ast: A) {
                if !self.trailing_comma { self.report(loc, "Missing comma"); }
                self.asts.push(ast);
                self.trailing_comma = false;
            }

            /// Record a comma.
            fn comma(&mut self, loc: Location) {
                if self.trailing_comma { self.report(loc, "Missing expression"); }
                self.trailing_comma = true;
            }
        }
        
        let mut state = State {asts: Vec::new(), report, is_valid: true, trailing_comma: false};
        let mut contents = round.0.iter();
        while let Some(&Token(Loc(ref result, loc))) = contents.next() {
            match result {
                Ok(tree) => {
                    if let Some(tree) = tree.downcast_ref::<A::Generous>() {
                        if let Ok(ast) = A::validate(state.report, tree) {
                            state.push(loc, ast);
                        } else {
                            state.is_valid = false;
                        }
                    } else if **tree == ',' {
                        state.comma(loc);
                    } else if state.trailing_comma {
                        state.report(loc, "Expected an expression");
                    } else if state.is_valid {
                        state.report(loc, "Expected a comma");
                    }
                },
                Err(msg) => {
                    state.report(loc, msg);
                },
            }
        }
        if state.is_valid {
            Ok(Self(state.asts.into(), state.trailing_comma))
        } else { Err(Invalid) }
    }
}

// ----------------------------------------------------------------------------

/// A Literal expression, representing a constant value.
pub enum Literal {
    Int(Loc<u64>),
    Char(Loc<char>),
    Str(Loc<String>),
}

impl AST for Loc<u64> {
    type Generous = Loc<String>;

    fn validate(report: &mut impl FnMut(Location, &str), value: &Self::Generous)
    -> Result<Self, Invalid> {
        if let Ok(i) = value.0.parse::<u64>() { return Ok(Loc(i, value.1)); }
        if let Ok(i) = value.0.parse::<i64>() { return Ok(Loc(i as u64, value.1)); }
        Err(report(value.1, "Invalid integer literal"))?
    }
}

// ----------------------------------------------------------------------------

/// An valid identifier.
///
/// Identifiers are written with capital and lower-case letters, digits and
/// underscores, and do not start with a digit.
#[derive(Debug, Clone)]
pub struct Name(Loc<String>);

impl std::borrow::Borrow<str> for Name {
    fn borrow(&self) -> &str { self.0.0.borrow() }
}

impl Name {
    /// Returns `value` as `Self` if possible.
    fn maybe_validate(value: &Loc<String>) -> Option<Self> {
        let mut cs = value.0.chars();
        if let Some(c) = cs.next() {
            if !matches!(c, '_' | 'A'..='Z' | 'a'..='z') { return None; }
            while let Some(c) = cs.next() {
                if !matches!(c, '_' | '0'..='9' | 'A'..='Z' | 'a'..='z') { return None; }
            }
            Some(Self(value.clone()))
        } else { None }
    }
}

impl AST for Name {
    type Generous = Loc<String>;

    fn validate(report: &mut impl FnMut(Location, &str), value: &Self::Generous)
    -> Result<Self, Invalid> {
        Ok(Name::maybe_validate(value).ok_or_else(|| report(value.1, "Invalid identifier"))?)
    }
}

// ----------------------------------------------------------------------------

/// An valid tag.
///
/// Tags are written with capital letters, digits and underscores, and do not
/// start with a digit.
#[derive(Debug, Clone)]
pub struct Tag(Loc<String>);

impl std::borrow::Borrow<str> for Tag {
    fn borrow(&self) -> &str { self.0.0.borrow() }
}

impl Tag {
    /// Returns `value` as `Self` if possible.
    fn maybe_validate(value: &Loc<String>) -> Option<Self> {
        let mut cs = value.0.chars();
        if let Some(c) = cs.next() {
            if !matches!(c, '_' | 'A'..='Z') { return None; }
            while let Some(c) = cs.next() {
                if !matches!(c, '_' | '0'..='9' | 'A'..='Z') { return None; }
            }
            Some(Self(value.clone()))
        } else { None }
    }

    /// Returns `value` as `Self` if possible.
    fn maybe_validate_expr(tree: &welly::Expr) -> Option<Self> {
        if let welly::Expr::Name(s) = tree { Self::maybe_validate(s) } else { None }
    }
}

// ----------------------------------------------------------------------------

/// An expression that can appear on the left-hand side of an assignment.
pub enum LExpr {
    Name(Name),
    Literal(Literal),
    Tuple(Loc<Box<[LExpr]>>),
    Field(Box<LExpr>, Name),
    Tag(Tag, Loc<Box<[LExpr]>>),
    Cast(Box<LExpr>, Location, Box<Type>),
}

impl AST for LExpr {
    type Generous = welly::Expr;

    fn validate(report: &mut impl FnMut(Location, &str), tree: &Self::Generous)
    -> Result<Self, Invalid> {
        Ok(match tree {
            welly::Expr::Char(c) => Self::Literal(Literal::Char(*c)),
            welly::Expr::String(s) => Self::Literal(Literal::Str(s.clone())),
            welly::Expr::Name(s) => {
                let c = s.0.chars().next().expect("Should be non-empty");
                if matches!(c, '0'..='9') {
                    Self::Literal(Literal::Int(Loc::<u64>::validate(report, s)?))
                } else {
                    Self::Name(Name::validate(report, s)?)
                }
            },
            welly::Expr::Round(round) => {
                let loc = Location::EVERYWHERE; // TODO.
                Tuple::validate(report, round)?.bracket_or_tuple(
                    |asts| Self::Tuple(Loc(asts, loc))
                )
            },
            welly::Expr::Function(_name, params, _return_type, _body) => {
                Err(report(params.1, "Expression is not assignable"))?
            },
            welly::Expr::Op(left, op, right) => {
                match op {
                    Loc(Op::Cast, loc) => {
                        let left = compulsory(left, || report(*loc, "Missing left operand"))?;
                        let right = compulsory(right, || report(*loc, "Missing right operand"))?;
                        let left = Box::<Self>::validate(report, &*left);
                        let right = Box::<Type>::validate(report, &*right);
                        Self::Cast(left?, *loc, right?)
                    },
                    Loc(Op::Missing, loc) => Err(report(*loc, "Missing operator"))?,
                    _ => Err(report(op.1, "This operator does not make an assignable expression"))?,
                }
            },
            welly::Expr::Field(object, field) => {
                let object = compulsory(object, || report(field.1, "Missing expression before `.field`"))?;
                let object = Box::<Self>::validate(report, &*object);
                let field = Name::validate(report, field);
                Self::Field(object?, field?)
            },
            welly::Expr::Call(tag, Loc(args, loc)) => {
                let tag = tag.as_ref().expect("Should have parsed as a tuple");
                let args = Tuple::validate(report, args);
                if let Some(tag) = Tag::maybe_validate_expr(tag) {
                    Self::Tag(tag, Loc(args?.0, *loc))
                } else { Err(report(*loc, "Expression is not assignable"))? }
            },
        })
    }
}

// ----------------------------------------------------------------------------

/// An expression.
pub enum Expr {
    Name(Name),
    Literal(Literal),
    Tuple(Loc<Box<[Expr]>>),
    Op(Box<Expr>, Loc<Op>, Box<Expr>),
    Function(Option<Name>, Loc<Box<[LExpr]>>, Option<Box<Type>>, Block),
    FunctionType(Option<Name>, Loc<Box<[LExpr]>>, Option<Box<Type>>),
    Field(Box<Expr>, Name),
    Tag(Tag, Loc<Box<[Expr]>>),
    Call(Box<Expr>, Loc<Box<[Expr]>>),
    Cast(Box<Expr>, Location, Box<Expr>),
}

impl AST for Expr {
    type Generous = welly::Expr;

    fn validate(report: &mut impl FnMut(Location, &str), tree: &Self::Generous)
    -> Result<Self, Invalid> {
        Ok(match tree {
            welly::Expr::Char(c) => Self::Literal(Literal::Char(*c)),
            welly::Expr::String(s) => Self::Literal(Literal::Str(s.clone())),
            welly::Expr::Name(s) => {
                let c = s.0.chars().next().expect("Should be non-empty");
                if matches!(c, '0'..='9') {
                    Self::Literal(Literal::Int(Loc::<u64>::validate(report, s)?))
                } else {
                    Self::Name(Name::validate(report, s)?)
                }
            },
            welly::Expr::Round(round) => {
                let loc = Location::EVERYWHERE; // TODO.
                Tuple::validate(report, round)?.bracket_or_tuple(
                    |asts| Self::Tuple(Loc(asts, loc))
                )
            },
            welly::Expr::Function(name, Loc(params, loc), return_type, body) => {
                let name = Option::<Name>::validate(report, name);
                let params = Tuple::validate(report, params);
                let return_type = Option::<Box<Type>>::validate(report, return_type);
                if let Some(body) = body {
                    let body = Block::validate(report, body);
                    Self::Function(name?, Loc(params?.0, *loc), return_type?, body?)
                } else {
                    Self::FunctionType(name?, Loc(params?.0, *loc), return_type?)
                }
            },
            welly::Expr::Op(left, op, right) => {
                match op {
                    Loc(Op::Cast, loc) => {
                        let left = compulsory(left, || report(*loc, "Missing expression"))?;
                        let right = compulsory(right, || report(*loc, "Missing expression"))?;
                        let left = Box::<Self>::validate(report, left);
                        let right = Box::<Type>::validate(report, right);
                        Self::Cast(left?, *loc, right?)
                    },
                    Loc(Op::Missing, loc) => Err(report(*loc, "Missing operator"))?,
                    _ => { todo!() },
                }
            },
            welly::Expr::Field(object, field) => {
                let object = compulsory(object, || report(field.1, "Missing expression before `.field`"))?;
                let object = Box::<Self>::validate(report, object);
                let field = Name::validate(report, field);
                Self::Field(object?, field?)
            },
            welly::Expr::Call(fn_, Loc(args, loc)) => {
                let fn_ = fn_.as_ref().expect("Should have parsed as a tuple");
                let args = Tuple::validate(report, args);
                if let Some(tag) = Tag::maybe_validate_expr(fn_) {
                    Self::Tag(tag, Loc(args?.0, *loc))
                } else {
                    let fn_ = Box::<Expr>::validate(report, fn_);
                    Self::Call(fn_?, Loc(args?.0, *loc))
                }
            },
        })
    }
}

/// An [`Expr`] used as a type.
type Type = Expr;

// ----------------------------------------------------------------------------

/// A `case` clause.
pub struct Case(Location, Box<LExpr>, Block);

impl AST for Case {
    type Generous = welly::Case;

    fn validate(report: &mut impl FnMut(Location, &str), case: &Self::Generous)
    -> Result<Self, Invalid> {
        let crate::stmt::Case(loc, pattern, body) = case;
        let pattern = compulsory(pattern, || report(*loc, "Missing pattern after `case`"))?;
        let pattern = Box::<LExpr>::validate(report, pattern);
        let body = Block::validate(report, body);
        Ok(Case(*loc, pattern?, body?))
    }
}

// ----------------------------------------------------------------------------

/// An `else` clause.
pub struct Else(Location, Block);

impl AST for Else {
    type Generous = welly::Else;

    fn validate(report: &mut impl FnMut(Location, &str), else_: &Self::Generous)
    -> Result<Self, Invalid> {
        let crate::stmt::Else(loc, body) = else_;
        Ok(Else(*loc, Block::validate(report, body)?))
    }
}

// ----------------------------------------------------------------------------

/// A statement.
pub enum Stmt {
    Empty,
    Expr(Box<Expr>),
    Let(Box<LExpr>, Location, Box<Expr>),
    Set(Box<LExpr>, Location, Box<Expr>),
    Mut(Box<LExpr>, Loc<Op>, Box<Expr>),
    If(Location, Box<Expr>, Block, Option<Else>),
    While(Location, Box<Expr>, Block, Option<Else>),
    For(Location, Box<LExpr>, Box<Expr>, Block, Option<Else>),
    Switch(Location, Box<Expr>, Box<[Case]>, Option<Else>),
    Break(Location),
    Continue(Location),
    Return(Location, Option<Box<Expr>>),
    Throw(Location, Box<Expr>),
    Assert(Location, Box<Expr>),
    Assume(Location, Box<Expr>),
}

impl AST for Stmt {
    type Generous = welly::Stmt;

    fn validate(report: &mut impl FnMut(Location, &str), tree: &Self::Generous)
    -> Result<Self, Invalid> {
        Ok(match tree {
            welly::Stmt::Expr(expr) => {
                if let Some(expr) = expr.as_ref() {
                    Self::Expr(Box::<Expr>::validate(report, expr)?)
                } else {
                    Self::Empty
                }
            },
            welly::Stmt::Assign(lhs, Loc(op, loc), rhs) => {
                let lhs = compulsory(lhs,
                    || report(*loc, "Missing pattern on left-hand side of assignment")
                )?;
                let rhs = compulsory(rhs,
                    || report(*loc, "Missing expression on right-hand side of assignment")
                )?;
                let lhs = Box::<LExpr>::validate(report, lhs);
                let rhs = Box::<Expr>::validate(report, rhs);
                match op {
                    AssignOp::Let => Self::Let(lhs?, *loc, rhs?),
                    AssignOp::Set => Self::Set(lhs?, *loc, rhs?),
                    AssignOp::Op(op) => Self::Mut(lhs?, Loc(*op, *loc), rhs?),
                }
            },
            welly::Stmt::If(loc, condition, body, else_) => {
                let condition = compulsory(condition, || report(*loc, "Missing condition"))?;
                let condition = Box::<Expr>::validate(report, condition);
                let body = Block::validate(report, body);
                let else_ = Option::<Else>::validate(report, else_);
                Self::If(*loc, condition?, body?, else_?)
            },
            welly::Stmt::While(loc, condition, body, else_) => {
                let condition = compulsory(condition, || report(*loc, "Missing condition"))?;
                let condition = Box::<Expr>::validate(report, condition);
                let body = Block::validate(report, body);
                let else_ = Option::<Else>::validate(report, else_);
                Self::While(*loc, condition?, body?, else_?)
            },
            welly::Stmt::For(loc, item_in_sequence, body, else_) => {
                let item_in_sequence = compulsory(item_in_sequence,
                    || report(*loc, "Missing `in` after `for`")
                )?;
                if let welly::Expr::Op(item, Loc(Op::In, in_loc), sequence) = &**item_in_sequence {
                    let item = compulsory(item,
                        || report(*loc, "Missing item pattern after `for`")
                    )?;
                    let sequence = compulsory(sequence,
                        || report(*in_loc, "Missing sequence expression after `for ... in`")
                    )?;
                    let item = Box::<LExpr>::validate(report, item);
                    let sequence = Box::<Expr>::validate(report, sequence);
                    let body = Block::validate(report, body);
                    let else_ = Option::<Else>::validate(report, else_);
                    Self::For(*loc, item?, sequence?, body?, else_?)
                } else { Err(report(*loc, "Missing `in` after for"))? }
            },
            welly::Stmt::Switch(loc, discriminant, cases, else_) => {
                let discriminant = compulsory(discriminant, || report(*loc, "Missing condition"))?;
                let discriminant = Box::<Expr>::validate(report, discriminant);
                let cases: Vec<Result<Case, Invalid>> = cases.iter().map(
                    |case| Case::validate(report, case)
                ).collect();
                let cases: Result<Box<[Case]>, Invalid> = cases.into_iter().collect();
                let else_ = Option::<Else>::validate(report, else_);
                Self::Switch(*loc, discriminant?, cases?, else_?)
            },
            welly::Stmt::Verb(Loc(verb, loc), expr) => match verb {
                Verb::Break => {
                    if let Some(_) = expr { Err(report(*loc, "Unexpected expression after `break`"))? }
                    Self::Break(*loc)
                },
                Verb::Continue => {
                    if let Some(_) = expr { Err(report(*loc, "Unexpected expression after `continue`"))? }
                    Self::Continue(*loc)
                },
                Verb::Return => {
                    Self::Return(*loc, Option::<Box<Expr>>::validate(report, expr)?)
                },
                Verb::Throw => {
                    let expr = compulsory(expr, || report(*loc, "Missing expression after `throw`"))?;
                    Self::Throw(*loc, Box::<Expr>::validate(report, expr)?)
                },
                Verb::Assert => {
                    let expr = compulsory(expr, || report(*loc, "Missing expression after `assert`"))?;
                    Self::Assert(*loc, Box::<Expr>::validate(report, expr)?)
                },
                Verb::Assume => {
                    let expr = compulsory(expr, || report(*loc, "Missing expression after `assume`"))?;
                    Self::Assume(*loc, Box::<Expr>::validate(report, expr)?)
                },
            },
        })
    }
}

// ----------------------------------------------------------------------------

/// A block of [`Stmt`]s.
pub struct Block(Box<[Stmt]>);

impl AST for Block {
    type Generous = welly::Brace;

    fn validate(report: &mut impl FnMut(Location, &str), tree: &welly::Brace)
    -> Result<Self, Invalid> {
        let mut ret = Vec::new();
        let mut is_valid = true;
        for Token(Loc(result, loc)) in &tree.0 {
            match result {
                Ok(tree) => {
                    if let Some(tree) = tree.downcast_ref::<welly::Stmt>() {
                        ret.push(Stmt::validate(report, tree)?);
                    } else {
                        report(*loc, "Expected a statement");
                        is_valid = false;
                    }
                },
                Err(msg) => { report(*loc, msg); is_valid = false; }
            }
        }
        if is_valid { Ok(Block(ret.into())) } else { Err(Invalid) }
    }
}

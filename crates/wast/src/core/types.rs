use crate::core::*;
use crate::kw;
use crate::parser::{Cursor, Parse, Parser, Peek, Result};
use crate::token::{Id, Index, LParen, NameAnnotation, Span};
use std::mem;
use crate::encode::Encode;

/// The value types for a wasm module.
#[allow(missing_docs)]
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum ValType<'a> {
    I32,
    I64,
    F32,
    F64,
    V128,
    Ref(RefType<'a>),
}

impl<'a> Parse<'a> for ValType<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let mut l = parser.lookahead1();
        if l.peek::<kw::i32>()? {
            parser.parse::<kw::i32>()?;
            Ok(ValType::I32)
        } else if l.peek::<kw::i64>()? {
            parser.parse::<kw::i64>()?;
            Ok(ValType::I64)
        } else if l.peek::<kw::f32>()? {
            parser.parse::<kw::f32>()?;
            Ok(ValType::F32)
        } else if l.peek::<kw::f64>()? {
            parser.parse::<kw::f64>()?;
            Ok(ValType::F64)
        } else if l.peek::<kw::v128>()? {
            parser.parse::<kw::v128>()?;
            Ok(ValType::V128)
        } else if l.peek::<RefType>()? {
            Ok(ValType::Ref(parser.parse()?))
        } else {
            Err(l.error())
        }
    }
}

impl<'a> Peek for ValType<'a> {
    fn peek(cursor: Cursor<'_>) -> Result<bool> {
        Ok(kw::i32::peek(cursor)?
            || kw::i64::peek(cursor)?
            || kw::f32::peek(cursor)?
            || kw::f64::peek(cursor)?
            || kw::v128::peek(cursor)?
            || RefType::peek(cursor)?)
    }
    fn display() -> &'static str {
        "valtype"
    }
}

/// An indexed type
#[allow(missing_docs)]
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct IndexedType<'a> {
    t: ValType<'a>,
    alpha: Id<'a>,
}

impl<'a> Parse<'a> for IndexedType<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        parser.parens(|p: Parser| {
            let t = p.parse::<ValType>()?;
            let alpha = p.parse::<Id>()?;
            Ok(Self {t, alpha} )
        })
    }
}

impl<'a> Peek for IndexedType<'a> {
    fn peek(cursor: Cursor<'_>) -> Result<bool> {
        if let Some(next) = cursor.lparen()? {
            return Ok(ValType::peek(next)? && Id::peek2(next)?)
        }

        Ok(false)
    }

    fn display() -> &'static str {
        "indexed type"
    }
}

macro_rules! index_expr {
    (pub enum $enum:ident {
        $(
            $name:ident $(($($arg:tt)*))? : [$($binary:tt)*] : $instr:tt,
        )*
    }) => (
        /// A listing of all WebAssembly instructions that can be in a module
        /// that this crate currently parses.
        #[allow(missing_docs)]
        #[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
        pub enum $enum {
            $(
                $name $(( $($arg)* ))?,
            )*
        }

        #[allow(non_snake_case)]
        impl Parse<'_> for $enum {
            fn parse(parser: Parser) -> Result<Self> {
                $(
                    fn $name<'a>(_parser: Parser<'a>) -> Result<$enum> {
                        Ok($enum::$name $((
                            $(_parser.parse::<$arg>())*?
                        ))?)
                    }
                )*
                let parse_remainder = parser.step(|c| {
                    let (kw, rest) = match c.keyword()? {
                        Some(pair) => pair,
                        None => return Err(c.error(stringify!(expected an $enum))),
                    };
                    match kw {
                        $($instr => Ok(($name as fn(_) -> _, rest)),)*
                        _ => return Err(c.error("unknown operator or unexpected token")),
                    }
                })?;
                parse_remainder(parser)
            }
        }

        impl Peek for $enum {
            fn peek(cursor: Cursor<'_>) -> Result<bool> {
                match cursor.keyword()? {
                    $(Some(($instr, _)) => Ok(true),)*
                    _ => Ok(false),
                }
            }

            fn display() -> &'static str {
                stringify!(indexed term - $enum)
            }
        }

        impl Encode for $enum {
            #[allow(non_snake_case)]
            fn encode(&self, v: &mut Vec<u8>) {
                match self {
                    $(
                        $enum::$name $((index_expr!(@first x $($arg)*)))? => {
                            fn encode($(arg: &index_expr!(@ty $($arg)*),)? v: &mut Vec<u8>) {
                                index_expr!(@encode v $($binary)*);
                                $(<index_expr!(@ty $($arg)*) as Encode>::encode(arg, v);)?
                            }
                            encode($( index_expr!(@first x $($arg)*), )? v)
                        }
                    )*
                }
            }
        }
    );

    (@ty $other:ty) => ($other);
    (@first $first:ident $($t:tt)*) => ($first);
    (@encode $dst:ident $($bytes:tt)*) => ($dst.extend_from_slice(&[$($bytes)*]););
}

index_expr! {
    pub enum BinOp {
        I32Add : [0x6a] : "i32.add",
        I32Sub : [0x6b] : "i32.sub",
        I32Mul : [0x6c] : "i32.mul",
        I32DivS : [0x6d] : "i32.div_s",
        I32DivU : [0x6e] : "i32.div_u",
        I32RemS : [0x6f] : "i32.rem_s",
        I32RemU : [0x70] : "i32.rem_u",
        I32And : [0x71] : "i32.and",
        I32Or : [0x72] : "i32.or",
        I32Xor : [0x73] : "i32.xor",
        I32Shl : [0x74] : "i32.shl",
        I32ShrS : [0x75] : "i32.shr_s",
        I32ShrU : [0x76] : "i32.shr_u",
        I32Rotl : [0x77] : "i32.rotl",
        I32Rotr : [0x78] : "i32.rotr",
        I64Add : [0x7c] : "i64.add",
        I64Sub : [0x7d] : "i64.sub",
        I64Mul : [0x7e] : "i64.mul",
        I64DivS : [0x7f] : "i64.div_s",
        I64DivU : [0x80] : "i64.div_u",
        I64RemS : [0x81] : "i64.rem_s",
        I64RemU : [0x82] : "i64.rem_u",
        I64And : [0x83] : "i64.and",
        I64Or : [0x84] : "i64.or",
        I64Xor : [0x85] : "i64.xor",
        I64Shl : [0x86] : "i64.shl",
        I64ShrS : [0x87] : "i64.shr_s",
        I64ShrU : [0x88] : "i64.shr_u",
        I64Rotl : [0x89] : "i64.rotl",
        I64Rotr : [0x8a] : "i64.rotr",
    }
}

index_expr! {
    pub enum RelOp {
        I32Eq : [0x46] : "i32.eq",
        I32Ne : [0x47] : "i32.ne",
        I32LtS : [0x48] : "i32.lt_s",
        I32LtU : [0x49] : "i32.lt_u",
        I32GtS : [0x4a] : "i32.gt_s",
        I32GtU : [0x4b] : "i32.gt_u",
        I32LeS : [0x4c] : "i32.le_s",
        I32LeU : [0x4d] : "i32.le_u",
        I32GeS : [0x4e] : "i32.ge_s",
        I32GeU : [0x4f] : "i32.ge_u",
        I64Eq : [0x51] : "i64.eq",
        I64Ne : [0x52] : "i64.ne",
        I64LtS : [0x53] : "i64.lt_s",
        I64LtU : [0x54] : "i64.lt_u",
        I64GtS : [0x55] : "i64.gt_s",
        I64GtU : [0x56] : "i64.gt_u",
        I64LeS : [0x57] : "i64.le_s",
        I64LeU : [0x58] : "i64.le_u",
        I64GeS : [0x59] : "i64.ge_s",
        I64GeU : [0x5a] : "i64.ge_u",
    }
}

index_expr! {
    pub enum UnOp {
        I32Clz : [0x67] : "i32.clz",
        I32Ctz : [0x68] : "i32.ctz",
        I32Popcnt : [0x69] : "i32.popcnt",
        I64Clz : [0x79] : "i64.clz",
        I64Ctz : [0x7a] : "i64.ctz",
        I64Popcnt : [0x7b] : "i64.popcnt",
    }
}

index_expr! {
    pub enum TestOp {
        I32Eqz : [0x45] : "i32.eqz",
        I64Eqz : [0x50] : "i64.eqz",
    }
}

index_expr! {
    pub enum Constant {
        I32Const(i32) : [0x41] : "i32",
        I64Const(i64) : [0x42] : "i64",
    }
}

#[allow(missing_docs)]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum IndexTerm<'a> {
    IBinOp(BinOp, Box<IndexTerm<'a>>, Box<IndexTerm<'a>>),
    IRelOp(RelOp, Box<IndexTerm<'a>>, Box<IndexTerm<'a>>),
    ITestOp(TestOp, Box<IndexTerm<'a>>),
    IUnOp(UnOp, Box<IndexTerm<'a>>),
    Alpha(Id<'a>),
    // Alpha will get resolved into one of the following two, they are not parseable ATM
    Pre(Index<'a>),
    Post(Index<'a>),
    Local(Index<'a>),
    OldLocal(Index<'a>),
    IConstant(Constant)
}

impl<'a> Parse<'a> for IndexTerm<'a> {
    #[allow(non_snake_case)]
    fn parse(parser: Parser<'a>) -> Result<IndexTerm<'a>> {
        fn IBinOp<'a>(_parser: Parser<'a>) -> Result<IndexTerm<'a>> {
            let bop = _parser.parse::<BinOp>()?;
            let x = _parser.parse::<IndexTerm>()?;
            let y = _parser.parse::<IndexTerm>()?;
            Ok(IndexTerm::IBinOp(bop, Box::new(x),Box::new(y)))
        }
        fn IRelOp<'a>(_parser: Parser<'a>) -> Result<IndexTerm<'a>> {
            let rop = _parser.parse::<RelOp>()?;
            let x = _parser.parse::<IndexTerm>()?;
            let y = _parser.parse::<IndexTerm>()?;
            Ok(IndexTerm::IRelOp(rop, Box::new(x),Box::new(y)))
        }
        fn ITestOp<'a>(_parser: Parser<'a>) -> Result<IndexTerm<'a>> {
            let testop = _parser.parse::<TestOp>()?;
            let x = _parser.parse::<IndexTerm>()?;
            Ok(IndexTerm::ITestOp(testop, Box::new(x)))
        }
        fn IUnOp<'a>(_parser: Parser<'a>) -> Result<IndexTerm<'a>> {
            let uop = _parser.parse::<UnOp>()?;
            let x = _parser.parse::<IndexTerm>()?;
            Ok(IndexTerm::IUnOp(uop, Box::new(x)))
        }
        fn Alpha<'a>(_parser: Parser<'a>) -> Result<IndexTerm<'a>> {
            let id = _parser.parse::<Id>()?;
            Ok(IndexTerm::Alpha(id))
        }
        fn Constant<'a>(_parser: Parser<'a>) -> Result<IndexTerm<'a>> {
            //let vty = _parser.parse::<ValType>()?;
            let constant = _parser.parse::<Constant>()?;
            Ok(IndexTerm::IConstant(constant))
        }
        fn Local<'a>(_parser: Parser<'a>) -> Result<IndexTerm<'a>> {
            //let vty = _parser.parse::<ValType>()?;
            _parser.parse::<kw::local>()?;
            Ok(IndexTerm::Local(_parser.parse()?))
        }
        fn OldLocal<'a>(_parser: Parser<'a>) -> Result<IndexTerm<'a>> {
            //let vty = _parser.parse::<ValType>()?;
            _parser.parse::<kw::old_local>()?;
            Ok(IndexTerm::OldLocal(_parser.parse()?))
        }

        if parser.peek::<Id>()? {
            return Alpha(parser);
        }

        parser.parens(|inner| {
            //let cursor = inner.cursor();

            if inner.peek::<BinOp>()? {
                return IBinOp(inner);
            } else if inner.peek::<RelOp>()? {
                return IRelOp(inner);
            } else if inner.peek::<UnOp>()? {
                return IUnOp(inner);
            } else if inner.peek::<TestOp>()? {
                return ITestOp(inner);
            } else if parser.peek::<Constant>()? { // This looks blatantly incorrect but works somehow???
                return Constant(parser);
            } else if inner.peek::<kw::local>()? {
                return Local(inner);
            } else if inner.peek::<kw::old_local>()? {
                return OldLocal(inner);
            }

            return Err(inner.error("expected index term"))
        })
    }
}

impl<'a> Peek for IndexTerm<'a> {
    #[allow(non_snake_case)]
    fn peek(cursor: Cursor<'_>) -> Result<bool> {
        if let Some(_) = cursor.id()? {
            return Ok(true)
        }

        if let Some(next) = cursor.lparen()? {
            if let Some(("local", _)) = next.keyword()? {
                return Ok(true)
            };

            if let Some(("old_local", _)) = next.keyword()? {
                return Ok(true)
            };

            return Ok(BinOp::peek(next)? || RelOp::peek(next)?
            || TestOp::peek(next)? || UnOp::peek(next)?
            || ValType::peek(next)?);
        }

        Ok(false)
    }

    fn display() -> &'static str {
        "index term"
    }
}

#[allow(missing_docs)]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Constraint<'a> {
    Eq(IndexTerm<'a>, IndexTerm<'a>),
    And(Box<Constraint<'a>>, Box<Constraint<'a>>),
    Or(Box<Constraint<'a>>, Box<Constraint<'a>>),
    If(Box<Constraint<'a>>,Box<Constraint<'a>>,Box<Constraint<'a>>),
    Not(Box<Constraint<'a>>),
}

impl<'a> Parse<'a> for Constraint<'a> {
    #[allow(non_snake_case)]
    fn parse(parser: Parser<'a>) -> Result<Constraint<'a>> {
        parser.parens(|inner| {
            let mut l = parser.lookahead1();
            if l.peek::<kw::eq>()? {
                parser.parse::<kw::eq>()?;
                let x = parser.parse::<IndexTerm>()?;
                let y = parser.parse::<IndexTerm>()?;
                return Ok(Constraint::Eq(x, y));
            } else if l.peek::<kw::and>()? {
                parser.parse::<kw::and>()?;
                let x = parser.parse::<Constraint>()?;
                let y = parser.parse::<Constraint>()?;
                return Ok(Constraint::And(Box::new(x), Box::new(y)));
            } else if l.peek::<kw::or>()? {
                parser.parse::<kw::or>()?;
                let x = parser.parse::<Constraint>()?;
                let y = parser.parse::<Constraint>()?;
                return Ok(Constraint::Or(Box::new(x), Box::new(y)));
            } else if l.peek::<kw::not>()? {
                parser.parse::<kw::not>()?;
                let x = parser.parse::<Constraint>()?;
                return Ok(Constraint::Not(Box::new(x)));
            } else if l.peek::<kw::r#if>()? {
                parser.parse::<kw::r#if>()?;
                let i = parser.parse::<Constraint>()?;
                let t = parser.parse::<Constraint>()?;
                let e = parser.parse::<Constraint>()?;
                return Ok(Constraint::If(Box::new(i), Box::new(t), Box::new(e)));
            }

            return Err(inner.error("expected constraint"));
        })
    }
}

impl<'a> Peek for Constraint<'a> {
    #[allow(non_snake_case)]
    fn peek(cursor: Cursor<'_>) -> Result<bool> {

        if let Some(next) = cursor.lparen()? {
            return match next.keyword()? {
                Some(("eq",_)) => Ok(true),
                Some(("if",_)) => Ok(true),
                Some(("and",_)) => Ok(true),
                Some(("or",_)) => Ok(true),
                Some(("not",_)) => Ok(true),
                _ => Ok(false),
            };
        }

        Ok(false)
    }

    fn display() -> &'static str {
        "constraint"
    }
}

/// A heap type for a reference type
#[allow(missing_docs)]
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum HeapType<'a> {
    /// An untyped function reference: funcref. This is part of the reference
    /// types proposal.
    Func,
    /// A reference to any host value: externref. This is part of the reference
    /// types proposal.
    Extern,
    /// A reference to a wasm exception. This is part of the exceptions proposal.
    Exn,
    /// A reference to any reference value: anyref. This is part of the GC
    /// proposal.
    Any,
    /// A reference that has an identity that can be compared: eqref. This is
    /// part of the GC proposal.
    Eq,
    /// A reference to a GC struct. This is part of the GC proposal.
    Struct,
    /// A reference to a GC array. This is part of the GC proposal.
    Array,
    /// An unboxed 31-bit integer: i31ref. Part of the GC proposal.
    I31,
    /// The bottom type of the funcref hierarchy. Part of the GC proposal.
    NoFunc,
    /// The bottom type of the externref hierarchy. Part of the GC proposal.
    NoExtern,
    /// The bottom type of the anyref hierarchy. Part of the GC proposal.
    None,
    /// A reference to a concrete function, struct, or array type defined by
    /// Wasm: `ref T`. This is part of the function references and GC proposals.
    Concrete(Index<'a>),
}

impl<'a> Parse<'a> for HeapType<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let mut l = parser.lookahead1();
        if l.peek::<kw::func>()? {
            parser.parse::<kw::func>()?;
            Ok(HeapType::Func)
        } else if l.peek::<kw::r#extern>()? {
            parser.parse::<kw::r#extern>()?;
            Ok(HeapType::Extern)
        } else if l.peek::<kw::exn>()? {
            parser.parse::<kw::exn>()?;
            Ok(HeapType::Exn)
        } else if l.peek::<kw::r#any>()? {
            parser.parse::<kw::r#any>()?;
            Ok(HeapType::Any)
        } else if l.peek::<kw::eq>()? {
            parser.parse::<kw::eq>()?;
            Ok(HeapType::Eq)
        } else if l.peek::<kw::r#struct>()? {
            parser.parse::<kw::r#struct>()?;
            Ok(HeapType::Struct)
        } else if l.peek::<kw::array>()? {
            parser.parse::<kw::array>()?;
            Ok(HeapType::Array)
        } else if l.peek::<kw::i31>()? {
            parser.parse::<kw::i31>()?;
            Ok(HeapType::I31)
        } else if l.peek::<kw::nofunc>()? {
            parser.parse::<kw::nofunc>()?;
            Ok(HeapType::NoFunc)
        } else if l.peek::<kw::noextern>()? {
            parser.parse::<kw::noextern>()?;
            Ok(HeapType::NoExtern)
        } else if l.peek::<kw::none>()? {
            parser.parse::<kw::none>()?;
            Ok(HeapType::None)
        } else if l.peek::<Index>()? {
            Ok(HeapType::Concrete(parser.parse()?))
        } else {
            Err(l.error())
        }
    }
}

impl<'a> Peek for HeapType<'a> {
    fn peek(cursor: Cursor<'_>) -> Result<bool> {
        Ok(kw::func::peek(cursor)?
            || kw::r#extern::peek(cursor)?
            || kw::exn::peek(cursor)?
            || kw::any::peek(cursor)?
            || kw::eq::peek(cursor)?
            || kw::r#struct::peek(cursor)?
            || kw::array::peek(cursor)?
            || kw::i31::peek(cursor)?
            || kw::nofunc::peek(cursor)?
            || kw::noextern::peek(cursor)?
            || kw::none::peek(cursor)?
            || (LParen::peek(cursor)? && kw::r#type::peek2(cursor)?))
    }
    fn display() -> &'static str {
        "heaptype"
    }
}

/// A reference type in a wasm module.
#[allow(missing_docs)]
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct RefType<'a> {
    pub nullable: bool,
    pub heap: HeapType<'a>,
}

impl<'a> RefType<'a> {
    /// A `funcref` as an abbreviation for `(ref null func)`.
    pub fn func() -> Self {
        RefType {
            nullable: true,
            heap: HeapType::Func,
        }
    }

    /// An `externref` as an abbreviation for `(ref null extern)`.
    pub fn r#extern() -> Self {
        RefType {
            nullable: true,
            heap: HeapType::Extern,
        }
    }

    /// An `exnrefr` as an abbreviation for `(ref null exn)`.
    pub fn exn() -> Self {
        RefType {
            nullable: true,
            heap: HeapType::Exn,
        }
    }

    /// An `anyref` as an abbreviation for `(ref null any)`.
    pub fn any() -> Self {
        RefType {
            nullable: true,
            heap: HeapType::Any,
        }
    }

    /// An `eqref` as an abbreviation for `(ref null eq)`.
    pub fn eq() -> Self {
        RefType {
            nullable: true,
            heap: HeapType::Eq,
        }
    }

    /// An `structref` as an abbreviation for `(ref null struct)`.
    pub fn r#struct() -> Self {
        RefType {
            nullable: true,
            heap: HeapType::Struct,
        }
    }

    /// An `arrayref` as an abbreviation for `(ref null array)`.
    pub fn array() -> Self {
        RefType {
            nullable: true,
            heap: HeapType::Array,
        }
    }

    /// An `i31ref` as an abbreviation for `(ref null i31)`.
    pub fn i31() -> Self {
        RefType {
            nullable: true,
            heap: HeapType::I31,
        }
    }

    /// A `nullfuncref` as an abbreviation for `(ref null nofunc)`.
    pub fn nullfuncref() -> Self {
        RefType {
            nullable: true,
            heap: HeapType::NoFunc,
        }
    }

    /// A `nullexternref` as an abbreviation for `(ref null noextern)`.
    pub fn nullexternref() -> Self {
        RefType {
            nullable: true,
            heap: HeapType::NoExtern,
        }
    }

    /// A `nullref` as an abbreviation for `(ref null none)`.
    pub fn nullref() -> Self {
        RefType {
            nullable: true,
            heap: HeapType::None,
        }
    }
}

impl<'a> Parse<'a> for RefType<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let mut l = parser.lookahead1();
        if l.peek::<kw::funcref>()? {
            parser.parse::<kw::funcref>()?;
            Ok(RefType::func())
        } else if l.peek::<kw::anyfunc>()? {
            parser.parse::<kw::anyfunc>()?;
            Ok(RefType::func())
        } else if l.peek::<kw::externref>()? {
            parser.parse::<kw::externref>()?;
            Ok(RefType::r#extern())
        } else if l.peek::<kw::exnref>()? {
            parser.parse::<kw::exnref>()?;
            Ok(RefType::exn())
        } else if l.peek::<kw::anyref>()? {
            parser.parse::<kw::anyref>()?;
            Ok(RefType::any())
        } else if l.peek::<kw::eqref>()? {
            parser.parse::<kw::eqref>()?;
            Ok(RefType::eq())
        } else if l.peek::<kw::structref>()? {
            parser.parse::<kw::structref>()?;
            Ok(RefType::r#struct())
        } else if l.peek::<kw::arrayref>()? {
            parser.parse::<kw::arrayref>()?;
            Ok(RefType::array())
        } else if l.peek::<kw::i31ref>()? {
            parser.parse::<kw::i31ref>()?;
            Ok(RefType::i31())
        } else if l.peek::<kw::nullfuncref>()? {
            parser.parse::<kw::nullfuncref>()?;
            Ok(RefType::nullfuncref())
        } else if l.peek::<kw::nullexternref>()? {
            parser.parse::<kw::nullexternref>()?;
            Ok(RefType::nullexternref())
        } else if l.peek::<kw::nullref>()? {
            parser.parse::<kw::nullref>()?;
            Ok(RefType::nullref())
        } else if l.peek::<LParen>()? {
            parser.parens(|p| {
                let mut l = parser.lookahead1();
                if l.peek::<kw::r#ref>()? {
                    p.parse::<kw::r#ref>()?;

                    let mut nullable = false;
                    if parser.peek::<kw::null>()? {
                        parser.parse::<kw::null>()?;
                        nullable = true;
                    }

                    Ok(RefType {
                        nullable,
                        heap: parser.parse()?,
                    })
                } else {
                    Err(l.error())
                }
            })
        } else {
            Err(l.error())
        }
    }
}

impl<'a> Peek for RefType<'a> {
    fn peek(cursor: Cursor<'_>) -> Result<bool> {
        Ok(kw::funcref::peek(cursor)?
            || /* legacy */ kw::anyfunc::peek(cursor)?
            || kw::externref::peek(cursor)?
            || kw::exnref::peek(cursor)?
            || kw::anyref::peek(cursor)?
            || kw::eqref::peek(cursor)?
            || kw::structref::peek(cursor)?
            || kw::arrayref::peek(cursor)?
            || kw::i31ref::peek(cursor)?
            || kw::nullfuncref::peek(cursor)?
            || kw::nullexternref::peek(cursor)?
            || kw::nullref::peek(cursor)?
            || (LParen::peek(cursor)? && kw::r#ref::peek2(cursor)?))
    }
    fn display() -> &'static str {
        "reftype"
    }
}

/// The types of values that may be used in a struct or array.
#[allow(missing_docs)]
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum StorageType<'a> {
    I8,
    I16,
    Val(ValType<'a>),
}

impl<'a> Parse<'a> for StorageType<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let mut l = parser.lookahead1();
        if l.peek::<kw::i8>()? {
            parser.parse::<kw::i8>()?;
            Ok(StorageType::I8)
        } else if l.peek::<kw::i16>()? {
            parser.parse::<kw::i16>()?;
            Ok(StorageType::I16)
        } else if l.peek::<ValType>()? {
            Ok(StorageType::Val(parser.parse()?))
        } else {
            Err(l.error())
        }
    }
}

/// Type for a `global` in a wasm module
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct GlobalType<'a> {
    /// The element type of this `global`
    pub ty: ValType<'a>,
    /// Whether or not the global is mutable or not.
    pub mutable: bool,
}

impl<'a> Parse<'a> for GlobalType<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        if parser.peek2::<kw::r#mut>()? {
            parser.parens(|p| {
                p.parse::<kw::r#mut>()?;
                Ok(GlobalType {
                    ty: parser.parse()?,
                    mutable: true,
                })
            })
        } else {
            Ok(GlobalType {
                ty: parser.parse()?,
                mutable: false,
            })
        }
    }
}

/// Min/max limits used for tables/memories.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Limits {
    /// The minimum number of units for this type.
    pub min: u32,
    /// An optional maximum number of units for this type.
    pub max: Option<u32>,
}

impl<'a> Parse<'a> for Limits {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let min = parser.parse()?;
        let max = if parser.peek::<u32>()? {
            Some(parser.parse()?)
        } else {
            None
        };
        Ok(Limits { min, max })
    }
}

/// Min/max limits used for 64-bit memories
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Limits64 {
    /// The minimum number of units for this type.
    pub min: u64,
    /// An optional maximum number of units for this type.
    pub max: Option<u64>,
}

impl<'a> Parse<'a> for Limits64 {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let min = parser.parse()?;
        let max = if parser.peek::<u64>()? {
            Some(parser.parse()?)
        } else {
            None
        };
        Ok(Limits64 { min, max })
    }
}

/// Configuration for a table of a wasm mdoule
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TableType<'a> {
    /// Limits on the element sizes of this table
    pub limits: Limits,
    /// The type of element stored in this table
    pub elem: RefType<'a>,
}

impl<'a> Parse<'a> for TableType<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        Ok(TableType {
            limits: parser.parse()?,
            elem: parser.parse()?,
        })
    }
}

/// Configuration for a memory of a wasm module
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum MemoryType {
    /// A 32-bit memory
    B32 {
        /// Limits on the page sizes of this memory
        limits: Limits,
        /// Whether or not this is a shared (atomic) memory type
        shared: bool,
    },
    /// A 64-bit memory
    B64 {
        /// Limits on the page sizes of this memory
        limits: Limits64,
        /// Whether or not this is a shared (atomic) memory type
        shared: bool,
    },
}

impl<'a> Parse<'a> for MemoryType {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        if parser.peek::<kw::i64>()? {
            parser.parse::<kw::i64>()?;
            let limits = parser.parse()?;
            let shared = parser.parse::<Option<kw::shared>>()?.is_some();
            Ok(MemoryType::B64 { limits, shared })
        } else {
            parser.parse::<Option<kw::i32>>()?;
            let limits = parser.parse()?;
            let shared = parser.parse::<Option<kw::shared>>()?.is_some();
            Ok(MemoryType::B32 { limits, shared })
        }
    }
}

// TODO: support non-indexed types
/// A function type with parameters and results.
#[derive(Clone, Debug, Default)]
pub struct IndexedFunctionType<'a> {
    /// The parameters of a function, optionally each having an identifier for
    /// name resolution and a name for the custom `name` section.
    pub params: Box<[(Option<Id<'a>>, Option<NameAnnotation<'a>>, ValType<'a>)]>,
    /// Constraints in the pre-condition
    pub pre_constraints: Box<[Constraint<'a>]>,
    /// The results types of a function.
    pub results: Box<[(Option<Id<'a>>, Option<NameAnnotation<'a>>, ValType<'a>)]>,
    /// Constraints in the post-condition
    pub post_constraints: Box<[Constraint<'a>]>,
}

impl<'a> IndexedFunctionType<'a> {
    fn finish_parse(&mut self, parser: Parser<'a>) -> Result<()> {
        let mut params = Vec::from(mem::take(&mut self.params));
        let mut pre_constraints: Vec<Constraint> = Vec::from(mem::take(&mut self.pre_constraints));
        let mut results = Vec::from(mem::take(&mut self.results));
        let mut post_constraints: Vec<Constraint> = Vec::from(mem::take(&mut self.post_constraints));
    
        while parser.peek2::<kw::pre>()? || parser.peek2::<kw::post>()? || parser.peek2::<kw::param>()? || parser.peek2::<kw::result>()? {
            parser.parens(|p| {
                let mut l = p.lookahead1();

                if l.peek::<kw::param>()? {
                    if results.len() > 0 {
                        return Err(p.error(
                            "result before parameter (or unexpected token): \
                             cannot list params after results",
                        ));
                    }
                    p.parse::<kw::param>()?;
                    if p.is_empty() {
                        return Ok(());
                    }
                    let id = p.parse::<Option<_>>()?;
                    let name = p.parse::<Option<_>>()?;
                    let parse_more = id.is_none() && name.is_none();
                    let ty = p.parse()?;
                    params.push((id, name, ty));
                    while parse_more && !p.is_empty() {
                        params.push((None, None, p.parse()?));
                    }
                } else if l.peek::<kw::result>()? {
                    p.parse::<kw::result>()?;
                    if p.is_empty() {
                        return Ok(());
                    }
                    let id = p.parse::<Option<_>>()?;
                    let name = p.parse::<Option<_>>()?;
                    let parse_more = id.is_none() && name.is_none();
                    let ty = p.parse()?;
                    results.push((id, name, ty));
                    while parse_more && !p.is_empty() {
                        results.push((None, None, p.parse()?));
                    }
                } else if l.peek::<kw::pre>()? {
                    p.parse::<kw::pre>()?;
                    /*p.parens(|inner| {
                        while let Ok(it) = inner.parse::<IndexedType>() {
                            params.push(it);
                        }
                        Ok(())
                    })?;*/
                    while !p.is_empty() {
                        pre_constraints.push(p.parse()?);
                    }
                } else if l.peek::<kw::post>()? {
                    p.parse::<kw::post>()?;
                    /*p.parens(|inner| {
                        while !inner.is_empty() {
                            results.push(inner.parse()?);
                        }
                        Ok(())
                    })?;*/
                    while !p.is_empty() {
                        post_constraints.push(p.parse()?);
                    }
                } else {
                    return Err(l.error());
                };
                Ok(())
            })?;
        }
        self.params = params.into();
        self.pre_constraints = pre_constraints.into();
        self.results = results.into();
        self.post_constraints = post_constraints.into();
        Ok(())
    }
}

impl<'a> Parse<'a> for IndexedFunctionType<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let mut ret = IndexedFunctionType {
            params: Box::new([]),
            pre_constraints: Box::new([]),
            results: Box::new([]),
            post_constraints: Box::new([]),
        };
        ret.finish_parse(parser)?;
        Ok(ret)
    }
}

impl<'a> Peek for IndexedFunctionType<'a> {
    fn peek(cursor: Cursor<'_>) -> Result<bool> {
        if let Some(next) = cursor.lparen()? {
            match next.keyword()? {
                Some(("pre", _)) | Some(("post", _)) | Some(("param", _)) | Some(("result", _)) => return Ok(true),
                _ => {}
            }
        }

        Ok(false)
    }

    fn display() -> &'static str {
        "indexed function type"
    }
}

/// A function type with parameters and results.
#[derive(Clone, Debug, Default)]
pub struct FunctionTypeNoNames<'a>(pub IndexedFunctionType<'a>);

impl<'a> Parse<'a> for FunctionTypeNoNames<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let mut ret = IndexedFunctionType {
            params: Box::new([]),
            results: Box::new([]),
            pre_constraints: Box::new([]),
            post_constraints: Box::new([]),
        };
        ret.finish_parse(parser)?;
        Ok(FunctionTypeNoNames(ret))
    }
}

impl<'a> Peek for FunctionTypeNoNames<'a> {
    fn peek(cursor: Cursor<'_>) -> Result<bool> {
        IndexedFunctionType::peek(cursor)
    }

    fn display() -> &'static str {
        IndexedFunctionType::display()
    }
}

impl<'a> From<FunctionTypeNoNames<'a>> for IndexedFunctionType<'a> {
    fn from(ty: FunctionTypeNoNames<'a>) -> IndexedFunctionType<'a> {
        ty.0
    }
}

/// A struct type with fields.
#[derive(Clone, Debug)]
pub struct StructType<'a> {
    /// The fields of the struct
    pub fields: Vec<StructField<'a>>,
}

impl<'a> Parse<'a> for StructType<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let mut ret = StructType { fields: Vec::new() };
        while !parser.is_empty() {
            parser.parens(|parser| {
                parser.parse::<kw::field>()?;
                if parser.peek::<Id>()? {
                    let field = StructField::parse(parser, true);
                    ret.fields.push(field?);
                } else {
                    while !parser.is_empty() {
                        let field = StructField::parse(parser, false);
                        ret.fields.push(field?);
                    }
                }
                Ok(())
            })?;
        }
        Ok(ret)
    }
}

/// A field of a struct type.
#[derive(Clone, Debug)]
pub struct StructField<'a> {
    /// An optional identifier for name resolution.
    pub id: Option<Id<'a>>,
    /// Whether this field may be mutated or not.
    pub mutable: bool,
    /// The storage type stored in this field.
    pub ty: StorageType<'a>,
}

impl<'a> StructField<'a> {
    fn parse(parser: Parser<'a>, with_id: bool) -> Result<Self> {
        let id = if with_id { parser.parse()? } else { None };
        let (ty, mutable) = if parser.peek2::<kw::r#mut>()? {
            let ty = parser.parens(|parser| {
                parser.parse::<kw::r#mut>()?;
                parser.parse()
            })?;
            (ty, true)
        } else {
            (parser.parse::<StorageType<'a>>()?, false)
        };
        Ok(StructField { id, mutable, ty })
    }
}

/// An array type with fields.
#[derive(Clone, Debug)]
pub struct ArrayType<'a> {
    /// Whether this field may be mutated or not.
    pub mutable: bool,
    /// The storage type stored in this field.
    pub ty: StorageType<'a>,
}

impl<'a> Parse<'a> for ArrayType<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let (ty, mutable) = if parser.peek2::<kw::r#mut>()? {
            let ty = parser.parens(|parser| {
                parser.parse::<kw::r#mut>()?;
                parser.parse()
            })?;
            (ty, true)
        } else {
            (parser.parse::<StorageType<'a>>()?, false)
        };
        Ok(ArrayType { mutable, ty })
    }
}

/// The type of an exported item from a module or instance.
#[derive(Debug, Clone)]
pub struct ExportType<'a> {
    /// Where this export was defined.
    pub span: Span,
    /// The name of this export.
    pub name: &'a str,
    /// The signature of the item that's exported.
    pub item: ItemSig<'a>,
}

impl<'a> Parse<'a> for ExportType<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let span = parser.parse::<kw::export>()?.0;
        let name = parser.parse()?;
        let item = parser.parens(|p| p.parse())?;
        Ok(ExportType { span, name, item })
    }
}

/// A definition of a type.
#[derive(Debug)]
pub enum TypeDef<'a> {
    /// A function type definition.
    Func(IndexedFunctionType<'a>),
    /// A struct type definition.
    Struct(StructType<'a>),
    /// An array type definition.
    Array(ArrayType<'a>),
}

impl<'a> Parse<'a> for TypeDef<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let mut l = parser.lookahead1();
        if l.peek::<kw::func>()? {
            parser.parse::<kw::func>()?;
            // let ift = parser.parse::<IndexedFunctionType>()?;
            // Ok(TypeDef::Func(ift.into()))
            Ok(TypeDef::Func(parser.parse()?))
        } else if l.peek::<kw::r#struct>()? {
            parser.parse::<kw::r#struct>()?;
            Ok(TypeDef::Struct(parser.parse()?))
        } else if l.peek::<kw::array>()? {
            parser.parse::<kw::array>()?;
            Ok(TypeDef::Array(parser.parse()?))
        } else {
            Err(l.error())
        }
    }
}

/// A type declaration in a module
#[derive(Debug)]
pub struct Type<'a> {
    /// Where this type was defined.
    pub span: Span,
    /// An optional identifier to refer to this `type` by as part of name
    /// resolution.
    pub id: Option<Id<'a>>,
    /// An optional name for this function stored in the custom `name` section.
    pub name: Option<NameAnnotation<'a>>,
    /// The type that we're declaring.
    pub def: TypeDef<'a>,
    /// The declared parent type of this definition.
    pub parent: Option<Index<'a>>,
    /// Whether this type is final or not. By default types are final.
    pub final_type: Option<bool>,
}

impl<'a> Peek for Type<'a> {
    fn peek(cursor: Cursor<'_>) -> Result<bool> {
        kw::r#type::peek(cursor)
    }
    fn display() -> &'static str {
        "type"
    }
}

impl<'a> Parse<'a> for Type<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let span = parser.parse::<kw::r#type>()?.0;
        let id = parser.parse()?;
        let name = parser.parse()?;

        let (parent, def, final_type) = if parser.peek2::<kw::sub>()? {
            parser.parens(|parser| {
                parser.parse::<kw::sub>()?;

                let final_type: Option<bool> = if parser.peek::<kw::r#final>()? {
                    parser.parse::<kw::r#final>()?;
                    Some(true)
                } else {
                    Some(false)
                };

                let parent = if parser.peek::<Index<'a>>()? {
                    parser.parse()?
                } else {
                    None
                };
                let def = parser.parens(|parser| parser.parse())?;
                Ok((parent, def, final_type))
            })?
        } else {
            (None, parser.parens(|parser| parser.parse())?, None)
        };

        Ok(Type {
            span,
            id,
            name,
            def,
            parent,
            final_type,
        })
    }
}

/// A recursion group declaration in a module
#[derive(Debug)]
pub struct Rec<'a> {
    /// Where this recursion group was defined.
    pub span: Span,
    /// The types that we're defining in this group.
    pub types: Vec<Type<'a>>,
}

impl<'a> Parse<'a> for Rec<'a> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let span = parser.parse::<kw::r#rec>()?.0;
        let mut types = Vec::new();
        while parser.peek2::<Type<'a>>()? {
            types.push(parser.parens(|p| p.parse())?);
        }
        Ok(Rec { span, types })
    }
}

/// A reference to a type defined in this module.
#[derive(Clone, Debug)]
pub struct TypeUse<'a, T> {
    /// The type that we're referencing, if it was present.
    pub index: Option<Index<'a>>,
    /// The inline type, if present.
    pub inline: Option<T>,
}

impl<'a, T> TypeUse<'a, T> {
    /// Constructs a new instance of `TypeUse` without an inline definition but
    /// with an index specified.
    pub fn new_with_index(idx: Index<'a>) -> TypeUse<'a, T> {
        TypeUse {
            index: Some(idx),
            inline: None,
        }
    }
}

impl<'a, T: Peek + Parse<'a>> Parse<'a> for TypeUse<'a, T> {
    fn parse(parser: Parser<'a>) -> Result<Self> {
        let index = if parser.peek2::<kw::r#type>()? {
            Some(parser.parens(|p| {
                p.parse::<kw::r#type>()?;
                p.parse()
            })?)
        } else {
            None
        };
        let inline = parser.parse()?;

        Ok(TypeUse { index, inline: inline})
    }
}

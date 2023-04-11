#![feature(proc_macro_quote)]

extern crate proc_macro;
use proc_macro::TokenStream;
use proc_macro2::{Delimiter, Group, Ident, Punct, Spacing, Span};
use quote::{quote, ToTokens, TokenStreamExt};
extern crate syn;
use syn::parse::{Parse, ParseBuffer, ParseStream};
use syn::token::{Dot, Paren};
use syn::{parenthesized, parse_macro_input, Expr, ExprBinary, ExprUnary, Result, Token};

macro_rules! parenthesize {
    ($first:ident, Boxed: $rest:ident $(,$commas:ident)*) => {
        {
            let mut inner = proc_macro2::TokenStream::new();
            $first.to_tokens(&mut inner);
            inner.append(Punct::new(',', Spacing::Alone));
            parenthesize!(@Box $rest inner);
            $(
                inner.append(Punct::new(',', Spacing::Alone));
                parenthesize!(@Box $commas inner);
            )*
            Group::new(Delimiter::Parenthesis, inner)
        }
    };
    (Boxed: $first:ident $(,$commas:ident)*) => {
        {
            let mut inner = proc_macro2::TokenStream::new();
            parenthesize!(@Box $first inner);
            $(
                inner.append(Punct::new(',', Spacing::Alone));
                parenthesize!(@Box $commas inner);
            )*
            Group::new(Delimiter::Parenthesis, inner)
        }
    };
    ($first:ident $(,$commas:ident)*) => {
        {
            let mut inner = proc_macro2::TokenStream::new();
            $first.to_tokens(&mut inner);
            $(
                inner.append(Punct::new(',', Spacing::Alone));
                $commas.to_tokens(&mut inner);
            )*
            Group::new(Delimiter::Parenthesis, inner)
        }
    };
    (@Box $first:ident $stream:ident) => {
        $stream.append(Ident::new("Box", Span::call_site()));
        $stream.append(Punct::new(':', Spacing::Joint));
        $stream.append(Punct::new(':', Spacing::Joint));
        $stream.append(Ident::new("new", Span::call_site()));
        parenthesize!($first).to_tokens(&mut $stream);
    }
}

mod kw {
    syn::custom_keyword!(i32);
    syn::custom_keyword!(i64);
    syn::custom_keyword!(r#const);
    syn::custom_keyword!(add);
    syn::custom_keyword!(sub);
    syn::custom_keyword!(mul);
    syn::custom_keyword!(div_s);
    syn::custom_keyword!(div_u);
    syn::custom_keyword!(rem_s);
    syn::custom_keyword!(rem_u);
    syn::custom_keyword!(and);
    syn::custom_keyword!(or);
    syn::custom_keyword!(xor);
    syn::custom_keyword!(shl);
    syn::custom_keyword!(shr_s);
    syn::custom_keyword!(shr_u);
    syn::custom_keyword!(rotl);
    syn::custom_keyword!(rotr);
    syn::custom_keyword!(eq);
    syn::custom_keyword!(ne);
    syn::custom_keyword!(lt_s);
    syn::custom_keyword!(lt_u);
    syn::custom_keyword!(gt_s);
    syn::custom_keyword!(gt_u);
    syn::custom_keyword!(le_s);
    syn::custom_keyword!(le_u);
    syn::custom_keyword!(ge_s);
    syn::custom_keyword!(ge_u);
    syn::custom_keyword!(clz);
    syn::custom_keyword!(ctz);
    syn::custom_keyword!(popcnt);
    syn::custom_keyword!(eqz);
    syn::custom_keyword!(r#if);
    syn::custom_keyword!(not);
}

#[allow(non_snake_case)]
#[derive(Clone, Copy, Debug)]
enum BinOp {
    I32Add,
    I32Sub,
    I32Mul,
    I32DivS,
    I32DivU,
    I32RemS,
    I32RemU,
    I32And,
    I32Or,
    I32Xor,
    I32Shl,
    I32ShrS,
    I32ShrU,
    I32Rotl,
    I32Rotr,
    I64Add,
    I64Sub,
    I64Mul,
    I64DivS,
    I64DivU,
    I64RemS,
    I64RemU,
    I64And,
    I64Or,
    I64Xor,
    I64Shl,
    I64ShrS,
    I64ShrU,
    I64Rotl,
    I64Rotr,
}

impl Parse for BinOp {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        let is_i32 = if lookahead.peek(kw::i32) {
            input.parse::<kw::i32>()?;
            true
        } else {
            input.parse::<kw::i64>()?;
            false
        };

        input.parse::<Dot>()?;
        let lookahead = input.lookahead1();
        let binop = if lookahead.peek(kw::add) {
            input.parse::<kw::add>()?;
            if is_i32 {
                Self::I32Add
            } else {
                Self::I64Add
            }
        } else if lookahead.peek(kw::sub) {
            input.parse::<kw::sub>()?;
            if is_i32 {
                Self::I32Sub
            } else {
                Self::I64Sub
            }
        } else if lookahead.peek(kw::mul) {
            input.parse::<kw::mul>()?;
            if is_i32 {
                Self::I32Mul
            } else {
                Self::I64Mul
            }
        } else if lookahead.peek(kw::div_s) {
            input.parse::<kw::div_s>()?;
            if is_i32 {
                Self::I32DivS
            } else {
                Self::I64DivS
            }
        } else if lookahead.peek(kw::div_u) {
            input.parse::<kw::div_u>()?;
            if is_i32 {
                Self::I32DivU
            } else {
                Self::I64DivU
            }
        } else if lookahead.peek(kw::rem_s) {
            input.parse::<kw::rem_s>()?;
            if is_i32 {
                Self::I32RemS
            } else {
                Self::I64RemS
            }
        } else if lookahead.peek(kw::rem_u) {
            input.parse::<kw::rem_u>()?;
            if is_i32 {
                Self::I32RemU
            } else {
                Self::I64RemU
            }
        } else if lookahead.peek(kw::and) {
            input.parse::<kw::and>()?;
            if is_i32 {
                Self::I32And
            } else {
                Self::I64And
            }
        } else if lookahead.peek(kw::or) {
            input.parse::<kw::or>()?;
            if is_i32 {
                Self::I32Or
            } else {
                Self::I64Or
            }
        } else if lookahead.peek(kw::xor) {
            input.parse::<kw::xor>()?;
            if is_i32 {
                Self::I32Xor
            } else {
                Self::I64Xor
            }
        } else if lookahead.peek(kw::shl) {
            input.parse::<kw::shl>()?;
            if is_i32 {
                Self::I32Shl
            } else {
                Self::I64Shl
            }
        } else if lookahead.peek(kw::shr_s) {
            input.parse::<kw::shr_s>()?;
            if is_i32 {
                Self::I32ShrS
            } else {
                Self::I64ShrS
            }
        } else if lookahead.peek(kw::shr_u) {
            input.parse::<kw::shr_u>()?;
            if is_i32 {
                Self::I32ShrU
            } else {
                Self::I64ShrU
            }
        } else if lookahead.peek(kw::rotl) {
            input.parse::<kw::rotl>()?;
            if is_i32 {
                Self::I32Rotl
            } else {
                Self::I64Rotl
            }
        } else if lookahead.peek(kw::rotr) {
            input.parse::<kw::rotr>()?;
            if is_i32 {
                Self::I32Rotr
            } else {
                Self::I64Rotr
            }
        } else {
            return Err(lookahead.error());
        };

        Ok(binop)
    }
}

impl ToTokens for BinOp {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        tokens.append(Ident::new("BinOp", Span::call_site()));
        tokens.append(Punct::new(':', Spacing::Joint));
        tokens.append(Punct::new(':', Spacing::Alone));
        let token = match self {
            BinOp::I32Add => Ident::new("I32Add", Span::call_site()),
            BinOp::I32Sub => Ident::new("I32Sub", Span::call_site()),
            BinOp::I32Mul => Ident::new("I32Mul", Span::call_site()),
            BinOp::I32DivS => Ident::new("I32DivS", Span::call_site()),
            BinOp::I32DivU => Ident::new("I32DivU", Span::call_site()),
            BinOp::I32RemS => Ident::new("I32RemS", Span::call_site()),
            BinOp::I32RemU => Ident::new("I32RemU", Span::call_site()),
            BinOp::I32And => Ident::new("I32And", Span::call_site()),
            BinOp::I32Or => Ident::new("I32Or", Span::call_site()),
            BinOp::I32Xor => Ident::new("I32Xor", Span::call_site()),
            BinOp::I32Shl => Ident::new("I32Shl", Span::call_site()),
            BinOp::I32ShrS => Ident::new("I32ShrS", Span::call_site()),
            BinOp::I32ShrU => Ident::new("I32ShrU", Span::call_site()),
            BinOp::I32Rotl => Ident::new("I32Rotl", Span::call_site()),
            BinOp::I32Rotr => Ident::new("I32Rotr", Span::call_site()),
            BinOp::I64Add => Ident::new("I64Add", Span::call_site()),
            BinOp::I64Sub => Ident::new("I64Sub", Span::call_site()),
            BinOp::I64Mul => Ident::new("I64Mul", Span::call_site()),
            BinOp::I64DivS => Ident::new("I64DivS", Span::call_site()),
            BinOp::I64DivU => Ident::new("I64DivU", Span::call_site()),
            BinOp::I64RemS => Ident::new("I64RemS", Span::call_site()),
            BinOp::I64RemU => Ident::new("I64RemU", Span::call_site()),
            BinOp::I64And => Ident::new("I64And", Span::call_site()),
            BinOp::I64Or => Ident::new("I64Or", Span::call_site()),
            BinOp::I64Xor => Ident::new("I64Xor", Span::call_site()),
            BinOp::I64Shl => Ident::new("I64Shl", Span::call_site()),
            BinOp::I64ShrS => Ident::new("I64ShrS", Span::call_site()),
            BinOp::I64ShrU => Ident::new("I64ShrU", Span::call_site()),
            BinOp::I64Rotl => Ident::new("I64Rotl", Span::call_site()),
            BinOp::I64Rotr => Ident::new("I64Rotr", Span::call_site()),
        };
        tokens.append(token);
    }
}

#[allow(non_snake_case)]
#[derive(Clone, Copy, Debug)]
enum RelOp {
    I32Eq,
    I32Ne,
    I32LtS,
    I32LtU,
    I32GtS,
    I32GtU,
    I32LeS,
    I32LeU,
    I32GeS,
    I32GeU,
    I64Eq,
    I64Ne,
    I64LtS,
    I64LtU,
    I64GtS,
    I64GtU,
    I64LeS,
    I64LeU,
    I64GeS,
    I64GeU,
}

impl Parse for RelOp {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        let is_i32 = if lookahead.peek(kw::i32) {
            input.parse::<kw::i32>()?;
            true
        } else {
            input.parse::<kw::i64>()?;
            false
        };

        input.parse::<Dot>()?;
        let lookahead = input.lookahead1();
        let relop = if lookahead.peek(kw::eq) {
            input.parse::<kw::eq>()?;
            if is_i32 {
                Self::I32Eq
            } else {
                Self::I64Eq
            }
        } else if lookahead.peek(kw::ne) {
            input.parse::<kw::ne>()?;
            if is_i32 {
                Self::I32Ne
            } else {
                Self::I64Ne
            }
        } else if lookahead.peek(kw::lt_s) {
            input.parse::<kw::lt_s>()?;
            if is_i32 {
                Self::I32LtS
            } else {
                Self::I64LtS
            }
        } else if lookahead.peek(kw::lt_u) {
            input.parse::<kw::lt_u>()?;
            if is_i32 {
                Self::I32LtU
            } else {
                Self::I64LtU
            }
        } else if lookahead.peek(kw::gt_s) {
            input.parse::<kw::gt_s>()?;
            if is_i32 {
                Self::I32GtS
            } else {
                Self::I64GtS
            }
        } else if lookahead.peek(kw::gt_u) {
            input.parse::<kw::gt_u>()?;
            if is_i32 {
                Self::I32GtU
            } else {
                Self::I64GtU
            }
        } else if lookahead.peek(kw::le_s) {
            input.parse::<kw::le_s>()?;
            if is_i32 {
                Self::I32LeS
            } else {
                Self::I64LeS
            }
        } else if lookahead.peek(kw::le_u) {
            input.parse::<kw::le_u>()?;
            if is_i32 {
                Self::I32LeU
            } else {
                Self::I64LeU
            }
        } else if lookahead.peek(kw::ge_s) {
            input.parse::<kw::ge_s>()?;
            if is_i32 {
                Self::I32GeS
            } else {
                Self::I64GeS
            }
        } else if lookahead.peek(kw::ge_u) {
            input.parse::<kw::ge_u>()?;
            if is_i32 {
                Self::I32GeU
            } else {
                Self::I64GeU
            }
        } else {
            return Err(lookahead.error());
        };

        Ok(relop)
    }
}

impl ToTokens for RelOp {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        tokens.append(Ident::new("RelOp", Span::call_site()));
        tokens.append(Punct::new(':', Spacing::Joint));
        tokens.append(Punct::new(':', Spacing::Alone));
        let token = match self {
            RelOp::I32Eq => Ident::new("I32Eq", Span::call_site()),
            RelOp::I32Ne => Ident::new("I32Ne", Span::call_site()),
            RelOp::I32LtS => Ident::new("I32LtS", Span::call_site()),
            RelOp::I32LtU => Ident::new("I32LtU", Span::call_site()),
            RelOp::I32GtS => Ident::new("I32GtS", Span::call_site()),
            RelOp::I32GtU => Ident::new("I32GtU", Span::call_site()),
            RelOp::I32LeS => Ident::new("I32LeS", Span::call_site()),
            RelOp::I32LeU => Ident::new("I32LeU", Span::call_site()),
            RelOp::I32GeS => Ident::new("I32GeS", Span::call_site()),
            RelOp::I32GeU => Ident::new("I32GeU", Span::call_site()),
            RelOp::I64Eq => Ident::new("I64Eq", Span::call_site()),
            RelOp::I64Ne => Ident::new("I64Ne", Span::call_site()),
            RelOp::I64LtS => Ident::new("I64LtS", Span::call_site()),
            RelOp::I64LtU => Ident::new("I64LtU", Span::call_site()),
            RelOp::I64GtS => Ident::new("I64GtS", Span::call_site()),
            RelOp::I64GtU => Ident::new("I64GtU", Span::call_site()),
            RelOp::I64LeS => Ident::new("I64LeS", Span::call_site()),
            RelOp::I64LeU => Ident::new("I64LeU", Span::call_site()),
            RelOp::I64GeS => Ident::new("I64GeS", Span::call_site()),
            RelOp::I64GeU => Ident::new("I64GeU", Span::call_site()),
        };
        tokens.append(token);
    }
}

#[allow(non_snake_case)]
#[derive(Clone, Copy, Debug)]
enum UnOp {
    I32Clz,
    I32Ctz,
    I32Popcnt,
    I64Clz,
    I64Ctz,
    I64Popcnt,
}

impl Parse for UnOp {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        let is_i32 = if lookahead.peek(kw::i32) {
            input.parse::<kw::i32>()?;
            true
        } else {
            input.parse::<kw::i64>()?;
            false
        };

        input.parse::<Dot>()?;
        let lookahead = input.lookahead1();
        let unop = if lookahead.peek(kw::clz) {
            input.parse::<kw::clz>()?;
            if is_i32 {
                Self::I32Clz
            } else {
                Self::I64Clz
            }
        } else if lookahead.peek(kw::ctz) {
            input.parse::<kw::ctz>()?;
            if is_i32 {
                Self::I32Ctz
            } else {
                Self::I64Ctz
            }
        } else if lookahead.peek(kw::popcnt) {
            input.parse::<kw::popcnt>()?;
            if is_i32 {
                Self::I32Popcnt
            } else {
                Self::I64Popcnt
            }
        } else {
            return Err(lookahead.error());
        };

        Ok(unop)
    }
}

impl ToTokens for UnOp {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        tokens.append(Ident::new("UnOp", Span::call_site()));
        tokens.append(Punct::new(':', Spacing::Joint));
        tokens.append(Punct::new(':', Spacing::Alone));
        let token = match self {
            UnOp::I32Clz => Ident::new("I32Clz", Span::call_site()),
            UnOp::I32Ctz => Ident::new("I32Ctz", Span::call_site()),
            UnOp::I32Popcnt => Ident::new("I32Popcnt", Span::call_site()),
            UnOp::I64Clz => Ident::new("I64Clz", Span::call_site()),
            UnOp::I64Ctz => Ident::new("I64Ctz", Span::call_site()),
            UnOp::I64Popcnt => Ident::new("I64Popcnt", Span::call_site()),
        };
        tokens.append(token);
    }
}

#[allow(non_snake_case)]
#[derive(Clone, Copy, Debug)]
enum TestOp {
    I32Eqz,
    I64Eqz,
}

impl Parse for TestOp {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        let is_i32 = if lookahead.peek(kw::i32) {
            input.parse::<kw::i32>()?;
            true
        } else {
            input.parse::<kw::i64>()?;
            false
        };

        input.parse::<Dot>()?;
        let lookahead = input.lookahead1();
        let testop = if lookahead.peek(kw::eqz) {
            input.parse::<kw::eqz>()?;
            if is_i32 {
                Self::I32Eqz
            } else {
                Self::I64Eqz
            }
        } else {
            return Err(lookahead.error());
        };

        Ok(testop)
    }
}

impl ToTokens for TestOp {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        tokens.append(Ident::new("TestOp", Span::call_site()));
        tokens.append(Punct::new(':', Spacing::Joint));
        tokens.append(Punct::new(':', Spacing::Alone));
        let token = match self {
            Self::I32Eqz => Ident::new("I32Eqz", Span::call_site()),
            Self::I64Eqz => Ident::new("I64Eqz", Span::call_site()),
        };
        tokens.append(token);
    }
}

#[derive(Debug)]
enum Constant {
    I32Const(Expr),
    I64Const(Expr),
}

impl Parse for Constant {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        let is_i32 = if lookahead.peek(kw::i32) {
            input.parse::<kw::i32>()?;
            true
        } else {
            input.parse::<kw::i64>()?;
            false
        };

        let expr = if input.fork().parse::<syn::Lit>().is_ok() {
            Expr::Lit(input.parse()?)
        } else if input.fork().parse::<ExprBinary>().is_ok() {
            Expr::Binary(input.parse::<ExprBinary>()?)
        } else if input.fork().parse::<ExprUnary>().is_ok() {
            Expr::Unary(input.parse::<ExprUnary>()?)
        } else if input.fork().parse::<syn::Path>().is_ok() {
            // identifier
            Expr::Path(input.parse()?)
        } else {
            return Err(input.error("expected const"));
        };

        let constant = if is_i32 {
            Self::I32Const(expr)
        } else {
            Self::I64Const(expr)
        };

        Ok(constant)
    }
}

impl ToTokens for Constant {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        tokens.append(Ident::new("Constant", Span::call_site()));
        tokens.append(Punct::new(':', Spacing::Joint));
        tokens.append(Punct::new(':', Spacing::Alone));
        let constant = match self {
            Self::I32Const(constant) => {
                tokens.append(Ident::new("I32Const", Span::call_site()));
                constant
            }
            Self::I64Const(constant) => {
                tokens.append(Ident::new("I64Const", Span::call_site()));
                constant
            }
        };
        parenthesize!(constant).to_tokens(tokens);
    }
}

#[derive(Debug)]
enum IndexTerm {
    IBinOp(BinOp, Box<IndexTerm>, Box<IndexTerm>),
    IRelOp(RelOp, Box<IndexTerm>, Box<IndexTerm>),
    ITestOp(TestOp, Box<IndexTerm>),
    IUnOp(UnOp, Box<IndexTerm>),
    Alpha(Expr),
    IConstant(Constant),
}

impl Parse for IndexTerm {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(Paren) {
            let content: ParseBuffer;
            parenthesized!(content in input);
            if content.fork().parse::<BinOp>().is_ok() {
                let bop = content.parse::<BinOp>()?;
                let x = content.parse::<IndexTerm>()?;
                let y = content.parse::<IndexTerm>()?;
                return Ok(Self::IBinOp(bop, Box::new(x), Box::new(y)));
            } else if content.fork().parse::<RelOp>().is_ok() {
                let rop = content.parse::<RelOp>()?;
                let x = content.parse::<IndexTerm>()?;
                let y = content.parse::<IndexTerm>()?;
                return Ok(Self::IRelOp(rop, Box::new(x), Box::new(y)));
            } else if content.fork().parse::<UnOp>().is_ok() {
                let uop = content.parse::<UnOp>()?;
                let x = content.parse::<IndexTerm>()?;
                return Ok(Self::IUnOp(uop, Box::new(x)));
            } else if content.fork().parse::<TestOp>().is_ok() {
                let top = content.parse::<TestOp>()?;
                let x = content.parse::<IndexTerm>()?;
                return Ok(Self::ITestOp(top, Box::new(x)));
            } else if content.fork().parse::<Constant>().is_ok() {
                return Ok(Self::IConstant(content.parse::<Constant>()?));
            } else {
                return Err(content.error("expected index term"));
            }
        }

        let expr = if lookahead.peek(syn::Lit) {
            Expr::Lit(input.parse()?)
        } else if input.fork().parse::<ExprBinary>().is_ok() {
            Expr::Binary(input.parse::<ExprBinary>()?)
        } else if input.fork().parse::<ExprUnary>().is_ok() {
            Expr::Unary(input.parse::<ExprUnary>()?)
        } else if input.fork().parse::<syn::Path>().is_ok() {
            // identifier
            Expr::Path(input.parse()?)
        } else {
            return Err(input.error("expected index term - not a good alpha"));
        };
        return Ok(Self::Alpha(expr));
    }
}

impl ToTokens for IndexTerm {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        tokens.append(Ident::new("IndexTerm", Span::call_site()));
        tokens.append(Punct::new(':', Spacing::Joint));
        tokens.append(Punct::new(':', Spacing::Alone));
        let group = match self {
            IndexTerm::IBinOp(bop, x, y) => {
                tokens.append(Ident::new("IBinOp", Span::call_site()));
                parenthesize!(bop, Boxed: x, y)
            }
            IndexTerm::IRelOp(rop, x, y) => {
                tokens.append(Ident::new("IRelOp", Span::call_site()));
                parenthesize!(rop, Boxed: x, y)
            }
            IndexTerm::ITestOp(top, x) => {
                tokens.append(Ident::new("ITestOp", Span::call_site()));
                parenthesize!(top, Boxed: x)
            }
            IndexTerm::IUnOp(uop, x) => {
                tokens.append(Ident::new("IUnOp", Span::call_site()));
                parenthesize!(uop, Boxed: x)
            }
            IndexTerm::Alpha(expr) => {
                tokens.append(Ident::new("Alpha", Span::call_site()));
                parenthesize!(expr)
            }
            IndexTerm::IConstant(c) => {
                tokens.append(Ident::new("IConstant", Span::call_site()));
                parenthesize!(c)
            }
        };
        group.to_tokens(tokens);
    }
}

#[derive(Debug)]
enum Constraint {
    Eq(IndexTerm, IndexTerm),
    And(Box<Constraint>, Box<Constraint>),
    Or(Box<Constraint>, Box<Constraint>),
    If(Box<Constraint>, Box<Constraint>, Box<Constraint>),
    Not(Box<Constraint>),
}

impl Parse for Constraint {
    fn parse(input: ParseStream) -> Result<Self> {
        fn help(content: ParseStream) -> Result<Constraint> {
            let lookahead = content.lookahead1();
            if lookahead.peek(Token![=]) {
                content.parse::<Token![=]>()?;
                let x = content.parse::<IndexTerm>()?;
                let y = content.parse::<IndexTerm>()?;
                return Ok(Constraint::Eq(x, y));
            } else if lookahead.peek(kw::and) {
                content.parse::<kw::and>()?;
                let x = content.parse::<Constraint>()?;
                let y = content.parse::<Constraint>()?;
                return Ok(Constraint::And(Box::new(x), Box::new(y)));
            } else if lookahead.peek(kw::or) {
                content.parse::<kw::or>()?;
                let x = content.parse::<Constraint>()?;
                let y = content.parse::<Constraint>()?;
                return Ok(Constraint::Or(Box::new(x), Box::new(y)));
            } else if lookahead.peek(kw::r#if) {
                content.parse::<kw::r#if>()?;
                let x = content.parse::<Constraint>()?;
                let y = content.parse::<Constraint>()?;
                let z = content.parse::<Constraint>()?;
                return Ok(Constraint::If(Box::new(x), Box::new(y), Box::new(z)));
            } else if lookahead.peek(kw::not) {
                content.parse::<kw::not>()?;
                let x = content.parse::<Constraint>()?;
                return Ok(Constraint::Not(Box::new(x)));
            }

            Err(lookahead.error())
        }

        let lookahead = input.lookahead1();
        if lookahead.peek(Paren) {
            let content: ParseBuffer;
            parenthesized!(content in input);
            return help(&content);
        } else {
            return help(&input);
        }
    }
}

impl ToTokens for Constraint {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        tokens.append(Ident::new("Constraint", Span::call_site()));
        tokens.append(Punct::new(':', Spacing::Joint));
        tokens.append(Punct::new(':', Spacing::Alone));
        let group = match self {
            Constraint::Eq(x, y) => {
                tokens.append(Ident::new("Eq", Span::call_site()));
                parenthesize!(x, y)
            }
            Constraint::And(x, y) => {
                tokens.append(Ident::new("And", Span::call_site()));
                parenthesize!(Boxed: x, y)
            }
            Constraint::Or(x, y) => {
                tokens.append(Ident::new("Or", Span::call_site()));
                parenthesize!(Boxed: x, y)
            }
            Constraint::If(x, y, z) => {
                tokens.append(Ident::new("If", Span::call_site()));
                parenthesize!(Boxed: x, y, z)
            }
            Constraint::Not(x) => {
                tokens.append(Ident::new("Not", Span::call_site()));
                parenthesize!(Boxed: x)
            }
        };

        group.to_tokens(tokens);
    }
}

#[proc_macro]
pub fn constraint(input: TokenStream) -> TokenStream {
    let c = parse_macro_input!(input as Constraint);
    quote!( #c ).into()
}

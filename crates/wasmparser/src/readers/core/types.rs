/* Copyright 2018 Mozilla Foundation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use crate::limits::{MAX_WASM_FUNCTION_PARAMS, MAX_WASM_FUNCTION_RETURNS};
use crate::{BinaryReader, FromReader, Result, SectionLimited};
use std::fmt::Debug;

/// Represents the types of values in a WebAssembly module.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ValType {
    /// The value type is i32.
    I32,
    /// The value type is i64.
    I64,
    /// The value type is f32.
    F32,
    /// The value type is f64.
    F64,
    /// The value type is v128.
    V128,
    /// The value type is a function reference.
    FuncRef,
    /// The value type is an extern reference.
    ExternRef,
}

impl ValType {
    /// Returns whether this value type is a "reference type".
    ///
    /// Only reference types are allowed in tables, for example, and with some
    /// instructions. Current reference types include `funcref` and `externref`.
    pub fn is_reference_type(&self) -> bool {
        matches!(self, ValType::FuncRef | ValType::ExternRef)
    }

    pub(crate) fn from_byte(byte: u8) -> Option<ValType> {
        match byte {
            0x7F => Some(ValType::I32),
            0x7E => Some(ValType::I64),
            0x7D => Some(ValType::F32),
            0x7C => Some(ValType::F64),
            0x7B => Some(ValType::V128),
            0x70 => Some(ValType::FuncRef),
            0x6F => Some(ValType::ExternRef),
            _ => None,
        }
    }
}

impl<'a> FromReader<'a> for ValType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        match ValType::from_byte(reader.peek()?) {
            Some(ty) => {
                reader.position += 1;
                Ok(ty)
            }
            None => bail!(reader.original_position(), "invalid value type"),
        }
    }
}

/// Represents a type in a WebAssembly module.
#[derive(Debug, Clone)]
pub enum Type {
    /// The type is for a function.
    Func(IndexedFuncType),
}

#[allow(missing_docs)]
#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum BinOp {
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

#[allow(missing_docs)]
#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum RelOp {
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

#[allow(missing_docs)]
#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum UnOp {
    I32Clz,
    I32Ctz,
    I32Popcnt,
    I64Clz,
    I64Ctz,
    I64Popcnt,
}

#[allow(missing_docs)]
#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum TestOp {
    I32Eqz,
    I64Eqz,
}

#[allow(missing_docs)]
#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum Constant {
    I32Const(i32),
    I64Const(i64),
}

#[allow(missing_docs)]
#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum IndexTerm {
    IBinOp(BinOp, Box<IndexTerm>, Box<IndexTerm>),
    IRelOp(RelOp, Box<IndexTerm>, Box<IndexTerm>),
    ITestOp(TestOp, Box<IndexTerm>),
    IUnOp(UnOp, Box<IndexTerm>),
    Alpha(u32),
    Pre(u32),
    Post(u32),
    Local(u32),
    IConstant(Constant),
}

#[allow(missing_docs)]
#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub enum Constraint {
    Eq(IndexTerm, IndexTerm),
    And(Box<Constraint>, Box<Constraint>),
    Or(Box<Constraint>, Box<Constraint>),
    If(Box<Constraint>, Box<Constraint>, Box<Constraint>),
    Not(Box<Constraint>),
}

/// Represents a type of a function in a WebAssembly module.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct IndexedFuncType {
    /// The combined parameters and result types.
    params_results: Box<[ValType]>,
    /// The number of parameter types.
    len_params: usize,
    // Combined pre and post constraints
    pres_posts: Box<[Constraint]>,
    /// The number of pre constraints
    len_pres: usize,
}

impl Debug for IndexedFuncType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FuncType")
            .field("params", &self.params())
            .field("returns", &self.results())
            .field("pres", &self.pres())
            .field("posts", &self.posts())
            .finish()
    }
}

impl IndexedFuncType {
    /// Creates a new [`FuncType`] from the given `params` and `results`.
    pub fn new<P, R, S, T>(params: P, results: R, pres: S, posts: T) -> Self
    where
        P: IntoIterator<Item = ValType>,
        R: IntoIterator<Item = ValType>,
        S: IntoIterator<Item = Constraint>,
        T: IntoIterator<Item = Constraint>,
    {
        let mut buffer = params.into_iter().collect::<Vec<_>>();
        let len_params = buffer.len();
        buffer.extend(results);
        let mut buffer2 = pres.into_iter().collect::<Vec<_>>();
        let len_pres = buffer2.len();
        buffer2.extend(posts);
        Self {
            params_results: buffer.into(),
            len_params,
            pres_posts: buffer2.into(),
            len_pres,
        }
    }

    /// Creates a new [`FuncType`] fom its raw parts.
    ///
    /// # Panics
    ///
    /// If `len_params` is greater than the length of `params_results` combined.
    #[allow(unused)]
    pub(crate) fn from_raw_parts(
        params_results: Box<[ValType]>,
        len_params: usize,
        pres_posts: Box<[Constraint]>,
        len_pres: usize,
    ) -> Self {
        assert!(len_params <= params_results.len());
        assert!(len_pres <= pres_posts.len());
        Self {
            params_results,
            len_params,
            pres_posts,
            len_pres,
        }
    }

    /// Returns a shared slice to the parameter types of the [`FuncType`].
    #[inline]
    pub fn params(&self) -> &[ValType] {
        &self.params_results[..self.len_params]
    }

    /// Returns a shared slice to the result types of the [`FuncType`].
    #[inline]
    pub fn results(&self) -> &[ValType] {
        &self.params_results[self.len_params..]
    }

    /// Returns a shared slice to the pre constraints
    #[inline]
    pub fn pres(&self) -> &[Constraint] {
        &self.pres_posts[..self.len_pres]
    }

    /// Returns a shared slice to the post constraints
    #[inline]
    pub fn posts(&self) -> &[Constraint] {
        &self.pres_posts[self.len_pres..]
    }
}

impl From<IndexedFuncType> for FuncType {
    fn from(value: IndexedFuncType) -> Self {
        let mut params = Vec::new();
        for param in value.params().iter() {
            params.push(*param);
        }
        let mut results = Vec::new();
        for result in value.results().iter() {
            results.push(*result);
        }
        FuncType::new(params, results)
    }
}
/*
impl From<&IndexedFuncType> for &FuncType {
    fn from(value: &IndexedFuncType) -> Self {
        let mut params = Vec::new();
        for param in value.params().iter() {
            params.push(*param);
        }
        let mut results = Vec::new();
        for result in value.results().iter() {
            results.push(*result);
        }
        &FuncType::new(params, results)
    }
}
*/

/// Represents a type of a function in a WebAssembly module.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct FuncType {
    /// The combined parameters and result types.
    params_results: Box<[ValType]>,
    /// The number of parameter types.
    len_params: usize,
}

impl Debug for FuncType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FuncType")
            .field("params", &self.params())
            .field("returns", &self.results())
            .finish()
    }
}

impl FuncType {
    /// Creates a new [`FuncType`] from the given `params` and `results`.
    pub fn new<P, R>(params: P, results: R) -> Self
    where
        P: IntoIterator<Item = ValType>,
        R: IntoIterator<Item = ValType>,
    {
        let mut buffer = params.into_iter().collect::<Vec<_>>();
        let len_params = buffer.len();
        buffer.extend(results);
        Self {
            params_results: buffer.into(),
            len_params,
        }
    }

    /// Creates a new [`FuncType`] fom its raw parts.
    ///
    /// # Panics
    ///
    /// If `len_params` is greater than the length of `params_results` combined.
    pub(crate) fn _from_raw_parts(params_results: Box<[ValType]>, len_params: usize) -> Self {
        assert!(len_params <= params_results.len());
        Self {
            params_results,
            len_params,
        }
    }

    /// Returns a shared slice to the parameter types of the [`FuncType`].
    #[inline]
    pub fn params(&self) -> &[ValType] {
        &self.params_results[..self.len_params]
    }

    /// Returns a shared slice to the result types of the [`FuncType`].
    #[inline]
    pub fn results(&self) -> &[ValType] {
        &self.params_results[self.len_params..]
    }
}

/// Represents a table's type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TableType {
    /// The table's element type.
    pub element_type: ValType,
    /// Initial size of this table, in elements.
    pub initial: u32,
    /// Optional maximum size of the table, in elements.
    pub maximum: Option<u32>,
}

/// Represents a memory's type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct MemoryType {
    /// Whether or not this is a 64-bit memory, using i64 as an index. If this
    /// is false it's a 32-bit memory using i32 as an index.
    ///
    /// This is part of the memory64 proposal in WebAssembly.
    pub memory64: bool,

    /// Whether or not this is a "shared" memory, indicating that it should be
    /// send-able across threads and the `maximum` field is always present for
    /// valid types.
    ///
    /// This is part of the threads proposal in WebAssembly.
    pub shared: bool,

    /// Initial size of this memory, in wasm pages.
    ///
    /// For 32-bit memories (when `memory64` is `false`) this is guaranteed to
    /// be at most `u32::MAX` for valid types.
    pub initial: u64,

    /// Optional maximum size of this memory, in wasm pages.
    ///
    /// For 32-bit memories (when `memory64` is `false`) this is guaranteed to
    /// be at most `u32::MAX` for valid types. This field is always present for
    /// valid wasm memories when `shared` is `true`.
    pub maximum: Option<u64>,
}

impl MemoryType {
    /// Gets the index type for the memory.
    pub fn index_type(&self) -> ValType {
        if self.memory64 {
            ValType::I64
        } else {
            ValType::I32
        }
    }
}

/// Represents a global's type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct GlobalType {
    /// The global's type.
    pub content_type: ValType,
    /// Whether or not the global is mutable.
    pub mutable: bool,
}

/// Represents a tag kind.
#[derive(Clone, Copy, Debug)]
pub enum TagKind {
    /// The tag is an exception type.
    Exception,
}

/// A tag's type.
#[derive(Clone, Copy, Debug)]
pub struct TagType {
    /// The kind of tag
    pub kind: TagKind,
    /// The function type this tag uses.
    pub func_type_idx: u32,
}

/// A reader for the type section of a WebAssembly module.
pub type TypeSectionReader<'a> = SectionLimited<'a, Type>;

impl<'a> FromReader<'a> for Type {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        Ok(match reader.read_u8()? {
            0x60 => Type::Func(reader.read()?),
            x => return reader.invalid_leading_byte(x, "type"),
        })
    }
}
/*
impl<'a> FromReader<'a> for FuncType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        let mut params_results = reader
            .read_iter(MAX_WASM_FUNCTION_PARAMS, "function params")?
            .collect::<Result<Vec<_>>>()?;
        let len_params = params_results.len();
        let results = reader.read_iter(MAX_WASM_FUNCTION_RETURNS, "function returns")?;
        params_results.reserve(results.size_hint().0);
        for result in results {
            params_results.push(result?);
        }
        Ok(FuncType::from_raw_parts(params_results.into(), len_params))
    }
}*/

impl<'a> FromReader<'a> for IndexedFuncType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        let mut params_results = reader
            .read_iter(MAX_WASM_FUNCTION_PARAMS, "function params")?
            .collect::<Result<Vec<_>>>()?;
        let len_params = params_results.len();
        let results = reader.read_iter(MAX_WASM_FUNCTION_RETURNS, "function returns")?;
        params_results.reserve(results.size_hint().0);
        for result in results {
            params_results.push(result?);
        }

        if reader.peek()? != 0xff {
            return Ok(IndexedFuncType::from_raw_parts(
                params_results.into(),
                len_params,
                vec![].into(),
                0,
            ));
        }

        reader.read_u8()?;

        let mut pres_posts = reader
            .read_iter(MAX_WASM_FUNCTION_PARAMS, "function pre-conditions")?
            .collect::<Result<Vec<_>>>()?;
        let len_pres = pres_posts.len();
        let posts = reader.read_iter(MAX_WASM_FUNCTION_RETURNS, "function post-conditions")?;
        pres_posts.reserve(posts.size_hint().0);
        for post in posts {
            pres_posts.push(post?);
        }

        Ok(IndexedFuncType::from_raw_parts(
            params_results.into(),
            len_params,
            pres_posts.into(),
            len_pres,
        ))
    }
}

impl<'a> FromReader<'a> for Constraint {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        let byte = reader.peek()?;
        reader.position += 1;
        let constraint = match byte {
            0x01 => {
                let x = reader.read()?;
                let y = reader.read()?;
                Constraint::Eq(x, y)
            }
            0x02 => {
                let x = reader.read()?;
                let y = reader.read()?;
                Constraint::And(Box::new(x), Box::new(y))
            }
            0x03 => {
                let x = reader.read()?;
                let y = reader.read()?;
                Constraint::Or(Box::new(x), Box::new(y))
            }
            0x04 => {
                let x = reader.read()?;
                let y = reader.read()?;
                let z = reader.read()?;
                Constraint::If(Box::new(x), Box::new(y), Box::new(z))
            }
            0x05 => {
                let x = reader.read()?;
                Constraint::Not(Box::new(x))
            }
            x => {
                return reader.invalid_leading_byte(x, "constraint");
            }
        };

        Ok(constraint)
    }
}

impl<'a> FromReader<'a> for IndexTerm {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        let byte = reader.peek()?;
        reader.position += 1;
        let index_term = match byte {
            0x41 => {
                IndexTerm::IConstant(Constant::I32Const(reader.read_var_i32()?))
            }
            0x42 => {
                IndexTerm::IConstant(Constant::I64Const(reader.read_var_i64()?))
            }
            x @ 0x6a..=0x78 | x @ 0x7c..=0x8a => {
                let binop = match x {
                    0x6a => BinOp::I32Add,
                    0x6b => BinOp::I32Sub,
                    0x6c => BinOp::I32Mul,
                    0x6d => BinOp::I32DivS,
                    0x6e => BinOp::I32DivU,
                    0x6f => BinOp::I32RemS,
                    0x70 => BinOp::I32RemU,
                    0x71 => BinOp::I32And,
                    0x72 => BinOp::I32Or,
                    0x73 => BinOp::I32Xor,
                    0x74 => BinOp::I32Shl,
                    0x75 => BinOp::I32ShrS,
                    0x76 => BinOp::I32ShrU,
                    0x77 => BinOp::I32Rotl,
                    0x78 => BinOp::I32Rotr,
                    0x7c => BinOp::I64Add,
                    0x7d => BinOp::I64Sub,
                    0x7e => BinOp::I64Mul,
                    0x7f => BinOp::I64DivS,
                    0x80 => BinOp::I64DivU,
                    0x81 => BinOp::I64RemS,
                    0x82 => BinOp::I64RemU,
                    0x83 => BinOp::I64And,
                    0x84 => BinOp::I64Or,
                    0x85 => BinOp::I64Xor,
                    0x86 => BinOp::I64Shl,
                    0x87 => BinOp::I64ShrS,
                    0x88 => BinOp::I64ShrU,
                    0x89 => BinOp::I64Rotl,
                    0x8a => BinOp::I64Rotr,
                    _ => panic!(),
                };
                let x = reader.read()?;
                let y = reader.read()?;
                IndexTerm::IBinOp(binop, Box::new(x), Box::new(y))
            }
            x @ 0x46..=0x4f | x @ 0x51..=0x5a => {
                let relop = match x {
                    0x46 => RelOp::I32Eq,
                    0x47 => RelOp::I32Ne,
                    0x48 => RelOp::I32LtS,
                    0x49 => RelOp::I32LtU,
                    0x4a => RelOp::I32GtS,
                    0x4b => RelOp::I32GtU,
                    0x4c => RelOp::I32LeS,
                    0x4d => RelOp::I32LeU,
                    0x4e => RelOp::I32GeS,
                    0x4f => RelOp::I32GeU,
                    0x51 => RelOp::I64Eq,
                    0x52 => RelOp::I64Ne,
                    0x53 => RelOp::I64LtS,
                    0x54 => RelOp::I64LtU,
                    0x55 => RelOp::I64GtS,
                    0x56 => RelOp::I64GtU,
                    0x57 => RelOp::I64LeS,
                    0x58 => RelOp::I64LeU,
                    0x59 => RelOp::I64GeS,
                    0x5a => RelOp::I64GeU,
                    _ => panic!(),
                };
                let x = reader.read()?;
                let y = reader.read()?;
                IndexTerm::IRelOp(relop, Box::new(x), Box::new(y))
            }
            x @ 0x45 | x @ 0x50 => {
                let testop = if x == 0x45 {
                    TestOp::I32Eqz
                } else {
                    TestOp::I64Eqz
                };
                let x = reader.read()?;
                IndexTerm::ITestOp(testop, Box::new(x))
            }
            x @ 0x67..=0x69 | x @ 0x79..=0x7b => {
                let unop = match x {
                    0x67 => UnOp::I32Clz,
                    0x68 => UnOp::I32Ctz,
                    0x69 => UnOp::I32Popcnt,
                    0x79 => UnOp::I64Clz,
                    0x7a => UnOp::I64Ctz,
                    0x7b => UnOp::I64Popcnt,
                    _ => panic!(),
                };
                let x = reader.read()?;
                IndexTerm::IUnOp(unop, Box::new(x))
            }
            x @ 0x20..=0x22 => {
                let index = reader.read()?;
                match x {
                    0x20 => IndexTerm::Local(index),
                    0x21 => IndexTerm::Pre(index),
                    0x22 => IndexTerm::Post(index),
                    _ => panic!(),
                }
            }
            x => {
                return reader.invalid_leading_byte(x, "index_term");
            }
        };

        Ok(index_term)
    }
}

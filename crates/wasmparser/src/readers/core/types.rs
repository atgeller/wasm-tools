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

use crate::{BinaryReader, Result, SectionIteratorLimited, SectionReader, SectionWithLimitedItems};
use std::fmt::Debug;
use std::ops::Range;

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
}

/// Represents a type in a WebAssembly module.
#[derive(Debug, Clone)]
pub enum Type {
    /// The type is for a function.
    Func(FuncType),
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
    // Alpha will get resolved into one of the following two, they are not parseable ATM
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
    pub(crate) fn from_raw_parts(params_results: Box<[ValType]>, len_params: usize) -> Self {
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
#[derive(Clone)]
pub struct TypeSectionReader<'a> {
    reader: BinaryReader<'a>,
    count: u32,
}

impl<'a> TypeSectionReader<'a> {
    /// Constructs a new `TypeSectionReader` for the given data and offset.
    pub fn new(data: &'a [u8], offset: usize) -> Result<Self> {
        let mut reader = BinaryReader::new_with_offset(data, offset);
        let count = reader.read_var_u32()?;
        Ok(Self { reader, count })
    }

    /// Gets the original position of the reader.
    pub fn original_position(&self) -> usize {
        self.reader.original_position()
    }

    /// Gets a count of items in the section.
    pub fn get_count(&self) -> u32 {
        self.count
    }

    /// Reads content of the type section.
    ///
    /// # Examples
    /// ```
    /// use wasmparser::TypeSectionReader;
    /// let data: &[u8] = &[0x01, 0x60, 0x00, 0x00];
    /// let mut reader = TypeSectionReader::new(data, 0).unwrap();
    /// for _ in 0..reader.get_count() {
    ///     let ty = reader.read().expect("type");
    ///     println!("Type {:?}", ty);
    /// }
    /// ```
    pub fn read(&mut self) -> Result<Type> {
        self.reader.read_type()
    }
}

impl<'a> SectionReader for TypeSectionReader<'a> {
    type Item = Type;

    fn read(&mut self) -> Result<Self::Item> {
        Self::read(self)
    }

    fn eof(&self) -> bool {
        self.reader.eof()
    }

    fn original_position(&self) -> usize {
        Self::original_position(self)
    }

    fn range(&self) -> Range<usize> {
        self.reader.range()
    }
}

impl<'a> SectionWithLimitedItems for TypeSectionReader<'a> {
    fn get_count(&self) -> u32 {
        Self::get_count(self)
    }
}

impl<'a> IntoIterator for TypeSectionReader<'a> {
    type Item = Result<Type>;
    type IntoIter = SectionIteratorLimited<Self>;

    /// Implements iterator over the type section.
    ///
    /// # Examples
    /// ```
    /// use wasmparser::TypeSectionReader;
    /// # let data: &[u8] = &[0x01, 0x60, 0x00, 0x00];
    /// let mut reader = TypeSectionReader::new(data, 0).unwrap();
    /// for ty in reader {
    ///     println!("Type {:?}", ty.expect("type"));
    /// }
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        SectionIteratorLimited::new(self)
    }
}

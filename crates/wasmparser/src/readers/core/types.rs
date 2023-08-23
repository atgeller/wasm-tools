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
use std::fmt::{self, Debug, Write};

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
    /// The value type is a reference.
    Ref(RefType),
}

/// Represents storage types introduced in the GC spec for array and struct fields.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum StorageType {
    /// The storage type is i8.
    I8,
    /// The storage type is i16.
    I16,
    /// The storage type is a value type.
    Val(ValType),
}

// The size of `ValType` is performance sensitive.
const _: () = {
    assert!(std::mem::size_of::<ValType>() == 4);
};

impl From<RefType> for ValType {
    fn from(ty: RefType) -> ValType {
        ValType::Ref(ty)
    }
}

impl ValType {
    /// Alias for the wasm `funcref` type.
    pub const FUNCREF: ValType = ValType::Ref(RefType::FUNCREF);

    /// Alias for the wasm `externref` type.
    pub const EXTERNREF: ValType = ValType::Ref(RefType::EXTERNREF);

    /// Returns whether this value type is a "reference type".
    ///
    /// Only reference types are allowed in tables, for example, and with some
    /// instructions. Current reference types include `funcref` and `externref`.
    pub fn is_reference_type(&self) -> bool {
        matches!(self, ValType::Ref(_))
    }

    /// Whether the type is defaultable, i.e. it is not a non-nullable reference
    /// type.
    pub fn is_defaultable(&self) -> bool {
        match *self {
            Self::I32 | Self::I64 | Self::F32 | Self::F64 | Self::V128 => true,
            Self::Ref(rt) => rt.is_nullable(),
        }
    }

    pub(crate) fn is_valtype_byte(byte: u8) -> bool {
        match byte {
            0x7F | 0x7E | 0x7D | 0x7C | 0x7B | 0x70 | 0x6F | 0x6B | 0x6C | 0x6E | 0x65 | 0x69
            | 0x68 | 0x6D | 0x67 | 0x66 | 0x6A => true,
            _ => false,
        }
    }
}

impl<'a> FromReader<'a> for StorageType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        match reader.peek()? {
            0x7A => {
                reader.position += 1;
                Ok(StorageType::I8)
            }
            0x79 => {
                reader.position += 1;
                Ok(StorageType::I16)
            }
            _ => Ok(StorageType::Val(reader.read()?)),
        }
    }
}

impl<'a> FromReader<'a> for ValType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        match reader.peek()? {
            0x7F => {
                reader.position += 1;
                Ok(ValType::I32)
            }
            0x7E => {
                reader.position += 1;
                Ok(ValType::I64)
            }
            0x7D => {
                reader.position += 1;
                Ok(ValType::F32)
            }
            0x7C => {
                reader.position += 1;
                Ok(ValType::F64)
            }
            0x7B => {
                reader.position += 1;
                Ok(ValType::V128)
            }
            0x70 | 0x6F | 0x6B | 0x6C | 0x6E | 0x65 | 0x69 | 0x68 | 0x6D | 0x67 | 0x66 | 0x6A => {
                Ok(ValType::Ref(reader.read()?))
            }
            _ => bail!(reader.original_position(), "invalid value type"),
        }
    }
}

impl fmt::Display for ValType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            ValType::I32 => "i32",
            ValType::I64 => "i64",
            ValType::F32 => "f32",
            ValType::F64 => "f64",
            ValType::V128 => "v128",
            ValType::Ref(r) => return fmt::Display::fmt(r, f),
        };
        f.write_str(s)
    }
}

/// A reference type.
///
/// The reference types proposal first introduced `externref` and `funcref`.
///
/// The function references proposal introduced typed function references.
///
/// The GC proposal introduces heap types: any, eq, i31, struct, array, nofunc, noextern, none.
//
// RefType is a bit-packed enum that fits in a `u24` aka `[u8; 3]`.
// Note that its content is opaque (and subject to change), but its API is stable.
// It has the following internal structure:
// ```
// [nullable:u1] [indexed==1:u1] [kind:u2] [index:u20]
// [nullable:u1] [indexed==0:u1] [type:u4] [(unused):u18]
// ```
// , where
// - `nullable` determines nullability of the ref
// - `indexed` determines if the ref is of a dynamically defined type with an index (encoded in a following bit-packing section) or of a known fixed type
// - `kind` determines what kind of indexed type the index is pointing to:
//   ```
//   10 = struct
//   11 = array
//   01 = function
//   ```
// - `index` is the type index
// - `type` is an enumeration of known types:
//   ```
//   1111 = any
//
//   1101 = eq
//   1000 = i31
//   1001 = struct
//   1100 = array
//
//   0101 = func
//   0100 = nofunc
//
//   0011 = extern
//   0010 = noextern
//
//   0000 = none
//   ```
// - `(unused)` is unused sequence of bits
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct RefType([u8; 3]);

impl Debug for RefType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.is_nullable(), self.heap_type()) {
            (true, HeapType::Any) => write!(f, "anyref"),
            (false, HeapType::Any) => write!(f, "(ref any)"),
            (true, HeapType::None) => write!(f, "nullref"),
            (false, HeapType::None) => write!(f, "(ref none)"),
            (true, HeapType::NoExtern) => write!(f, "nullexternref"),
            (false, HeapType::NoExtern) => write!(f, "(ref noextern)"),
            (true, HeapType::NoFunc) => write!(f, "nullfuncref"),
            (false, HeapType::NoFunc) => write!(f, "(ref nofunc)"),
            (true, HeapType::Eq) => write!(f, "eqref"),
            (false, HeapType::Eq) => write!(f, "(ref eq)"),
            (true, HeapType::Struct) => write!(f, "structref"),
            (false, HeapType::Struct) => write!(f, "(ref struct)"),
            (true, HeapType::Array) => write!(f, "arrayref"),
            (false, HeapType::Array) => write!(f, "(ref array)"),
            (true, HeapType::I31) => write!(f, "i31ref"),
            (false, HeapType::I31) => write!(f, "(ref i31)"),
            (true, HeapType::Extern) => write!(f, "externref"),
            (false, HeapType::Extern) => write!(f, "(ref extern)"),
            (true, HeapType::Func) => write!(f, "funcref"),
            (false, HeapType::Func) => write!(f, "(ref func)"),
            (true, HeapType::Indexed(idx)) => write!(f, "(ref null {idx})"),
            (false, HeapType::Indexed(idx)) => write!(f, "(ref {idx})"),
        }
    }
}

// Static assert that we can fit indices up to `MAX_WASM_TYPES` inside `RefType`.
const _: () = {
    const fn can_roundtrip_index(index: u32) -> bool {
        assert!(RefType::can_represent_type_index(index));
        let rt = match RefType::indexed_func(true, index) {
            Some(rt) => rt,
            None => panic!(),
        };
        assert!(rt.is_nullable());
        let actual_index = match rt.type_index() {
            Some(i) => i,
            None => panic!(),
        };
        actual_index == index
    }

    assert!(can_roundtrip_index(crate::limits::MAX_WASM_TYPES as u32));
    assert!(can_roundtrip_index(0b00000000_00001111_00000000_00000000));
    assert!(can_roundtrip_index(0b00000000_00000000_11111111_00000000));
    assert!(can_roundtrip_index(0b00000000_00000000_00000000_11111111));
    assert!(can_roundtrip_index(0));
};

impl RefType {
    const NULLABLE_BIT: u32 = 1 << 23; // bit #23
    const INDEXED_BIT: u32 = 1 << 22; // bit #22

    const TYPE_MASK: u32 = 0b1111 << 18; // 4 bits #21-#18 (if `indexed == 0`)
    const ANY_TYPE: u32 = 0b1111 << 18;
    const EQ_TYPE: u32 = 0b1101 << 18;
    const I31_TYPE: u32 = 0b1000 << 18;
    const STRUCT_TYPE: u32 = 0b1001 << 18;
    const ARRAY_TYPE: u32 = 0b1100 << 18;
    const FUNC_TYPE: u32 = 0b0101 << 18;
    const NOFUNC_TYPE: u32 = 0b0100 << 18;
    const EXTERN_TYPE: u32 = 0b0011 << 18;
    const NOEXTERN_TYPE: u32 = 0b0010 << 18;
    const NONE_TYPE: u32 = 0b0000 << 18;

    const KIND_MASK: u32 = 0b11 << 20; // 2 bits #21-#20 (if `indexed == 1`)
    const STRUCT_KIND: u32 = 0b10 << 20;
    const ARRAY_KIND: u32 = 0b11 << 20;
    const FUNC_KIND: u32 = 0b01 << 20;

    const INDEX_MASK: u32 = (1 << 20) - 1; // 20 bits #19-#0 (if `indexed == 1`)

    /// A nullable untyped function reference aka `(ref null func)` aka
    /// `funcref` aka `anyfunc`.
    pub const FUNCREF: Self = RefType::FUNC.nullable();

    /// A nullable reference to an extern object aka `(ref null extern)` aka
    /// `externref`.
    pub const EXTERNREF: Self = RefType::EXTERN.nullable();

    /// A non-nullable untyped function reference aka `(ref func)`.
    pub const FUNC: Self = RefType::from_u32(Self::FUNC_TYPE);

    /// A non-nullable reference to an extern object aka `(ref extern)`.
    pub const EXTERN: Self = RefType::from_u32(Self::EXTERN_TYPE);

    /// A non-nullable reference to any object aka `(ref any)`.
    pub const ANY: Self = RefType::from_u32(Self::ANY_TYPE);

    /// A non-nullable reference to no object aka `(ref none)`.
    pub const NONE: Self = RefType::from_u32(Self::NONE_TYPE);

    /// A non-nullable reference to a noextern object aka `(ref noextern)`.
    pub const NOEXTERN: Self = RefType::from_u32(Self::NOEXTERN_TYPE);

    /// A non-nullable reference to a nofunc object aka `(ref nofunc)`.
    pub const NOFUNC: Self = RefType::from_u32(Self::NOFUNC_TYPE);

    /// A non-nullable reference to an eq object aka `(ref eq)`.
    pub const EQ: Self = RefType::from_u32(Self::EQ_TYPE);

    /// A non-nullable reference to a struct aka `(ref struct)`.
    pub const STRUCT: Self = RefType::from_u32(Self::STRUCT_TYPE);

    /// A non-nullable reference to an array aka `(ref array)`.
    pub const ARRAY: Self = RefType::from_u32(Self::ARRAY_TYPE);

    /// A non-nullable reference to an i31 object aka `(ref i31)`.
    pub const I31: Self = RefType::from_u32(Self::I31_TYPE);

    const fn can_represent_type_index(index: u32) -> bool {
        index & Self::INDEX_MASK == index
    }

    const fn u24_to_u32(bytes: [u8; 3]) -> u32 {
        let expanded_bytes = [bytes[0], bytes[1], bytes[2], 0];
        u32::from_le_bytes(expanded_bytes)
    }

    const fn u32_to_u24(x: u32) -> [u8; 3] {
        let bytes = x.to_le_bytes();
        debug_assert!(bytes[3] == 0);
        [bytes[0], bytes[1], bytes[2]]
    }

    #[inline]
    const fn as_u32(&self) -> u32 {
        Self::u24_to_u32(self.0)
    }

    #[inline]
    const fn from_u32(x: u32) -> Self {
        debug_assert!(x & (0b11111111 << 24) == 0);

        // if not indexed, type must be any/eq/i31/struct/array/func/extern/nofunc/noextern/none
        debug_assert!(
            x & Self::INDEXED_BIT != 0
                || matches!(
                    x & Self::TYPE_MASK,
                    Self::ANY_TYPE
                        | Self::EQ_TYPE
                        | Self::I31_TYPE
                        | Self::STRUCT_TYPE
                        | Self::ARRAY_TYPE
                        | Self::FUNC_TYPE
                        | Self::NOFUNC_TYPE
                        | Self::EXTERN_TYPE
                        | Self::NOEXTERN_TYPE
                        | Self::NONE_TYPE
                )
        );
        RefType(Self::u32_to_u24(x))
    }

    /// Create a reference to a typed function with the type at the given index.
    ///
    /// Returns `None` when the type index is beyond this crate's implementation
    /// limits and therefore is not representable.
    pub const fn indexed_func(nullable: bool, index: u32) -> Option<Self> {
        Self::indexed(nullable, Self::FUNC_KIND, index)
    }

    /// Create a reference to an array with the type at the given index.
    ///
    /// Returns `None` when the type index is beyond this crate's implementation
    /// limits and therefore is not representable.
    pub const fn indexed_array(nullable: bool, index: u32) -> Option<Self> {
        Self::indexed(nullable, Self::ARRAY_KIND, index)
    }

    /// Create a reference to a struct with the type at the given index.
    ///
    /// Returns `None` when the type index is beyond this crate's implementation
    /// limits and therefore is not representable.
    pub const fn indexed_struct(nullable: bool, index: u32) -> Option<Self> {
        Self::indexed(nullable, Self::STRUCT_KIND, index)
    }

    /// Create a reference to a user defined type at the given index.
    ///
    /// Returns `None` when the type index is beyond this crate's implementation
    /// limits and therefore is not representable, or when the heap type is not
    /// a typed array, struct or function.
    const fn indexed(nullable: bool, kind: u32, index: u32) -> Option<Self> {
        if Self::can_represent_type_index(index) {
            let nullable32 = Self::NULLABLE_BIT * nullable as u32;
            Some(RefType::from_u32(
                nullable32 | Self::INDEXED_BIT | kind | index,
            ))
        } else {
            None
        }
    }

    /// Create a new `RefType`.
    ///
    /// Returns `None` when the heap type's type index (if any) is beyond this
    /// crate's implementation limits and therfore is not representable.
    pub const fn new(nullable: bool, heap_type: HeapType) -> Option<Self> {
        let nullable32 = Self::NULLABLE_BIT * nullable as u32;
        match heap_type {
            HeapType::Indexed(index) => RefType::indexed(nullable, 0, index), // 0 bc we don't know the kind
            HeapType::Func => Some(Self::from_u32(nullable32 | Self::FUNC_TYPE)),
            HeapType::Extern => Some(Self::from_u32(nullable32 | Self::EXTERN_TYPE)),
            HeapType::Any => Some(Self::from_u32(nullable32 | Self::ANY_TYPE)),
            HeapType::None => Some(Self::from_u32(nullable32 | Self::NONE_TYPE)),
            HeapType::NoExtern => Some(Self::from_u32(nullable32 | Self::NOEXTERN_TYPE)),
            HeapType::NoFunc => Some(Self::from_u32(nullable32 | Self::NOFUNC_TYPE)),
            HeapType::Eq => Some(Self::from_u32(nullable32 | Self::EQ_TYPE)),
            HeapType::Struct => Some(Self::from_u32(nullable32 | Self::STRUCT_TYPE)),
            HeapType::Array => Some(Self::from_u32(nullable32 | Self::ARRAY_TYPE)),
            HeapType::I31 => Some(Self::from_u32(nullable32 | Self::I31_TYPE)),
        }
    }

    /// Is this a reference to a typed function?
    pub const fn is_typed_func_ref(&self) -> bool {
        self.is_indexed_type_ref() && self.as_u32() & Self::KIND_MASK == Self::FUNC_KIND
    }

    /// Is this a reference to an indexed type?
    pub const fn is_indexed_type_ref(&self) -> bool {
        self.as_u32() & Self::INDEXED_BIT != 0
    }

    /// If this is a reference to a typed function, get its type index.
    pub const fn type_index(&self) -> Option<u32> {
        if self.is_indexed_type_ref() {
            Some(self.as_u32() & Self::INDEX_MASK)
        } else {
            None
        }
    }

    /// Is this an untyped function reference aka `(ref null func)` aka `funcref` aka `anyfunc`?
    pub const fn is_func_ref(&self) -> bool {
        !self.is_indexed_type_ref() && self.as_u32() & Self::TYPE_MASK == Self::FUNC_TYPE
    }

    /// Is this a `(ref null extern)` aka `externref`?
    pub const fn is_extern_ref(&self) -> bool {
        !self.is_indexed_type_ref() && self.as_u32() & Self::TYPE_MASK == Self::EXTERN_TYPE
    }

    /// Is this ref type nullable?
    pub const fn is_nullable(&self) -> bool {
        self.as_u32() & Self::NULLABLE_BIT != 0
    }

    /// Get the non-nullable version of this ref type.
    pub const fn as_non_null(&self) -> Self {
        Self::from_u32(self.as_u32() & !Self::NULLABLE_BIT)
    }

    /// Get the non-nullable version of this ref type.
    pub const fn nullable(&self) -> Self {
        Self::from_u32(self.as_u32() | Self::NULLABLE_BIT)
    }

    /// Get the heap type that this is a reference to.
    pub fn heap_type(&self) -> HeapType {
        let s = self.as_u32();
        if self.is_indexed_type_ref() {
            HeapType::Indexed(self.type_index().unwrap())
        } else {
            match s & Self::TYPE_MASK {
                Self::FUNC_TYPE => HeapType::Func,
                Self::EXTERN_TYPE => HeapType::Extern,
                Self::ANY_TYPE => HeapType::Any,
                Self::NONE_TYPE => HeapType::None,
                Self::NOEXTERN_TYPE => HeapType::NoExtern,
                Self::NOFUNC_TYPE => HeapType::NoFunc,
                Self::EQ_TYPE => HeapType::Eq,
                Self::STRUCT_TYPE => HeapType::Struct,
                Self::ARRAY_TYPE => HeapType::Array,
                Self::I31_TYPE => HeapType::I31,
                _ => unreachable!(),
            }
        }
    }

    // Note that this is similar to `Display for RefType` except that it has
    // the indexes stubbed out.
    pub(crate) fn wat(&self) -> &'static str {
        match (self.is_nullable(), self.heap_type()) {
            (true, HeapType::Func) => "funcref",
            (true, HeapType::Extern) => "externref",
            (true, HeapType::Indexed(_)) => "(ref null $type)",
            (true, HeapType::Any) => "anyref",
            (true, HeapType::None) => "nullref",
            (true, HeapType::NoExtern) => "nullexternref",
            (true, HeapType::NoFunc) => "nullfuncref",
            (true, HeapType::Eq) => "eqref",
            (true, HeapType::Struct) => "structref",
            (true, HeapType::Array) => "arrayref",
            (true, HeapType::I31) => "i31ref",
            (false, HeapType::Func) => "(ref func)",
            (false, HeapType::Extern) => "(ref extern)",
            (false, HeapType::Indexed(_)) => "(ref $type)",
            (false, HeapType::Any) => "(ref any)",
            (false, HeapType::None) => "(ref none)",
            (false, HeapType::NoExtern) => "(ref noextern)",
            (false, HeapType::NoFunc) => "(ref nofunc)",
            (false, HeapType::Eq) => "(ref eq)",
            (false, HeapType::Struct) => "(ref struct)",
            (false, HeapType::Array) => "(ref array)",
            (false, HeapType::I31) => "(ref i31)",
        }
    }
}

impl<'a> FromReader<'a> for RefType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        match reader.read()? {
            0x70 => Ok(RefType::FUNC.nullable()),
            0x6F => Ok(RefType::EXTERN.nullable()),
            0x6E => Ok(RefType::ANY.nullable()),
            0x65 => Ok(RefType::NONE.nullable()),
            0x69 => Ok(RefType::NOEXTERN.nullable()),
            0x68 => Ok(RefType::NOFUNC.nullable()),
            0x6D => Ok(RefType::EQ.nullable()),
            0x67 => Ok(RefType::STRUCT.nullable()),
            0x66 => Ok(RefType::ARRAY.nullable()),
            0x6A => Ok(RefType::I31.nullable()),
            byte @ (0x6B | 0x6C) => {
                let nullable = byte == 0x6C;
                let pos = reader.original_position();
                RefType::new(nullable, reader.read()?)
                    .ok_or_else(|| crate::BinaryReaderError::new("type index too large", pos))
            }
            _ => bail!(reader.original_position(), "malformed reference type"),
        }
    }
}

impl fmt::Display for RefType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Note that this is similar to `RefType::wat` except that it has the
        // indexes filled out.
        let s = match (self.is_nullable(), self.heap_type()) {
            (true, HeapType::Func) => "funcref",
            (true, HeapType::Extern) => "externref",
            (true, HeapType::Indexed(i)) => return write!(f, "(ref null {i})"),
            (true, HeapType::Any) => "anyref",
            (true, HeapType::None) => "nullref",
            (true, HeapType::NoExtern) => "nullexternref",
            (true, HeapType::NoFunc) => "nullfuncref",
            (true, HeapType::Eq) => "eqref",
            (true, HeapType::Struct) => "structref",
            (true, HeapType::Array) => "arrayref",
            (true, HeapType::I31) => "i31ref",
            (false, HeapType::Func) => "(ref func)",
            (false, HeapType::Extern) => "(ref extern)",
            (false, HeapType::Indexed(i)) => return write!(f, "(ref {i})"),
            (false, HeapType::Any) => "(ref any)",
            (false, HeapType::None) => "(ref none)",
            (false, HeapType::NoExtern) => "(ref noextern)",
            (false, HeapType::NoFunc) => "(ref nofunc)",
            (false, HeapType::Eq) => "(ref eq)",
            (false, HeapType::Struct) => "(ref struct)",
            (false, HeapType::Array) => "(ref array)",
            (false, HeapType::I31) => "(ref i31)",
        };
        f.write_str(s)
    }
}

/// A heap type from function references. When the proposal is disabled, Index
/// is an invalid type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum HeapType {
    /// User defined type at the given index.
    Indexed(u32),
    /// Untyped (any) function.
    Func,
    /// External heap type.
    Extern,
    /// The `any` heap type. The common supertype (a.k.a. top) of all internal types.
    Any,
    /// The `none` heap type. The common subtype (a.k.a. bottom) of all internal types.
    None,
    /// The `noextern` heap type. The common subtype (a.k.a. bottom) of all external types.
    NoExtern,
    /// The `nofunc` heap type. The common subtype (a.k.a. bottom) of all function types.
    NoFunc,
    /// The `eq` heap type. The common supertype of all referenceable types on which comparison
    /// (ref.eq) is allowed.
    Eq,
    /// The `struct` heap type. The common supertype of all struct types.
    Struct,
    /// The `array` heap type. The common supertype of all array types.
    Array,
    /// The i31 heap type.
    I31,
}

impl<'a> FromReader<'a> for HeapType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        match reader.peek()? {
            0x70 => {
                reader.position += 1;
                Ok(HeapType::Func)
            }
            0x6F => {
                reader.position += 1;
                Ok(HeapType::Extern)
            }
            0x6E => {
                reader.position += 1;
                Ok(HeapType::Any)
            }
            0x65 => {
                reader.position += 1;
                Ok(HeapType::None)
            }
            0x69 => {
                reader.position += 1;
                Ok(HeapType::NoExtern)
            }
            0x68 => {
                reader.position += 1;
                Ok(HeapType::NoFunc)
            }
            0x6D => {
                reader.position += 1;
                Ok(HeapType::Eq)
            }
            0x67 => {
                reader.position += 1;
                Ok(HeapType::Struct)
            }
            0x66 => {
                reader.position += 1;
                Ok(HeapType::Array)
            }
            0x6A => {
                reader.position += 1;
                Ok(HeapType::I31)
            }
            _ => {
                let idx = match u32::try_from(reader.read_var_s33()?) {
                    Ok(idx) => idx,
                    Err(_) => {
                        bail!(reader.original_position(), "invalid indexed ref heap type");
                    }
                };
                Ok(HeapType::Indexed(idx))
            }
        }
    }
}

/// Represents a type in a WebAssembly module.
#[derive(Debug, Clone)]
pub enum Type {
    /// The type is for a function.
    Func(IndexedFuncType),
    /// The type is for an array.
    Array(ArrayType),
    // Struct(StructType),
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
    OldLocal(u32),
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

    pub(crate) fn desc(&self) -> String {
        let mut s = String::new();
        s.push_str("[");
        for (i, param) in self.params().iter().enumerate() {
            if i > 0 {
                s.push_str(" ");
            }
            write!(s, "{param}").unwrap();
        }
        s.push_str("] -> [");
        for (i, result) in self.results().iter().enumerate() {
            if i > 0 {
                s.push_str(" ");
            }
            write!(s, "{result}").unwrap();
        }
        s.push_str("]");
        // TODO: Add constraints
        s
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

/// Represents a type of an array in a WebAssembly module.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ArrayType {
    /// Array element type.
    pub element_type: StorageType,
    /// Are elements mutable.
    pub mutable: bool,
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

    pub(crate) fn desc(&self) -> String {
        let mut s = String::new();
        s.push_str("[");
        for (i, param) in self.params().iter().enumerate() {
            if i > 0 {
                s.push_str(" ");
            }
            write!(s, "{param}").unwrap();
        }
        s.push_str("] -> [");
        for (i, result) in self.results().iter().enumerate() {
            if i > 0 {
                s.push_str(" ");
            }
            write!(s, "{result}").unwrap();
        }
        s.push_str("]");
        s
    }
}

/// Represents a table's type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TableType {
    /// The table's element type.
    pub element_type: RefType,
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
            0x5e => Type::Array(reader.read()?),
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
            0x41 => IndexTerm::IConstant(Constant::I32Const(reader.read_var_i32()?)),
            0x42 => IndexTerm::IConstant(Constant::I64Const(reader.read_var_i64()?)),
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
            x @ 0x20..=0x23 => {
                let index = reader.read()?;
                match x {
                    0x20 => IndexTerm::Local(index),
                    0x21 => IndexTerm::Pre(index),
                    0x22 => IndexTerm::Post(index),
                    0x23 => IndexTerm::OldLocal(index),
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

impl<'a> FromReader<'a> for ArrayType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        let element_type = reader.read()?;
        let mutable = reader.read_u8()?;
        Ok(ArrayType {
            element_type,
            mutable: match mutable {
                0 => false,
                1 => true,
                _ => bail!(
                    reader.original_position(),
                    "invalid mutability byte for array type"
                ),
            },
        })
    }
}

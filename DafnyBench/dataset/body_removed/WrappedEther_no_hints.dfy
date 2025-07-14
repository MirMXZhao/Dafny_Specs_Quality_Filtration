/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */
module Int {
    const TWO_7   : int := 0x0_80
    const TWO_8   : int := 0x1_00
    const TWO_15  : int := 0x0_8000
    const TWO_16  : int := 0x1_0000
    const TWO_24  : int := 0x1_0000_00
    const TWO_31  : int := 0x0_8000_0000
    const TWO_32  : int := 0x1_0000_0000
    const TWO_40  : int := 0x1_0000_0000_00
    const TWO_48  : int := 0x1_0000_0000_0000
    const TWO_56  : int := 0x1_0000_0000_0000_00
    const TWO_63  : int := 0x0_8000_0000_0000_0000
    const TWO_64  : int := 0x1_0000_0000_0000_0000
    const TWO_127 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000
    const TWO_128 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_160 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_255 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_256 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000

    // Signed Integers
    const MIN_I8   : int := -TWO_7
    const MAX_I8   : int :=  TWO_7 - 1
    const MIN_I16  : int := -TWO_15
    const MAX_I16  : int :=  TWO_15 - 1
    const MIN_I32  : int := -TWO_31
    const MAX_I32  : int :=  TWO_31 - 1
    const MIN_I64  : int := -TWO_63
    const MAX_I64  : int :=  TWO_63 - 1
    const MIN_I128 : int := -TWO_127
    const MAX_I128 : int :=  TWO_127 - 1
    const MIN_I256 : int := -TWO_255
    const MAX_I256 : int :=  TWO_255 - 1

    newtype{:nativeType "sbyte"} i8 = i:int   | MIN_I8 <= i <= MAX_I8
    newtype{:nativeType "short"} i16 = i:int  | MIN_I16 <= i <= MAX_I16
    newtype{:nativeType "int"}   i32 = i:int  | MIN_I32 <= i <= MAX_I32
    newtype{:nativeType "long"}  i64 = i:int  | MIN_I64 <= i <= MAX_I64
    newtype i128 = i:int | MIN_I128 <= i <= MAX_I128
    newtype i256 = i:int | MIN_I256 <= i <= MAX_I256

    // Unsigned Integers
    const MAX_U8 : int :=  TWO_8 - 1
    const MAX_U16 : int := TWO_16 - 1
    const MAX_U24 : int := TWO_24 - 1
    const MAX_U32 : int := TWO_32 - 1
    const MAX_U40 : int := TWO_40 - 1
    const MAX_U48 : int := TWO_48 - 1
    const MAX_U56 : int := TWO_56 - 1
    const MAX_U64 : int := TWO_64 - 1
    const MAX_U128 : int := TWO_128 - 1
    const MAX_U160: int := TWO_160 - 1
    const MAX_U256: int := TWO_256 - 1

    newtype{:nativeType "byte"} u8 = i:int    | 0 <= i <= MAX_U8
    newtype{} u16 = i:int | 0 <= i <= MAX_U16
    newtype{:nativeType "uint"} u24 = i:int | 0 <= i <= MAX_U24
    newtype{:nativeType "uint"} u32 = i:int   | 0 <= i <= MAX_U32
    newtype{:nativeType "ulong"} u40 = i:int   | 0 <= i <= MAX_U40
    newtype{:nativeType "ulong"} u48 = i:int   | 0 <= i <= MAX_U48
    newtype{:nativeType "ulong"} u56 = i:int   | 0 <= i <= MAX_U56
    newtype{:nativeType "ulong"} u64 = i:int  | 0 <= i <= MAX_U64
    newtype u128 = i:int | 0 <= i <= MAX_U128
    newtype u160 = i:int | 0 <= i <= MAX_U160
    newtype u256 = i:int | 0 <= i <= MAX_U256


    // Determine maximum of two u256 integers.
    function Max(i1: int, i2: int) : int {}

    // Determine maximum of two u256 integers.
    function Min(i1: int, i2: int) : int {}

    // Round up a given number (i) by a given multiple (r).
    function RoundUp(i: int, r: nat) : int
    requires r > 0 {}

    // Return the maximum value representable using exactly n unsigned bytes.
    // This is essentially computing (2^n - 1).  However, the point of doing it
    // in this fashion is to avoid using Pow() as this is challenging for the
    // verifier.
    function MaxUnsignedN(n:nat) : (r:nat)
    requires 1 <= n <= 32 {}


    // =========================================================
    // Exponent
    // =========================================================

    /**
     * Compute n^k.
     */
    function Pow(n:nat, k:nat) : (r:nat)
    // Following needed for some proofs
    ensures n > 0 ==> r > 0 {}

    // Simple lemma about POW.
    lemma lemma_pow2(k:nat)
    ensures Pow(2,k) > 0 {
        if k == 0 {
        } else if k == 1 {
            } else {
            lemma_pow2(k/2);
        }
    }

    // =========================================================
    // Non-Euclidean Division / Remainder
    // =========================================================

    // This provides a non-Euclidean division operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  This operator, therefore,
    // always divides *towards* zero.
    function Div(lhs: int, rhs: int) : int
    requires rhs != 0 {}

    // This provides a non-Euclidean Remainder operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  Observe that this is a
    // true Remainder operator, and not a modulus operator.  For
    // emxaple, this means the result can be negative.
    function Rem(lhs: int, rhs: int) : int
    requires rhs != 0 {}
}

/**
 * Various helper methods related to unsigned 8bit integers.
 */
module U8 {
    import opened Int
    // Compute the log of a value at base 2 where the result is rounded down.
    function Log2(v:u8) : (r:nat)
    ensures r < 8 {}
}

/**
 * Various helper methods related to unsigned 16bit integers.
 */
module U16 {
    import opened Int
    import U8

    // Read nth 8bit word (i.e. byte) out of this u16, where 0
    // identifies the most significant byte.
    function NthUint8(v:u16, k: nat) : u8
        // Cannot read more than two words!
    requires k < 2 {}

    /**
     * Compute the log of a value at base 2 where the result is rounded down.
     */
    function Log2(v:u16) : (r:nat)
    ensures r < 16 {}

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u16) : (r:nat)
    ensures r <= 1 {}

    /**
     * Convert a u16 into a sequence of 2 bytes (in big endian representation).
     */
    function ToBytes(v:u16) : (r:seq<u8>)
    ensures |r| == 2 {}

    function Read(bytes: seq<u8>, address:nat) : u16
    requires (address+1) < |bytes| {}
}

/**
 * Various helper methods related to unsigned 32bit integers.
 */
module U32 {
    import U16
    import opened Int

    // Read nth 16bit word out of this u32, where 0 identifies the most
    // significant word.
    function NthUint16(v:u32, k: nat) : u16
        // Cannot read more than two words!
    requires k < 2 {}

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log2(v:u32) : (r:nat)
    ensures r < 32 {}

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u32) : (r:nat)
    ensures r <= 3 {}

    /**
     * Convert a u32 into a sequence of 4 bytes (in big endian representation).
     */
    function ToBytes(v:u32) : (r:seq<u8>)
    ensures |r| == 4 {}

    function Read(bytes: seq<u8>, address:nat) : u32
    requires (address+3) < |bytes| {}
}

/**
 * Various helper methods related to unsigned 64bit integers.
 */
module U64 {
    import U32
    import opened Int

    // Read nth 32bit word out of this u64, where 0 identifies the most
    // significant word.
    function NthUint32(v:u64, k: nat) : u32
        // Cannot read more than two words!
    requires k < 2 {}

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log2(v:u64) : (r:nat)
    ensures r < 64 {}

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u64) : (r:nat)
    ensures r <= 7 {}

    /**
     * Convert a u64 into a sequence of 8bytes (in big endian representation).
     */
    function ToBytes(v:u64) : (r:seq<u8>)
    ensures |r| == 8 {}

    function Read(bytes: seq<u8>, address:nat) : u64
    requires (address+7) < |bytes| {}
}

/**
 * Various helper methods related to unsigned 128bit integers.
 */
module U128 {
    import U64
    import opened Int

    // Read nth 64bit word out of this u128, where 0 identifies the most
    // significant word.
    function NthUint64(v:u128, k: nat) : u64
        // Cannot read more than two words!
    requires k < 2 {}

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log2(v:u128) : (r:nat)
    ensures r < 128 {}

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u128) : (r:nat)
    ensures r <= 15 {}

    /**
     * Convert a u128 into a sequence of 16bytes (in big endian representation).
     */
    function ToBytes(v:u128) : (r:seq<u8>)
    ensures |r| == 16 {}

    function Read(bytes: seq<u8>, address:nat) : u128
    requires (address+15) < |bytes| {}
}

/**
 * Various helper methods related to unsigned 256bit integers.
 */
module U256 {
    import opened Int
    import U8
    import U16
    import U32
    import U64
    import U128

    /** An axiom stating that a bv256 converted as a nat is bounded by 2^256. */
    lemma {:axiom} as_bv256_as_u256(v: bv256)
        ensures v as nat < TWO_256

    function Shl(lhs: u256, rhs: u256) : u256
    {}

    function Shr(lhs: u256, rhs: u256) : u256 {}

    /**
     * Compute the log of a value at base 2, where the result in rounded down.
     * This effectively determines the position of the highest on bit.
     */
    function Log2(v:u256) : (r:nat)
    ensures r < 256 {}

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u256) : (r:nat)
    ensures r <= 31 {}

    // Read nth 128bit word out of this u256, where 0 identifies the most
    // significant word.
    function NthUint128(v:u256, k: nat) : u128
        // Cannot read more than two words!
        requires k < 2 {}

    // Read nth byte out of this u256, where 0 identifies the most
    // significant byte.
    function NthUint8(v:u256, k: nat) : u8
    // Cannot read more than 32bytes!
    requires k < 32 {}

    function Read(bytes: seq<u8>, address:nat) : u256
    requires (address+31) < |bytes| {}

    /**
     * Convert a u256 into a sequence of 32bytes in big endian representation.
     */
    function ToBytes(v:u256) : (r:seq<u8>)
    ensures |r| == 32 {}

    /**
     *
     */
    function SignExtend(v: u256, k: nat) : u256 {}
}

module I256 {
    import U256
    import Word
    import opened Int

    // This provides a non-Euclidean division operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  This operator, therefore,
    // always divides *towards* zero.
    function Div(lhs: i256, rhs: i256) : i256
        // Cannot divide by zero!
        requires rhs != 0
        // Range restriction to prevent overflow
        requires (rhs != -1 || lhs != (-TWO_255 as i256)) {}

    // This provides a non-Euclidean Remainder operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  Observe that this is a
    // true Remainder operator, and not a modulus operator.  For
    // emxaple, this means the result can be negative.
    function Rem(lhs: i256, rhs: i256) : i256
        // Cannot divide by zero!
        requires rhs != 0 {}

    /**
     *  Shifting 1 left less than 256 times produces a non-zero value.
     *
     *  More generally, shifting-left 1 less than k times over k bits
     *  yield a non-zero number.
     *
     *  @example    over 2 bits, left-shift 1 once: 01 -> 10
     *  @example    over 4 bits, left-shift 1 3 times: 0001 -> 0010 -> 0100 -> 1000
     */
    lemma ShiftYieldsNonZero(x: u256)
        requires 0 < x < 256
        ensures U256.Shl(1, x) > 0
    {}

    // Shift Arithmetic Right.  This implementation follows the Yellow Paper quite
    // accurately.
    function Sar(lhs: i256, rhs: u256): i256 {}
}

module Word {
  import opened Int

  // Decode a 256bit word as a signed 256bit integer.  Since words
  // are represented as u256, the parameter has type u256.  However,
  // its important to note that this does not mean the value in
  // question represents an unsigned 256 bit integer.  Rather, it is a
  // signed integer encoded into an unsigned integer.
  function asI256(w: u256) : i256 {}

  // Encode a 256bit signed integer as a 256bit word.  Since words are
  // represented as u256, the return is represented as u256.  However,
  // its important to note that this does not mean the value in
  // question represents an unsigned 256 bit integer.  Rather, it is a
  // signed integer encoded into an unsigned integer.
  function fromI256(w: Int.i256) : u256 {}
}


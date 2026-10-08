// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Specification of hex encoding and decoding (ghost code only; erased from normal builds).
//!
//! The public API contracts in `lib.rs` are stated with these predicates. Nothing here is
//! trusted: every `spec fn` is a definition and every `proof fn` is checked by Verus.
#![allow(unused_imports)]

#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)] // ghost items: they do not exist in the erased (normal) build
use vstd::utf8::{
    decode_utf8, encode_utf8, encode_utf8_decode_utf8, encode_utf8_valid_utf8, is_ascii_chars,
    is_ascii_chars_encode_utf8, valid_utf8,
};

use crate::FromHexError;

verus! {

// ---------------------------------------------------------------- digits

/// Numeric value of an ASCII hex digit, if `c` is one (`0-9`, `a-f`, `A-F`).
pub open spec fn hex_val(c: u8) -> Option<u8> {
    if 0x30 <= c <= 0x39 {
        Some((c - 0x30) as u8)
    } else if 0x61 <= c <= 0x66 {
        Some((c - 0x61 + 10) as u8)
    } else if 0x41 <= c <= 0x46 {
        Some((c - 0x41 + 10) as u8)
    } else {
        None
    }
}

pub open spec fn is_hex_digit(c: u8) -> bool {
    hex_val(c) is Some
}

/// The byte denoted by the two hex digits `hi`, `lo`.
pub open spec fn decoded_byte(hi: u8, lo: u8) -> u8
    recommends
        is_hex_digit(hi),
        is_hex_digit(lo),
{
    (hex_val(hi)->Some_0 * 16 + hex_val(lo)->Some_0) as u8
}

/// What the decode lookup table must hold at `c`: the digit value, or `0xff`.
pub open spec fn spec_decode_table(c: u8) -> u8 {
    match hex_val(c) {
        Some(v) => v,
        None => 0xff,
    }
}

/// ASCII digit for the nibble `n`, in lower or upper case.
pub open spec fn hex_digit(upper: bool, n: u8) -> u8
    recommends
        n < 16,
{
    if n < 10 {
        (0x30 + n) as u8
    } else if upper {
        (0x41 + (n - 10)) as u8
    } else {
        (0x61 + (n - 10)) as u8
    }
}

/// `table` is the 16-entry digit table for one case.
pub open spec fn is_digit_table(table: Seq<u8>, upper: bool) -> bool {
    &&& table.len() == 16
    &&& forall|n: int| 0 <= n < 16 ==> #[trigger] table[n] == hex_digit(upper, n as u8)
}

// ---------------------------------------------------------------- encoding

/// `out` is the hex encoding of `inp`: two digits per byte, high nibble first.
pub open spec fn is_hex_encoding(out: Seq<u8>, inp: Seq<u8>, upper: bool) -> bool {
    &&& out.len() == 2 * inp.len()
    &&& forall|i: int|
        0 <= i < inp.len() ==> {
            &&& out[2 * i] == hex_digit(upper, ((#[trigger] inp[i]) >> 4) as u8)
            &&& out[2 * i + 1] == hex_digit(upper, (inp[i] & 0x0f) as u8)
        }
}

/// Same, for a character sequence (the `String` results).
pub open spec fn is_hex_encoding_chars(out: Seq<char>, inp: Seq<u8>, upper: bool) -> bool {
    &&& out.len() == 2 * inp.len()
    &&& forall|i: int|
        0 <= i < inp.len() ==> {
            &&& out[2 * i] == hex_digit(upper, ((#[trigger] inp[i]) >> 4) as u8) as char
            &&& out[2 * i + 1] == hex_digit(upper, (inp[i] & 0x0f) as u8) as char
        }
}

/// Encoding through an arbitrary 16-entry table (implementation-facing).
pub open spec fn is_hex_encoding_table(out: Seq<u8>, inp: Seq<u8>, table: Seq<u8>) -> bool {
    &&& out.len() == 2 * inp.len()
    &&& forall|i: int|
        0 <= i < inp.len() ==> {
            &&& out[2 * i] == table[((#[trigger] inp[i]) >> 4) as int]
            &&& out[2 * i + 1] == table[(inp[i] & 0x0f) as int]
        }
}

/// Contract of `encode_to_slice` / `encode_to_slice_upper`.
pub open spec fn encode_to_slice_post(
    input: Seq<u8>,
    old_out: Seq<u8>,
    out: Seq<u8>,
    upper: bool,
    r: Result<(), FromHexError>,
) -> bool {
    &&& out.len() == old_out.len()
    &&& match r {
        Ok(()) => is_hex_encoding(out, input, upper),
        Err(FromHexError::InvalidStringLength) => {
            &&& old_out.len() != 2 * input.len()
            &&& out == old_out
        },
        Err(_) => false,
    }
}

// ---------------------------------------------------------------- decoding

/// Every byte of `data` before index `n` is a hex digit.
pub open spec fn all_hex(data: Seq<u8>, n: int) -> bool {
    forall|k: int| 0 <= k < n ==> is_hex_digit(#[trigger] data[k])
}

/// `j` is the index of the first byte of `data` that is not a hex digit.
pub open spec fn first_invalid_at(data: Seq<u8>, j: int) -> bool {
    &&& 0 <= j < data.len()
    &&& !is_hex_digit(data[j])
    &&& all_hex(data, j)
}

/// `out[i]` is the decoding of `data[2i], data[2i+1]` for every `i < n`.
pub open spec fn decoded_prefix(out: Seq<u8>, data: Seq<u8>, n: int) -> bool {
    forall|i: int| 0 <= i < n ==> #[trigger] out[i] == decoded_byte(data[2 * i], data[2 * i + 1])
}

/// `out[i] == orig[i]` for every `i >= n`.
pub open spec fn unchanged_from(out: Seq<u8>, orig: Seq<u8>, n: int) -> bool {
    forall|i: int| n <= i < out.len() ==> #[trigger] out[i] == orig[i]
}

/// Contract of `decode_to_slice`: `data` is read, `old_out` becomes `out`.
/// Error precedence: odd length, then length mismatch, then first invalid character.
/// On an invalid character the bytes before it are already decoded into `out`.
pub open spec fn decode_to_slice_post(
    data: Seq<u8>,
    old_out: Seq<u8>,
    out: Seq<u8>,
    r: Result<(), FromHexError>,
) -> bool {
    &&& out.len() == old_out.len()
    &&& match r {
        Ok(()) => {
            &&& data.len() == 2 * old_out.len()
            &&& all_hex(data, data.len() as int)
            &&& decoded_prefix(out, data, old_out.len() as int)
        },
        Err(FromHexError::OddLength) => {
            &&& data.len() % 2 == 1
            &&& out == old_out
        },
        Err(FromHexError::InvalidStringLength) => {
            &&& data.len() % 2 == 0
            &&& data.len() != 2 * old_out.len()
            &&& out == old_out
        },
        Err(FromHexError::InvalidHexCharacter { c, index }) => {
            &&& data.len() == 2 * old_out.len()
            &&& first_invalid_at(data, index as int)
            &&& c == data[index as int] as char
            &&& decoded_prefix(out, data, index as int / 2)
            &&& unchanged_from(out, old_out, index as int / 2)
        },
    }
}

/// Contract of `decode_in_slice`: `orig` is the buffer on entry, `io` on exit.
/// The decoded bytes occupy the first half; the second half is untouched.
pub open spec fn decode_in_slice_post(orig: Seq<u8>, io: Seq<u8>, r: Result<(), FromHexError>) -> bool {
    &&& io.len() == orig.len()
    &&& match r {
        Ok(()) => {
            &&& orig.len() % 2 == 0
            &&& all_hex(orig, orig.len() as int)
            &&& decoded_prefix(io, orig, orig.len() as int / 2)
            &&& unchanged_from(io, orig, orig.len() as int / 2)
        },
        Err(FromHexError::OddLength) => {
            &&& orig.len() % 2 == 1
            &&& io == orig
        },
        Err(FromHexError::InvalidStringLength) => false,
        Err(FromHexError::InvalidHexCharacter { c, index }) => {
            &&& orig.len() % 2 == 0
            &&& first_invalid_at(orig, index as int)
            &&& c == orig[index as int] as char
            &&& decoded_prefix(io, orig, index as int / 2)
            &&& unchanged_from(io, orig, index as int / 2)
        },
    }
}

/// Contract of `decode` and `<Vec<u8> as FromHex>::from_hex`.
#[cfg(feature = "alloc")]
pub open spec fn decode_post(data: Seq<u8>, r: Result<Vec<u8>, FromHexError>) -> bool {
    match r {
        Ok(v) => {
            &&& data.len() % 2 == 0
            &&& all_hex(data, data.len() as int)
            &&& v@.len() == data.len() / 2
            &&& decoded_prefix(v@, data, v@.len() as int)
        },
        Err(FromHexError::OddLength) => data.len() % 2 == 1,
        Err(FromHexError::InvalidStringLength) => false,
        Err(FromHexError::InvalidHexCharacter { c, index }) => {
            &&& data.len() % 2 == 0
            &&& first_invalid_at(data, index as int)
            &&& c == data[index as int] as char
        },
    }
}

/// Contract of `<[u8; N] as FromHex>::from_hex`.
pub open spec fn decode_array_post<const N: usize>(data: Seq<u8>, r: Result<[u8; N], FromHexError>) -> bool {
    match r {
        Ok(a) => {
            &&& data.len() == 2 * N
            &&& all_hex(data, data.len() as int)
            &&& decoded_prefix(a@, data, N as int)
        },
        Err(FromHexError::OddLength) => data.len() % 2 == 1,
        Err(FromHexError::InvalidStringLength) => {
            &&& data.len() % 2 == 0
            &&& data.len() != 2 * N
        },
        Err(FromHexError::InvalidHexCharacter { c, index }) => {
            &&& data.len() == 2 * N
            &&& first_invalid_at(data, index as int)
            &&& c == data[index as int] as char
        },
    }
}

// ---------------------------------------------------------------- lemmas

/// An encoding through the digit table for `upper` is a hex encoding in that case.
pub proof fn lemma_table_encoding(out: Seq<u8>, inp: Seq<u8>, table: Seq<u8>, upper: bool)
    requires
        is_digit_table(table, upper),
        is_hex_encoding_table(out, inp, table),
    ensures
        is_hex_encoding(out, inp, upper),
{
    assert forall|i: int| 0 <= i < inp.len() implies {
        &&& out[2 * i] == hex_digit(upper, ((#[trigger] inp[i]) >> 4) as u8)
        &&& out[2 * i + 1] == hex_digit(upper, (inp[i] & 0x0f) as u8)
    } by {
        let b = inp[i];
        assert(b >> 4 < 16 && b & 0x0f < 16) by (bit_vector);
    }
}

/// Bytes below 128 are valid UTF-8 and decode to themselves as characters.
pub proof fn lemma_ascii_bytes_utf8(bytes: Seq<u8>)
    requires
        forall|i: int| 0 <= i < bytes.len() ==> #[trigger] bytes[i] < 128,
    ensures
        valid_utf8(bytes),
        decode_utf8(bytes).len() == bytes.len(),
        forall|i: int| 0 <= i < bytes.len() ==> #[trigger] decode_utf8(bytes)[i] == bytes[i] as char,
{
    let chars = Seq::new(bytes.len(), |i: int| bytes[i] as char);
    assert(is_ascii_chars(chars));
    is_ascii_chars_encode_utf8(chars);
    assert(encode_utf8(chars) =~= bytes);
    encode_utf8_valid_utf8(chars);
    encode_utf8_decode_utf8(chars);
}

/// A hex encoding is ASCII, so it is valid UTF-8 and decodes to the same digits as characters.
pub proof fn lemma_hex_encoding_utf8(bytes: Seq<u8>, inp: Seq<u8>, upper: bool)
    requires
        is_hex_encoding(bytes, inp, upper),
    ensures
        valid_utf8(bytes),
        is_hex_encoding_chars(decode_utf8(bytes), inp, upper),
{
    assert forall|k: int| 0 <= k < bytes.len() implies #[trigger] bytes[k] < 128 by {
        let i = k / 2;
        let b = inp[i];
        assert(b >> 4 < 16 && b & 0x0f < 16) by (bit_vector);
        if k % 2 == 0 {
            assert(bytes[k] == hex_digit(upper, (b >> 4) as u8));
        } else {
            assert(bytes[k] == hex_digit(upper, (b & 0x0f) as u8));
        }
    }
    lemma_ascii_bytes_utf8(bytes);
}

/// Decoding an encoding gives the input back: the two contracts are mutually consistent
/// and neither is vacuous. Proved from the definitions alone.
pub proof fn lemma_encode_decode_roundtrip(out: Seq<u8>, inp: Seq<u8>, upper: bool)
    requires
        is_hex_encoding(out, inp, upper),
    ensures
        all_hex(out, out.len() as int),
        decoded_prefix(inp, out, inp.len() as int),
{
    assert forall|i: int| 0 <= i < inp.len() implies {
        &&& is_hex_digit(out[2 * i])
        &&& is_hex_digit(out[2 * i + 1])
        &&& #[trigger] inp[i] == decoded_byte(out[2 * i], out[2 * i + 1])
    } by {
        let b = inp[i];
        assert(b >> 4 < 16 && b & 0x0f < 16 && b == (b >> 4) * 16 + (b & 0x0f)) by (bit_vector);
    }
    assert forall|k: int| 0 <= k < out.len() implies is_hex_digit(#[trigger] out[k]) by {
        let i = k / 2;
        assert(0 <= i < inp.len());
        assert(inp[i] == decoded_byte(out[2 * i], out[2 * i + 1])); // instantiates the forall above
        if k % 2 == 0 {
            assert(out[k] == out[2 * i]);
        } else {
            assert(out[k] == out[2 * i + 1]);
        }
    }
}

} // verus!

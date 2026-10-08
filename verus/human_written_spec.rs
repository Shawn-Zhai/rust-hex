use vstd::prelude::*;

verus! {

// --- Hexadecimal Helpers ---

// Check whether a byte represents a valid hexadecimal character
spec fn is_hex_digit(b: u8) -> bool {
    (48 <= b && b <= 57)     // '0'..'9'
    || (65 <= b && b <= 70)  // 'A'..'F'
    || (97 <= b && b <= 102) // 'a'..'f'
}

// Check whether every byte in a sequence is a valid hexadecimal character
spec fn valid_hex(s: Seq<u8>) -> bool {
    forall |i: int|
        0 <= i < s.len() ==> is_hex_digit(s[i])
}

// Convert one hexadecimal character byte into its numeric value
spec fn hex_value(b: u8) -> int
    requires is_hex_digit(b)
{
    if 48 <= b && b <= 57 {
        (b - 48) as int
    } else if 65 <= b && b <= 70 {
        (b - 65 + 10) as int
    } else {
        (b - 97 + 10) as int
    }
}

// Convert a numeric value into the corresponding hexadecimal character byte, 
// using uppercase or lowercase letters
spec fn hex_digit_byte(v: int, upper: bool) -> u8
    requires 0 <= v < 16
{
    if v < 10 {
        (48 + v) as u8
    } else if upper {
        (55 + v) as u8       // A = 65, 65 - 10 = 55
    } else {
        (87 + v) as u8       // a = 97, 97 - 10 = 87
    }
}

// Encode a sequence of bytes into hexadecimal ASCII bytes, 
// producing two hex characters for each input byte
spec fn encode_bytes(
    src: Seq<u8>,
    upper: bool,
) -> Seq<u8> {
    Seq::new(
        src.len() * 2,
        |i: int| {
            let b = src[i / 2];
            let nibble =
                if i % 2 == 0 {
                    (b / 16) as int
                } else {
                    (b % 16) as int
                };

            hex_digit_byte(nibble, upper)
        },
    )
}

// Encode a sequence of bytes into hexadecimal characters (Seq<char>), 
// mainly for specifying functions that return a Rust String
spec fn encode_chars(
    src: Seq<u8>,
    upper: bool,
) -> Seq<char> {
    let encoded = encode_bytes(src, upper);

    Seq::new(
        encoded.len(),
        |i: int| encoded[i] as char,
    )
}

// Decode a valid even-length hexadecimal byte sequence into the original byte sequence, 
// combining every two hex characters into one byte
spec fn decode_bytes(src: Seq<u8>) -> Seq<u8>
    requires
        src.len() % 2 == 0,
        valid_hex(src),
{
    Seq::new(
        src.len() / 2,
        |i: int| {
            (
                hex_value(src[2 * i]) * 16
                + hex_value(src[2 * i + 1])
            ) as u8
        },
    )
}

// Return the index of the first invalid hex character
spec fn first_invalid(src: Seq<u8>) -> int
    requires !valid_hex(src)
{
    choose |i: int|
        0 <= i < src.len()
        && !is_hex_digit(src[i])
        && forall |j: int|
            0 <= j < i ==> is_hex_digit(src[j])
}

// --- Specs for Public Functions ---

// Converts every input byte into exactly two lowercase hexadecimal characters
// It cannot return an encoding error
pub fn encode<T: AsRef<[u8]>>(data: T) -> (result: String)
    ensures
        result@ == encode_chars(data.as_ref()@, false),
        result@.len() == 2 * data.as_ref()@.len(),
        forall |i: int|
            0 <= i < result@.len()
            ==> (
                ('0' <= result@[i] && result@[i] <= '9')
                || ('a' <= result@[i] && result@[i] <= 'f')
            ),

// Same as above except uppercase
pub fn encode_upper<T: AsRef<[u8]>>(data: T) -> (result: String)
    ensures
        result@ == encode_chars(data_bytes(data), true),
        result@.len() == 2 * data_bytes(data).len(),
        forall |i: int|
            0 <= i < result@.len()
            ==> (
                ('0' <= result@[i] && result@[i] <= '9')
                || ('A' <= result@[i] && result@[i] <= 'F')
            ),

// Decodes a hex string into raw bytes
// InvalidStringLength is impossible because it dynamically 
// creates a Vec of exactly input.len() / 2
pub fn decode<T: AsRef<[u8]>>(
    data: T,
) -> (result: Result<Vec<u8>, FromHexError>)
    ensures
        ({
            let src = src.as_ref();

            if src.len() % 2 != 0 {
                result == Err(FromHexError::OddLength)
            } else if !valid_hex(src) {
                let i = first_invalid(src);

                result == Err(
                    FromHexError::InvalidHexCharacter {
                        c: src[i] as char,
                        index: i as usize,
                    }
                )
            } else {
                match result {
                    Ok(v) => v@ == decode_bytes(src),
                    Err(_) => false,
                }
            }
        }),

// Decode a hex string into a mutable bytes slice
pub fn decode_to_slice<T: AsRef<[u8]>>(
    data: T,
    out: &mut [u8],
) -> (result: Result<(), FromHexError>)
    ensures
        ({
            let src = data.as_ref();

            if src.len() % 2 != 0 {
                // fails before writing anything.
                &&& result == Err(FromHexError::OddLength)
                &&& final(out)@ == old(out)@

            } else if src.len() / 2 != old(out)@.len() {
                // fails before writing anything.
                &&& result == Err(
                    FromHexError::InvalidStringLength
                )
                &&& final(out)@ == old(out)@

            } else if !valid_hex(src) {
                let k = first_invalid(src);
                let p = k / 2;

                &&& result == Err(
                    FromHexError::InvalidHexCharacter {
                        c: src[k] as char,
                        index: k as usize,
                    }
                )

                // all complete pairs before the invalid character
                // have already been decoded
                &&& final(out)@.subrange(0, p)
                    ==
                    decode_bytes(
                        src.subrange(0, 2 * p)
                    )

                // current and later output bytes remain unchanged
                &&& final(out)@.subrange(
                        p,
                        final(out)@.len() as int,
                    )
                    ==
                    old(out)@.subrange(
                        p,
                        old(out)@.len() as int,
                    )

            } else {
                &&& result == Ok(())
                &&& final(out)@ == decode_bytes(src)
            }
        }),

// Decode in place
// On success, only the first half becomes decoded bytee,
// the second half remains unchanged
pub fn decode_in_slice(
    in_out: &mut [u8],
) -> (result: Result<(), FromHexError>)
    ensures
        ({
            let src = data.as_ref();

            if src.len() % 2 != 0 {
                // fails before writing anything.
                &&& result == Err(FromHexError::OddLength)
                &&& final(in_out)@ == src

            } else if !valid_hex(src) {
                let k = first_invalid(src);
                let p = k / 2;

                &&& result == Err(
                    FromHexError::InvalidHexCharacter {
                        c: src[k] as char,
                        index: k as usize,
                    }
                )

                // all complete pairs before the invalid character
                // have already been decoded
                &&& final(in_out)@.subrange(0, p)
                    ==
                    decode_bytes(
                        src.subrange(0, 2 * p)
                    )

                // current and later output bytes remain unchanged
                &&& final(in_out)@.subrange(
                        p,
                        src.len() as int,
                    )
                    ==
                    src.subrange(
                        p,
                        src.len() as int,
                    )

            } else {
                &&& result == Ok(())

                // decoded data occupies first half
                &&& final(in_out)@.subrange(
                        0,
                        src.len() / 2,
                    )
                    ==
                    decode_bytes(src)

                // remaining half is untouched
                &&& final(in_out)@.subrange(
                        src.len() / 2,
                        src.len() as int,
                    )
                    ==
                    src.subrange(
                        src.len() / 2,
                        src.len() as int,
                    )
            }
        }),

// Encode bytes into a mutable slice of bytes using lowercase characters
pub fn encode_to_slice<T: AsRef<[u8]>>(
    input: T,
    output: &mut [u8],
) -> (result: Result<(), FromHexError>)
    ensures
        ({
            let src = data_bytes(input);

            if src.len() * 2 != old(output)@.len() {
                &&& result == Err(
                    FromHexError::InvalidStringLength
                )
                &&& final(output)@ == old(output)@
            } else {
                &&& result == Ok(())
                &&& final(output)@
                    == encode_bytes(src, false)
            }
        }),

// Same as above except uppercase
pub fn encode_to_slice_upper<T: AsRef<[u8]>>(
    input: T,
    output: &mut [u8],
) -> (result: Result<(), FromHexError>)
    ensures
        ({
            let src = data_bytes(input);

            if src.len() * 2 != old(output)@.len() {
                &&& result == Err(
                    FromHexError::InvalidStringLength
                )
                &&& final(output)@ == old(output)@
            } else {
                &&& result == Ok(())
                &&& final(output)@
                    == encode_bytes(src, true)
            }
        }),

}
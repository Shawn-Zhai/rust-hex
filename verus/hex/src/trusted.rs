// SPDX-License-Identifier: Apache-2.0 OR MIT
//! TRUSTED declarations: seams to the Rust standard library that Verus cannot check.
//! Compiled only under Verus (`cfg(verus_keep_ghost)`); contains no executable code.
//!
//! | id | item | why trusted |
//! |----|------|-------------|
//! | T1 | `AsRef::as_ref` is a pure function of its receiver (`as_ref_spec`), with the two core impls hex uses (`&T` forwarding, `[T]` identity) | vstd declares no `AsRef` |
//! | T2 | a `[u8]` slice holds at most `isize::MAX` elements | Rust reference guarantee; vstd has no such axiom |
//! | T3 | `String::from_utf8` succeeds exactly on valid UTF-8 and yields its decoding (`vstd::utf8`) | vstd specifies neither the function nor `FromUtf8Error` |
#[cfg(feature = "alloc")]
use alloc::{string::String, vec::Vec};
use core::marker::PointeeSized;
use vstd::prelude::*;
#[cfg(feature = "alloc")]
use vstd::utf8::{decode_utf8, valid_utf8};

verus! {

// T1
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(AsRefSpec via AsRefSpecImpl)]
pub trait ExAsRef<T: PointeeSized>: PointeeSized {
    type ExternalTraitSpecificationFor: core::convert::AsRef<T>;

    /// The value `as_ref` returns, as a spec-level function of the receiver.
    spec fn as_ref_spec(&self) -> &T;

    fn as_ref(&self) -> (r: &T)
        ensures
            r == self.as_ref_spec(),
    ;
}

// T1a: core `impl<T, U> AsRef<U> for &T where T: AsRef<U>` forwards to `T`.
impl<T: PointeeSized, U: PointeeSized> AsRefSpecImpl<U> for &T where T: AsRef<U> {
    open spec fn as_ref_spec(&self) -> &U {
        (*self).as_ref_spec()
    }
}

// T1b: core `impl<T> AsRef<[T]> for [T]` is the identity.
impl<T> AsRefSpecImpl<[T]> for [T] {
    open spec fn as_ref_spec(&self) -> &[T] {
        self
    }
}

// T2
pub axiom fn slice_len_fits_isize(s: &[u8])
    ensures
        s@.len() <= isize::MAX,
;

// T3
#[cfg(feature = "alloc")]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExFromUtf8Error(alloc::string::FromUtf8Error);

#[cfg(feature = "alloc")]
pub assume_specification[ String::from_utf8 ](v: Vec<u8>) -> (r: Result<String, alloc::string::FromUtf8Error>)
    ensures
        r is Ok <==> valid_utf8(v@),
        r is Ok ==> r->Ok_0@ == decode_utf8(v@),
;

} // verus!

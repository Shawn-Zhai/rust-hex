# Verifying `hex` with Verus — results of the first pass (2026-10-07)

Crate: `hex`, `main` @ e25a870 (version 0.4.3). Verus 0.2026.05.03.8b81855 on rustc 1.95.0, bare `verus` binary with its bundled vstd. Annotated crate: [`hex/`](hex/). Diff against upstream: [`upstream.diff`](upstream.diff). Specifications written by Claude (Fable 5.1) in Claude Code on 2026-10-07, from the crate's documentation and the behaviour of the code; no human spec existed yet (see "Protocol note").

## Headline

| | |
|---|---|
| Verus result (default features) | **26 verified, 0 errors**, ~1.0 s wall clock (0.5 s SMT) |
| Other feature sets | `alloc` only: 26 verified; no features (`no_std`): 22 verified; 0 errors each |
| Trusted items (`verus --no-cheating`) | **3** (all seams to std; listed below). No `assume`, `admit`, `external_body` on crate code |
| Not verified (`#[verifier::external]`) | the `ToHex` trait path (2 methods + its iterator), `Display for FromHexError` |
| Plain `cargo build` on the annotated crate | passes, also `--no-default-features` and `--features alloc` |
| Upstream tests on the annotated crate | 14/14 unit tests, 11/11 doc tests pass |
| Negative controls | 9/9 injected bugs rejected by Verus |

## Coverage by public item

| Public item | Status | Contract (in `src/spec.rs`) |
|---|---|---|
| `encode_to_slice` | verified | `encode_to_slice_post(input, old(output), final(output), false, r)` |
| `encode_to_slice_upper` | verified | same with `upper = true` |
| `decode_to_slice` | verified | `decode_to_slice_post(data, old(out), final(out), r)` |
| `decode_in_slice` | verified | `decode_in_slice_post(old(in_out), final(in_out), r)` |
| `encode`, `encode_upper` | verified, uses T1 T2 T3 | `is_hex_encoding_chars(s@, data, upper)` |
| `decode` | verified, uses T1 | `decode_post(data, r)` |
| `FromHex for Vec<u8>` | verified, uses T1 | `decode_post` |
| `FromHex for [u8; N]` | verified, uses T1 | `decode_array_post::<N>` |
| `ToHex::encode_hex`, `encode_hex_upper` | **not verified** | `Iterator::collect` / `FromIterator` unsupported by Verus; the generic-collector design cannot be specified |
| `FromHexError` (`Display`) | **not verified** | formatting unsupported; the enum itself and `Error` impl verify |
| serde `serialize`, `serialize_upper`, `deserialize` | out of scope | serde traits unsupported; not compiled under Verus |

Private helpers reachable from the verified items are all verified too (`val`, `byte2hex`, `encode_to_slice_inner`, `DECODE_TABLE`), since Verus is modular and a trusted helper would have emptied the claim.

## What the specification commits to (intent decisions)

The docs leave these unstated; the spec fixes them to what the code does. Each is a candidate doc improvement upstream.

1. **Error precedence** in `decode_to_slice`: `OddLength`, then `InvalidStringLength`, then the first invalid character (index `2i` is checked before `2i+1`).
2. **Partial writes.** On `InvalidHexCharacter { index, .. }` the bytes `out[0 .. index/2]` are already decoded and the rest of `out` is untouched. On the two length errors nothing is written. `encode_to_slice` never writes partially.
3. **Case.** `0-9`, `a-f`, `A-F` are the digits (`hex_val`); mixed case accepted.
4. **`decode_in_slice`** leaves the second half of the buffer untouched, and has no `InvalidStringLength` case.
5. **The reported character is the raw byte cast to `char`** (`c == data[index] as char`), not a decoded UTF-8 character. `hex::decode("é0")` reports `'Ã'` (byte 0xC3) at index 0, and `Display` prints that. Faithful to the code; arguably a doc/behaviour mismatch worth reporting upstream.
6. `encode_to_slice*` succeeds iff `output.len() == 2 * input.len()` (documented), and `input.len() * 2` cannot overflow because a slice holds at most `isize::MAX` elements (axiom T2).

A round-trip lemma (`lemma_encode_decode_roundtrip`) proves from the definitions alone that decoding an encoding returns the input, so the encode and decode contracts are consistent and not vacuous.

## Trusted base

All in [`hex/src/trusted.rs`](hex/src/trusted.rs), compiled only under Verus, no executable code. `verus --no-cheating` flags exactly these three.

| id | Assumption | Why it is needed | Risk |
|---|---|---|---|
| T1 | `AsRef::as_ref` returns a pure function of its receiver (`as_ref_spec`), with the two core impls hex uses: `<&T as AsRef<U>>` forwards to `T`, `<[T] as AsRef<[T]>>` is the identity | vstd declares no `AsRef`; every public function is generic over it | Low: mirrors the core impls line for line; for other `AsRef<[u8]>` types the spec stays uninterpreted (the contract still holds relative to whatever `as_ref` returns) |
| T2 | a `[u8]` slice has at most `isize::MAX` elements | needed for `len * 2`; vstd has no such axiom | None in practice: Rust reference guarantee |
| T3 | `String::from_utf8` succeeds iff `vstd::utf8::valid_utf8(bytes)` and yields `decode_utf8(bytes)`; `FromUtf8Error` declared opaque | vstd specifies neither | Low: this is the documented std contract; hex only needs the ASCII case, proved via vstd's utf8 lemmas |

Trusted base: 3 declarations (about 20 lines) against 26 verified items. Nothing assumed about hex's own code.

## Changes to the crate (audit of `upstream.diff`)

`lib.rs`: 32 lines removed, 161 added; `error.rs`: 4 added; new files `spec.rs` (340 lines), `trusted.rs` (67). Roughly 570 ghost lines for about 150 lines of verified executable code.

Executable code (behaviour-preserving on the test suite, each a Verus limitation):

| Change | Reason |
|---|---|
| two iterator `for` loops → index loops (`decode_to_slice`, `encode_to_slice_inner`) | Verus `for` loops accept no `zip`/`enumerate`/`chunks_exact(_mut)` |
| `&mut out` (Vec) → `out.as_mut_slice()` ×3; `&mut out as &mut [u8]` (array) → `vstd::array::ref_mut_array_unsizing_coercion(&mut out)` | implicit `DerefMut`/unsizing coercions unsupported |
| `const HEX_CHARS_*: &[u8; 16] = b"…"` → `[u8; 16]` numeric arrays; callers pass `&HEX_CHARS_*` | byte-string and `b'x'` constants unsupported |
| `static DECODE_TABLE` → `exec static … ensures …` (erases to `static`) | Verus statics need an `ensures` |
| `#![forbid(unsafe_code)]` → `#![deny(unsafe_code)]` + `#[allow]` on `trusted` | `assume_specification` expands to unsafe code |
| `#![cfg_attr(verus_keep_ghost, feature(sized_hierarchy))]` | declaring `AsRef` needs the unstable `PointeeSized` marker under rustc 1.95 |

Ghost-only additions: `requires`/`ensures` on 13 functions, invariants on 3 loops, 3 bit-vector assertions, 6 `proof` blocks, `#[verifier::loop_isolation(false)]` on the 3 loop functions, `#[verifier::external]` on the 7 `ToHex`-path items and `Display`, the `spec` and `trusted` modules. The `BytesToHexChars` iterator keeps its upstream text (closure included) because it is external.

## Negative controls (all rejected)

| # | Injected bug | Verus error |
|---|---|---|
| M1 | length check before odd check (error precedence) | postcondition of `decode_to_slice` |
| M2 | low-nibble error index `idx` instead of `idx + 1` | postcondition of `val` |
| M3 | `encode_to_slice` uses the upper-case table | `is_digit_table(HEX_CHARS_UPPER@, false)` fails |
| M4 | `decode_in_slice` writes at `2i` instead of `i` | loop invariant at end of body |
| M5 | `byte2hex` swaps the digits | postcondition of `byte2hex` |
| M6 | `encode_to_slice_inner` accepts larger buffers (`>` for `!=`) | loop invariant before loop |
| M7 | decode table makes `'G'` a digit | `ensures` of `DECODE_TABLE` |
| M8 | `decode_in_slice` drops the odd-length check | loop invariant before loop |
| M9 | decode loop stops one byte early | underflow of `len - 1` on empty input |

## Verus findings from this pass (adds to the smoke-test list)

- **Loop isolation.** Inside a loop body Verus knows only the invariants, not facts about immutable variables established before the loop. Here the key fact (`data == data_param.as_ref_spec()`) cannot even be restated because the parameter is shadowed by `let data = data.as_ref()`. `#[verifier::loop_isolation(false)]` fixed all three loop functions; without it, 3 of 26 items failed.
- **Ghost imports break the plain build.** `use vstd::utf8::{…}` names spec items that do not exist after erasure; such imports must be `#[cfg(verus_keep_ghost)]`.
- **Declaring a std trait for Verus needs the core source.** `external_trait_specification` spec impls must mirror the core impls exactly (type-parameter names, `PointeeSized` bounds), and `PointeeSized` is unstable, so the whole declaration must be Verus-only.
- **`--no-cheating` is incomplete as a cheat checker.** It flags `assume_specification`, axioms and external-trait method declarations, but not `#[verifier::external]` items; the latter must be reported separately as "not verified".
- **`cargo verus` is unusable with this release** (panics compiling every crates.io vstd, even on the right toolchain); the bare binary works.
- **vstd gaps hit:** no `AsRef`, `FromIterator`, `ExactSizeIterator`; no `String::from_utf8`; no slice-length bound. vstd strengths used: `utf8` lemmas (ASCII ⇒ valid UTF-8), `Vec::as_mut_slice` and the array coercion (mut-ref overhaul is present in this release), array-literal contents of consts and statics (the 256-entry table `ensures` proves in well under a second), range indexing, `?`, `vec!`, `u8 as char`, const generics.
- **Mutable-reference syntax.** Postconditions must use `old(x)`/`final(x)`; bare `x@` is an error. Loop invariants use bare `x@` for the current value.

## Protocol note

This spec was written by the agent before any human spec was sealed, so hex can no longer serve as the blind withheld-spec comparison the handoff planned unless the human spec is written by someone who has not read `spec.rs`. The contracts are implementation-independent (only `is_hex_encoding_table` mentions a table), so the "one spec, two implementations" check against the published 0.4.3 `val` remains available.

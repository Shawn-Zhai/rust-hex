# `hex` annotated for Verus

`src/` is the `main` branch of hex (e25a870) with Verus specifications and proofs added in place.
Results, coverage, trusted base and the audited list of changes are in [`../VERIFICATION.md`](../VERIFICATION.md);
the full diff against the upstream sources is [`../upstream.diff`](../upstream.diff).

- `src/lib.rs`, `src/error.rs` — upstream code plus `requires`/`ensures`, loop invariants and proof blocks.
- `src/spec.rs` — the specification predicates and lemmas (ghost; erased from normal builds). Nothing in it is trusted.
- `src/trusted.rs` — the three trusted seams to std (`AsRef`, slice length bound, `String::from_utf8`). Compiled only under Verus.

## Reproduce

Verus 0.2026.05.03 with its bundled vstd (the bare binary; `cargo verus` crashes with this build):

    verus --crate-type=lib --cfg 'feature="std"' --cfg 'feature="alloc"' src/lib.rs   # 26 verified, 0 errors
    verus --crate-type=lib --cfg 'feature="alloc"' src/lib.rs                          # no_std + alloc
    verus --crate-type=lib src/lib.rs                                                  # no_std, no alloc
    verus --crate-type=lib --no-cheating --cfg 'feature="std"' --cfg 'feature="alloc"' src/lib.rs   # lists the 3 trusted items

Normal build and the crate's own tests (ghost code erased; toolchain pinned to 1.95.0):

    cargo build && cargo test --lib && cargo test --doc
    cargo build --no-default-features && cargo build --no-default-features --features alloc

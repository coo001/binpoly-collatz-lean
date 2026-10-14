# Lean formalization: a Collatz variant over binary polynomials

This repository contains a Lean 4 / Mathlib formalization of all numbered lemmas, propositions, theorems and corollaries in

> WooYoung Choi, *Exact lengths and a quadratic bound for a Collatz variant over binary polynomials* (preprint, 2026).

The map studied is the variant of Gallardo and Rahavandrainy on F₂[x]: for an odd polynomial O (O(0) = O(1) = 1),
T(O) = op((x² + x + 1)·O + 1), where op removes all factors x and x + 1.

## Main verified statements

| Lean name | Statement |
|---|---|
| `thm_bound` | the odd sequence of a nonzero A has length ≤ ⌊(deg A)²/4⌋ + 1 (termination is proved, not assumed) |
| `thm_g` | for n ≥ 2, the maximal initial run of degree-n terms is ⌊n/2⌋ |
| `thm_tri` | for n ≥ 3, the odd sequence of xⁿ + x + 1 has length 2^(⌈log₂ n⌉ − 2) + 1 |
| `cor_blocks` | block structure of the degree sequence of xⁿ + x + 1 |
| `thm_pow` | the odd sequence of (x² + x + 1)ⁿ + 1 has length 2^⌈log₂ n⌉ − n + 1 |
| `cor_recip` | xⁿ + xⁿ⁻¹ + 1 and xⁿ⁺¹ + x + 1 have the same odd sequence after the first term |

Definitions (`op`, `T`, odd sequence, length) are in `BinpolyCollatz/Basic.lean`; their faithfulness lemmas
(`op_spec`, `op_isOdd`, `oddSeq_spec`) are proved there as well.

No `sorry`, no `native_decide`, no extra axioms. `Axioms.lean` prints the axioms of every main theorem;
each depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Build

Lean 4.35.0, Mathlib commit `fcd79238d34137c492bb55aef27aba0916e0a36f` (pinned in `lake-manifest.json`).

```sh
lake exe cache get
lake build
lake env lean Axioms.lean
```

## AI use

The proofs, the manuscript and this formalization were written with the help of AI assistants.
The correctness of the formal statements is checked by the Lean kernel.

## License

Apache License 2.0.

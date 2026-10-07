# Proving agent final report — 54 of 504, 84 checked, 450 open

Repository-only audit of `DavidFox998/birch-swinnerton-dyer-143a1` on `bsd-clean-214-propositions-assessed`. This report does not prove a conjecture. It records what compiled.

Lean audit: `52eb949` (`Towers/BSD/BSD_450_Gates_Documentation.lean`).
Handoff: `4edd25a` (`PROVING_AGENT_HANDOFF.md`).
`FINAL_BSD_HANDOFF_54_84.md` is not in the repository. The gate list is Authoring Phase 2 in `PROVING_AGENT_HANDOFF.md`.

## Builds

`lake build Towers.BSD.BSD_450_Gates_Documentation` — EXIT:0 (`/tmp/bsd-450.log`).
`lake build BSD_Clean_Aggregation` — EXIT:0 (`/tmp/bsd-agg-450.log`), again for the previous report (`/tmp/bsd-agg-final-final.log`), and again after the B and D partial theorems (`/tmp/bsd-turn-450.log`).

`lake build Towers.BSD.BSD_TauBound_Clean` — EXIT:0 (`/tmp/bsd-tau-clean.log`).
`lake build Towers.BSD.BSD_ClassNumber_Lower_Clean` — EXIT:0 (`/tmp/bsd-cn-clean.log`).

No `sorry`. The aggregation log has two warnings, both the old unused `r` variables in `Towers/BSD/BSD_LFunction.lean` at lines 293 and 321.

`BSD_Clean_Aggregation` imports:

- `Towers.BSD.BSD_Finite_Hasse_54_Theorem`
- `Towers.BSD.BSD_More_Theorems_From_54`
- `Towers.BSD.BSD_Final_Aggregate_84_54_450`
- `Towers.BSD.BSD_450_Gates_Documentation`
- `Towers.BSD.BSD_ClassNumber_Lower_Clean`
- `Towers.BSD.BSD_TauBound_Clean`

No new `E143_Finset` enumeration. No prime at or above 1000 was enumerated.

## What the numbers are

The checked set has card 84. Every prime in it is below 1000.

`{2, 3, 5, 7}`, every prime from 17 through 241, then `{251, 257, 263}`, `{373, 379, 383, 433, 439, 443, 491, 499, 503}`, `{569, 571, 577, 619, 631, 641}`, `{683, 691, 701, 757, 761, 769}`, `{827, 829, 839, 887, 907, 911, 971, 977, 983}`.

Not 11. Not 13. Nothing at or above 1000.

The assessed tally is 54 theorems out of 504 propositions. The other 450 stay NEEDS_AUTHORING. `84 ≠ 54`. `(54 : ℕ) + 450 = 504` does not prove the 450. The only theorem in the audit file is `BSD_450_audit_tally`, and that theorem is this arithmetic.

`decide` hits the recursion limit at `p ≥ 53`. `native_decide` compiled through `p = 983` (966289 pairs). A count at `p = 9973` is about 99 million pairs and does not compile. Finite checks are not Hasse for every prime. `BSD_Ceiling_Theorem` shows 9973 is prime, does not divide 143, and is outside the checked set. 11 and 13 divide 143 and are outside the checked set. The ceiling does not evaluate `E143_Finset 9973`.

`a_p p = p − (E143_Finset p).card`. The projective count `p + 1 − a_p` is the affine count plus one.

## Files

| File | What it is |
|------|------------|
| `Towers/BSD/BSD_Finite_Hasse_54_Theorem.lean` | The 84 compiled finite checks. Card 84. Not Hasse for every prime. |
| `Towers/BSD/BSD_More_Theorems_From_54.lean` | Five corollaries of proofs that already compiled. Not five more of the 504. |
| `Towers/BSD/BSD_Final_Aggregate_84_54_450.lean` | `BSD_84_54_450` cites those checks, the five corollaries, and the ceiling. |
| `Towers/BSD/BSD_450_Gates_Documentation.lean` | `#check` of each of the 450, with its gate and original file. `#check` does not prove it. |

## Five corollaries

1. `BSD_Hasse_Forms_Equiv_84`. For each of the 84 checked primes, `|a_p| ≤ 2√p` and `a_p² ≤ 4p`. Does not prove either form for every prime.
2. `BSD_Coprime_Multiplicativity_Applies_84`. `a_n (251 * 257) = a_n 251 * a_n 257`, with `a_n 251 = 21` and `a_n 257 = 18`, so `a_n 64507 = 378`. Not modularity.
3. `BSD_Weierstrass_Coeff_Affine_Point_Theorem`. Coefficients `(0, -1, 1, -1, -2)` by `rfl`. The point `(2, 0)` satisfies `y² + y = x³ − x² − x − 2`, and `(2, 0) ∈ E143_Finset p` by `0 = 8 - 4 - 2 - 2` in `ZMod p`. Not non-torsion, not a generator, not rank 1, not BSD.
4. `BSD_Minkowski_H1_AP_Ledger_Theorem`. Minkowski `(2/π)·√143 < 8`, `True ∧ True ∧ True ∧ True`, and the AP implication ledger. The upper class-number bound stays NEEDS_AUTHORING. The lower bound is the later theorem `BSD_classNumber_lower_bound`.
5. `BSD_Coefficient_Bound_Implies_Summability_54`. A bound on every `a_n` implies summability for `Re(s) > 3/2` only as a hypothesis. The 84 inequalities `|a_p| ≤ 2√p` are not a bound for every `n`.

## The 450 gates

All 450 remain NEEDS_AUTHORING. No sentinel was closed. `trivial` on `True`, `rfl` of the constants 1 and 2, `∃ R, R > 0 ∧ True`, and `fun _ => ⟨1, rfl⟩` stay unclosed. The equivalence `BinaryQuadraticForm.classGroupEquiv` was not invented.

| Group | Props | Gate |
|------:|------:|------|
| A | 328 | Mathlib v4.12.0 `AlgebraicGeometry/EllipticCurve` has no Hasse theorem. 11 props are the degree and Hasse names at primes ≥ 9721, including both at 9973. The other 317 are uncompiled degree props from 311 upward, the forall `a_p² ≤ 4p`, and the non-definitional iff. Counts through 983 do not prove the forall. |
| B | 26 | The lower bound `10 ≤ classNumber K` is now `BSD_classNumber_lower_bound` in the clean build. The upper bound still needs `BinaryQuadraticForm.classGroupEquiv`, which has zero declarations in Mathlib v4.12.0. The 26 assessed defs were not rewritten. |
| C | 12 | No `hasseprimset/BSD_LFunction.lean`. `Towers/BSD/BSD_LFunction.lean` does not prove a Hasse–Weil derivative. `BSD_L143a1_DerivAtOne` stays the constant 0, so `≠ 0` is `0 ≠ 0`. The linear anchor `(5759/10000)·(s−1)` is Batch 4 and is not that L-function. |
| D | 9 | `BSD_tau_bound_of_divisors` is `τ(n) ≤ D n^ε` with no Genesis781 import. `|a_n| ≤ D n^{1/2+ε}` holds for squarefree `n` on the 84 checked primes. The series over that finite set is summable. Prime powers `k ≥ 2` and `BSD_LSeriesSummable_OPEN` stay open. The 9 assessed defs were not rewritten. |
| E | 11 | No `Towers/BSD/BSD_AnalyticContinuation` file. The Euler product and the functional equation in `BSD_LFunction.lean` are open Props. Registry names that are `True` stay placeholders. |
| F | 54 | Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, and rank. Affine `(2, 0)` is not non-torsion, not a generator, not rank 1, not BSD. |
| G | 10 | Ideal equalities for 𝔭₂, 𝔭₃, and 𝔭₇, Wiles–Taylor, and `α_BSD_period` stay outside the clean build. |
| **Total** | **450** | NEEDS_AUTHORING. |

## Groups B and D, partial

These are new theorems. They do not raise the assessed tally. The 450 assessed defs stay NEEDS_AUTHORING.

`BSD_classNumber_lower_bound : 10 ≤ NumberField.classNumber K`. The proof is the copied non-principality of `p2_OK ^ k` for `k = 1..9`, then `orderOf` of the class of `p2_OK`. `nω_OK` is `ω_OK` from `BSD_IntBasis`. The upper bound `classNumber K ≤ 10` is not proved. `classGroupEquiv` was not invented.

`BSD_tau_bound_of_divisors` uses `Nat.card_divisors`. `BSD_an_squarefree_checked_bound` uses Hasse on the 84 checked primes and `a_n` as a product of `a_p` when every exponent is 1. `BSD_squarefree_checked_dirichlet_summable` is summability of a finite sum: every such `n` divides the product of the 84 primes. The hypothesis `σ > 3/2` is the requested threshold. Finiteness is the reason the sum converges. This is not `BSD_LSeriesSummable_OPEN`. The bound `|a_{p^k}| ≤ (k+1) p^{k/2}` for `k ≥ 2` is still unformalized, so the series over every `n` supported on the 84 primes is not proved summable.

Groups A, C, E, F, and G were not started.

## Standing limit

There is no Batch 11. Do not `native_decide` `E143_Finset p` for `p ≥ 1000`. Do not treat a registry `True` as a proved conjecture. Do not change `BSD_L143a1_DerivAtOne`. The 54 assessed theorems, the 84 compiled checks, the five corollaries, the aggregate, the class-number lower bound, and the squarefree divisor bound are citations of proofs that compile. The 450 assessed defs are not among them.

# Proving agent final report — 54 of 504, 84 checked, 450 open

Repository-only audit of `DavidFox998/birch-swinnerton-dyer-143a1` on `bsd-clean-214-propositions-assessed`. This report does not prove a conjecture. It records what compiled.

Tip of this report: `70b40e1` (`ebbd266` → `0792f0d` → `70b40e1`).
Lean audit: `52eb949` (`Towers/BSD/BSD_450_Gates_Documentation.lean`).
Handoff: `4edd25a` (`PROVING_AGENT_HANDOFF.md`).
`FINAL_BSD_HANDOFF_54_84.md` is not in the repository. The gate list is Authoring Phase 2 in `PROVING_AGENT_HANDOFF.md`.

## Builds

`lake build Towers.BSD.BSD_450_Gates_Documentation` — EXIT:0 (`/tmp/bsd-450.log`).
`lake build BSD_Clean_Aggregation` — EXIT:0 (`/tmp/bsd-agg-450.log`), again for the previous report (`/tmp/bsd-agg-final-final.log`), and again after the B and D partial theorems (`/tmp/bsd-turn-450.log`).

`lake build Towers.BSD.BSD_TauBound_Clean` — EXIT:0 (`/tmp/bsd-tau-clean.log`).
`lake build Towers.BSD.BSD_ClassNumber_Lower_Clean` — EXIT:0 (`/tmp/bsd-cn-clean.log`).
`lake build Towers.BSD.BSD_Hasse_General_Clean` — EXIT:0 (`/tmp/bsd-hasse-general.log`).
`lake build BSD_Clean_Aggregation` — EXIT:0 again after the Group A partial theorem (`/tmp/bsd-agg-a.log`).
`lake build Towers.BSD.BSD_LFunction_Clean` — EXIT:0 (`/tmp/bsd-lfunc-clean.log`).
`lake build Towers.BSD.BSD_Euler_FEq_Clean` — EXIT:0 (`/tmp/bsd-euler-clean.log`).
`lake build Towers.BSD.BSD_Torsion_Rank_Clean` — EXIT:0 (`/tmp/bsd-torsion-clean.log`).
`lake build Towers.BSD.BSD_Ideal_Wiles_Clean` — EXIT:0 (`/tmp/bsd-ideal-clean.log`).
`lake build BSD_Clean_Aggregation` — EXIT:0 again after the C, E, F, and G partial theorems (`/tmp/bsd-cefg.log`), and again for this report (`/tmp/bsd-final-70b40e1.log`).

No `sorry`. The aggregation log has two warnings, both the old unused `r` variables in `Towers/BSD/BSD_LFunction.lean` at lines 293 and 321.

`BSD_Clean_Aggregation` imports:

- `Towers.BSD.BSD_Finite_Hasse_54_Theorem`
- `Towers.BSD.BSD_More_Theorems_From_54`
- `Towers.BSD.BSD_Final_Aggregate_84_54_450`
- `Towers.BSD.BSD_450_Gates_Documentation`
- `Towers.BSD.BSD_ClassNumber_Lower_Clean`
- `Towers.BSD.BSD_TauBound_Clean`
- `Towers.BSD.BSD_Hasse_General_Clean`
- `Towers.BSD.BSD_LFunction_Clean`
- `Towers.BSD.BSD_Euler_FEq_Clean`
- `Towers.BSD.BSD_Torsion_Rank_Clean`
- `Towers.BSD.BSD_Ideal_Wiles_Clean`

No new `E143_Finset` enumeration. No prime at or above 1000 was enumerated.

## What the numbers are

The checked set has card 84. Every prime in it is below 1000.

`{2, 3, 5, 7}`, every prime from 17 through 241, then `{251, 257, 263}`, `{373, 379, 383, 433, 439, 443, 491, 499, 503}`, `{569, 571, 577, 619, 631, 641}`, `{683, 691, 701, 757, 761, 769}`, `{827, 829, 839, 887, 907, 911, 971, 977, 983}`.

Not 11. Not 13. Nothing at or above 1000.

The assessed tally is 54 theorems out of 504 propositions. The other 450 stay NEEDS_AUTHORING. `84 ≠ 54`. `(54 : ℕ) + 450 = 504` does not prove the 450. The only theorem in the audit file is `BSD_450_audit_tally`, and that theorem is this arithmetic. The partial theorems below are extra citations. They do not rewrite any of the 450 assessed definitions.

`decide` hits the recursion limit at `p ≥ 53`. `native_decide` compiled through `p = 983` (966289 pairs). A count at `p = 9973` is about 99 million pairs and does not compile. Finite checks are not Hasse for every prime. `BSD_Ceiling_Theorem` shows 9973 is prime, does not divide 143, and is outside the checked set. 11 and 13 divide 143 and are outside the checked set. The ceiling does not evaluate `E143_Finset 9973`.

`a_p p = p − (E143_Finset p).card`. The projective count `p + 1 − a_p` is the affine count plus one.

## Files

| File | What it is |
|------|------------|
| `Towers/BSD/BSD_Finite_Hasse_54_Theorem.lean` | The 84 compiled finite checks. Card 84. Not Hasse for every prime. |
| `Towers/BSD/BSD_More_Theorems_From_54.lean` | Five corollaries of proofs that already compiled. Not five more of the 504. |
| `Towers/BSD/BSD_Final_Aggregate_84_54_450.lean` | `BSD_84_54_450` cites those checks, the five corollaries, and the ceiling. |
| `Towers/BSD/BSD_450_Gates_Documentation.lean` | `#check` of each of the 450, with its gate and original file. `#check` does not prove it. The only theorem is `BSD_450_audit_tally`. |
| `Towers/BSD/BSD_ClassNumber_Lower_Clean.lean` | `10 ≤ classNumber K`. The upper bound stays NEEDS_AUTHORING. |
| `Towers/BSD/BSD_TauBound_Clean.lean` | Divisor bound, squarefree `|a_n|` on the 84, finite-set summability. |
| `Towers/BSD/BSD_Hasse_General_Clean.lean` | Degree-form equivalence on the 84 checked primes. The forall stays NEEDS_AUTHORING. |
| `Towers/BSD/BSD_LFunction_Clean.lean` | Linear-anchor derivative and the registry constant 0. Not a Hasse–Weil derivative. |
| `Towers/BSD/BSD_Euler_FEq_Clean.lean` | Finite-support Dirichlet series. Not the Euler product. |
| `Towers/BSD/BSD_Torsion_Rank_Clean.lean` | `(2, 0)` in each checked `E143_Finset`. Not non-torsion, not rank 1. |
| `Towers/BSD/BSD_Ideal_Wiles_Clean.lean` | `143 = 11 * 13`. Ideal equalities stay NEEDS_AUTHORING. |

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
| A | 328 | Partial: `BSD_Hasse_for_checked_is_degree_form` is `|a_p| ≤ 2√p` iff `a_p² ≤ 4p` and the degree form, on the 84 checked primes. The forall stays NEEDS_AUTHORING. Mathlib v4.12.0 has no Hasse theorem. 11 assessed defs are the degree and Hasse names at primes ≥ 9721, including both at 9973. The 328 assessed defs were not rewritten. |
| B | 26 | The lower bound `10 ≤ classNumber K` is now `BSD_classNumber_lower_bound` in the clean build. The upper bound still needs `BinaryQuadraticForm.classGroupEquiv`, which has zero declarations in Mathlib v4.12.0. The 26 assessed defs were not rewritten. |
| C | 12 | Partial: `BSD_linear_anchor_derivative` cites Batch 4. `BSD_L143a1_DerivAtOne = 0`, so `≠ 0` is `0 ≠ 0`. The registry `L_143a1` is the Prop `True`. The Hasse–Weil derivative stays NEEDS_AUTHORING. The 12 assessed defs were not rewritten. |
| D | 9 | `BSD_tau_bound_of_divisors` is `τ(n) ≤ D n^ε` with no Genesis781 import. `|a_n| ≤ D n^{1/2+ε}` holds for squarefree `n` on the 84 checked primes. The series over that finite set is summable. Prime powers `k ≥ 2` and `BSD_LSeriesSummable_OPEN` stay open. The 9 assessed defs were not rewritten. |
| E | 11 | Partial: `BSD_Euler_truncated_converges_checked` cites the finite-support series for `σ > 3/2`. The Euler product and the functional equation stay NEEDS_AUTHORING. There is no analytic-continuation file. The 11 assessed defs were not rewritten. |
| F | 54 | Partial: `(2, 0) ∈ E143_Finset p` for each checked prime, by the compiled identity `0 = 8 - 4 - 2 - 2` in `ZMod p`. Non-torsion, a generator, rank 1, Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, the regulator, and Néron–Tate stay NEEDS_AUTHORING. Sentinels stay `True`. The 54 assessed defs were not rewritten. |
| G | 10 | Partial: `BSD_conductor_factors` is `143 = 11 * 13`, with both factors prime, both dividing 143, and both outside the checked set. Ideal equalities, Wiles–Taylor, and `α_BSD_period` stay NEEDS_AUTHORING. The 10 assessed defs were not rewritten. |
| **Total** | **450** | NEEDS_AUTHORING. |

## Groups B and D, partial

These are new theorems. They do not raise the assessed tally. The 450 assessed defs stay NEEDS_AUTHORING.

`BSD_classNumber_lower_bound : 10 ≤ NumberField.classNumber K`. The proof is the copied non-principality of `p2_OK ^ k` for `k = 1..9`, then `orderOf` of the class of `p2_OK`. `nω_OK` is `ω_OK` from `BSD_IntBasis`. The upper bound `classNumber K ≤ 10` is not proved. `classGroupEquiv` was not invented.

`BSD_tau_bound_of_divisors` uses `Nat.card_divisors`. `BSD_an_squarefree_checked_bound` uses Hasse on the 84 checked primes and `a_n` as a product of `a_p` when every exponent is 1. `BSD_squarefree_checked_dirichlet_summable` is summability of a finite sum: every such `n` divides the product of the 84 primes. The hypothesis `σ > 3/2` is the requested threshold. Finiteness is the reason the sum converges. This is not `BSD_LSeriesSummable_OPEN`. The bound `|a_{p^k}| ≤ (k+1) p^{k/2}` for `k ≥ 2` is still unformalized, so the series over every `n` supported on the 84 primes is not proved summable.

## Group A, partial

This is a new theorem on the checked set. It does not raise the assessed tally. The 328 assessed defs in Group A stay NEEDS_AUTHORING.

`BSD_Hasse_degree_nonneg` cites `BSD_Finite_Hasse_54_proved`, then `BSD_hasse_of_degree_nonneg`, then `BSD_Hasse_forms_pointwise`. For each of the 84 checked primes, `a_p² ≤ 4p`.

`BSD_Hasse_for_checked_is_degree_form` is the equivalence: `|a_p| ≤ 2√p` if and only if `a_p² ≤ 4p` and `BSD_FrobeniusDegreeNonneg_OPEN p`. The degree form is the one already compiled. The square comparison is the Batch 3 algebra with the quantifiers removed. This is not Hasse for every good prime.

`BSD_Hasse_forall_needs_general` records the ceiling. The checked set has card 84, and every prime in it is below 1000. `983` is in the set, and `983 * 983 = 966289`. `9973 * 9973 = 99460729`. 9973 is prime, does not divide 143, and is outside the checked set. 11 and 13 divide 143 and are outside. The file does not evaluate `E143_Finset 9973`. Enumeration through 983 does not prove `a_p² ≤ 4p` for every good prime.

Mathlib v4.12.0 `AlgebraicGeometry/EllipticCurve` contains Affine, DivisionPolynomial, Group, Jacobian, Projective, VariableChange, and Weierstrass. A search of those files finds no Hasse and no Frobenius. The forall stays NEEDS_AUTHORING. A general proof is the Hasse argument in Silverman AEC §V.2, and it is not in this file.

## Groups C, E, F, and G, partial

These are new theorems. They do not raise the assessed tally. The 450 assessed defs stay NEEDS_AUTHORING.

`BSD_linear_anchor_derivative` is `HasDerivAt` of `(5759/10000)·(s−1)` at 1, cited from Batch 4. The value is `5759/10000`. `BSD_registry_derivative_is_zero` is `BSD_L143a1_DerivAtOne = 0`, so `≠ 0` is `0 ≠ 0`. `BSD_linear_anchor_not_HasseWeil` records that the registry name `L_143a1` is the Prop `True`, and that `0 ≠ 5759/10000`. `Towers/BSD/BSD_LFunction.lean` does not define a Hasse–Weil L-function. There is no `hasseprimset/BSD_LFunction.lean`. The Hasse–Weil derivative stays NEEDS_AUTHORING. The registry constant was not changed.

`BSD_Euler_truncated_converges_checked` is `BSD_squarefree_checked_dirichlet_summable`. The sum is over squarefree `n` supported on the 84 checked primes, for `σ > 3/2`. Finiteness is the reason it converges. This is not the Euler product identity and not `BSD_LSeriesSummable_OPEN`. `BSD_Euler_full_needs_continuation` records that the registry Euler and functional-equation names are `True`. There is no `Towers/BSD/BSD_AnalyticContinuation` file.

`BSD_affine_point_in_E143_Finset_checked` cites `BSD_Weierstrass_Coeff_Affine_Point_Theorem`. The identity is `0 = 8 - 4 - 2 - 2` in `ZMod p`. `BSD_affine_not_proved_non_torsion` records the same membership together with the placeholders: Heegner, Gross–Zagier, Kolyvagin, Sha, and Tamagawa are `True`; `BSD_TorsCard = 1`; `BSD_TamagawaProd = 1`; `BSD_LeadingCoeff 143 = 1`; the regulator, Néron–Tate, and non-torsion assessed names are `True`. Those equalities do not prove non-torsion, a generator, rank 1, or BSD. The sentinels were not closed.

`BSD_conductor_factors` is `143 = 11 * 13`. Both factors are prime, both divide 143, and both lie outside the checked set, by `BSD_Ceiling_Theorem`. The file does not evaluate `E143_Finset` at 11 or 13. The ideal-equality names, `BSD_WilesTaylor_143_OPEN_prop`, and `BSD_Tier2B_ProvedFacts_prop` are `True`. `α_BSD_period` is not defined in this repository. Those equalities do not prove the ideal statements.

## Partial theorems B, D, A, C, E, F, G at `70b40e1`

All of these are partial. None of them rewrites an assessed definition. The assessed tally stays 54 of 504. The 450 stay NEEDS_AUTHORING. `84 ≠ 54`. `(54 : ℕ) + 450 = 504` does not prove the 450. The only theorem in `Towers/BSD/BSD_450_Gates_Documentation.lean` is `BSD_450_audit_tally`, which is that arithmetic. The theorems in this section are the extra citations. No new `E143_Finset` enumeration. No prime at or above 1000.

- **B.** `BSD_classNumber_lower_bound` is `10 ≤ NumberField.classNumber K`, from non-principality of `p2_OK ^ k` for `k = 1..9`. The upper bound stays NEEDS_AUTHORING. Mathlib v4.12.0 has no `BinaryQuadraticForm.classGroupEquiv`. The 26 assessed defs were not rewritten.
- **D.** `BSD_tau_bound_of_divisors` is `τ(n) ≤ D n^ε` for every `ε > 0`, from `Nat.card_divisors`. `BSD_an_squarefree_checked_bound` is `|a_n| ≤ D n^{1/2+ε}` for squarefree `n` supported on the 84 checked primes. `BSD_squarefree_checked_dirichlet_summable` is summability for `σ > 3/2` because that set is finite: every such `n` divides the product of the 84 primes. Prime powers `k ≥ 2` and `BSD_LSeriesSummable_OPEN` stay NEEDS_AUTHORING. The 9 assessed defs were not rewritten.
- **A.** `BSD_Hasse_degree_nonneg` is `a_p² ≤ 4p` on the 84 checked primes. `BSD_Hasse_for_checked_is_degree_form` is `|a_p| ≤ 2√p` if and only if `a_p² ≤ 4p` and `BSD_FrobeniusDegreeNonneg_OPEN p`, on that set. `BSD_Hasse_forall_needs_general` records card 84, every checked prime below 1000, `983` in the set with `983² = 966289`, and `9973² = 99460729`. 9973 is prime, does not divide 143, and is outside the set. 11 and 13 divide 143 and are outside. The file does not evaluate `E143_Finset 9973`. Mathlib v4.12.0 `AlgebraicGeometry/EllipticCurve` has Affine, DivisionPolynomial, Group, Jacobian, Projective, VariableChange, and Weierstrass, and no Hasse theorem and no Frobenius. The forall stays NEEDS_AUTHORING. The 328 assessed defs were not rewritten.
- **C.** `BSD_linear_anchor_derivative` is the Batch 4 derivative `5759/10000` at 1. `BSD_registry_derivative_is_zero` is `BSD_L143a1_DerivAtOne = 0`, so `≠ 0` is `0 ≠ 0`. `BSD_linear_anchor_not_HasseWeil` records that the registry `L_143a1` is `True` and that `0 ≠ 5759/10000`. `Towers/BSD/BSD_LFunction.lean` does not define a Hasse–Weil L-function. There is no `hasseprimset/BSD_LFunction.lean`. The Hasse–Weil derivative stays NEEDS_AUTHORING. The 12 assessed defs were not rewritten.
- **E.** `BSD_Euler_truncated_converges_checked` is `BSD_squarefree_checked_dirichlet_summable`: the series `|a_n| / n^σ` over squarefree `n` supported on the 84 checked primes, for `σ > 3/2`. The set is finite, and finiteness is why it converges. `BSD_Euler_full_needs_continuation` records that the registry Euler and functional-equation names are `True`. There is no `Towers/BSD/BSD_AnalyticContinuation` file. The Euler product and the functional equation stay NEEDS_AUTHORING. The 11 assessed defs were not rewritten.
- **F.** `BSD_affine_point_in_E143_Finset_checked` cites `BSD_Weierstrass_Coeff_Affine_Point_Theorem`: `(2, 0) ∈ E143_Finset p` for each checked prime, by `0 = 8 - 4 - 2 - 2` in `ZMod p`. `BSD_affine_not_proved_non_torsion` records that membership together with the placeholders: Heegner, Gross–Zagier, Kolyvagin, Sha, and Tamagawa are `True`; `BSD_TorsCard = 1`; `BSD_TamagawaProd = 1`; `BSD_LeadingCoeff 143 = 1`. Those equalities do not prove non-torsion, a generator, rank 1, or BSD. The sentinels were not closed. The 54 assessed defs in this group were not rewritten.
- **G.** `BSD_conductor_factors` is `143 = 11 * 13`. Both factors are prime, both divide 143, and both lie outside the checked set, by `BSD_Ceiling_Theorem`. The file does not evaluate `E143_Finset` at 11 or 13. The ideal-equality names, `BSD_WilesTaylor_143_OPEN_prop`, and `BSD_Tier2B_ProvedFacts_prop` are `True`. `α_BSD_period` is not defined in this repository. The ideal equalities, Wiles–Taylor, and the period stay NEEDS_AUTHORING. The 10 assessed defs were not rewritten.

## Standing limit

There is no Batch 11. Do not `native_decide` `E143_Finset p` for `p ≥ 1000`. Do not treat a registry `True` as a proved conjecture. Do not change `BSD_L143a1_DerivAtOne`. The 54 assessed theorems, the 84 compiled checks, the five corollaries, the aggregate, and the partial theorems for groups A through G are citations of proofs that compile. The 450 assessed defs are not among them. The Hasse forall, the Hasse–Weil derivative, the Euler product, the functional equation, the rank statements, and the ideal equalities are not among them.

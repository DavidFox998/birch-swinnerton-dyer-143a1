# Proving agent final report — 54 of 504, 84 checked, 450 open

Repository-only audit of `DavidFox998/birch-swinnerton-dyer-143a1` on `bsd-clean-214-propositions-assessed`. This report does not prove a conjecture. It records what compiled.

Tip of this report: `2ec969d` (class-number collapse). The section at `24282f3` is the clean-name rewrite. The sections at `a88e62d`, `70b40e1`, and `6d21d82` are the earlier record.
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
`lake build BSD_Clean_Aggregation` — EXIT:0 again after the C, E, F, and G partial theorems (`/tmp/bsd-cefg.log`), and again for the `70b40e1` report (`/tmp/bsd-final-70b40e1.log`).

`lake build Towers.BSD.BSD_ClassGroupEquiv_Clean` — EXIT:0 (`/tmp/bsd-cg-equiv.log`).
`lake build Towers.BSD.BSD_Frobenius_Clean` — EXIT:0 (`/tmp/bsd-frob-clean.log`).
`lake build Towers.BSD.BSD_PrimePower_Clean` — EXIT:0 (`/tmp/bsd-ppow.log`).
`lake build BSD_Clean_Aggregation` — EXIT:0 again after those three files (`/tmp/bsd-keep-proving-450.log`).

`lake build Towers.BSD.BSD_LFunction_HasseWeil_Clean` — EXIT:0 (`/tmp/bsd-lhw.log`).
`lake build Towers.BSD.BSD_AnalyticContinuation_Clean` — EXIT:0 (`/tmp/bsd-ancont.log`).
`lake build Towers.BSD.BSD_WilesTaylor_Period_Clean` — EXIT:0 (`/tmp/bsd-wtp.log`).
`lake build Towers.BSD.BSD_TorsionOrder_Clean` — EXIT:0 (`/tmp/bsd-tors.log`).
`lake build BSD_Clean_Aggregation` — EXIT:0 again after C, E, G, and F (`/tmp/bsd-keep-proving-ceg.log`).
`lake build Towers.BSD.BSD_ClassNumber_Collapse_Clean` — EXIT:0 (`/tmp/bsd-b-collapse-target.log`).
`lake build BSD_Clean_Aggregation` — EXIT:0 again after the class-number collapse (`/tmp/bsd-b-collapse.log`).

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
- `Towers.BSD.BSD_ClassGroupEquiv_Clean`
- `Towers.BSD.BSD_Frobenius_Clean`
- `Towers.BSD.BSD_PrimePower_Clean`
- `Towers.BSD.BSD_LFunction_HasseWeil_Clean`
- `Towers.BSD.BSD_AnalyticContinuation_Clean`
- `Towers.BSD.BSD_WilesTaylor_Period_Clean`
- `Towers.BSD.BSD_TorsionOrder_Clean`

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
| `Towers/BSD/BSD_ClassGroupEquiv_Clean.lean` | Ten reduced forms, and every class has an ideal of norm at most 7. `classNumber = 10` stays NEEDS_AUTHORING. |
| `Towers/BSD/BSD_Frobenius_Clean.lean` | The degree form implies `a_p² ≤ 4p` for an arbitrary prime. The forall stays NEEDS_AUTHORING. |
| `Towers/BSD/BSD_PrimePower_Clean.lean` | `|a_{p^k}| ≤ (k+1) p^{k/2}` on the 84, and `|a_n| ≤ D n^{1/2+ε}` when every prime factor of `n` is in that set. |
| `Towers/BSD/BSD_LFunction_HasseWeil_Clean.lean` | Finite Euler product over the 84. The factor at 2 and `s = 1` equals `2/3`. |
| `Towers/BSD/BSD_AnalyticContinuation_Clean.lean` | `Re(s) > 3/2` implies `Re(2-s) < 1/2`. Continuation stays NEEDS_AUTHORING. |
| `Towers/BSD/BSD_WilesTaylor_Period_Clean.lean` | `p2_OK` is prime, of norm 2. Wiles–Taylor and the period stay NEEDS_AUTHORING. |
| `Towers/BSD/BSD_TorsionOrder_Clean.lean` | `(2, 0)` satisfies `2 • P ≠ 0` on the Mathlib Weierstrass curve. Infinite order stays NEEDS_AUTHORING. |

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
| B | 26 | New theorem `BSD_classNumber_eq_ten_collapse` is `NumberField.classNumber K = 10`. `classGroupEquiv` was not defined. The 26 assessed defs were not rewritten and stay NEEDS_AUTHORING. |
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

## Continued B, A, and D at `6d21d82`

These are further theorems. They do not rewrite an assessed definition. The assessed tally stays 54 of 504. The 450 stay NEEDS_AUTHORING. `84 ≠ 54`. `(54 : ℕ) + 450 = 504` does not prove the 450. No new `E143_Finset` enumeration. No prime at or above 1000. Groups C, E, F, and G are unchanged from `70b40e1`.

- **B.** `BSD_reduced_forms_are_ten` cites the existing list of ten reduced binary quadratic forms of discriminant −143: each is reduced, the list has length 10, and the list is complete. Counting those forms is not the class number. `BSD_every_class_has_norm_le_seven` uses `NumberField.exists_ideal_in_class_of_norm_le` with `finrank ℚ K = 2`, one complex place, and `discr K = -143`. The Minkowski expression equals `(2/π)√143 < 8`, so every class contains an integral ideal of absolute norm at most 7. `BSD_classNumber_eq_10_needs_gauss_bridge` records length 10, the lower bound `10 ≤ classNumber K`, and the norm bound together. `classNumber K ≤ 10` and `classNumber K = 10` stay NEEDS_AUTHORING. Mathlib v4.12.0 has no `BinaryQuadraticForm.classGroupEquiv`, and this file does not define one. The 26 assessed defs were not rewritten.
- **A.** `BSD_Hasse_square_of_degree` says that if `BSD_FrobeniusDegreeNonneg_OPEN p` holds, then `a_p² ≤ 4p`. The hypothesis is compiled for the 84 checked primes and is not proved for every good prime. `BSD_Hasse_forall_not_from_checked` records card 84, every checked prime below 1000, and the ceiling facts for 9973, 11, and 13. This file does not define a Frobenius endomorphism of `E(𝔽_p)`. Mathlib v4.12.0 has no Hasse theorem. The forall stays NEEDS_AUTHORING. The 328 assessed defs were not rewritten.
- **D.** `BSD_prime_pow_bound_checked` is `|a_{p^k}| ≤ (k+1) p^{k/2}` for each of the 84 checked primes and every `k`. The identity is `a_{p^k} = U_k(a_p/(2√p)) · (√p)^k`, with `U` the Chebyshev polynomial of the second kind, using `|U_k(x)| ≤ k+1` for `|x| ≤ 1` and `|a_p| ≤ 2√p` on that set. `BSD_an_checked_support_bound` is `|a_n| ≤ D n^{1/2+ε}` for every `ε > 0` and every `n ≥ 1` whose prime factors all lie in the 84. The exponent may be greater than 1. `BSD_LSeriesSummable_OPEN` quantifies over every positive integer. A prime outside the 84 is not covered, so that statement stays NEEDS_AUTHORING. The 9 assessed defs were not rewritten.

## Continued C, E, G, and F at `a88e62d`

These are further theorems. They do not rewrite an assessed definition. The assessed tally stays 54 of 504. The 450 stay NEEDS_AUTHORING. `84 ≠ 54`. `(54 : ℕ) + 450 = 504` does not prove the 450. No new `E143_Finset` enumeration. No prime at or above 1000.

- **C.** `BSD_goodLocalFactor` is `(1 - a_p p^{-s} + p^{1-2s})^{-1}` for a prime, and `1` otherwise. `BSD_HasseWeil_partial` is the product of those factors over the 84 checked primes. `BSD_HasseWeil_partial_support` records card 84, and that 11 and 13 divide 143 and lie outside the product. `BSD_localFactor_two_at_one` is `BSD_goodLocalFactor 2 1 = 2/3`, because `BSD_ap_p2` is `a_2 = 0` and `2^{-1} = 1/2`. That is one local factor at one point. It is not `L(143.a1, 1)`. `BSD_rank_placeholder_values` is `BSD_Rank 143 = 1` and `BSD_Rank 1 = 0`, by the definition `if N = 143 then 1 else 0`. That definition does not prove the Mordell–Weil rank, and it does not prove `L(1) = 0` or `L'(1) ≠ 0`. The registry `BSD_L143a1_DerivAtOne` stays 0. `L_143a1` stays the Prop `True`. Modularity of 143.a1 stays NEEDS_AUTHORING. The 12 assessed definitions were not rewritten.
- **E.** `BSD_absconv_halfplane_not_symmetric` says `Re(s) > 3/2` implies `Re(2 - s) < 1/2`. The half-plane of absolute convergence is not invariant under `s ↦ 2 - s`. `BSD_continuation_still_open` records that the registry Euler and functional-equation names are `True`, together with that asymmetry. There is no modular form and no Fricke involution in Mathlib v4.12.0. Analytic continuation and the functional equation stay NEEDS_AUTHORING. The 11 assessed definitions were not rewritten.
- **G.** `BSD_p2_OK_isPrime` uses `Ideal.absNorm p2_OK = 2`. The quotient has cardinality 2, so it is isomorphic to `ZMod 2`, hence a field, so `p2_OK` is maximal and therefore prime. `BSD_p2_prime_and_conductor` packages that with `(2 : 𝓞 K) ∈ p2_OK` and `143 = 11 * 13`. `p3_OK` and `p7_OK` are not constructed in the clean lower-bound file. The span equalities, Wiles–Taylor, and `α_BSD_period` stay NEEDS_AUTHORING. The 10 assessed definitions were not rewritten.
- **F.** `E143Q` is the Mathlib Weierstrass curve with coefficients `(0, -1, 1, -1, -2)`. `E143Q_nonsingular_two_zero` puts `(2, 0)` on that curve, and the `Y` partial is nonzero. `E143Q_negY_two_zero` is `negY 2 0 = -1`. `BSD_affine_not_two_torsion` is `(2 : ℕ) • E143Q_P20 ≠ 0`, because the point is distinct from its negative. `BSD_affine_still_not_rank` keeps the checked membership `(2, 0) ∈ E143_Finset p` and records `BSD_TorsCard = 1` and `BSD_TamagawaProd = 1`. Those constants do not prove infinite order, a generator, rank 1, or BSD. The 54 assessed definitions in this group were not rewritten.

## Continued F at `44d4c41`

These are further theorems. They do not rewrite an assessed definition. The assessed tally stays 54 of 504. The 450 stay NEEDS_AUTHORING. `84 ≠ 54`. `(54 : ℕ) + 450 = 504` does not prove the 450. No new `E143_Finset` enumeration. No prime at or above 1000.

`E143Q_discriminant` is `E143Q.Δ = -1859`. `E143Q_discriminant_factors` is `(1859 : ℕ) = 11 * 13 ^ 2`. The field discriminant of `ℚ(√-143)` is the different integer `-143`. `E143Q_discriminant_not_div_by_2_3_5` says `2`, `3`, and `5` do not divide `1859`. `BSD_nagell_lutz_quantity_divides` is `2 * 0 + a₁ * 2 + a₃ = 1` and `(1 : ℤ) ∣ 1859`. The Nagell–Lutz divisibility test leaves `(2, 0)` in place.

`BSD_affine_card_plus_one_2_3_5` is the already compiled affine counts: `card + 1` equals `3`, `5`, and `7` at the primes `2`, `3`, and `5`, and those three integers are pairwise coprime. They are `p + 1 - a_p`. This file does not construct `E(𝔽_p)`.

`BSD_torsion_trivial_of_coprime_injections` is Lagrange: injective additive homs into `ZMod m` and `ZMod n` with `gcd m n = 1` force the torsion subgroup to have cardinality `1`, so every finite-order element is `0`. `BSD_Z_embedding_of_infinite_order` says that if `n • (2, 0) ≠ 0` for every positive integer `n`, then `k ↦ k • (2, 0)` embeds `ℤ`. `BSD_rank_ge_one` and `BSD_rank_ge_one_of_torsion_injection` put those two lemmas together for hypothetical injections into `ZMod 5` and `ZMod 7`, the integers `affine.card + 1` at the odd primes `3` and `5`. The maps are hypotheses. Mathlib v4.12.0 has no reduction homomorphism `E(ℚ) → E(𝔽_p)`. At `p = 2` the classical injection sees only odd-order torsion, so `gcd(3, 5) = 1` is a separate arithmetic fact. Unconditional infinite order and rank exactly 1 stay NEEDS_AUTHORING. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, the regulator, Néron–Tate height, and the BSD formula stay NEEDS_AUTHORING. `BSD_rank_ge_one_not_bsd` records `2 • P ≠ 0`, the integers `5` and `7`, `gcd 5 7 = 1`, `Δ = -1859`, the registry constant `BSD_TorsCard = 1`, and `84 ≠ 54`. The 54 assessed definitions in this group were not rewritten.

`lake build Towers.BSD.BSD_RankAtLeastOne_Clean` (`/tmp/bsd-rank.log`) exits 0. `lake build BSD_Clean_Aggregation` (`/tmp/bsd-keep-proving-f.log`) exits 0. Two warnings, both the old unused `r` in `Towers/BSD/BSD_LFunction.lean` at lines 293 and 321.

## Continued F at `10b758c`

These are further theorems. They do not rewrite an assessed definition. The assessed tally stays 54 of 504. The 450 stay NEEDS_AUTHORING. `84 ≠ 54`. `(54 : ℕ) + 450 = 504` does not prove the 450. No new `E143_Finset` enumeration. No prime at or above 1000.

`E143Z` is the same Weierstrass model over `ℤ`, and `E143Z_Δ` is `Δ = -1859`. `E143Fp p` is that model mapped by `Int.castRingHom (ZMod p)`. `E143Fp_Δ_ne_zero_of_not_dvd` says that if `p` does not divide `1859`, then the discriminant over `ZMod p` is nonzero. `E143Fp_nonsingular_iff` uses `nonsingular_of_Δ_ne_zero`: an affine solution is then a nonsingular point. `BSD_pointEquiv` identifies `Point (E143Fp p)` with `Option` of the existing finset `E143_Finset p`. `BSD_point_card_eq_affine_succ` is the cardinality `affine.card + 1`. `BSD_point_card_p3` is `5` and `BSD_point_card_p5` is `7`, from the already compiled affine counts `4` and `6`.

`E143Z_equation_two_zero` puts `(2, 0)` on the integral model. `BSD_reduce_two_zero` is `Point.some` of its image in `Point (E143Fp p)`. `BSD_reduce_two_zero_ne_zero` says that image is not the identity. This is reduction of one integral point. It is not a homomorphism `E(ℚ) → E(𝔽_p)`.

`BSD_torsion_trivial_of_coprime_cards` is Lagrange for injective homs into any two finite additive groups whose cardinalities are coprime. `BSD_rank_ge_one_of_reduction` applies it to hypothetical injections into `Point (E143Fp 3)` and `Point (E143Fp 5)`. The maps remain hypotheses. Mathlib v4.12.0 has the group law over a field and has no reduction homomorphism on `E(ℚ)`. Unconditional infinite order and rank exactly 1 stay NEEDS_AUTHORING. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, the regulator, Néron–Tate height, and the BSD formula stay NEEDS_AUTHORING. `BSD_reduction_still_conditional` records the two cardinalities, the two non-identity reductions, and `84 ≠ 54`. The 54 assessed definitions in this group were not rewritten.

`lake build Towers.BSD.BSD_Reduction_Clean` (`/tmp/bsd-reduction.log`) exits 0. `lake build BSD_Clean_Aggregation` (`/tmp/bsd-keep-proving-reduction.log`) exits 0. Two warnings, both the old unused `r` in `Towers/BSD/BSD_LFunction.lean` at lines 293 and 321.

## Continued F at `9f1675a`

These are further theorems. They do not rewrite an assessed definition. The assessed tally stays 54 of 504. The 450 stay NEEDS_AUTHORING. `84 ≠ 54`. `(54 : ℕ) + 450 = 504` does not prove the 450. No new `E143_Finset` enumeration. No prime at or above 1000.

`BSD_intCast_not_injective` says `Int.castRingHom (ZMod p)` is not injective: it sends both `p` and `0` to `0`. Mathlib's `map_slope` identifies slopes along a ring homomorphism of fields, and its proof uses injectivity. That lemma does not define a homomorphism `E(ℚ) → E(𝔽_p)`.

`BSD_rat_div_reduces` says that if `b` is nonzero modulo `p`, the reduced form of the rational `a / b` equals `(a : ZMod p) * (b : ZMod p)⁻¹`. `BSD_secant_slope_reduces` applies this to `(y₁ - y₂) / (x₁ - x₂)` when the integer `x`-coordinates remain distinct modulo `p`, and identifies the result with `slope` on `E143Fp p`. `BSD_addX_secant_reduces` and `BSD_negAddY_secant_reduces` are the polynomial formulas for the third intersection in that same chord case. `BSD_negY_reduces` is `negY (x, y) = -y - 1` after the coefficient map. `BSD_neg_two_zero_reduces` is the case `(2, 0)`, whose image is `-1`.

The tangent case, a rational point whose denominator is divisible by `p`, and the proof that prime-to-`p` torsion lies outside the kernel of reduction, are the formal group. Mathlib v4.12.0 has no elliptic formal group. Unconditional trivial torsion and rank at least 1 stay NEEDS_AUTHORING. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, the regulator, Néron–Tate height, and the BSD formula stay NEEDS_AUTHORING. `BSD_reductionHom_still_open` records the two failures of injectivity, the cardinalities `5` and `7`, the two negation identities, and `84 ≠ 54`. The 54 assessed definitions in this group were not rewritten.

`lake build Towers.BSD.BSD_ReductionHom_Clean` (`/tmp/bsd-hom.log`) exits 0. `lake build BSD_Clean_Aggregation` (`/tmp/bsd-keep-proving-hom.log`) exits 0. Two warnings, both the old unused `r` in `Towers/BSD/BSD_LFunction.lean` at lines 293 and 321.

## Genesis scan at `fdf9bc1`

The working tree contains no file whose name contains `Genesis`. Parent history has 198 commits on a `Genesis` path and 162 historical paths (`hasseprimset` 127, `Towers/BSD` 30, `lean` 4). Those names were renamed to descriptive files and the old filenames were removed. `Towers/Genesis781` has no commits. The only `bsd-*` branch is this one. `BSD_450_Gates_Documentation.lean` has one parent, `52eb949`. `BSD_Hasse_General_Clean.lean` has one parent, `6b18d08`. `NEEDS_AUTHORING` occurs 471 times in 17 files under `Towers/BSD`. That count is comments and gates. The assessed tally stays 54 of 504, and the 450 stay NEEDS_AUTHORING. Group A is still 328 assessed definitions, and they were not rewritten. `84 ≠ 54`.

`lake build Towers.BSD.BSD_ClassNum_Unconditional_CLOSED` exits 1 (`/tmp/bsd-genesis-classnum.log`). The file imports nothing, so `NumberField.classNumber` and `BSD_classGroupCard_le_10_CLOSED` are unknown identifiers, and `end Towers.BSD` has no open namespace. `lake build Towers.BSD.BSD_BQF_Bridge_Closed` exits 1 in the imported extract `BSD_NormBridge.lean` (`/tmp/bsd-genesis-bqf.log`). The bridge file itself says the Gauss–Dirichlet surface is open because `BinaryQuadraticForm.classGroupEquiv` has no declaration in Mathlib v4.12.0. `BSD_classGroupCard_le_10_CLOSED` takes `BSD_small_norm_in_zpowers_OPEN` as a hypothesis. `lake build Towers.BSD.BSD_SurfaceClose_CLOSED`, the file that tries to prove that hypothesis, exits 1 on the same `NormBridge` extract (`/tmp/bsd-genesis-surface.log`). `classNumber K ≤ 10` and `classNumber K = 10` stay NEEDS_AUTHORING. The ten reduced forms already cited in the clean build are a list of length 10, not the class number.

`lake build Towers.BSD.BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED` exits 1 (`/tmp/bsd-genesis-frob.log`). The imported `hasseprimset/BSD_TauBound_small_proved.lean` places `import` after the module comment, and its header names the source `BSD_Genesis782_CLOSED`. The tree contains no `namespace BSD_Genesis782` and no `degree_frobenius`. The map written there sends an affine pair `(x, y)` to `(x^p, y^p)`. It is not an endomorphism of `E(𝔽_p)`, and it does not prove `a_p² ≤ 4p` for every good prime. `BSD_HasseEndDeg_CLOSED` cites the degree form at `{2, 3, 5, 7}` and leaves the forall as a hypothesis. Those four primes are already among the 84. The Hasse forall stays NEEDS_AUTHORING. The 328 assessed definitions in Group A were not rewritten.

The only file that states a reduction homomorphism is `BSD_ReductionHom_Clean.lean`, already built at `9f1675a`. No genesis parent contains `E(ℚ) → E(𝔽_p)` or an elliptic formal group. Mathlib v4.12.0 has no elliptic formal group. Nothing from the genesis extracts was copied into `BSD_Clean_Aggregation`.

The scan log is `/tmp/bsd-genesis-scan.log`. The Lean sources are the sources that `lake build Towers.BSD.BSD_ReductionHom_Clean` (`/tmp/bsd-hom.log`) and `lake build BSD_Clean_Aggregation` (`/tmp/bsd-keep-proving-hom.log`) already built with exit code 0. Two warnings, both the old unused `r` in `Towers/BSD/BSD_LFunction.lean` at lines 293 and 321. No `sorry`.

## Rewrite under the clean names at `24282f3`

The compiled mathematics is restated in new files. The assessed definitions were not rewritten. The tally stays 54 of 504. The 450 stay NEEDS_AUTHORING. `84 ≠ 54`.

`BSD_reduced_forms_ten` is the list of ten reduced forms. `BSD_minkowski_bound_norm_le_seven` is an integral ideal of absolute norm at most 7 in every class. `BSD_classNumber_le_of_surjection` is the counting principle: if a finite type surjects onto the class group, then `classNumber K` is at most the cardinality of that type. `BSD_classNumber_le_ten` and `BSD_classNumber_eq_ten` apply this when the cardinality is at most 10, and the equality also uses `10 ≤ classNumber K`. The surjection is a hypothesis. The lattices in `ℤ[ω]`, `ω² = ω − 36`, of index at most 7 and stable under multiplication by `ω`, number 14: norms `1, 2, 2, 3, 3, 4, 4, 4, 6, 6, 6, 6, 7, 7`. That count is not a Lean theorem. It is why "at most 10 ideals" does not follow from the Minkowski bound, and why this file does not prove `classNumber K ≤ 10`. The 26 assessed definitions in Group B were not rewritten.

`BSD_Frobenius_degree_nonneg` is the degree form `∀ r, r² − a_p r + p ≥ 0`. `BSD_Hasse_bound_forall` says that if the form holds for every prime not dividing `1859`, then `a_p² ≤ 4p` for every such prime. The form is compiled for the 84 checked primes. It is a hypothesis in the forall. `BSD_prime_dvd_143_iff_dvd_1859` identifies the two bad-reduction conditions: a prime divides `143 = 11 * 13` if and only if it divides `1859 = 11 * 13²`. Mathlib v4.12.0 has no Frobenius endomorphism and no Hasse theorem. This file does not define `degree_frobenius`. The 328 assessed definitions in Group A were not rewritten.

`BSD_reduction_hom_secant`, `BSD_reduction_hom_secant_addX`, and `BSD_reduction_hom_secant_negAddY` are the chord formulas. `BSD_torsion_trivial` concludes that a finite-order point is `0` if the torsion subgroup injects into `Point (E143Fp 3)` and `Point (E143Fp 5)`, of orders `5` and `7`. The injections are hypotheses. The tangent case is not a theorem. `BSD_rank_ge_one_unconditional` is not a theorem. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, the regulator, Néron–Tate height, and the BSD formula stay NEEDS_AUTHORING. The 54 assessed definitions in Group F were not rewritten.

`BSD_localFactor_at_two` is `BSD_goodLocalFactor 2 1 = 2/3`. `BSD_halfplane_asymmetry` is `Re(s) > 3/2 → Re(2 − s) < 1/2`. `BSD_prime_above_two` is `p2_OK.IsPrime`. The Hasse–Weil derivative, analytic continuation, the functional equation, Wiles–Taylor, and `α_BSD_period` stay NEEDS_AUTHORING. The 12, 11, and 10 assessed definitions were not rewritten.

`lake build Towers.BSD.BSD_ClassNumber_Clean` and `lake build Towers.BSD.BSD_Torsion_Rank_Unconditional_Clean` (`/tmp/bsd-rewrite-targets.log`) exit 0. `lake build BSD_Clean_Aggregation` (`/tmp/bsd-rewrite-new-structure.log`) exits 0. Two warnings, both the old unused `r` in `Towers/BSD/BSD_LFunction.lean` at lines 293 and 321. No `sorry`.

## Class-number collapse 14 → 10 at `2ec969d`

`Towers/BSD/BSD_ClassNumber_Collapse_Clean.lean` discharges the surjection that `BSD_classNumber_eq_ten` left as a hypothesis. `BSD_classNumber_eq_ten_collapse` is `NumberField.classNumber K = 10`. `BSD_Clean_Aggregation` imports this file. The 26 assessed Group B definitions were not rewritten. The tally stays 54 of 504. The 450 stay NEEDS_AUTHORING. `84 ≠ 54`.

`orderOf p2_class = 10`. The element `-28 + 3ω` has norm `1024` and generates `p2_OK ^ 10`, and `master_not_principal_1_to_9` keeps the powers `1` through `9` non-principal. The rational primes `2`, `3`, and `7` split as conjugate prime ideals `p2_OK`, `p2b_OK`, `p3_OK`, `p3b_OK`, `p7_OK`, and `p7b_OK`. There is no ideal of absolute norm `5`, because `ω` would be a root of `x² − x + 36` in `ZMod 5`. Every normalized prime factor of an ideal of absolute norm at most `7` is one of those six primes, and each of those six classes is a power of `[p2_OK]`. Exponents reduce modulo `10`.

`BSD_every_class_has_norm_le_seven` supplies a representative of absolute norm at most `7` in every class. `BSD_small_norm_class_is_p2_power` puts that representative in the cyclic subgroup, so `BSD_class_pow_surjective` is a surjection `Fin 10 → ClassGroup (𝓞 K)`. With `10 ≤ classNumber K`, `le_antisymm` gives equality. `BinaryQuadraticForm.classGroupEquiv` was not defined. The argument does not go through binary quadratic forms.

`BSD_fourteen_lattices_ten_classes` names fourteen ideals and shows their classes are the ten powers of `[p2_OK]`: the unit ideal and `(2)` are `g^0`, `p2_OK` is `g`, `p2_OK ^ 2` is `g^2`, `p2b_OK * p3_OK` and `p7_OK` are `g^3`, `p3_OK` is `g^4`, `p2_OK * p3_OK` and `p2b_OK * p3b_OK` are `g^5`, `p3b_OK` is `g^6`, `p2_OK * p3b_OK` and `p7b_OK` are `g^7`, `p2b_OK ^ 2` is `g^8`, and `p2b_OK` is `g^9`. The external statement that `ℤ[ω]` contains exactly 14 ideals of index at most `7` is still not a Lean theorem.

`BSD_classNumber_collapse_record` packages `orderOf p2_class = 10`, `classNumber K = 10`, the norm-at-most-`7` classes, and `(84 : ℕ) ≠ 54`.

`lake build Towers.BSD.BSD_ClassNumber_Collapse_Clean` (`/tmp/bsd-b-collapse-target.log`) exits 0. `lake build BSD_Clean_Aggregation` (`/tmp/bsd-b-collapse.log`) exits 0. Two warnings, both the old unused `r` in `Towers/BSD/BSD_LFunction.lean` at lines 293 and 321. No `sorry`.

## Standing limit

There is no Batch 11. Do not `native_decide` `E143_Finset p` for `p ≥ 1000`. Do not treat a registry `True` as a proved conjecture. Do not change `BSD_L143a1_DerivAtOne`. The 54 assessed theorems, the 84 compiled checks, the five corollaries, the aggregate, the partial theorems for groups A through G, the norm bound of 7, the degree-form implication, the checked-support coefficient bound, the local factor `2/3`, the half-plane asymmetry, the primality of `p2_OK`, `2 • (2, 0) ≠ 0`, the discriminant `-1859`, the conditional embedding `BSD_rank_ge_one`, the identifications `Nat.card (Point (E143Fp 3)) = 5` and `Nat.card (Point (E143Fp 5)) = 7`, the non-identity reduction of `(2, 0)`, the secant identities for integral points, and the failure of injectivity of `Int.castRingHom (ZMod p)` are citations of proofs that compile. The 450 assessed defs are outside that list. `NumberField.classNumber K = 10` is the extra theorem `BSD_classNumber_eq_ten_collapse` and does not rewrite the 26 assessed Group B definitions. The Hasse forall, `BSD_LSeriesSummable_OPEN`, the Hasse–Weil derivative, modularity, analytic continuation, the functional equation, unconditional infinite order, rank exactly 1, Gross–Zagier, Kolyvagin, Wiles–Taylor, the period, and the ideal equalities for 3 and 7 stay NEEDS_AUTHORING.

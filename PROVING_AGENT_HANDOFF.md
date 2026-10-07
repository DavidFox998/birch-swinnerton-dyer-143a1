# Proving Agent Handoff — BSD 504 Propositions

## Status

- Batch 1 is done at `9474564`. Three theorems. The rest of Batch 1 is NEEDS_AUTHORING.
- Batch 2 is done at `3c62767`. `lake build BSD_Assessed_Batch2` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 3 is done at `cd0eafc`. `lake build BSD_Assessed_Batch3` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 4 is done at `82af374`. `lake build BSD_Assessed_Batch4` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 5 is done at `d86e7e9`. `lake build BSD_Assessed_Batch5` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 6 is done at `0b28ede`. `lake build BSD_Assessed_Batch6` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 7 is done at `8742b26`. `lake build BSD_Assessed_Batch7` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 8 is done at `8784abe`. `lake build BSD_Assessed_Batch8` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 9 is done at `a96b7b8`. `lake build BSD_Assessed_Batch9` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 10 is done at `09c726c`. `lake build BSD_Assessed_Batch10` and `lake build BSD_Clean_Aggregation` both exit 0.
- There is no Batch 11. The ten assessed files are done. What remains is NEEDS_AUTHORING.
- `Towers/BSD/BSD_Finite_Hasse_54_Theorem.lean` is at `66f0326`. It cites the 84 compiled finite checks. The assessed tally stays 54 of 504. The checked set is not every good prime.
- Five corollaries are in `Towers/BSD/BSD_More_Theorems_From_54.lean` at `767d141`. `lake build Towers.BSD.BSD_More_Theorems_From_54` and `lake build BSD_Clean_Aggregation` both exit 0. They are not five more of the 504. The assessed tally stays 54 of 504. The other 450 stay NEEDS_AUTHORING.
- `Towers/BSD/BSD_Final_Aggregate_84_54_450.lean` packages those citations in `BSD_84_54_450`. `lake build Towers.BSD.BSD_Final_Aggregate_84_54_450` and `lake build BSD_Clean_Aggregation` both exit 0. No new `E143_Finset` enumeration. The assessed tally stays 54 of 504. `84 ≠ 54`. `54 + 450 = 504` does not prove the 450.
- `Towers/BSD/BSD_450_Gates_Documentation.lean` names each of the 450 and records its gate. It does not prove them. `lake build Towers.BSD.BSD_450_Gates_Documentation` and `lake build BSD_Clean_Aggregation` both exit 0. `FINAL_BSD_HANDOFF_54_84.md` is not in the repository.
- Do not treat a registry `True` as a proved conjecture. No `sorry`. No invented mathematics.

Batch 2 theorems, and only these:

- `BSD_EndomorphismDegree_Partial_CLOSED_prop` and `BSD_Hasse_OPEN_partial_CLOSED_prop` for p ∈ {2, 3, 5, 7}, from `Towers/BSD/BSD_Hasse_Points_2_7.lean`. Not Hasse for every prime.
- `BSD_HeegnerPoint_CLOSED_prop` and `BSD_HeegnerPoint_surface_ledger_prop`: the affine point (2, 0). Not non-torsion, not rank 1, not BSD.
- `BSD_VanishingOrder_APIBridge_RETRACTED_prop`: the B01 constant-function counterexample. Not `¬ True`.
- Sentinels that do not discharge an open: `BSD_endeg_sentinel_prop`, `BSD_linFunc_sentinel_prop`, `BSD_modularityE143_is_open_prop`, `BSD_bsdFormula_is_open_prop`.

Batch 3 theorems, and only these:

- `BSD_HeckeMultiplicativity_143_CLOSED_prop`: `a_n (m * n) = a_n m * a_n n` when `Nat.Coprime m n`. Not modularity.
- `BSD_RamanujanBound_iff_Discriminant_prop`: `|a_p| ≤ 2√p` if and only if `a_p² ≤ 4p`, for good primes. Neither side is proved for every prime.
- Class number `10 ≤ h(K)` and `h(K) ≤ 10` are restored and not proved. Sha, Tamagawa, torsion injection, Gross–Zagier, Kolyvagin, and the ideal equalities stay NEEDS_AUTHORING.

Batch 4 theorems, and only these:

- `E143a1_prop`: coefficients `(0, -1, 1, -1, -2)` of the Weierstrass model.
- `E143a1_has_rational_point_prop`: affine point `(2, 0)`. Not rank 1, not BSD.
- `E143a1_bost_bound_prop`: the literal `11.42214868898 > 2√13`, by comparing squares. Not a derivation of Bost's sum.
- `BSD_isBigO_to_LSeries_close_prop`: a coefficient bound implies summability for `Re(s) > 3/2`. The bound is a hypothesis.
- `BSD_L143a1_HasDerivAt_CLOSED_prop`: derivative of `(5759/10000)·(s−1)`. Not the Hasse–Weil L-function. Registry derivative stays 0.
- `p≥1009` degree checks stay NEEDS_AUTHORING. Those proofs are `native_decide` on `E143_Finset p`. Batch 4 left the compiled counts at 241.

Batch 5 theorems, and only these:

- `BSD_DegreeNonneg_p251_prop`, `BSD_DegreeNonneg_p257_prop`, `BSD_DegreeNonneg_p263_prop`, from `Towers/BSD/BSD_Hasse_Points_251_263.lean`. Counts: p=251 card 230, `a_p=21`; p=257 card 239, `a_p=18`; p=263 card 281, `a_p=−18`. The original `decide` proofs were replaced by `native_decide`.
- Not Hasse for every prime. After Batch 5 the clean build checked finite point counts through 263, with the earlier gap at 11 and 13, and nothing past 263. Primes from 311 upward in Batch 5 stay NEEDS_AUTHORING.

Batch 6 theorems, and only these:

- `BSD_DegreeNonneg_p373_prop`, `BSD_DegreeNonneg_p379_prop`, `BSD_DegreeNonneg_p383_prop`, `BSD_DegreeNonneg_p433_prop`, `BSD_DegreeNonneg_p439_prop`, `BSD_DegreeNonneg_p443_prop`, `BSD_DegreeNonneg_p491_prop`, `BSD_DegreeNonneg_p499_prop`, `BSD_DegreeNonneg_p503_prop`, from `Towers/BSD/BSD_Hasse_Points_373_503.lean`. Counts: p=373 card 347, `a_p=26`; p=379 card 390, `a_p=−11`; p=383 card 402, `a_p=−19`; p=433 card 400, `a_p=33`; p=439 card 433, `a_p=6`; p=443 card 466, `a_p=−23`; p=491 card 479, `a_p=12`; p=499 card 471, `a_p=28`; p=503 card 473, `a_p=30`. The original `decide` proofs were replaced by `native_decide`.
- Not Hasse for every prime. The clean build now checks finite point counts for `{2,3,5,7}`, primes 17 through 241, `{251,257,263}`, and `{373,379,383,433,439,443,491,499,503}`. Primes 11 and 13 divide 143. Nothing past 503 is in the clean build. The 51 props with `p≥3559` stay NEEDS_AUTHORING.
- Batch 7 is the same degree-nonnegativity shape. The only primes there small enough to match this method are `{569,571,577,619,631,641}`. Primes from 4999 upward stay NEEDS_AUTHORING.

Batch 7 theorems, and only these:

- `BSD_DegreeNonneg_p569_prop`, `BSD_DegreeNonneg_p571_prop`, `BSD_DegreeNonneg_p577_prop`, `BSD_DegreeNonneg_p619_prop`, `BSD_DegreeNonneg_p631_prop`, `BSD_DegreeNonneg_p641_prop`, from `Towers/BSD/BSD_Hasse_Points_569_641.lean`. Counts: p=569 card 601, `a_p=−32`; p=571 card 531, `a_p=40`; p=577 card 546, `a_p=31`; p=619 card 626, `a_p=−7`; p=631 card 658, `a_p=−27`; p=641 card 674, `a_p=−33`. The original `decide` proofs were replaced by `native_decide`.
- Not Hasse for every prime. The clean build now checks finite point counts for `{2,3,5,7}`, primes 17 through 241, `{251,257,263}`, `{373,379,383,433,439,443,491,499,503}`, and `{569,571,577,619,631,641}`. Primes 11 and 13 divide 143. Nothing past 641 is in the clean build. The 54 props with `p≥4999` stay NEEDS_AUTHORING.
- Batch 8 is the same degree-nonnegativity shape. The only primes there small enough to match this method are `{683,691,701,757,761,769}`. Primes from 6569 upward stay NEEDS_AUTHORING.

Batch 8 theorems, and only these:

- `BSD_DegreeNonneg_p683_prop`, `BSD_DegreeNonneg_p691_prop`, `BSD_DegreeNonneg_p701_prop`, `BSD_DegreeNonneg_p757_prop`, `BSD_DegreeNonneg_p761_prop`, `BSD_DegreeNonneg_p769_prop`, from `Towers/BSD/BSD_Hasse_Points_683_769.lean`. Counts: p=683 card 687, `a_p=−4`; p=691 card 736, `a_p=−45`; p=701 card 711, `a_p=−10`; p=757 card 727, `a_p=30`; p=761 card 795, `a_p=−34`; p=769 card 769, `a_p=0`. The original `decide` proofs were replaced by `native_decide`.
- Not Hasse for every prime. The clean build now checks finite point counts for `{2,3,5,7}`, primes 17 through 241, `{251,257,263}`, `{373,379,383,433,439,443,491,499,503}`, `{569,571,577,619,631,641}`, and `{683,691,701,757,761,769}`. Primes 11 and 13 divide 143. Nothing past 769 is in the clean build. The 54 props with `p≥6569` stay NEEDS_AUTHORING.
- Batch 9 is the same degree-nonnegativity shape. The only primes there small enough to match this method are `{827,829,839,887,907,911,971,977,983}`. Primes from 8209 upward stay NEEDS_AUTHORING. `971`, `977`, and `983` are larger enumerations than `769`; if `native_decide` does not finish, drop those three first.

Batch 9 theorems, and only these:

- `BSD_DegreeNonneg_p827_prop`, `BSD_DegreeNonneg_p829_prop`, `BSD_DegreeNonneg_p839_prop`, `BSD_DegreeNonneg_p887_prop`, `BSD_DegreeNonneg_p907_prop`, `BSD_DegreeNonneg_p911_prop`, `BSD_DegreeNonneg_p971_prop`, `BSD_DegreeNonneg_p977_prop`, `BSD_DegreeNonneg_p983_prop`, from `Towers/BSD/BSD_Hasse_Points_827_983.lean`. Counts: p=827 card 777, `a_p=50`; p=829 card 800, `a_p=29`; p=839 card 786, `a_p=53`; p=887 card 875, `a_p=12`; p=907 card 855, `a_p=52`; p=911 card 919, `a_p=−8`; p=971 card 1020, `a_p=−49`; p=977 card 986, `a_p=−9`; p=983 card 1014, `a_p=−31`. The original `decide` proofs were replaced by `native_decide`. All nine compiled, including 971, 977, and 983.
- Not Hasse for every prime. The clean build now checks finite point counts for `{2,3,5,7}`, primes 17 through 241, `{251,257,263}`, `{373,379,383,433,439,443,491,499,503}`, `{569,571,577,619,631,641}`, `{683,691,701,757,761,769}`, and `{827,829,839,887,907,911,971,977,983}`. Primes 11 and 13 divide 143. Nothing past 983 is in the clean build. The 51 props with `p≥8209` stay NEEDS_AUTHORING.
- Batch 10 is the last file. Its degree checks and `BSD_Hasse_OPEN 9973` are primes at or above 9721. Those enumerations are far larger than 983, so they stay NEEDS_AUTHORING. `BSD_WeilHasse_eq_Gate1` is `Iff.rfl` only in the non-building original, where both sides are the same statement. In the registry, `BSD_HasseBound_Discriminant_OPEN` is `True` and `BSD_WeilHasse_Weierstrass_OPEN` is the forall, so the assessed iff is not definitional. Do not prove it. The tau-bound file is a long argument, not a tactic rename. Flag it unless those pieces already build in the clean tree.

Batch 10 theorems, and only these:

- `BSD_isBigO_to_LSeries_OPEN_prop` cites `BSD_isBigO_to_LSeries_close_prop` from Batch 4. Same implication: a coefficient bound implies summability for `Re(s) > 3/2`. The bound is a hypothesis. Not a new bound.
- `BSD_aNBound_to_LSeries_OPEN_prop` is the original sentinel `BSD_LSeriesSummable_OPEN → True`. It does not prove summability, and it is not the missing divisor bound.
- Not Hasse for every prime. Nothing past 983 is in the clean build. The 11 props at `p≥9721`, the Hasse forall, the non-definitional iff, the Weierstrass structure (a type, not a Prop), and the tau-bound arguments stay NEEDS_AUTHORING. Nineteen props in this file stay NEEDS_AUTHORING.
- The ten assessed files are done. Running total is 54 theorems out of 504. The other 450 stay NEEDS_AUTHORING. Do not treat a registry `True` as a proved conjecture.

## Authoring Phase 2

Mechanical enumeration is finished. `native_decide` of `E143_Finset p` compiled through p=983 (966289 pairs). `decide` hits the recursion limit at p≥53. Do not `native_decide` p≥1000. A count at p=9973 is about 99 million pairs and will not compile. Finite counts are not Hasse for every prime. There is no Batch 11. Phase 2 does not add theorems.

1. **Class number.** `10 ≤ classNumber K` and `classNumber K ≤ 10` stay NEEDS_AUTHORING. There is no `Towers/BSD/B01_ClassNumber.lean`. The lower bound is `Towers/BSD/BSD_ClassNumberLowerProof.lean` and `Towers/BSD/BSD_MasterProof.lean`, using `master_not_principal_1_to_9` and `p2_OK`, outside the clean build. The upper bound is the binary-quadratic-form gate in `Towers/BSD/BSD_ClassNum_Upper_CLOSED.lean`, `Towers/BSD/BSD_ReducedForms.lean`, and `Towers/BSD/BSD_MasterProof.lean`. It needs `BinaryQuadraticForm.classGroupEquiv`. That declaration is absent from Mathlib v4.12.0. Do not invent it.

2. **Registry derivative.** `BSD_L143a1_DerivAtOne` in `Towers/BSD/BSD_MissingDefinitionsRegistry.lean` is the constant 0, so `BSD_L143a1_DerivAtOne ≠ 0` is `0 ≠ 0`. `Towers/BSD/BSD_VanishingOrder_Kolyvagin_Closed.lean` differentiates `(5759/10000)·(s−1)`, and Batch 4 proved that derivative is `5759/10000`. That is not the Hasse–Weil L-function. Do not change the registry constant. Stays NEEDS_AUTHORING until an actual `L_143a1` derivative is proved.

3. **Hasse for every prime.** `BSD_WeilHasse_Weierstrass_OPEN` is `a_p² ≤ 4p` for every good prime. `BSD_WeilHasse_eq_Gate1` is that forall if and only if `True`, because `BSD_HasseBound_Discriminant_OPEN` is `True`. The original `Iff.rfl` in `hasseprimset/BSD_WeilDeligne_Closed.lean` used two copies of the same statement. Counts through 983 do not prove the forall. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve. Do not extend the enumeration to 3559, 4999, 6569, 8209, 9721, or 9973.

4. **Opens that are not finite counts.** Euler product (`Towers/BSD/BSD_EulerProduct_Closed.lean`), functional equation (`Towers/BSD/BSD_BSD_FuncEq.lean`), Gross–Zagier (`Towers/BSD/BSD_GrossZagier_Closed.lean`), Kolyvagin, Sha and Tamagawa (`Towers/BSD/BSD_SHA_Tamagawa_Closed.lean`, `Towers/BSD/BSD_Tamagawa_Scaffold.lean`), regulator and Néron–Tate height, torsion and non-torsion, modularity (`Towers/BSD/B02_Modularity.lean`), and the ideal equalities `BSD_w3_ideal_equality_OPEN` and `BSD_w4_ideal_equality_OPEN` in `Towers/BSD/BSD_ClassNumber_UpperBound_CLOSED.lean` stay NEEDS_AUTHORING. Originals that are `trivial` on `True`, `rfl` of Tamagawa constants 1 and 2, `∃ R, R > 0 ∧ True`, `fun _ => ⟨1, rfl⟩`, or a function that ignores its arguments and returns 1 are sentinels. Do not close them with `trivial`.

5. **Tau bound.** `BSD_PrimePowBound_to_aNBound_OPEN` is marked unformalized in `hasseprimset/BSD_antisupersingular.lean`. The divisor estimate is `hasseprimset/BSD_TauBound_small_proved.lean` and is not in the clean build. Do not invent it.

The compiled finite checks are collected in `Towers/BSD/BSD_Finite_Hasse_54_Theorem.lean`. `BSD_Finite_Hasse_CheckedPrimes.card = 84`, not 54. The 54 is the assessed-theorem tally (`54 + 450 = 504`), and `84 ≠ 54`. `a_p p = p − (E143_Finset p).card` by definition. `BSD_Ceiling_Theorem` shows 9973 is prime, does not divide 143, and is not in the checked set. It does not evaluate `E143_Finset 9973`.

## Corollaries from the 84 checks

`Towers/BSD/BSD_More_Theorems_From_54.lean` imports Batches 1–10 and `BSD_Finite_Hasse_54_Theorem`. `BSD_Clean_Aggregation` imports it. No new `E143_Finset` enumeration. No sorry. These five theorems are corollaries of proofs that already compile. They do not change the assessed tally.

1. `BSD_Hasse_Forms_Equiv_84`. For each of the 84 checked primes, `|a_p| ≤ 2√p` and `a_p² ≤ 4p`. The pointwise comparison is the Batch 3 square algebra with the quantifiers removed. `BSD_RamanujanBound_iff_Discriminant_prop` still equates two unproved foralls. This does not prove Hasse for every prime.

2. `BSD_Coprime_Multiplicativity_Applies_84`. Cites `BSD_HeckeMultiplicativity_143_CLOSED_prop`. `a_n p = a_p p` for a prime, so the compiled counts give `a_n 251 = 21` and `a_n 257 = 18`. Then `a_n (251 * 257) = a_n 251 * a_n 257` and `a_n 64507 = 378`. Not modularity.

3. `BSD_Weierstrass_Coeff_Affine_Point_Theorem`. Coefficients `(0, -1, 1, -1, -2)` by rfl. The rational point `(2, 0)` satisfies `y² + y = x³ − x² − x − 2`. The same point lies in `E143_Finset p` for each checked prime, by the ring identity `0 = 8 - 4 - 2 - 2` in `ZMod p`. Not non-torsion, not a generator, not rank 1, not BSD. `BSD_HeegnerPoint_OPEN` stays the registry `True`.

4. `BSD_Minkowski_H1_AP_Ledger_Theorem`. Conjunction of `BSD_minkowski_lt_8_prop`, `BSD_H1_decomp_verified_prop` (`True ∧ True ∧ True ∧ True`), and `BSD_AP_surface_ledger_prop`. Class number stays NEEDS_AUTHORING. `BinaryQuadraticForm.classGroupEquiv` is absent from Mathlib v4.12.0. The ledger does not discharge the empirical `a_p` props.

5. `BSD_Coefficient_Bound_Implies_Summability_54`. Cites `BSD_isBigO_to_LSeries_close_prop`. A bound on every `a_n` implies summability for `Re(s) > 3/2`. Each checked prime satisfies `|a_p| ≤ 2√p`. Those 84 inequalities are not a bound for every `n`. Summability of the L-series is not discharged. There is no truncated L-series.

## Final aggregate

`Towers/BSD/BSD_Final_Aggregate_84_54_450.lean` imports `BSD_Finite_Hasse_54_Theorem`, `BSD_More_Theorems_From_54`, and Batches 1–10. `BSD_Clean_Aggregation` imports it. `BSD_84_54_450` is one conjunction, for each checked prime:

- `BSD_Finite_Hasse_CheckedPrimes.card = 84`, and every checked prime is below 1000.
- The degree form is nonnegative, so `|a_p| ≤ 2√p` and `a_p² ≤ 4p`. `a_p = p − (affine count)`, so the projective count `p + 1 − a_p` equals the affine count plus one.
- `a_n (251 * 257) = a_n 251 * a_n 257`, with `a_n 251 = 21`, `a_n 257 = 18`, and `a_n 64507 = 378`.
- Coefficients `(0, -1, 1, -1, -2)` by rfl. `(2, 0)` is a rational point, and `(2, 0) ∈ E143_Finset p` by `0 = 8 - 4 - 2 - 2` in `ZMod p`. Not non-torsion.
- Minkowski `(2/π)·√143 < 8`, `True ∧ True ∧ True ∧ True`, and the AP implication ledger.
- `(54 : ℕ) + 450 = 504`, `54 < 504`, and `84 ≠ 54`. The arithmetic does not prove the 450 props.
- `BSD_Ceiling_Theorem`: 9973 is prime, does not divide 143, and is outside the checked set. 11 and 13 divide 143 and are outside. This does not evaluate `E143_Finset 9973`.
- The coefficient-bound implication, still a hypothesis on every `n`. `BSD_LSeriesSummable_OPEN → True` is the existing sentinel and does not prove summability.
- Registry placeholders, each definitionally `True` or the constant 0: `BSD_L143a1_DerivAtOne = 0`, `BSD_HasseBound_Discriminant_OPEN`, Gross–Zagier, Kolyvagin, Sha, Tamagawa, Euler convergence, Heegner, the registry `BSD_FuncEq_OPEN` (not the root declaration), the regulator placeholder, the Néron–Tate placeholder, the tau-bound placeholder, and `BSD_PrimePowBound_to_aNBound_OPEN_prop`. These equalities do not prove those conjectures. `BSD_WeilHasse_Weierstrass_OPEN` stays unproved. `BinaryQuadraticForm.classGroupEquiv` stays absent from Mathlib v4.12.0. No prime ≥ 1000 is enumerated.

## The 450 gates

`Towers/BSD/BSD_450_Gates_Documentation.lean` is an audit. Each of the 450 assessed defs is `#check`ed and marked NEEDS_AUTHORING. `#check` does not prove the prop. `BSD_450_audit_tally` is `(54 : ℕ) + 450 = 504 ∧ (84 : ℕ) ≠ 54`. That arithmetic does not discharge the 450. No sorry. No new enumeration.

Searches this round:

- Mathlib v4.12.0 `AlgebraicGeometry/EllipticCurve` has Affine, DivisionPolynomial, Group, Jacobian, Projective, VariableChange, and Weierstrass. No Hasse bound. Group A stays NEEDS_AUTHORING.
- `BinaryQuadraticForm` and `classGroupEquiv`: zero declarations in Mathlib v4.12.0. Group B stays NEEDS_AUTHORING. The lower bound still depends on `master_not_principal_1_to_9` and `p2_OK` outside the clean build.
- There is no `hasseprimset/BSD_LFunction.lean` and no `Towers/BSD/BSD_AnalyticContinuation` file. `Towers/BSD/BSD_LFunction.lean` defines `BSD_LSeriesSummable_OPEN`, `BSD_EulerProduct_OPEN`, `BSD_AnalyticOn_OPEN`, and `BSD_FuncEq_OPEN` and does not prove a Hasse–Weil derivative. The registry derivative stays the constant 0. Group C stays NEEDS_AUTHORING.
- `hasseprimset/BSD_TauBound_small_proved.lean` imports `Towers.BSD.BSD_Genesis781_CLOSED` and is outside the clean build. `hasseprimset/BSD_antisupersingular.lean` leaves the Finsupp product unformalized. Group D stays NEEDS_AUTHORING.
- Groups E, F, and G stay NEEDS_AUTHORING. Sentinels `trivial` on `True`, `rfl` of the constants 1 and 2, `∃ R, R > 0 ∧ True`, and `fun _ => ⟨1, rfl⟩` are not closed.

| Group | Props | Gate |
|-------|------:|------|
| A | 328 | No general Hasse theorem in Mathlib v4.12.0. 11 of these are the degree and Hasse props at primes ≥ 9721, including both props at 9973. The other 317 are uncompiled degree props from 311 upward, the forall `a_p² ≤ 4p`, the non-definitional iff, and the Weierstrass structure placeholder. |
| B | 26 | Class number. `classGroupEquiv` absent. |
| C | 12 | Registry derivative is 0. Linear anchor is not the Hasse–Weil L-function. |
| D | 9 | Divisor estimate outside the clean build. Summability not proved. |
| E | 11 | Euler product, functional equation, analytic continuation. |
| F | 54 | Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank. |
| G | 10 | Ideal equalities, modularity, Wiles–Taylor, α_BSD_period. |
| **Total** | **450** | Still NEEDS_AUTHORING. |

## Where everything lives

**Repo:** `DavidFox998/birch-swinnerton-dyer-143a1`
**Branch:** `bsd-clean-214-propositions-assessed`
**Local:** `~/workspace/work/opera/birch-swinnerton-dyer-143a1/`

## The 504 propositions

**Files:** `BSD_Assessed_Batch1.lean` through `BSD_Assessed_Batch10.lean` (root directory)

| Batch | Props | With real statement | True placeholder |
|-------|-------|---------------------|------------------|
| 1 | 39 | 16 | 23 |
| 2 | 42 | 15 | 27 |
| 3 | 46 | 8 | 38 |
| 4 | 56 | 4 | 52 |
| 5 | 60 | 0 | 60 |
| 6 | 60 | 0 | 60 |
| 7 | 60 | 0 | 60 |
| 8 | 60 | 0 | 60 |
| 9 | 60 | 0 | 60 |
| 10 | 21 | 1 | 20 |
| **Total** | **504** | **44** | **460** |

## Structure of each proposition

```lean
namespace <OriginalFile>_Assessed
  def <Name>_prop : Prop := <statement>  -- or True with docs
end <OriginalFile>_Assessed
```

Each def has:
- **Name:** `<OriginalTheoremName>_prop` (e.g., `BSD_L_Analytic_143_OPEN_prop`)
- **Source file:** in the namespace name (e.g., `Towers_BSD_B02_Modularity_Assessed` → `Towers/BSD/B02_Modularity.lean`)
- **Statement:** either the real proposition (44 cases) or `True` with the original statement in a `-- was:` comment (460 cases)

## Dependencies (already wired)

Each batch file imports:
```lean
import Towers.BSD.BSD_MissingDefinitionsRegistry
open BSD_MissingDefinitionsRegistry
```

The registry (`Towers/BSD/BSD_MissingDefinitionsRegistry.lean`) provides:
- 20 core BSD OPEN props (BSD_143_OPEN, BSD_GrossZagier_OPEN, etc.)
- 23 additional missing definitions from assessment
- 6 more from iterative fixing
- All as honest `def ... : Prop := True` placeholders

Also available:
- `Towers.BSD.BSD_LFunction` — E143_Finset, a_p, BSD_Hasse_OPEN (builds)
- `Towers.BSD.BSD_Frobenius_Certificate_Clean` — BSD_FrobeniusDegreeNonneg_OPEN (builds)
- `Towers.BSD.BSD_Targeted_Placeholders` — honest axioms for missing deps (builds)

## What the proving agent should do

For each `def <Name>_prop : Prop := True` (or real statement):

1. **Look up the original file** (from namespace name) to see the full context and any existing proof attempt
2. **Prove the proposition:** change to `theorem <Name>_prop : <Prop> := by ...`
3. **Verify:** `lake build BSD_Assessed_Batch<N>` must still succeed
4. **Mechanical fixes allowed:** tactic renames, `decide` → `native_decide`, import fixes, `set_option maxRecDepth`
5. **Do NOT:** invent mathematics, change the proposition statement, or use `sorry`/`admit`

## Priority order (easiest first)

1. **Batch 1-2** (81 props, 31 with real statements) — most likely to have mechanical fixes
2. **Batch 3-4** (102 props, 12 with real statements) — mixed
3. **Done** — Batches 1 through 10 are assessed. There is no Batch 11. Authoring Phase 2 is recorded above. The five corollaries, `BSD_84_54_450`, and the 450-gate audit do not add to the 54. Do not enumerate further primes. The 450 props stay NEEDS_AUTHORING. Their gates are in `BSD_450_Gates_Documentation.lean`.

## Verification

After proving a batch:
```bash
cd ~/workspace/work/opera/birch-swinnerton-dyer-143a1
lake build BSD_Assessed_Batch<N>  # must succeed
lake build BSD_Clean_Aggregation  # must still succeed
```

## Authorship

Proofs are authored by the human (David Fox). The agent does mechanical proof repair and verification only. Do not author novel mathematical arguments — flag those as `NEEDS_AUTHORING` and move on.

## Original files (preserved for reference)

All 251 original files are in the repo:
- `Towers/BSD/` (97 files)
- `hasseprimset/` (127 files)
- `lean/` (21 files)
- Root (6 files)

The originals are the source of truth for proposition statements and any existing proof attempts.

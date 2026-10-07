/-
  One conjunction of what already compiles.
  No new `E143_Finset` enumeration. No sorry.
  The assessed tally stays 54 of 504. The checked set stays 84 primes below 1000.
  `84 ≠ 54`. The equality `54 + 450 = 504` does not prove the 450 props.
  Finite checks are not Hasse for every prime.
  `decide` hits the recursion limit at p≥53. `native_decide` compiled through
  p=983 (966289 pairs). A count at p=9973 is about 99 million pairs and does
  not compile. This file does not evaluate `E143_Finset 9973`.
  Gates, still open, named in Authoring Phase 2 (`53a9a83`):
  - class number needs `BinaryQuadraticForm.classGroupEquiv`, absent from
    Mathlib v4.12.0 (`Towers/BSD/BSD_ClassNum_Upper_CLOSED.lean`,
    `Towers/BSD/BSD_ClassNumberLowerProof.lean`)
  - `BSD_L143a1_DerivAtOne` is the registry constant 0, not a derivative of
    the Hasse–Weil L-function
    (`Towers/BSD/BSD_MissingDefinitionsRegistry.lean`,
    `Towers/BSD/BSD_VanishingOrder_Kolyvagin_Closed.lean`)
  - `BSD_HasseBound_Discriminant_OPEN` is the name `True`. The forall
    `BSD_WeilHasse_Weierstrass_OPEN` is not proved, and this file does not
    prove that forall if and only if `True`
  - Euler product `Towers/BSD/BSD_EulerProduct_Closed.lean`,
    functional equation `Towers/BSD/BSD_BSD_FuncEq.lean`,
    Gross–Zagier `Towers/BSD/BSD_GrossZagier_Closed.lean`,
    Kolyvagin, Sha and Tamagawa `Towers/BSD/BSD_SHA_Tamagawa_Closed.lean`,
    regulator and Néron–Tate, tau bound
    `hasseprimset/BSD_antisupersingular.lean` and
    `hasseprimset/BSD_TauBound_small_proved.lean`
  Equalities of those names with `True` record the placeholders.
  They do not prove Gross–Zagier, Kolyvagin, Sha, Tamagawa, the regulator,
  Néron–Tate height, or the tau bound. Sentinels `trivial` on `True`,
  `rfl` of the constants 1 and 2, `∃ R, R > 0 ∧ True`, and
  `fun _ => ⟨1, rfl⟩` are not closed here.
-/

import Towers.BSD.BSD_Finite_Hasse_54_Theorem
import Towers.BSD.BSD_More_Theorems_From_54
import BSD_Assessed_Batch1
import BSD_Assessed_Batch2
import BSD_Assessed_Batch3
import BSD_Assessed_Batch4
import BSD_Assessed_Batch5
import BSD_Assessed_Batch6
import BSD_Assessed_Batch7
import BSD_Assessed_Batch8
import BSD_Assessed_Batch9
import BSD_Assessed_Batch10

open BSD_MissingDefinitionsRegistry

namespace Towers.BSD

/-- The compiled checks, the five corollaries, the ceiling, and the placeholders.
    For each checked prime the degree form is nonnegative, so both Hasse forms hold,
    and `p + 1 - a_p` is the affine count plus one.
    `(2, 0)` lies on the model by `0 = 8 - 4 - 2 - 2` in `ZMod p`.
    `a_n 64507 = 378` is coprime multiplicativity at 251 and 257.
    Not Hasse for every prime. Not modularity. Not non-torsion. Not rank 1.
    Not BSD. The 450 props stay NEEDS_AUTHORING. -/
theorem BSD_84_54_450
    (p : ℕ) [Fact p.Prime] (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) :
    BSD_Finite_Hasse_CheckedPrimes.card = 84 ∧
      (∀ q : ℕ, q ∈ BSD_Finite_Hasse_CheckedPrimes → q < 1000) ∧
      |(a_p p : ℝ)| ≤ 2 * Real.sqrt (p : ℝ) ∧
      (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) ∧
      BSD_FrobeniusDegreeNonneg_OPEN p ∧
      a_p p = (p : ℤ) - ((E143_Finset p).card : ℤ) ∧
      (p : ℤ) + 1 - a_p p = ((E143_Finset p).card : ℤ) + 1 ∧
      a_n (251 * 257) = a_n 251 * a_n 257 ∧
      a_n 251 = 21 ∧ a_n 257 = 18 ∧
      251 * 257 = 64507 ∧ a_n 64507 = 378 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₁ = 0 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₂ = -1 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₃ = 1 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₄ = -1 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₆ = -2 ∧
      (∃ x y : ℚ, y ^ 2 + y = x ^ 3 - x ^ 2 - x - 2) ∧
      ((2 : ZMod p), (0 : ZMod p)) ∈ E143_Finset p ∧
      (2 / Real.pi * Real.sqrt 143 < 8) ∧
      (True ∧ True ∧ True ∧ True) ∧
      ((BSD_ap11_card_EMPIRICAL → False → False) ∧
        (BSD_ap13_card_EMPIRICAL → False → False) ∧
        (BSD_ap17_card_EMPIRICAL → False → False) ∧
        (BSD_ap19_card_EMPIRICAL → False → False) ∧
        (BSD_ap23_card_EMPIRICAL → False → False) ∧
        (BSD_ap29_card_EMPIRICAL → False → False) ∧
        (BSD_ap191_card_EMPIRICAL → False → False)) ∧
      ((54 : ℕ) + 450 = 504) ∧
      ((54 : ℕ) < 504) ∧
      ((84 : ℕ) ≠ 54) ∧
      Nat.Prime 9973 ∧ ¬ (9973 ∣ 143) ∧
      9973 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      11 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      13 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      11 ∣ 143 ∧ 13 ∣ 143 ∧
      ((∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ+,
          |(a_n n : ℝ)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε)) →
        (∀ s : ℂ, 3 / 2 < s.re →
          Summable fun n : ℕ+ => (a_n n : ℂ) / (n : ℂ) ^ s)) ∧
      (BSD_LSeriesSummable_OPEN → True) ∧
      BSD_L143a1_DerivAtOne = 0 ∧
      BSD_HasseBound_Discriminant_OPEN = True ∧
      BSD_GrossZagier_OPEN = True ∧
      BSD_Kolyvagin_OPEN = True ∧
      BSD_Sha_OPEN = True ∧
      BSD_TamagawaConj_OPEN = True ∧
      BSD_Tamagawa_OPEN = True ∧
      BSD_EulerConvergence_OPEN = True ∧
      BSD_HeegnerPoint_OPEN = True ∧
      BSD_MissingDefinitionsRegistry.BSD_FuncEq_OPEN = True ∧
      hasseprimset_BSD_ANBound_Generator_Closed_Assessed.BSD_Regulator_OPEN_prop = True ∧
      hasseprimset_BSD_ANBound_Generator_Closed_Assessed.BSD_NeronTateHeight_OPEN_prop = True ∧
      hasseprimset_BSD_abs_prod_real_Assessed.BSD_TauBound_OPEN_prop = True ∧
      hasseprimset_BSD_antisupersingular_Assessed.BSD_PrimePowBound_to_aNBound_OPEN_prop = True := by
  rcases BSD_Finite_Hasse_54_proved p hp with ⟨hdeg, _hHasse, hap⟩
  rcases BSD_Hasse_Forms_Equiv_84 p hp with ⟨habs, hsq⟩
  rcases BSD_Coprime_Multiplicativity_Applies_84 with ⟨hmul, h251, h257, hN, h378⟩
  rcases BSD_Weierstrass_Coeff_Affine_Point_Theorem p hp with
    ⟨ha1, ha2, ha3, ha4, ha6, hQ, hmem, _hlt⟩
  rcases BSD_Minkowski_H1_AP_Ledger_Theorem with ⟨hmink, hH1, hAP⟩
  rcases BSD_54_of_504 with ⟨hsum, hlt54, hne⟩
  rcases BSD_Ceiling_Theorem with ⟨hp9973, hnd, hnset, h11, h13, h11d, h13d, _hcard⟩
  rcases BSD_Coefficient_Bound_Implies_Summability_54 p hp with ⟨himp, _habs'⟩
  have hproj : (p : ℤ) + 1 - a_p p = ((E143_Finset p).card : ℤ) + 1 := by
    rw [hap]
    ring
  have hall : ∀ q : ℕ, q ∈ BSD_Finite_Hasse_CheckedPrimes → q < 1000 :=
    fun q hq => BSD_Finite_Hasse_CheckedPrimes_lt_1000 hq
  exact ⟨BSD_Finite_Hasse_CheckedPrimes_card, hall, habs, hsq, hdeg, hap, hproj,
    hmul, h251, h257, hN, h378,
    ha1, ha2, ha3, ha4, ha6, hQ, hmem,
    hmink, hH1, hAP,
    hsum, hlt54, hne,
    hp9973, hnd, hnset, h11, h13, h11d, h13d,
    himp,
    hasseprimset_BSD_antisupersingular_Assessed.BSD_aNBound_to_LSeries_OPEN_prop,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

end Towers.BSD

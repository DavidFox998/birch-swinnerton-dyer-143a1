/-
  Partial Group C, continued. A finite Euler product, not the Hasse–Weil L-function.

  `BSD_goodLocalFactor p s` is the good-reduction factor
  `(1 - a_p p^{-s} + p^{1-2s})^{-1}`.
  `BSD_HasseWeil_partial` multiplies those factors over the 84 checked primes.
  11 and 13 divide 143 and are outside that product.

  At `p = 2` and `s = 1`, `a_2 = 0`, so the factor equals `2/3`.
  That is one local factor. It is not `L(143.a1, 1)`.

  `BSD_Rank 143 = 1` is the definition `if N = 143 then 1 else 0`.
  It does not prove the Mordell–Weil rank. The comments in `B01_EllipticCurve`
  record an LMFDB analytic rank of 1; that note is not a proof that `L(1) = 0`
  or that `L'(1) ≠ 0`. The registry `BSD_L143a1_DerivAtOne` stays the constant 0.
  Modularity of 143.a1 is not in Mathlib v4.12.0. The 12 assessed definitions
  were not rewritten. No new point count. No sorry.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Towers.BSD.BSD_Hasse_Points_2_7
import Towers.BSD.BSD_Ideal_Wiles_Clean
import Towers.BSD.B01_EllipticCurve

open Complex

namespace Towers.BSD

/-- Good-reduction Euler factor. For a composite argument the factor is `1`. -/
noncomputable def BSD_goodLocalFactor (p : ℕ) (s : ℂ) : ℂ :=
  if h : p.Prime then
    haveI : Fact p.Prime := ⟨h⟩
    (1 - (a_p p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ ((1 : ℂ) - 2 * s))⁻¹
  else
    1

/-- Product of the good factors at the 84 checked primes. Not the Euler
    product over every prime, and not a modular L-function. -/
noncomputable def BSD_HasseWeil_partial (s : ℂ) : ℂ :=
  ∏ p in BSD_Finite_Hasse_CheckedPrimes, BSD_goodLocalFactor p s

theorem BSD_HasseWeil_partial_support :
    BSD_Finite_Hasse_CheckedPrimes.card = 84 ∧
      11 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      13 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      11 ∣ 143 ∧ 13 ∣ 143 := by
  have h := BSD_conductor_factors
  exact ⟨BSD_Finite_Hasse_CheckedPrimes_card, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.1, h.2.2.2.2.1⟩

/-- `a_2 = 0`, so the local factor at `s = 1` is `(1 + 2^{-1})^{-1} = 2/3`. -/
theorem BSD_localFactor_two_at_one :
    BSD_goodLocalFactor 2 1 = (2 : ℂ) / 3 := by
  unfold BSD_goodLocalFactor
  rw [dif_pos Nat.prime_two]
  have ha : (a_p 2 : ℂ) = 0 := by exact_mod_cast BSD_ap_p2
  rw [ha, zero_mul, sub_zero]
  have hexp : ((1 : ℂ) - 2 * 1) = (-1 : ℂ) := by ring
  rw [hexp, cpow_neg_one]
  field_simp
  ring

/-- `BSD_Rank` returns 1 at conductor 143 by its definition, and 0 at
    conductor 1. This is not the Mordell–Weil theorem. -/
theorem BSD_rank_placeholder_values :
    BSD_Rank 143 = 1 ∧ BSD_Rank 1 = 0 := by
  constructor <;> rfl

/-- The registry derivative stays 0. The partial product above is not
    differentiated here. `L_143a1` stays the Prop `True`. -/
theorem BSD_hasseWeil_partial_not_registry_derivative :
    BSD_MissingDefinitionsRegistry.BSD_L143a1_DerivAtOne = (0 : ℝ) ∧
      BSD_MissingDefinitionsRegistry.L_143a1 = True ∧
      BSD_goodLocalFactor 2 1 = (2 : ℂ) / 3 ∧
      (84 : ℕ) ≠ 54 :=
  ⟨rfl, rfl, BSD_localFactor_two_at_one, BSD_54_of_504.2.2⟩

end Towers.BSD

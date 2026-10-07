/-
  Partial Group B, continued. Reduced forms and a Minkowski representative.

  Mathlib v4.12.0 has no `BinaryQuadraticForm` and no `classGroupEquiv`.
  This file does not define that equivalence.

  `reducedForms143` is the list of 10 reduced positive-definite forms of
  discriminant -143. Each is reduced, and every reduced form is on the list.
  That count is not `NumberField.classNumber K`.

  `NumberField.exists_ideal_in_class_of_norm_le` puts an integral ideal of
  norm at most the Minkowski bound in every class. For this field the bound
  is `(2/π)√143 < 8`, so the norm is at most 7. Counting those ideals, and
  proving `classNumber K ≤ 10`, is not done here.

  The lower bound `10 ≤ classNumber K` is cited. `classNumber K = 10` stays
  NEEDS_AUTHORING. The 26 assessed definitions were not rewritten.
  No sorry.
-/

import Towers.BSD.BSD_ReducedForms
import Towers.BSD.BSD_ClassNumber_Lower_Clean

open NumberField

namespace Towers.BSD

/-- Ten reduced forms, each reduced, and no others. Cites
    `BSD_ReducedForms`. This is not the class number. -/
theorem BSD_reduced_forms_are_ten :
    reducedForms143.length = 10 ∧
      (∀ t ∈ reducedForms143, IsReducedBQF143 t.1 t.2.1 t.2.2) ∧
      (∀ a b c : ℤ, IsReducedBQF143 a b c → (a, b, c) ∈ reducedForms143) :=
  ⟨BSD_numReducedForms143, reducedForms143_all_reduced,
    fun a b c h => reducedForms143_complete a b c h⟩

/-- Every ideal class contains an integral ideal of absolute norm at most 7.
    The bound is Mathlib's Minkowski estimate, specialized with
    `finrank ℚ K = 2`, one complex place, and `discr K = -143`.
    This is not `classNumber K ≤ 10`. -/
theorem BSD_every_class_has_norm_le_seven (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰,
      ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 7 := by
  obtain ⟨I, hI, hle⟩ := exists_ideal_in_class_of_norm_le C
  have hfin : finrank ℚ K = 2 := BSD_finrank_proved
  have hcx : NrComplexPlaces K = 1 := nrComplexPlaces_one_BSD BSD_finrank_proved
  have hdisc : discr K = -143 := BSD_K_disc_neg143
  have hbound :
      (4 / Real.pi) ^ NrComplexPlaces K *
        ((finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) *
          Real.sqrt |discr K|) =
        2 / Real.pi * Real.sqrt 143 := by
    rw [hcx, hfin, hdisc]
    norm_num
    ring
  have hlt : (4 / Real.pi) ^ NrComplexPlaces K *
      ((finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) *
        Real.sqrt |discr K|) < 8 := by
    rw [hbound]
    exact minkowski_lt_eight_BSD
  have hnorm : (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) < 8 := lt_of_le_of_lt hle hlt
  have hnat : Ideal.absNorm (I : Ideal (𝓞 K)) < 8 := by exact_mod_cast hnorm
  refine ⟨I, hI, ?_⟩
  omega

/-- The form count is 10, the class number is at least 10, and every class
    has an ideal of norm at most 7. `classNumber K ≤ 10` is not proved.
    `BinaryQuadraticForm.classGroupEquiv` is not defined. -/
theorem BSD_classNumber_eq_10_needs_gauss_bridge :
    reducedForms143.length = 10 ∧
      10 ≤ NumberField.classNumber K ∧
      (∀ C : ClassGroup (𝓞 K), ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 7) :=
  ⟨BSD_numReducedForms143, BSD_classNumber_lower_bound,
    BSD_every_class_has_norm_le_seven⟩

end Towers.BSD

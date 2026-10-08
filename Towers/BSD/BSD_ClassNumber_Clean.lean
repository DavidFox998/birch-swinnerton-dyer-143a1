/-
  Group B, rewritten under the clean names.

  The compiled pieces are the ten reduced forms, the Minkowski representative
  of absolute norm at most 7, and the lower bound `10 ≤ classNumber K`.
  They are cited here under `BSD_reduced_forms_ten` and
  `BSD_minkowski_bound_norm_le_seven`.

  `BSD_classNumber_le_of_surjection` is the counting step that does follow:
  a surjection onto the class group from a finite type bounds the class
  number by that cardinality. `BSD_classNumber_le_ten` and
  `BSD_classNumber_eq_ten` apply it when that cardinality is at most 10,
  and then use the lower bound. The surjection is a hypothesis.

  The lattices in `ℤ[ω]` of index at most 7 that are stable under
  multiplication by `ω` number 14: one of norm 1, two of norm 2, two of
  norm 3, three of norm 4, none of norm 5, four of norm 6, and two of
  norm 7. That external count is not a Lean theorem. It shows why
  "at most 10 ideals of norm ≤ 7" is the wrong bound, so this file does
  not conclude `classNumber K ≤ 10` from the Minkowski representative alone.
  `BinaryQuadraticForm.classGroupEquiv` is absent from Mathlib v4.12.0
  and is not defined here.

  The 26 assessed definitions were not rewritten. No sorry.
-/

import Towers.BSD.BSD_ClassGroupEquiv_Clean
import Towers.BSD.BSD_Finite_Hasse_54_Theorem
import Mathlib.Data.Fintype.Card

open NumberField
open scoped nonZeroDivisors

namespace Towers.BSD

/-- Ten reduced positive-definite forms of discriminant `-143`.
    This is not `classNumber K`. -/
theorem BSD_reduced_forms_ten :
    reducedForms143.length = 10 ∧
      (∀ t ∈ reducedForms143, IsReducedBQF143 t.1 t.2.1 t.2.2) ∧
      (∀ a b c : ℤ, IsReducedBQF143 a b c → (a, b, c) ∈ reducedForms143) :=
  BSD_reduced_forms_are_ten

/-- Every ideal class contains an integral ideal of absolute norm at most 7. -/
theorem BSD_minkowski_bound_norm_le_seven (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰,
      ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 7 :=
  BSD_every_class_has_norm_le_seven C

/-- A finite set of representatives that hits every class bounds the class number. -/
theorem BSD_classNumber_le_of_surjection
    {ι : Type*} [Fintype ι] (f : ι → ClassGroup (𝓞 K))
    (hf : Function.Surjective f) :
    NumberField.classNumber K ≤ Fintype.card ι := by
  simpa [NumberField.classNumber] using Fintype.card_le_of_surjective f hf

/-- `classNumber K ≤ 10` given a set of at most 10 class representatives.
    The set is not constructed in this file. -/
theorem BSD_classNumber_le_ten
    {ι : Type*} [Fintype ι] (f : ι → ClassGroup (𝓞 K))
    (hf : Function.Surjective f) (hcard : Fintype.card ι ≤ 10) :
    NumberField.classNumber K ≤ 10 :=
  (BSD_classNumber_le_of_surjection f hf).trans hcard

/-- `classNumber K = 10` given those representatives and the proved lower bound.
    The representatives are a hypothesis. -/
theorem BSD_classNumber_eq_ten
    {ι : Type*} [Fintype ι] (f : ι → ClassGroup (𝓞 K))
    (hf : Function.Surjective f) (hcard : Fintype.card ι ≤ 10) :
    NumberField.classNumber K = 10 :=
  le_antisymm (BSD_classNumber_le_ten f hf hcard) BSD_classNumber_lower_bound

/-- The form count, the lower bound, and the norm bound, together.
    They do not discharge the surjection in `BSD_classNumber_eq_ten`. -/
theorem BSD_classNumber_still_needs_representatives :
    reducedForms143.length = 10 ∧
      10 ≤ NumberField.classNumber K ∧
      (∀ C : ClassGroup (𝓞 K), ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 7) ∧
      (84 : ℕ) ≠ 54 :=
  ⟨BSD_numReducedForms143, BSD_classNumber_lower_bound,
    BSD_minkowski_bound_norm_le_seven, BSD_54_of_504.2.2⟩

end Towers.BSD

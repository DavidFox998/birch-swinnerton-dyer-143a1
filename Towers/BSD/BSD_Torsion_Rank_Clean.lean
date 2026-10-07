/-
  Partial Group F. The affine point `(2, 0)` on each checked prime.

  Membership in `E143_Finset p` is the identity already compiled in
  `BSD_Weierstrass_Coeff_Affine_Point_Theorem`: `0 = 8 - 4 - 2 - 2` in
  `ZMod p`. No new point count.

  That membership does not prove that `(2, 0)` is non-torsion, a generator,
  of infinite order, or that the Mordell–Weil rank is 1. It does not prove
  BSD. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, the regulator, and
  Néron–Tate height stay NEEDS_AUTHORING.

  The equalities with `True`, and the constants `BSD_TorsCard = 1` and
  `BSD_TamagawaProd = 1`, record placeholders. They do not close those
  sentinels. No sorry.
-/

import Towers.BSD.BSD_More_Theorems_From_54

namespace Towers.BSD

/-- `(2, 0)` lies in `E143_Finset p` for each checked prime.
    Cites `BSD_Weierstrass_Coeff_Affine_Point_Theorem`.
    The ring identity is `0 = 8 - 4 - 2 - 2` in `ZMod p`. -/
theorem BSD_affine_point_in_E143_Finset_checked
    (p : ℕ) [Fact p.Prime] (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) :
    ((2 : ZMod p), (0 : ZMod p)) ∈ E143_Finset p := by
  rcases BSD_Weierstrass_Coeff_Affine_Point_Theorem p hp with
    ⟨_, _, _, _, _, _, hmem, _⟩
  exact hmem

/-- The affine point is in each checked `E143_Finset`. The registry names
    for Heegner, Gross–Zagier, Kolyvagin, Sha, and Tamagawa are `True`.
    `BSD_TorsCard` is the constant 1. `BSD_TamagawaProd` is the constant 1.
    The regulator and Néron–Tate assessed names are `True`.
    The non-torsion assessed name is `True`.
    These equalities do not prove non-torsion, a generator, rank 1, or BSD.
    The sentinels stay unclosed. -/
theorem BSD_affine_not_proved_non_torsion
    (p : ℕ) [Fact p.Prime] (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) :
    ((2 : ZMod p), (0 : ZMod p)) ∈ E143_Finset p ∧
      BSD_MissingDefinitionsRegistry.BSD_HeegnerPoint_OPEN = True ∧
      BSD_MissingDefinitionsRegistry.BSD_GrossZagier_OPEN = True ∧
      BSD_MissingDefinitionsRegistry.BSD_Kolyvagin_OPEN = True ∧
      BSD_MissingDefinitionsRegistry.BSD_Sha_OPEN = True ∧
      BSD_MissingDefinitionsRegistry.BSD_Tamagawa_OPEN = True ∧
      BSD_MissingDefinitionsRegistry.BSD_TamagawaConj_OPEN = True ∧
      BSD_MissingDefinitionsRegistry.BSD_TorsCard = 1 ∧
      BSD_MissingDefinitionsRegistry.BSD_TamagawaProd = 1 ∧
      BSD_MissingDefinitionsRegistry.BSD_LeadingCoeff 143 = 1 ∧
      hasseprimset_BSD_ANBound_Generator_Closed_Assessed.BSD_Regulator_OPEN_prop = True ∧
      hasseprimset_BSD_ANBound_Generator_Closed_Assessed.BSD_NeronTateHeight_OPEN_prop = True ∧
      Towers_BSD_BSD_SemistableReduction_CLOSED_Assessed.BSD_NonTorsion_OPEN_prop = True ∧
      Towers_BSD_BSD_TorsionBound_CLOSED_Assessed.BSD_TorsionBound_p2_OPEN_prop = True := by
  refine ⟨BSD_affine_point_in_E143_Finset_checked p hp,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Towers.BSD

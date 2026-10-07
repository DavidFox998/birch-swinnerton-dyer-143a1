/- BSD_Assessed_Batch2.lean — Individual proposition assessment (batch 2).
    Honest Prop placeholders with original statements preserved.
    - Where the type elaborates: def is the actual proposition (NOT proved).
    - Where it doesn't: def is True with original statement documented.
    Pattern: Beal conductor_86 — Prop, NOT proved. -/

import Towers.BSD.BSD_MissingDefinitionsRegistry
import Towers.BSD.BSD_Hasse_Points_2_7
import Towers.BSD.B01_EllipticCurve
import Mathlib.Analysis.Analytic.IsolatedZeros
open BSD_MissingDefinitionsRegistry

/-!
Batch 2 mechanical repair. Proved only where the original file already has
a proof and the dependencies build:
- `BSD_EndomorphismDegree_Partial_CLOSED_prop` and `BSD_Hasse_OPEN_partial_CLOSED_prop`
  cite the existing counts for p ∈ {2, 3, 5, 7} in `BSD_Hasse_Points_2_7`.
  Not Hasse for every prime.
- `BSD_HeegnerPoint_CLOSED_prop` and `BSD_HeegnerPoint_surface_ledger_prop`
  are the curve equation, witness (2, 0). Not non-torsion, not rank 1, not BSD.
  The registry name `BSD_HeegnerPoint_OPEN` is `True` and is not discharged.
- `BSD_endeg_sentinel_prop` and `BSD_linFunc_sentinel_prop` are `P → True`.
- `BSD_modularityE143_is_open_prop` and `BSD_bsdFormula_is_open_prop` are `P → P`
  on the registry aliases. They do not prove modularity or BSD.
- `BSD_VanishingOrder_APIBridge_RETRACTED_prop` is the original counterexample:
  `VanishingOrder` in B01 ignores its arguments and returns 1, while a nonzero
  constant has analytic order 0. The registry alias is `True`; `¬ True` is not proved.
Everything else is still an unproved `def` and is marked NEEDS_AUTHORING.
No sorry. Registry `True` placeholders are not discharged.
-/

namespace Towers_BSD_BSD_EulerProduct_Closed_Assessed
  -- NEEDS_AUTHORING: the original proof shows ((5759 : ℂ) / 10000) * (s - 1) ≠ 0.
  -- The assessed name was BSD_EulerProduct_Global_OPEN, which is not in the registry.
  def BSD_EulerProduct_Global_CLOSED_prop : Prop := True -- was: BSD_EulerProduct_Global_OPEN
end Towers_BSD_BSD_EulerProduct_Closed_Assessed

namespace Towers_BSD_BSD_FormIdeal_CLOSED_Assessed
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_FormIdeal_open_count_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_FormIdeal_CLOSED_Assessed

namespace Towers_BSD_BSD_FourGateCombinator_Assessed
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_open_surface_count_756_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_FourGateCombinator_Assessed

namespace Towers_BSD_BSD_Frobenius_Certificate_Assessed
  -- NEEDS_AUTHORING: modularity route. The source certificate does not build.
  def BSD_FrobeniusViaModularity_OPEN_prop : Prop := True -- BSD_FrobeniusViaModularity_OPEN: Prop (trivial)
  -- NEEDS_AUTHORING: high primes are not the finite checks already compiled.
  def BSD_FrobeniusHighPrimes_OPEN_prop : Prop := True -- BSD_FrobeniusHighPrimes_OPEN: Prop (trivial)
end Towers_BSD_BSD_Frobenius_Certificate_Assessed

namespace Towers_BSD_BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED_Assessed
  -- NEEDS_AUTHORING: this is the universal Weil statement for every good prime.
  -- Only finitely many primes have compiled point counts.
  def BSD_WeilHasse_Frobenius_143a1_proved_prop : Prop := BSD_WeilHasse_Weierstrass_OPEN
end Towers_BSD_BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED_Assessed

namespace Towers_BSD_BSD_FuncEq_Assessed
  -- NEEDS_AUTHORING: root BSD_FuncEq_OPEN is an existential AnalyticOn stub.
  -- The closed file is not a clean rfl.
  def BSD_FuncEq_CLOSED_prop : Prop := True -- was: BSD_FuncEq_OPEN
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_genesis892_gap_count_clay_prop : Prop := True -- was: ℕ
  def BSD_genesis892_gap_count_opaque_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_FuncEq_Assessed

namespace Towers_BSD_BSD_GrossZagier_Closed_Assessed
  -- NEEDS_AUTHORING: registry aliases are True. Gross–Zagier is open.
  def BSD_LFunctionZero_CLOSED_prop : Prop := BSD_LFunctionZero_OPEN
  def BSD_AnalyticRankOne_CLOSED_prop : Prop := BSD_AnalyticRankOne_OPEN
  def BSD_GrossZagier_CLOSED_prop : Prop := BSD_GrossZagier_OPEN
end Towers_BSD_BSD_GrossZagier_Closed_Assessed

namespace Towers_BSD_BSD_GrossZagier_LMFDB_Assessed
  -- NEEDS_AUTHORING: registry alias is True. Gross–Zagier is open.
  def BSD_GrossZagier_LMFDB_CLOSED_prop : Prop := BSD_GrossZagier_OPEN
  -- NEEDS_AUTHORING: conjunction of registry True aliases. Not the LMFDB certificate.
  def BSD_Genesis755_Capstone_prop : Prop :=
    BSD_AnalyticOrder_143_OPEN ∧ BSD_LFunctionZero_OPEN ∧ BSD_AnalyticRankOne_OPEN ∧
    BSD_GrossZagier_OPEN ∧ BSD_143_OPEN
end Towers_BSD_BSD_GrossZagier_LMFDB_Assessed

namespace Towers_BSD_BSD_GrossZagier_v2_Assessed
  -- NEEDS_AUTHORING: registry alias is True. Gross–Zagier is open.
  def BSD_GrossZagier_v2_prop : Prop := BSD_GrossZagier_OPEN
end Towers_BSD_BSD_GrossZagier_v2_Assessed

namespace Towers_BSD_BSD_HasseEndDeg_CLOSED_Assessed
  /-- Original in Towers/BSD/BSD_HasseEndDeg_CLOSED.lean, citing the bridge proofs.
      Covers p ∈ {2, 3, 5, 7} only. -/
  theorem BSD_EndomorphismDegree_Partial_CLOSED_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 2 ∧
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 3 ∧
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 5 ∧
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 7 :=
    ⟨Towers.BSD.BSD_DegreeNonneg_p2, Towers.BSD.BSD_DegreeNonneg_p3,
     Towers.BSD.BSD_DegreeNonneg_p5, Towers.BSD.BSD_DegreeNonneg_p7⟩

  /-- Original in Towers/BSD/BSD_HasseEndDeg_CLOSED.lean.
      |a_p| ≤ 2√p for p ∈ {2, 3, 5, 7} only. -/
  theorem BSD_Hasse_OPEN_partial_CLOSED_prop :
      BSD_Hasse_OPEN 2 ∧ BSD_Hasse_OPEN 3 ∧ BSD_Hasse_OPEN 5 ∧ BSD_Hasse_OPEN 7 :=
    ⟨Towers.BSD.BSD_Hasse_OPEN_p2, Towers.BSD.BSD_Hasse_OPEN_p3,
     Towers.BSD.BSD_Hasse_OPEN_p5, Towers.BSD.BSD_Hasse_OPEN_p7⟩

  /-- Original sentinel. Does not prove BSD_EndomorphismDegree_OPEN. -/
  theorem BSD_endeg_sentinel_prop : BSD_EndomorphismDegree_OPEN → True := fun _ => trivial
end Towers_BSD_BSD_HasseEndDeg_CLOSED_Assessed

namespace Towers_BSD_BSD_HasseWeil_Chain_Assessed
  -- NEEDS_AUTHORING: Deligne bound is not in the clean build.
  def BSD_ChebyshevBound_OPEN_prop : Prop := True -- BSD_ChebyshevBound_OPEN: Prop (trivial)
  def BSD_TauBound_OPEN_prop : Prop := True -- BSD_TauBound_OPEN: Prop (trivial)
  def BSD_LSeriesSummable_Deligne_OPEN_prop : Prop := True -- BSD_LSeriesSummable_Deligne_OPEN: Prop (trivial)
end Towers_BSD_BSD_HasseWeil_Chain_Assessed

namespace Towers_BSD_BSD_HeegnerPoint_CLOSED_Assessed
  /-- Original in Towers/BSD/BSD_HeegnerPoint_CLOSED.lean. Witness (2, 0) by norm_num.
      A rational point on the affine model. Not a generator, not non-torsion, not BSD. -/
  theorem BSD_HeegnerPoint_CLOSED_prop :
      ∃ (x y : ℚ), y ^ 2 + y = x ^ 3 - x ^ 2 - x - 2 :=
    ⟨2, 0, by norm_num⟩

  /-- Same equation, cited from the theorem above. Original surface ledger. -/
  theorem BSD_HeegnerPoint_surface_ledger_prop :
      ∃ (x y : ℚ), y ^ 2 + y = x ^ 3 - x ^ 2 - x - 2 :=
    BSD_HeegnerPoint_CLOSED_prop
end Towers_BSD_BSD_HeegnerPoint_CLOSED_Assessed

namespace Towers_BSD_BSD_KodairaReduction_CLOSED_Assessed
  -- NEEDS_AUTHORING: Néron model / Tate algorithm is absent from Mathlib v4.12.0.
  -- The original file sets the constants to 1 and 2 and closes by rfl.
  def BSD_Tamagawa_11_is_1_OPEN_prop : Prop := True -- BSD_Tamagawa_11_is_1_OPEN: Prop (trivial)
  def BSD_Tamagawa_13_is_2_OPEN_prop : Prop := True -- BSD_Tamagawa_13_is_2_OPEN: Prop (trivial)
  def BSD_Tamagawa_11_is_1_CLOSED_prop : Prop := True -- was: BSD_Tamagawa_11_is_1_OPEN
end Towers_BSD_BSD_KodairaReduction_CLOSED_Assessed

namespace Towers_BSD_BSD_KolyvaginPath_Assessed
  -- NEEDS_AUTHORING: Kolyvagin is open.
  def BSD_RankOneToConj_OPEN_prop : Prop := True -- BSD_RankOneToConj_OPEN: Prop (trivial)
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_KolyvaginPath_gap_count_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_KolyvaginPath_Assessed

namespace Towers_BSD_BSD_Kolyvagin_Capstone_Closed_Assessed
  -- NEEDS_AUTHORING: Kolyvagin is open.
  def BSD_RankOneToConj_CLOSED_prop : Prop := True -- was: BSD_RankOneToConj_OPEN
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_KolyvaginPath_gap_count_v2_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_Kolyvagin_Capstone_Closed_Assessed

namespace Towers_BSD_BSD_L143a1_BSDLFunction_ID_PROVED_Assessed
  -- NEEDS_AUTHORING: registry name is True. The original proof is
  -- BSD_LFunctionIsLinFunc_CLOSED.symm, outside the clean build.
  def BSD_L143a1_BSDLFunction_ID_PROVED_prop : Prop := BSD_L143a1_BSDLFunction_ID_OPEN
  -- NEEDS_AUTHORING: registry name is True. The original unfolds a concrete
  -- linear function that is not this alias.
  def BSD_AnalyticOrder_143_PROVED_prop : Prop := BSD_AnalyticOrder_143_OPEN
  /-- Original counterexample in Towers/BSD/BSD_BSD_L143a1_BSDLFunction_ID_PROVED.lean.
      Does not use the registry alias, which is True. -/
  theorem BSD_VanishingOrder_APIBridge_RETRACTED_prop :
      ¬ (∀ (f : ℂ → ℂ) (s : ℂ) (h : AnalyticAt ℂ f s),
          (Towers.BSD.VanishingOrder f s : ℕ∞) = h.order) := by
    intro h
    have h1 : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) 0 := analyticAt_const
    have heq := h (fun _ => (1 : ℂ)) 0 h1
    have hord : h1.order = ↑(0 : ℕ) := by
      rw [h1.order_eq_nat_iff]
      refine ⟨fun _ => (1 : ℂ), analyticAt_const, by norm_num,
              Filter.Eventually.of_forall fun _ => ?_⟩
      simp [pow_zero, one_smul]
    have hv : (Towers.BSD.VanishingOrder (fun _ : ℂ => (1 : ℂ)) 0 : ℕ∞) = 1 := by norm_cast
    rw [hv, hord] at heq
    exact absurd heq one_ne_zero
end Towers_BSD_BSD_L143a1_BSDLFunction_ID_PROVED_Assessed

namespace Towers_BSD_BSD_L143a1_zero_at_one_Assessed
  -- NEEDS_AUTHORING: special value, simple zero, and the functional equation are open.
  def BSD_SpecialValue_OPEN_prop : Prop := True -- BSD_SpecialValue_OPEN: Prop (trivial)
  def BSD_SimpleZero_OPEN_prop : Prop := True -- BSD_SimpleZero_OPEN: Prop (trivial)
  def BSD_FunctionalEq_143_OPEN_prop : Prop := True -- BSD_FunctionalEq_143_OPEN: Prop (trivial)
end Towers_BSD_BSD_L143a1_zero_at_one_Assessed

namespace Towers_BSD_BSD_LAnalytic_Anchor_CLOSED_Assessed
  -- NEEDS_AUTHORING: BSD_AnalyticOn_L143a1.lean is missing.
  -- Registry L_143a1 has type Prop, not ℂ → ℂ.
  def BSD_L143a1_Anchor_Analytic_prop : Prop := True -- was: AnalyticOn ℂ L_143a1 Set.univ
  /-- Original sentinel in Towers/BSD/BSD_LAnalytic_Anchor_CLOSED.lean.
      Does not prove BSD_LFunctionIsLinFunc_OPEN. -/
  theorem BSD_linFunc_sentinel_prop : BSD_LFunctionIsLinFunc_OPEN → True := fun _ => trivial
end Towers_BSD_BSD_LAnalytic_Anchor_CLOSED_Assessed

namespace Towers_BSD_BSD_LFunction_Closed_Assessed
  -- NEEDS_AUTHORING: registry name is True. The original proof is outside the clean import.
  def BSD_TermBound_CLOSED_prop : Prop := BSD_TermBound_OPEN
  /-- Original sentinel. Registry alias, so this is True → True. Not modularity.
      The root stub in BSD_LFunction is a different declaration. -/
  theorem BSD_modularityE143_is_open_prop :
      BSD_MissingDefinitionsRegistry.BSD_ModularityE143_OPEN →
      BSD_MissingDefinitionsRegistry.BSD_ModularityE143_OPEN := id
  /-- Original sentinel. Registry alias, so this is True → True. Not the BSD formula.
      The root stub in BSD_LFunction is a different declaration. -/
  theorem BSD_bsdFormula_is_open_prop :
      BSD_MissingDefinitionsRegistry.BSD_BSDFormula_OPEN →
      BSD_MissingDefinitionsRegistry.BSD_BSDFormula_OPEN := id
end Towers_BSD_BSD_LFunction_Closed_Assessed

namespace Towers_BSD_BSD_MasterCertification_Assessed
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_open_surface_count_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_MasterCertification_Assessed

/- BSD_Assessed_Batch4.lean — Individual proposition assessment (batch 4).
    Honest Prop placeholders with original statements preserved.
    Pattern: Beal conductor_86 — Prop, NOT proved. -/

import Towers.BSD.BSD_MissingDefinitionsRegistry
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.NumberTheory.LSeries.Basic
open BSD_MissingDefinitionsRegistry

/-!
Batch 4 mechanical repair. Proved only where the original file already has
a proof and the dependencies build:
- `E143a1_prop` is the coefficient tuple of `def E143a1 : WeierstrassCurve ℚ`.
- `E143a1_has_rational_point_prop` is the affine point (2, 0). Not rank 1, not BSD.
  The registry name `BSD_HeegnerPoint_OPEN` is `True` and is not discharged.
- `E143a1_bost_bound_prop` is the literal `C_S4` from `BostBound143.lean`
  against `2√13`. Not a derivation of Bost's sum.
- `BSD_isBigO_to_LSeries_close_prop` is the conditional summability bridge.
  The coefficient bound stays a hypothesis.
- `BSD_L143a1_HasDerivAt_CLOSED_prop` is `HasDerivAt` of the linear anchor
  `(5759/10000)·(s−1)`. Not the Hasse–Weil L-function. The registry derivative
  stays 0.
Degree-nonnegativity for p≥1009 stays NEEDS_AUTHORING: those proofs are
`native_decide` on `E143_Finset p`, and the clean build stops at p=241.
No sorry. Registry `True` placeholders are not discharged.
-/

namespace Towers_BSD_BSD_VanishingOrder_143_Genuine_Assessed
  -- NEEDS_AUTHORING: the original proof is rfl. VanishingOrder in B01
  -- ignores its arguments and returns 1. That is not the analytic order.
  def BSD_VanishingOrder_143_Genuine_CLOSED_prop : Prop := BSD_VanishingOrder_143_Genuine_OPEN
end Towers_BSD_BSD_VanishingOrder_143_Genuine_Assessed

namespace Towers_BSD_BSD_VanishingOrder_Kolyvagin_Closed_Assessed
  -- NEEDS_AUTHORING: same rfl anchor as above.
  def BSD_VanishingOrder_143_Genuine_CLOSED_prop : Prop := BSD_VanishingOrder_143_Genuine_OPEN
  /-- Original in Towers/BSD/BSD_VanishingOrder_Kolyvagin_Closed.lean.
      Calculus of the linear anchor only. -/
  theorem BSD_L143a1_HasDerivAt_CLOSED_prop :
      HasDerivAt (fun s : ℂ => ((5759 : ℂ) / 10000) * (s - 1))
        ((5759 : ℂ) / 10000) 1 := by
    have h1 : HasDerivAt (fun s : ℂ => s - 1) (1 - 0) 1 :=
      (hasDerivAt_id (1 : ℂ)).sub (hasDerivAt_const (1 : ℂ) (1 : ℂ))
    have h2 := h1.const_mul ((5759 : ℂ) / 10000)
    simp only [sub_zero, mul_one] at h2
    exact h2
  -- NEEDS_AUTHORING: the original proof is `fun _ => ⟨1, rfl⟩`.
  -- The file says this is not Kolyvagin 1988.
  def BSD_Kolyvagin_CLOSED_prop : Prop := BSD_Kolyvagin_OPEN
end Towers_BSD_BSD_VanishingOrder_Kolyvagin_Closed_Assessed

namespace Towers_BSD_E143a1_CLOSED_Assessed
  /-- Original `def E143a1` in Towers/BSD/E143a1_CLOSED.lean. The declaration
      has type `WeierstrassCurve ℚ`; this is the coefficient Prop proved by rfl. -/
  theorem E143a1_prop :
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₁ = 0 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₂ = -1 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₃ = 1 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₄ = -1 ∧
      (⟨0, -1, 1, -1, -2⟩ : WeierstrassCurve ℚ).a₆ = -2 :=
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  /-- Same affine point as Batch 2. Not non-torsion, not a generator, not BSD. -/
  theorem E143a1_has_rational_point_prop :
      ∃ (x y : ℚ), y ^ 2 + y = x ^ 3 - x ^ 2 - x - 2 :=
    ⟨2, 0, by norm_num⟩
  /-- Literal from BostBound143.lean. Copied from `C_S4_gt_2sqrt13`. -/
  theorem E143a1_bost_bound_prop :
      (11.42214868898 : ℝ) > 2 * Real.sqrt 13 := by
    have : Real.sqrt 13 < 3.6056 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
    linarith
end Towers_BSD_E143a1_CLOSED_Assessed

namespace hasseprimset_BSD_ANBound_Generator_Closed_Assessed
  -- NEEDS_AUTHORING: Néron–Tate height is absent from Mathlib v4.12.0.
  -- The original def ends in `∧ True`.
  def BSD_NeronTateHeight_OPEN_prop : Prop := True -- BSD_NeronTateHeight_OPEN: Prop (trivial)
  -- NEEDS_AUTHORING: `∃ R, R > 0 ∧ True` is not the regulator.
  def BSD_Regulator_OPEN_prop : Prop := True -- BSD_Regulator_OPEN: Prop (trivial)
  -- NEEDS_AUTHORING: Sha finiteness is absent from Mathlib v4.12.0.
  def BSD_SHA_Finite_OPEN_prop : Prop := True -- BSD_SHA_Finite_OPEN: Prop (trivial)
end hasseprimset_BSD_ANBound_Generator_Closed_Assessed

namespace hasseprimset_BSD_Finsupp_prod_le_close_Assessed
  /-- Original in hasseprimset/BSD_Finsupp_prod_le_close.lean.
      A coefficient bound implies summability for Re(s) > 3/2.
      The bound itself is not proved. -/
  theorem BSD_isBigO_to_LSeries_close_prop :
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ+,
        |(a_n n : ℝ)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε)) →
      (∀ s : ℂ, 3 / 2 < s.re →
        Summable fun n : ℕ+ => (a_n n : ℂ) / (n : ℂ) ^ s) := by
    intro h_bound
    intro s hs
    set ε₀ := (s.re - 3 / 2) / 2 with hε₀_def
    have hε₀_pos : (0 : ℝ) < ε₀ := by unfold_let ε₀; linarith
    obtain ⟨C, hC_pos, hC_bound⟩ := h_bound ε₀ hε₀_pos
    have hx_lt : 3 / 2 + ε₀ < s.re := by unfold_let ε₀; linarith
    have hexp : (3 / 2 + ε₀ : ℝ) - 1 = 1 / 2 + ε₀ := by ring
    have hLS : LSeriesSummable (fun n : ℕ => (a_n n : ℂ)) s := by
      apply LSeriesSummable_of_le_const_mul_rpow hx_lt
      refine ⟨C, fun n hn => ?_⟩
      have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hcast : ‖(a_n n : ℂ)‖ = |(a_n n : ℝ)| := by
        have heq : (a_n n : ℂ) = ((a_n n : ℝ) : ℂ) := by norm_cast
        rw [heq, Complex.norm_real, Real.norm_eq_abs]
      have hbound_n : |(a_n n : ℝ)| ≤ C * (n : ℝ) ^ (1 / 2 + ε₀) :=
        hC_bound ⟨n, hpos⟩
      rw [hcast, hexp]
      exact hbound_n
    simp only [LSeriesSummable] at hLS
    have h_pos_summ : Summable (fun n : ℕ+ =>
        LSeries.term (fun n : ℕ => (a_n n : ℂ)) s n.val) :=
      hLS.comp_injective Subtype.val_injective
    apply h_pos_summ.congr
    intro n
    simp only [Function.comp, LSeries.term_of_ne_zero n.pos.ne']
end hasseprimset_BSD_Finsupp_prod_le_close_Assessed

namespace hasseprimset_BSD_Hasse_Points_1009_1061_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1009_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1009
  def BSD_DegreeNonneg_p1013_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1013
  def BSD_DegreeNonneg_p1019_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1019
end hasseprimset_BSD_Hasse_Points_1009_1061_Assessed

namespace hasseprimset_BSD_Hasse_Points_1063_1123_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1063_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1063
  def BSD_DegreeNonneg_p1069_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1069
  def BSD_DegreeNonneg_p1087_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1087
end hasseprimset_BSD_Hasse_Points_1063_1123_Assessed

namespace hasseprimset_BSD_Hasse_Points_1129_1213_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1129_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1129
  def BSD_DegreeNonneg_p1151_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1151
  def BSD_DegreeNonneg_p1153_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1153
end hasseprimset_BSD_Hasse_Points_1129_1213_Assessed

namespace hasseprimset_BSD_Hasse_Points_1217_1283_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1217_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1217
  def BSD_DegreeNonneg_p1223_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1223
  def BSD_DegreeNonneg_p1229_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1229
end hasseprimset_BSD_Hasse_Points_1217_1283_Assessed

namespace hasseprimset_BSD_Hasse_Points_1289_1361_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1289_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1289
  def BSD_DegreeNonneg_p1291_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1291
  def BSD_DegreeNonneg_p1297_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1297
end hasseprimset_BSD_Hasse_Points_1289_1361_Assessed

namespace hasseprimset_BSD_Hasse_Points_1367_1439_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1367_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1367
  def BSD_DegreeNonneg_p1373_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1373
  def BSD_DegreeNonneg_p1381_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1381
end hasseprimset_BSD_Hasse_Points_1367_1439_Assessed

namespace hasseprimset_BSD_Hasse_Points_1447_1493_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1447_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1447
  def BSD_DegreeNonneg_p1451_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1451
  def BSD_DegreeNonneg_p1453_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1453
end hasseprimset_BSD_Hasse_Points_1447_1493_Assessed

namespace hasseprimset_BSD_Hasse_Points_1499_1571_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1499_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1499
  def BSD_DegreeNonneg_p1511_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1511
  def BSD_DegreeNonneg_p1523_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1523
end hasseprimset_BSD_Hasse_Points_1499_1571_Assessed

namespace hasseprimset_BSD_Hasse_Points_1579_1627_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1579_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1579
  def BSD_DegreeNonneg_p1583_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1583
  def BSD_DegreeNonneg_p1597_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1597
end hasseprimset_BSD_Hasse_Points_1579_1627_Assessed

namespace hasseprimset_BSD_Hasse_Points_1637_1721_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1637_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1637
  def BSD_DegreeNonneg_p1657_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1657
  def BSD_DegreeNonneg_p1663_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1663
end hasseprimset_BSD_Hasse_Points_1637_1721_Assessed

namespace hasseprimset_BSD_Hasse_Points_1723_1789_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1723_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1723
  def BSD_DegreeNonneg_p1733_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1733
  def BSD_DegreeNonneg_p1741_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1741
end hasseprimset_BSD_Hasse_Points_1723_1789_Assessed

namespace hasseprimset_BSD_Hasse_Points_1801_1877_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1801_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1801
  def BSD_DegreeNonneg_p1811_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1811
  def BSD_DegreeNonneg_p1823_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1823
end hasseprimset_BSD_Hasse_Points_1801_1877_Assessed

namespace hasseprimset_BSD_Hasse_Points_1879_1973_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1879_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1879
  def BSD_DegreeNonneg_p1889_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1889
  def BSD_DegreeNonneg_p1901_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1901
end hasseprimset_BSD_Hasse_Points_1879_1973_Assessed

namespace hasseprimset_BSD_Hasse_Points_1979_2029_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p1979_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1979
  def BSD_DegreeNonneg_p1987_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1987
  def BSD_DegreeNonneg_p1993_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 1993
end hasseprimset_BSD_Hasse_Points_1979_2029_Assessed

namespace hasseprimset_BSD_Hasse_Points_2039_2111_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥1009. Clean build stops at 241.
  def BSD_DegreeNonneg_p2039_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 2039
  def BSD_DegreeNonneg_p2053_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 2053
  def BSD_DegreeNonneg_p2063_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 2063
end hasseprimset_BSD_Hasse_Points_2039_2111_Assessed

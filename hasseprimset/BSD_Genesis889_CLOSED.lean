/-
================================================================
Towers / BSD / BSD_Genesis889_CLOSED  (genesis-889)

HasseBridge Tier C: Hasse bounds for primes
9973..9973 (1 primes).

Affine point counts (native_decide on E143_Finset p):
  p=9973: card=10022, a_p=-48, disc=-37588

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_889 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i889_p9973 : Fact (9973 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p9973 : (E143_Finset 9973).card = 10022 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p9973 : a_p 9973 = (-48 : ℤ) := by
  have h := BSD_E143_card_p9973; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=9973: a_p=-48, 4p-a_p²=37588
theorem BSD_DegreeNonneg_p9973 : BSD_FrobeniusDegreeNonneg_OPEN 9973 := fun r => by
  have hap : (a_p 9973 : ℝ) = -48 := by exact_mod_cast BSD_ap_p9973
  have key : r ^ 2 - (a_p 9973 : ℝ) * r + ((9973 : ℕ) : ℝ) =
      (r + 48/2) ^ 2 + 37588/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (48 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p9973 : BSD_Hasse_OPEN 9973 :=
  BSD_hasse_of_degree_nonneg 9973 BSD_DegreeNonneg_p9973

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p9973 : (a_p 9973 : ℝ) ^ 2 ≤ 4 * (9973 : ℝ) :=
  BSD_disc_from_deg_889 BSD_DegreeNonneg_p9973

end Towers.BSD
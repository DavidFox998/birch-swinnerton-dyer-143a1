/-
================================================================
Towers / BSD / BSD_Genesis821_CLOSED  (genesis-821)

HasseBridge Tier C: Hasse bounds for primes
3967..4049 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=3967: card=3992, a_p=-24, disc=-15292
  p=3989: card=4048, a_p=-58, disc=-12592
  p=4001: card=4008, a_p=-6, disc=-15968
  p=4003: card=3890, a_p=+114, disc=-3016
  p=4007: card=4032, a_p=-24, disc=-15452
  p=4013: card=4060, a_p=-46, disc=-13936
  p=4019: card=4015, a_p=+5, disc=-16051
  p=4021: card=3990, a_p=+32, disc=-15060
  p=4027: card=4000, a_p=+28, disc=-15324
  p=4049: card=3951, a_p=+99, disc=-6395

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_821 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i821_p3967 : Fact (3967 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p3989 : Fact (3989 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4001 : Fact (4001 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4003 : Fact (4003 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4007 : Fact (4007 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4013 : Fact (4013 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4019 : Fact (4019 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4021 : Fact (4021 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4027 : Fact (4027 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4049 : Fact (4049 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p3967 : (E143_Finset 3967).card = 3992 := by native_decide
theorem BSD_E143_card_p3989 : (E143_Finset 3989).card = 4048 := by native_decide
theorem BSD_E143_card_p4001 : (E143_Finset 4001).card = 4008 := by native_decide
theorem BSD_E143_card_p4003 : (E143_Finset 4003).card = 3890 := by native_decide
theorem BSD_E143_card_p4007 : (E143_Finset 4007).card = 4032 := by native_decide
theorem BSD_E143_card_p4013 : (E143_Finset 4013).card = 4060 := by native_decide
theorem BSD_E143_card_p4019 : (E143_Finset 4019).card = 4015 := by native_decide
theorem BSD_E143_card_p4021 : (E143_Finset 4021).card = 3990 := by native_decide
theorem BSD_E143_card_p4027 : (E143_Finset 4027).card = 4000 := by native_decide
theorem BSD_E143_card_p4049 : (E143_Finset 4049).card = 3951 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p3967 : a_p 3967 = (-24 : ℤ) := by
  have h := BSD_E143_card_p3967; unfold a_p; omega
theorem BSD_ap_p3989 : a_p 3989 = (-58 : ℤ) := by
  have h := BSD_E143_card_p3989; unfold a_p; omega
theorem BSD_ap_p4001 : a_p 4001 = (-6 : ℤ) := by
  have h := BSD_E143_card_p4001; unfold a_p; omega
theorem BSD_ap_p4003 : a_p 4003 = (114 : ℤ) := by
  have h := BSD_E143_card_p4003; unfold a_p; omega
theorem BSD_ap_p4007 : a_p 4007 = (-24 : ℤ) := by
  have h := BSD_E143_card_p4007; unfold a_p; omega
theorem BSD_ap_p4013 : a_p 4013 = (-46 : ℤ) := by
  have h := BSD_E143_card_p4013; unfold a_p; omega
theorem BSD_ap_p4019 : a_p 4019 = (5 : ℤ) := by
  have h := BSD_E143_card_p4019; unfold a_p; omega
theorem BSD_ap_p4021 : a_p 4021 = (32 : ℤ) := by
  have h := BSD_E143_card_p4021; unfold a_p; omega
theorem BSD_ap_p4027 : a_p 4027 = (28 : ℤ) := by
  have h := BSD_E143_card_p4027; unfold a_p; omega
theorem BSD_ap_p4049 : a_p 4049 = (99 : ℤ) := by
  have h := BSD_E143_card_p4049; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=3967: a_p=-24, 4p-a_p²=15292
theorem BSD_DegreeNonneg_p3967 : BSD_FrobeniusDegreeNonneg_OPEN 3967 := fun r => by
  have hap : (a_p 3967 : ℝ) = -24 := by exact_mod_cast BSD_ap_p3967
  have key : r ^ 2 - (a_p 3967 : ℝ) * r + ((3967 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 15292/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

-- p=3989: a_p=-58, 4p-a_p²=12592
theorem BSD_DegreeNonneg_p3989 : BSD_FrobeniusDegreeNonneg_OPEN 3989 := fun r => by
  have hap : (a_p 3989 : ℝ) = -58 := by exact_mod_cast BSD_ap_p3989
  have key : r ^ 2 - (a_p 3989 : ℝ) * r + ((3989 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 12592/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

-- p=4001: a_p=-6, 4p-a_p²=15968
theorem BSD_DegreeNonneg_p4001 : BSD_FrobeniusDegreeNonneg_OPEN 4001 := fun r => by
  have hap : (a_p 4001 : ℝ) = -6 := by exact_mod_cast BSD_ap_p4001
  have key : r ^ 2 - (a_p 4001 : ℝ) * r + ((4001 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 15968/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

-- p=4003: a_p=+114, 4p-a_p²=3016
theorem BSD_DegreeNonneg_p4003 : BSD_FrobeniusDegreeNonneg_OPEN 4003 := fun r => by
  have hap : (a_p 4003 : ℝ) = 114 := by exact_mod_cast BSD_ap_p4003
  have key : r ^ 2 - (a_p 4003 : ℝ) * r + ((4003 : ℕ) : ℝ) =
      (r - 114/2) ^ 2 + 3016/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (114 : ℝ)/2)]

-- p=4007: a_p=-24, 4p-a_p²=15452
theorem BSD_DegreeNonneg_p4007 : BSD_FrobeniusDegreeNonneg_OPEN 4007 := fun r => by
  have hap : (a_p 4007 : ℝ) = -24 := by exact_mod_cast BSD_ap_p4007
  have key : r ^ 2 - (a_p 4007 : ℝ) * r + ((4007 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 15452/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

-- p=4013: a_p=-46, 4p-a_p²=13936
theorem BSD_DegreeNonneg_p4013 : BSD_FrobeniusDegreeNonneg_OPEN 4013 := fun r => by
  have hap : (a_p 4013 : ℝ) = -46 := by exact_mod_cast BSD_ap_p4013
  have key : r ^ 2 - (a_p 4013 : ℝ) * r + ((4013 : ℕ) : ℝ) =
      (r + 46/2) ^ 2 + 13936/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (46 : ℝ)/2)]

-- p=4019: a_p=+5, 4p-a_p²=16051
theorem BSD_DegreeNonneg_p4019 : BSD_FrobeniusDegreeNonneg_OPEN 4019 := fun r => by
  have hap : (a_p 4019 : ℝ) = 5 := by exact_mod_cast BSD_ap_p4019
  have key : r ^ 2 - (a_p 4019 : ℝ) * r + ((4019 : ℕ) : ℝ) =
      (r - 5/2) ^ 2 + 16051/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (5 : ℝ)/2)]

-- p=4021: a_p=+32, 4p-a_p²=15060
theorem BSD_DegreeNonneg_p4021 : BSD_FrobeniusDegreeNonneg_OPEN 4021 := fun r => by
  have hap : (a_p 4021 : ℝ) = 32 := by exact_mod_cast BSD_ap_p4021
  have key : r ^ 2 - (a_p 4021 : ℝ) * r + ((4021 : ℕ) : ℝ) =
      (r - 32/2) ^ 2 + 15060/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (32 : ℝ)/2)]

-- p=4027: a_p=+28, 4p-a_p²=15324
theorem BSD_DegreeNonneg_p4027 : BSD_FrobeniusDegreeNonneg_OPEN 4027 := fun r => by
  have hap : (a_p 4027 : ℝ) = 28 := by exact_mod_cast BSD_ap_p4027
  have key : r ^ 2 - (a_p 4027 : ℝ) * r + ((4027 : ℕ) : ℝ) =
      (r - 28/2) ^ 2 + 15324/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (28 : ℝ)/2)]

-- p=4049: a_p=+99, 4p-a_p²=6395
theorem BSD_DegreeNonneg_p4049 : BSD_FrobeniusDegreeNonneg_OPEN 4049 := fun r => by
  have hap : (a_p 4049 : ℝ) = 99 := by exact_mod_cast BSD_ap_p4049
  have key : r ^ 2 - (a_p 4049 : ℝ) * r + ((4049 : ℕ) : ℝ) =
      (r - 99/2) ^ 2 + 6395/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (99 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p3967 : BSD_Hasse_OPEN 3967 :=
  BSD_hasse_of_degree_nonneg 3967 BSD_DegreeNonneg_p3967
theorem BSD_Hasse_OPEN_p3989 : BSD_Hasse_OPEN 3989 :=
  BSD_hasse_of_degree_nonneg 3989 BSD_DegreeNonneg_p3989
theorem BSD_Hasse_OPEN_p4001 : BSD_Hasse_OPEN 4001 :=
  BSD_hasse_of_degree_nonneg 4001 BSD_DegreeNonneg_p4001
theorem BSD_Hasse_OPEN_p4003 : BSD_Hasse_OPEN 4003 :=
  BSD_hasse_of_degree_nonneg 4003 BSD_DegreeNonneg_p4003
theorem BSD_Hasse_OPEN_p4007 : BSD_Hasse_OPEN 4007 :=
  BSD_hasse_of_degree_nonneg 4007 BSD_DegreeNonneg_p4007
theorem BSD_Hasse_OPEN_p4013 : BSD_Hasse_OPEN 4013 :=
  BSD_hasse_of_degree_nonneg 4013 BSD_DegreeNonneg_p4013
theorem BSD_Hasse_OPEN_p4019 : BSD_Hasse_OPEN 4019 :=
  BSD_hasse_of_degree_nonneg 4019 BSD_DegreeNonneg_p4019
theorem BSD_Hasse_OPEN_p4021 : BSD_Hasse_OPEN 4021 :=
  BSD_hasse_of_degree_nonneg 4021 BSD_DegreeNonneg_p4021
theorem BSD_Hasse_OPEN_p4027 : BSD_Hasse_OPEN 4027 :=
  BSD_hasse_of_degree_nonneg 4027 BSD_DegreeNonneg_p4027
theorem BSD_Hasse_OPEN_p4049 : BSD_Hasse_OPEN 4049 :=
  BSD_hasse_of_degree_nonneg 4049 BSD_DegreeNonneg_p4049

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p3967 : (a_p 3967 : ℝ) ^ 2 ≤ 4 * (3967 : ℝ) :=
  BSD_disc_from_deg_821 BSD_DegreeNonneg_p3967
theorem BSD_HasseBound_Disc_p3989 : (a_p 3989 : ℝ) ^ 2 ≤ 4 * (3989 : ℝ) :=
  BSD_disc_from_deg_821 BSD_DegreeNonneg_p3989
theorem BSD_HasseBound_Disc_p4001 : (a_p 4001 : ℝ) ^ 2 ≤ 4 * (4001 : ℝ) :=
  BSD_disc_from_deg_821 BSD_DegreeNonneg_p4001
theorem BSD_HasseBound_Disc_p4003 : (a_p 4003 : ℝ) ^ 2 ≤ 4 * (4003 : ℝ) :=
  BSD_disc_from_deg_821 BSD_DegreeNonneg_p4003
theorem BSD_HasseBound_Disc_p4007 : (a_p 4007 : ℝ) ^ 2 ≤ 4 * (4007 : ℝ) :=
  BSD_disc_from_deg_821 BSD_DegreeNonneg_p4007
theorem BSD_HasseBound_Disc_p4013 : (a_p 4013 : ℝ) ^ 2 ≤ 4 * (4013 : ℝ) :=
  BSD_disc_from_deg_821 BSD_DegreeNonneg_p4013
theorem BSD_HasseBound_Disc_p4019 : (a_p 4019 : ℝ) ^ 2 ≤ 4 * (4019 : ℝ) :=
  BSD_disc_from_deg_821 BSD_DegreeNonneg_p4019
theorem BSD_HasseBound_Disc_p4021 : (a_p 4021 : ℝ) ^ 2 ≤ 4 * (4021 : ℝ) :=
  BSD_disc_from_deg_821 BSD_DegreeNonneg_p4021
theorem BSD_HasseBound_Disc_p4027 : (a_p 4027 : ℝ) ^ 2 ≤ 4 * (4027 : ℝ) :=
  BSD_disc_from_deg_821 BSD_DegreeNonneg_p4027
theorem BSD_HasseBound_Disc_p4049 : (a_p 4049 : ℝ) ^ 2 ≤ 4 * (4049 : ℝ) :=
  BSD_disc_from_deg_821 BSD_DegreeNonneg_p4049

end Towers.BSD
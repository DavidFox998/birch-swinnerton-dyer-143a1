/-
================================================================
Towers / BSD / BSD_Genesis833_CLOSED  (genesis-833)

HasseBridge Tier C: Hasse bounds for primes
4999..5077 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=4999: card=5112, a_p=-112, disc=-7452
  p=5003: card=5107, a_p=-103, disc=-9403
  p=5009: card=5003, a_p=+7, disc=-19987
  p=5011: card=4904, a_p=+108, disc=-8380
  p=5021: card=4937, a_p=+85, disc=-12859
  p=5023: card=4952, a_p=+72, disc=-14908
  p=5039: card=5023, a_p=+17, disc=-19867
  p=5051: card=4950, a_p=+102, disc=-9800
  p=5059: card=5038, a_p=+22, disc=-19752
  p=5077: card=5064, a_p=+14, disc=-20112

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_833 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i833_p4999 : Fact (4999 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5003 : Fact (5003 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5009 : Fact (5009 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5011 : Fact (5011 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5021 : Fact (5021 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5023 : Fact (5023 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5039 : Fact (5039 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5051 : Fact (5051 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5059 : Fact (5059 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5077 : Fact (5077 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p4999 : (E143_Finset 4999).card = 5112 := by native_decide
theorem BSD_E143_card_p5003 : (E143_Finset 5003).card = 5107 := by native_decide
theorem BSD_E143_card_p5009 : (E143_Finset 5009).card = 5003 := by native_decide
theorem BSD_E143_card_p5011 : (E143_Finset 5011).card = 4904 := by native_decide
theorem BSD_E143_card_p5021 : (E143_Finset 5021).card = 4937 := by native_decide
theorem BSD_E143_card_p5023 : (E143_Finset 5023).card = 4952 := by native_decide
theorem BSD_E143_card_p5039 : (E143_Finset 5039).card = 5023 := by native_decide
theorem BSD_E143_card_p5051 : (E143_Finset 5051).card = 4950 := by native_decide
theorem BSD_E143_card_p5059 : (E143_Finset 5059).card = 5038 := by native_decide
theorem BSD_E143_card_p5077 : (E143_Finset 5077).card = 5064 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p4999 : a_p 4999 = (-112 : ℤ) := by
  have h := BSD_E143_card_p4999; unfold a_p; omega
theorem BSD_ap_p5003 : a_p 5003 = (-103 : ℤ) := by
  have h := BSD_E143_card_p5003; unfold a_p; omega
theorem BSD_ap_p5009 : a_p 5009 = (7 : ℤ) := by
  have h := BSD_E143_card_p5009; unfold a_p; omega
theorem BSD_ap_p5011 : a_p 5011 = (108 : ℤ) := by
  have h := BSD_E143_card_p5011; unfold a_p; omega
theorem BSD_ap_p5021 : a_p 5021 = (85 : ℤ) := by
  have h := BSD_E143_card_p5021; unfold a_p; omega
theorem BSD_ap_p5023 : a_p 5023 = (72 : ℤ) := by
  have h := BSD_E143_card_p5023; unfold a_p; omega
theorem BSD_ap_p5039 : a_p 5039 = (17 : ℤ) := by
  have h := BSD_E143_card_p5039; unfold a_p; omega
theorem BSD_ap_p5051 : a_p 5051 = (102 : ℤ) := by
  have h := BSD_E143_card_p5051; unfold a_p; omega
theorem BSD_ap_p5059 : a_p 5059 = (22 : ℤ) := by
  have h := BSD_E143_card_p5059; unfold a_p; omega
theorem BSD_ap_p5077 : a_p 5077 = (14 : ℤ) := by
  have h := BSD_E143_card_p5077; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=4999: a_p=-112, 4p-a_p²=7452
theorem BSD_DegreeNonneg_p4999 : BSD_FrobeniusDegreeNonneg_OPEN 4999 := fun r => by
  have hap : (a_p 4999 : ℝ) = -112 := by exact_mod_cast BSD_ap_p4999
  have key : r ^ 2 - (a_p 4999 : ℝ) * r + ((4999 : ℕ) : ℝ) =
      (r + 112/2) ^ 2 + 7452/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (112 : ℝ)/2)]

-- p=5003: a_p=-103, 4p-a_p²=9403
theorem BSD_DegreeNonneg_p5003 : BSD_FrobeniusDegreeNonneg_OPEN 5003 := fun r => by
  have hap : (a_p 5003 : ℝ) = -103 := by exact_mod_cast BSD_ap_p5003
  have key : r ^ 2 - (a_p 5003 : ℝ) * r + ((5003 : ℕ) : ℝ) =
      (r + 103/2) ^ 2 + 9403/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (103 : ℝ)/2)]

-- p=5009: a_p=+7, 4p-a_p²=19987
theorem BSD_DegreeNonneg_p5009 : BSD_FrobeniusDegreeNonneg_OPEN 5009 := fun r => by
  have hap : (a_p 5009 : ℝ) = 7 := by exact_mod_cast BSD_ap_p5009
  have key : r ^ 2 - (a_p 5009 : ℝ) * r + ((5009 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 19987/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

-- p=5011: a_p=+108, 4p-a_p²=8380
theorem BSD_DegreeNonneg_p5011 : BSD_FrobeniusDegreeNonneg_OPEN 5011 := fun r => by
  have hap : (a_p 5011 : ℝ) = 108 := by exact_mod_cast BSD_ap_p5011
  have key : r ^ 2 - (a_p 5011 : ℝ) * r + ((5011 : ℕ) : ℝ) =
      (r - 108/2) ^ 2 + 8380/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (108 : ℝ)/2)]

-- p=5021: a_p=+85, 4p-a_p²=12859
theorem BSD_DegreeNonneg_p5021 : BSD_FrobeniusDegreeNonneg_OPEN 5021 := fun r => by
  have hap : (a_p 5021 : ℝ) = 85 := by exact_mod_cast BSD_ap_p5021
  have key : r ^ 2 - (a_p 5021 : ℝ) * r + ((5021 : ℕ) : ℝ) =
      (r - 85/2) ^ 2 + 12859/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (85 : ℝ)/2)]

-- p=5023: a_p=+72, 4p-a_p²=14908
theorem BSD_DegreeNonneg_p5023 : BSD_FrobeniusDegreeNonneg_OPEN 5023 := fun r => by
  have hap : (a_p 5023 : ℝ) = 72 := by exact_mod_cast BSD_ap_p5023
  have key : r ^ 2 - (a_p 5023 : ℝ) * r + ((5023 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 14908/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

-- p=5039: a_p=+17, 4p-a_p²=19867
theorem BSD_DegreeNonneg_p5039 : BSD_FrobeniusDegreeNonneg_OPEN 5039 := fun r => by
  have hap : (a_p 5039 : ℝ) = 17 := by exact_mod_cast BSD_ap_p5039
  have key : r ^ 2 - (a_p 5039 : ℝ) * r + ((5039 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 19867/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

-- p=5051: a_p=+102, 4p-a_p²=9800
theorem BSD_DegreeNonneg_p5051 : BSD_FrobeniusDegreeNonneg_OPEN 5051 := fun r => by
  have hap : (a_p 5051 : ℝ) = 102 := by exact_mod_cast BSD_ap_p5051
  have key : r ^ 2 - (a_p 5051 : ℝ) * r + ((5051 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 9800/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

-- p=5059: a_p=+22, 4p-a_p²=19752
theorem BSD_DegreeNonneg_p5059 : BSD_FrobeniusDegreeNonneg_OPEN 5059 := fun r => by
  have hap : (a_p 5059 : ℝ) = 22 := by exact_mod_cast BSD_ap_p5059
  have key : r ^ 2 - (a_p 5059 : ℝ) * r + ((5059 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 19752/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

-- p=5077: a_p=+14, 4p-a_p²=20112
theorem BSD_DegreeNonneg_p5077 : BSD_FrobeniusDegreeNonneg_OPEN 5077 := fun r => by
  have hap : (a_p 5077 : ℝ) = 14 := by exact_mod_cast BSD_ap_p5077
  have key : r ^ 2 - (a_p 5077 : ℝ) * r + ((5077 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 20112/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p4999 : BSD_Hasse_OPEN 4999 :=
  BSD_hasse_of_degree_nonneg 4999 BSD_DegreeNonneg_p4999
theorem BSD_Hasse_OPEN_p5003 : BSD_Hasse_OPEN 5003 :=
  BSD_hasse_of_degree_nonneg 5003 BSD_DegreeNonneg_p5003
theorem BSD_Hasse_OPEN_p5009 : BSD_Hasse_OPEN 5009 :=
  BSD_hasse_of_degree_nonneg 5009 BSD_DegreeNonneg_p5009
theorem BSD_Hasse_OPEN_p5011 : BSD_Hasse_OPEN 5011 :=
  BSD_hasse_of_degree_nonneg 5011 BSD_DegreeNonneg_p5011
theorem BSD_Hasse_OPEN_p5021 : BSD_Hasse_OPEN 5021 :=
  BSD_hasse_of_degree_nonneg 5021 BSD_DegreeNonneg_p5021
theorem BSD_Hasse_OPEN_p5023 : BSD_Hasse_OPEN 5023 :=
  BSD_hasse_of_degree_nonneg 5023 BSD_DegreeNonneg_p5023
theorem BSD_Hasse_OPEN_p5039 : BSD_Hasse_OPEN 5039 :=
  BSD_hasse_of_degree_nonneg 5039 BSD_DegreeNonneg_p5039
theorem BSD_Hasse_OPEN_p5051 : BSD_Hasse_OPEN 5051 :=
  BSD_hasse_of_degree_nonneg 5051 BSD_DegreeNonneg_p5051
theorem BSD_Hasse_OPEN_p5059 : BSD_Hasse_OPEN 5059 :=
  BSD_hasse_of_degree_nonneg 5059 BSD_DegreeNonneg_p5059
theorem BSD_Hasse_OPEN_p5077 : BSD_Hasse_OPEN 5077 :=
  BSD_hasse_of_degree_nonneg 5077 BSD_DegreeNonneg_p5077

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p4999 : (a_p 4999 : ℝ) ^ 2 ≤ 4 * (4999 : ℝ) :=
  BSD_disc_from_deg_833 BSD_DegreeNonneg_p4999
theorem BSD_HasseBound_Disc_p5003 : (a_p 5003 : ℝ) ^ 2 ≤ 4 * (5003 : ℝ) :=
  BSD_disc_from_deg_833 BSD_DegreeNonneg_p5003
theorem BSD_HasseBound_Disc_p5009 : (a_p 5009 : ℝ) ^ 2 ≤ 4 * (5009 : ℝ) :=
  BSD_disc_from_deg_833 BSD_DegreeNonneg_p5009
theorem BSD_HasseBound_Disc_p5011 : (a_p 5011 : ℝ) ^ 2 ≤ 4 * (5011 : ℝ) :=
  BSD_disc_from_deg_833 BSD_DegreeNonneg_p5011
theorem BSD_HasseBound_Disc_p5021 : (a_p 5021 : ℝ) ^ 2 ≤ 4 * (5021 : ℝ) :=
  BSD_disc_from_deg_833 BSD_DegreeNonneg_p5021
theorem BSD_HasseBound_Disc_p5023 : (a_p 5023 : ℝ) ^ 2 ≤ 4 * (5023 : ℝ) :=
  BSD_disc_from_deg_833 BSD_DegreeNonneg_p5023
theorem BSD_HasseBound_Disc_p5039 : (a_p 5039 : ℝ) ^ 2 ≤ 4 * (5039 : ℝ) :=
  BSD_disc_from_deg_833 BSD_DegreeNonneg_p5039
theorem BSD_HasseBound_Disc_p5051 : (a_p 5051 : ℝ) ^ 2 ≤ 4 * (5051 : ℝ) :=
  BSD_disc_from_deg_833 BSD_DegreeNonneg_p5051
theorem BSD_HasseBound_Disc_p5059 : (a_p 5059 : ℝ) ^ 2 ≤ 4 * (5059 : ℝ) :=
  BSD_disc_from_deg_833 BSD_DegreeNonneg_p5059
theorem BSD_HasseBound_Disc_p5077 : (a_p 5077 : ℝ) ^ 2 ≤ 4 * (5077 : ℝ) :=
  BSD_disc_from_deg_833 BSD_DegreeNonneg_p5077

end Towers.BSD
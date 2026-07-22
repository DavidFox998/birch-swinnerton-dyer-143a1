/-
================================================================
Towers / BSD / BSD_Genesis842_CLOSED  (genesis-842)

HasseBridge Tier C: Hasse bounds for primes
5783..5849 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=5783: card=5770, a_p=+14, disc=-22936
  p=5791: card=5716, a_p=+76, disc=-17388
  p=5801: card=5752, a_p=+50, disc=-20704
  p=5807: card=5886, a_p=-78, disc=-17144
  p=5813: card=5701, a_p=+113, disc=-10483
  p=5821: card=5880, a_p=-58, disc=-19920
  p=5827: card=5764, a_p=+64, disc=-19212
  p=5839: card=5864, a_p=-24, disc=-22780
  p=5843: card=5956, a_p=-112, disc=-10828
  p=5849: card=5862, a_p=-12, disc=-23252

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_842 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i842_p5783 : Fact (5783 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5791 : Fact (5791 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5801 : Fact (5801 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5807 : Fact (5807 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5813 : Fact (5813 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5821 : Fact (5821 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5827 : Fact (5827 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5839 : Fact (5839 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5843 : Fact (5843 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5849 : Fact (5849 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p5783 : (E143_Finset 5783).card = 5770 := by native_decide
theorem BSD_E143_card_p5791 : (E143_Finset 5791).card = 5716 := by native_decide
theorem BSD_E143_card_p5801 : (E143_Finset 5801).card = 5752 := by native_decide
theorem BSD_E143_card_p5807 : (E143_Finset 5807).card = 5886 := by native_decide
theorem BSD_E143_card_p5813 : (E143_Finset 5813).card = 5701 := by native_decide
theorem BSD_E143_card_p5821 : (E143_Finset 5821).card = 5880 := by native_decide
theorem BSD_E143_card_p5827 : (E143_Finset 5827).card = 5764 := by native_decide
theorem BSD_E143_card_p5839 : (E143_Finset 5839).card = 5864 := by native_decide
theorem BSD_E143_card_p5843 : (E143_Finset 5843).card = 5956 := by native_decide
theorem BSD_E143_card_p5849 : (E143_Finset 5849).card = 5862 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p5783 : a_p 5783 = (14 : ℤ) := by
  have h := BSD_E143_card_p5783; unfold a_p; omega
theorem BSD_ap_p5791 : a_p 5791 = (76 : ℤ) := by
  have h := BSD_E143_card_p5791; unfold a_p; omega
theorem BSD_ap_p5801 : a_p 5801 = (50 : ℤ) := by
  have h := BSD_E143_card_p5801; unfold a_p; omega
theorem BSD_ap_p5807 : a_p 5807 = (-78 : ℤ) := by
  have h := BSD_E143_card_p5807; unfold a_p; omega
theorem BSD_ap_p5813 : a_p 5813 = (113 : ℤ) := by
  have h := BSD_E143_card_p5813; unfold a_p; omega
theorem BSD_ap_p5821 : a_p 5821 = (-58 : ℤ) := by
  have h := BSD_E143_card_p5821; unfold a_p; omega
theorem BSD_ap_p5827 : a_p 5827 = (64 : ℤ) := by
  have h := BSD_E143_card_p5827; unfold a_p; omega
theorem BSD_ap_p5839 : a_p 5839 = (-24 : ℤ) := by
  have h := BSD_E143_card_p5839; unfold a_p; omega
theorem BSD_ap_p5843 : a_p 5843 = (-112 : ℤ) := by
  have h := BSD_E143_card_p5843; unfold a_p; omega
theorem BSD_ap_p5849 : a_p 5849 = (-12 : ℤ) := by
  have h := BSD_E143_card_p5849; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=5783: a_p=+14, 4p-a_p²=22936
theorem BSD_DegreeNonneg_p5783 : BSD_FrobeniusDegreeNonneg_OPEN 5783 := fun r => by
  have hap : (a_p 5783 : ℝ) = 14 := by exact_mod_cast BSD_ap_p5783
  have key : r ^ 2 - (a_p 5783 : ℝ) * r + ((5783 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 22936/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

-- p=5791: a_p=+76, 4p-a_p²=17388
theorem BSD_DegreeNonneg_p5791 : BSD_FrobeniusDegreeNonneg_OPEN 5791 := fun r => by
  have hap : (a_p 5791 : ℝ) = 76 := by exact_mod_cast BSD_ap_p5791
  have key : r ^ 2 - (a_p 5791 : ℝ) * r + ((5791 : ℕ) : ℝ) =
      (r - 76/2) ^ 2 + 17388/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (76 : ℝ)/2)]

-- p=5801: a_p=+50, 4p-a_p²=20704
theorem BSD_DegreeNonneg_p5801 : BSD_FrobeniusDegreeNonneg_OPEN 5801 := fun r => by
  have hap : (a_p 5801 : ℝ) = 50 := by exact_mod_cast BSD_ap_p5801
  have key : r ^ 2 - (a_p 5801 : ℝ) * r + ((5801 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 20704/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

-- p=5807: a_p=-78, 4p-a_p²=17144
theorem BSD_DegreeNonneg_p5807 : BSD_FrobeniusDegreeNonneg_OPEN 5807 := fun r => by
  have hap : (a_p 5807 : ℝ) = -78 := by exact_mod_cast BSD_ap_p5807
  have key : r ^ 2 - (a_p 5807 : ℝ) * r + ((5807 : ℕ) : ℝ) =
      (r + 78/2) ^ 2 + 17144/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (78 : ℝ)/2)]

-- p=5813: a_p=+113, 4p-a_p²=10483
theorem BSD_DegreeNonneg_p5813 : BSD_FrobeniusDegreeNonneg_OPEN 5813 := fun r => by
  have hap : (a_p 5813 : ℝ) = 113 := by exact_mod_cast BSD_ap_p5813
  have key : r ^ 2 - (a_p 5813 : ℝ) * r + ((5813 : ℕ) : ℝ) =
      (r - 113/2) ^ 2 + 10483/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (113 : ℝ)/2)]

-- p=5821: a_p=-58, 4p-a_p²=19920
theorem BSD_DegreeNonneg_p5821 : BSD_FrobeniusDegreeNonneg_OPEN 5821 := fun r => by
  have hap : (a_p 5821 : ℝ) = -58 := by exact_mod_cast BSD_ap_p5821
  have key : r ^ 2 - (a_p 5821 : ℝ) * r + ((5821 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 19920/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

-- p=5827: a_p=+64, 4p-a_p²=19212
theorem BSD_DegreeNonneg_p5827 : BSD_FrobeniusDegreeNonneg_OPEN 5827 := fun r => by
  have hap : (a_p 5827 : ℝ) = 64 := by exact_mod_cast BSD_ap_p5827
  have key : r ^ 2 - (a_p 5827 : ℝ) * r + ((5827 : ℕ) : ℝ) =
      (r - 64/2) ^ 2 + 19212/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (64 : ℝ)/2)]

-- p=5839: a_p=-24, 4p-a_p²=22780
theorem BSD_DegreeNonneg_p5839 : BSD_FrobeniusDegreeNonneg_OPEN 5839 := fun r => by
  have hap : (a_p 5839 : ℝ) = -24 := by exact_mod_cast BSD_ap_p5839
  have key : r ^ 2 - (a_p 5839 : ℝ) * r + ((5839 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 22780/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

-- p=5843: a_p=-112, 4p-a_p²=10828
theorem BSD_DegreeNonneg_p5843 : BSD_FrobeniusDegreeNonneg_OPEN 5843 := fun r => by
  have hap : (a_p 5843 : ℝ) = -112 := by exact_mod_cast BSD_ap_p5843
  have key : r ^ 2 - (a_p 5843 : ℝ) * r + ((5843 : ℕ) : ℝ) =
      (r + 112/2) ^ 2 + 10828/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (112 : ℝ)/2)]

-- p=5849: a_p=-12, 4p-a_p²=23252
theorem BSD_DegreeNonneg_p5849 : BSD_FrobeniusDegreeNonneg_OPEN 5849 := fun r => by
  have hap : (a_p 5849 : ℝ) = -12 := by exact_mod_cast BSD_ap_p5849
  have key : r ^ 2 - (a_p 5849 : ℝ) * r + ((5849 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 23252/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p5783 : BSD_Hasse_OPEN 5783 :=
  BSD_hasse_of_degree_nonneg 5783 BSD_DegreeNonneg_p5783
theorem BSD_Hasse_OPEN_p5791 : BSD_Hasse_OPEN 5791 :=
  BSD_hasse_of_degree_nonneg 5791 BSD_DegreeNonneg_p5791
theorem BSD_Hasse_OPEN_p5801 : BSD_Hasse_OPEN 5801 :=
  BSD_hasse_of_degree_nonneg 5801 BSD_DegreeNonneg_p5801
theorem BSD_Hasse_OPEN_p5807 : BSD_Hasse_OPEN 5807 :=
  BSD_hasse_of_degree_nonneg 5807 BSD_DegreeNonneg_p5807
theorem BSD_Hasse_OPEN_p5813 : BSD_Hasse_OPEN 5813 :=
  BSD_hasse_of_degree_nonneg 5813 BSD_DegreeNonneg_p5813
theorem BSD_Hasse_OPEN_p5821 : BSD_Hasse_OPEN 5821 :=
  BSD_hasse_of_degree_nonneg 5821 BSD_DegreeNonneg_p5821
theorem BSD_Hasse_OPEN_p5827 : BSD_Hasse_OPEN 5827 :=
  BSD_hasse_of_degree_nonneg 5827 BSD_DegreeNonneg_p5827
theorem BSD_Hasse_OPEN_p5839 : BSD_Hasse_OPEN 5839 :=
  BSD_hasse_of_degree_nonneg 5839 BSD_DegreeNonneg_p5839
theorem BSD_Hasse_OPEN_p5843 : BSD_Hasse_OPEN 5843 :=
  BSD_hasse_of_degree_nonneg 5843 BSD_DegreeNonneg_p5843
theorem BSD_Hasse_OPEN_p5849 : BSD_Hasse_OPEN 5849 :=
  BSD_hasse_of_degree_nonneg 5849 BSD_DegreeNonneg_p5849

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p5783 : (a_p 5783 : ℝ) ^ 2 ≤ 4 * (5783 : ℝ) :=
  BSD_disc_from_deg_842 BSD_DegreeNonneg_p5783
theorem BSD_HasseBound_Disc_p5791 : (a_p 5791 : ℝ) ^ 2 ≤ 4 * (5791 : ℝ) :=
  BSD_disc_from_deg_842 BSD_DegreeNonneg_p5791
theorem BSD_HasseBound_Disc_p5801 : (a_p 5801 : ℝ) ^ 2 ≤ 4 * (5801 : ℝ) :=
  BSD_disc_from_deg_842 BSD_DegreeNonneg_p5801
theorem BSD_HasseBound_Disc_p5807 : (a_p 5807 : ℝ) ^ 2 ≤ 4 * (5807 : ℝ) :=
  BSD_disc_from_deg_842 BSD_DegreeNonneg_p5807
theorem BSD_HasseBound_Disc_p5813 : (a_p 5813 : ℝ) ^ 2 ≤ 4 * (5813 : ℝ) :=
  BSD_disc_from_deg_842 BSD_DegreeNonneg_p5813
theorem BSD_HasseBound_Disc_p5821 : (a_p 5821 : ℝ) ^ 2 ≤ 4 * (5821 : ℝ) :=
  BSD_disc_from_deg_842 BSD_DegreeNonneg_p5821
theorem BSD_HasseBound_Disc_p5827 : (a_p 5827 : ℝ) ^ 2 ≤ 4 * (5827 : ℝ) :=
  BSD_disc_from_deg_842 BSD_DegreeNonneg_p5827
theorem BSD_HasseBound_Disc_p5839 : (a_p 5839 : ℝ) ^ 2 ≤ 4 * (5839 : ℝ) :=
  BSD_disc_from_deg_842 BSD_DegreeNonneg_p5839
theorem BSD_HasseBound_Disc_p5843 : (a_p 5843 : ℝ) ^ 2 ≤ 4 * (5843 : ℝ) :=
  BSD_disc_from_deg_842 BSD_DegreeNonneg_p5843
theorem BSD_HasseBound_Disc_p5849 : (a_p 5849 : ℝ) ^ 2 ≤ 4 * (5849 : ℝ) :=
  BSD_disc_from_deg_842 BSD_DegreeNonneg_p5849

end Towers.BSD
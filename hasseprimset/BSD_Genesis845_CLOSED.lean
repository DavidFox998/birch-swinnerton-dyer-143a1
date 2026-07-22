/-
================================================================
Towers / BSD / BSD_Genesis845_CLOSED  (genesis-845)

HasseBridge Tier C: Hasse bounds for primes
6047..6121 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=6047: card=6008, a_p=+40, disc=-22588
  p=6053: card=5976, a_p=+78, disc=-18128
  p=6067: card=6034, a_p=+34, disc=-23112
  p=6073: card=6068, a_p=+6, disc=-24256
  p=6079: card=6030, a_p=+50, disc=-21816
  p=6089: card=6000, a_p=+90, disc=-16256
  p=6091: card=6190, a_p=-98, disc=-14760
  p=6101: card=5990, a_p=+112, disc=-11860
  p=6113: card=6172, a_p=-58, disc=-21088
  p=6121: card=6223, a_p=-101, disc=-14283

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_845 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i845_p6047 : Fact (6047 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6053 : Fact (6053 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6067 : Fact (6067 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6073 : Fact (6073 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6079 : Fact (6079 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6089 : Fact (6089 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6091 : Fact (6091 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6101 : Fact (6101 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6113 : Fact (6113 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6121 : Fact (6121 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p6047 : (E143_Finset 6047).card = 6008 := by native_decide
theorem BSD_E143_card_p6053 : (E143_Finset 6053).card = 5976 := by native_decide
theorem BSD_E143_card_p6067 : (E143_Finset 6067).card = 6034 := by native_decide
theorem BSD_E143_card_p6073 : (E143_Finset 6073).card = 6068 := by native_decide
theorem BSD_E143_card_p6079 : (E143_Finset 6079).card = 6030 := by native_decide
theorem BSD_E143_card_p6089 : (E143_Finset 6089).card = 6000 := by native_decide
theorem BSD_E143_card_p6091 : (E143_Finset 6091).card = 6190 := by native_decide
theorem BSD_E143_card_p6101 : (E143_Finset 6101).card = 5990 := by native_decide
theorem BSD_E143_card_p6113 : (E143_Finset 6113).card = 6172 := by native_decide
theorem BSD_E143_card_p6121 : (E143_Finset 6121).card = 6223 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p6047 : a_p 6047 = (40 : ℤ) := by
  have h := BSD_E143_card_p6047; unfold a_p; omega
theorem BSD_ap_p6053 : a_p 6053 = (78 : ℤ) := by
  have h := BSD_E143_card_p6053; unfold a_p; omega
theorem BSD_ap_p6067 : a_p 6067 = (34 : ℤ) := by
  have h := BSD_E143_card_p6067; unfold a_p; omega
theorem BSD_ap_p6073 : a_p 6073 = (6 : ℤ) := by
  have h := BSD_E143_card_p6073; unfold a_p; omega
theorem BSD_ap_p6079 : a_p 6079 = (50 : ℤ) := by
  have h := BSD_E143_card_p6079; unfold a_p; omega
theorem BSD_ap_p6089 : a_p 6089 = (90 : ℤ) := by
  have h := BSD_E143_card_p6089; unfold a_p; omega
theorem BSD_ap_p6091 : a_p 6091 = (-98 : ℤ) := by
  have h := BSD_E143_card_p6091; unfold a_p; omega
theorem BSD_ap_p6101 : a_p 6101 = (112 : ℤ) := by
  have h := BSD_E143_card_p6101; unfold a_p; omega
theorem BSD_ap_p6113 : a_p 6113 = (-58 : ℤ) := by
  have h := BSD_E143_card_p6113; unfold a_p; omega
theorem BSD_ap_p6121 : a_p 6121 = (-101 : ℤ) := by
  have h := BSD_E143_card_p6121; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=6047: a_p=+40, 4p-a_p²=22588
theorem BSD_DegreeNonneg_p6047 : BSD_FrobeniusDegreeNonneg_OPEN 6047 := fun r => by
  have hap : (a_p 6047 : ℝ) = 40 := by exact_mod_cast BSD_ap_p6047
  have key : r ^ 2 - (a_p 6047 : ℝ) * r + ((6047 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 22588/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

-- p=6053: a_p=+78, 4p-a_p²=18128
theorem BSD_DegreeNonneg_p6053 : BSD_FrobeniusDegreeNonneg_OPEN 6053 := fun r => by
  have hap : (a_p 6053 : ℝ) = 78 := by exact_mod_cast BSD_ap_p6053
  have key : r ^ 2 - (a_p 6053 : ℝ) * r + ((6053 : ℕ) : ℝ) =
      (r - 78/2) ^ 2 + 18128/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (78 : ℝ)/2)]

-- p=6067: a_p=+34, 4p-a_p²=23112
theorem BSD_DegreeNonneg_p6067 : BSD_FrobeniusDegreeNonneg_OPEN 6067 := fun r => by
  have hap : (a_p 6067 : ℝ) = 34 := by exact_mod_cast BSD_ap_p6067
  have key : r ^ 2 - (a_p 6067 : ℝ) * r + ((6067 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 23112/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

-- p=6073: a_p=+6, 4p-a_p²=24256
theorem BSD_DegreeNonneg_p6073 : BSD_FrobeniusDegreeNonneg_OPEN 6073 := fun r => by
  have hap : (a_p 6073 : ℝ) = 6 := by exact_mod_cast BSD_ap_p6073
  have key : r ^ 2 - (a_p 6073 : ℝ) * r + ((6073 : ℕ) : ℝ) =
      (r - 6/2) ^ 2 + 24256/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (6 : ℝ)/2)]

-- p=6079: a_p=+50, 4p-a_p²=21816
theorem BSD_DegreeNonneg_p6079 : BSD_FrobeniusDegreeNonneg_OPEN 6079 := fun r => by
  have hap : (a_p 6079 : ℝ) = 50 := by exact_mod_cast BSD_ap_p6079
  have key : r ^ 2 - (a_p 6079 : ℝ) * r + ((6079 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 21816/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

-- p=6089: a_p=+90, 4p-a_p²=16256
theorem BSD_DegreeNonneg_p6089 : BSD_FrobeniusDegreeNonneg_OPEN 6089 := fun r => by
  have hap : (a_p 6089 : ℝ) = 90 := by exact_mod_cast BSD_ap_p6089
  have key : r ^ 2 - (a_p 6089 : ℝ) * r + ((6089 : ℕ) : ℝ) =
      (r - 90/2) ^ 2 + 16256/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (90 : ℝ)/2)]

-- p=6091: a_p=-98, 4p-a_p²=14760
theorem BSD_DegreeNonneg_p6091 : BSD_FrobeniusDegreeNonneg_OPEN 6091 := fun r => by
  have hap : (a_p 6091 : ℝ) = -98 := by exact_mod_cast BSD_ap_p6091
  have key : r ^ 2 - (a_p 6091 : ℝ) * r + ((6091 : ℕ) : ℝ) =
      (r + 98/2) ^ 2 + 14760/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (98 : ℝ)/2)]

-- p=6101: a_p=+112, 4p-a_p²=11860
theorem BSD_DegreeNonneg_p6101 : BSD_FrobeniusDegreeNonneg_OPEN 6101 := fun r => by
  have hap : (a_p 6101 : ℝ) = 112 := by exact_mod_cast BSD_ap_p6101
  have key : r ^ 2 - (a_p 6101 : ℝ) * r + ((6101 : ℕ) : ℝ) =
      (r - 112/2) ^ 2 + 11860/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (112 : ℝ)/2)]

-- p=6113: a_p=-58, 4p-a_p²=21088
theorem BSD_DegreeNonneg_p6113 : BSD_FrobeniusDegreeNonneg_OPEN 6113 := fun r => by
  have hap : (a_p 6113 : ℝ) = -58 := by exact_mod_cast BSD_ap_p6113
  have key : r ^ 2 - (a_p 6113 : ℝ) * r + ((6113 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 21088/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

-- p=6121: a_p=-101, 4p-a_p²=14283
theorem BSD_DegreeNonneg_p6121 : BSD_FrobeniusDegreeNonneg_OPEN 6121 := fun r => by
  have hap : (a_p 6121 : ℝ) = -101 := by exact_mod_cast BSD_ap_p6121
  have key : r ^ 2 - (a_p 6121 : ℝ) * r + ((6121 : ℕ) : ℝ) =
      (r + 101/2) ^ 2 + 14283/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (101 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p6047 : BSD_Hasse_OPEN 6047 :=
  BSD_hasse_of_degree_nonneg 6047 BSD_DegreeNonneg_p6047
theorem BSD_Hasse_OPEN_p6053 : BSD_Hasse_OPEN 6053 :=
  BSD_hasse_of_degree_nonneg 6053 BSD_DegreeNonneg_p6053
theorem BSD_Hasse_OPEN_p6067 : BSD_Hasse_OPEN 6067 :=
  BSD_hasse_of_degree_nonneg 6067 BSD_DegreeNonneg_p6067
theorem BSD_Hasse_OPEN_p6073 : BSD_Hasse_OPEN 6073 :=
  BSD_hasse_of_degree_nonneg 6073 BSD_DegreeNonneg_p6073
theorem BSD_Hasse_OPEN_p6079 : BSD_Hasse_OPEN 6079 :=
  BSD_hasse_of_degree_nonneg 6079 BSD_DegreeNonneg_p6079
theorem BSD_Hasse_OPEN_p6089 : BSD_Hasse_OPEN 6089 :=
  BSD_hasse_of_degree_nonneg 6089 BSD_DegreeNonneg_p6089
theorem BSD_Hasse_OPEN_p6091 : BSD_Hasse_OPEN 6091 :=
  BSD_hasse_of_degree_nonneg 6091 BSD_DegreeNonneg_p6091
theorem BSD_Hasse_OPEN_p6101 : BSD_Hasse_OPEN 6101 :=
  BSD_hasse_of_degree_nonneg 6101 BSD_DegreeNonneg_p6101
theorem BSD_Hasse_OPEN_p6113 : BSD_Hasse_OPEN 6113 :=
  BSD_hasse_of_degree_nonneg 6113 BSD_DegreeNonneg_p6113
theorem BSD_Hasse_OPEN_p6121 : BSD_Hasse_OPEN 6121 :=
  BSD_hasse_of_degree_nonneg 6121 BSD_DegreeNonneg_p6121

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p6047 : (a_p 6047 : ℝ) ^ 2 ≤ 4 * (6047 : ℝ) :=
  BSD_disc_from_deg_845 BSD_DegreeNonneg_p6047
theorem BSD_HasseBound_Disc_p6053 : (a_p 6053 : ℝ) ^ 2 ≤ 4 * (6053 : ℝ) :=
  BSD_disc_from_deg_845 BSD_DegreeNonneg_p6053
theorem BSD_HasseBound_Disc_p6067 : (a_p 6067 : ℝ) ^ 2 ≤ 4 * (6067 : ℝ) :=
  BSD_disc_from_deg_845 BSD_DegreeNonneg_p6067
theorem BSD_HasseBound_Disc_p6073 : (a_p 6073 : ℝ) ^ 2 ≤ 4 * (6073 : ℝ) :=
  BSD_disc_from_deg_845 BSD_DegreeNonneg_p6073
theorem BSD_HasseBound_Disc_p6079 : (a_p 6079 : ℝ) ^ 2 ≤ 4 * (6079 : ℝ) :=
  BSD_disc_from_deg_845 BSD_DegreeNonneg_p6079
theorem BSD_HasseBound_Disc_p6089 : (a_p 6089 : ℝ) ^ 2 ≤ 4 * (6089 : ℝ) :=
  BSD_disc_from_deg_845 BSD_DegreeNonneg_p6089
theorem BSD_HasseBound_Disc_p6091 : (a_p 6091 : ℝ) ^ 2 ≤ 4 * (6091 : ℝ) :=
  BSD_disc_from_deg_845 BSD_DegreeNonneg_p6091
theorem BSD_HasseBound_Disc_p6101 : (a_p 6101 : ℝ) ^ 2 ≤ 4 * (6101 : ℝ) :=
  BSD_disc_from_deg_845 BSD_DegreeNonneg_p6101
theorem BSD_HasseBound_Disc_p6113 : (a_p 6113 : ℝ) ^ 2 ≤ 4 * (6113 : ℝ) :=
  BSD_disc_from_deg_845 BSD_DegreeNonneg_p6113
theorem BSD_HasseBound_Disc_p6121 : (a_p 6121 : ℝ) ^ 2 ≤ 4 * (6121 : ℝ) :=
  BSD_disc_from_deg_845 BSD_DegreeNonneg_p6121

end Towers.BSD
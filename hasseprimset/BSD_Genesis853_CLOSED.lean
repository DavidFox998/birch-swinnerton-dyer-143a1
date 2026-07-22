/-
================================================================
Towers / BSD / BSD_Genesis853_CLOSED  (genesis-853)

HasseBridge Tier C: Hasse bounds for primes
6737..6827 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=6737: card=6692, a_p=+46, disc=-24832
  p=6761: card=6838, a_p=-76, disc=-21268
  p=6763: card=6767, a_p=-3, disc=-27043
  p=6779: card=6800, a_p=-20, disc=-26716
  p=6781: card=6825, a_p=-43, disc=-25275
  p=6791: card=6797, a_p=-5, disc=-27139
  p=6793: card=6732, a_p=+62, disc=-23328
  p=6803: card=6747, a_p=+57, disc=-23963
  p=6823: card=6736, a_p=+88, disc=-19548
  p=6827: card=6880, a_p=-52, disc=-24604

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_853 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i853_p6737 : Fact (6737 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6761 : Fact (6761 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6763 : Fact (6763 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6779 : Fact (6779 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6781 : Fact (6781 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6791 : Fact (6791 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6793 : Fact (6793 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6803 : Fact (6803 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6823 : Fact (6823 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6827 : Fact (6827 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p6737 : (E143_Finset 6737).card = 6692 := by native_decide
theorem BSD_E143_card_p6761 : (E143_Finset 6761).card = 6838 := by native_decide
theorem BSD_E143_card_p6763 : (E143_Finset 6763).card = 6767 := by native_decide
theorem BSD_E143_card_p6779 : (E143_Finset 6779).card = 6800 := by native_decide
theorem BSD_E143_card_p6781 : (E143_Finset 6781).card = 6825 := by native_decide
theorem BSD_E143_card_p6791 : (E143_Finset 6791).card = 6797 := by native_decide
theorem BSD_E143_card_p6793 : (E143_Finset 6793).card = 6732 := by native_decide
theorem BSD_E143_card_p6803 : (E143_Finset 6803).card = 6747 := by native_decide
theorem BSD_E143_card_p6823 : (E143_Finset 6823).card = 6736 := by native_decide
theorem BSD_E143_card_p6827 : (E143_Finset 6827).card = 6880 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p6737 : a_p 6737 = (46 : ℤ) := by
  have h := BSD_E143_card_p6737; unfold a_p; omega
theorem BSD_ap_p6761 : a_p 6761 = (-76 : ℤ) := by
  have h := BSD_E143_card_p6761; unfold a_p; omega
theorem BSD_ap_p6763 : a_p 6763 = (-3 : ℤ) := by
  have h := BSD_E143_card_p6763; unfold a_p; omega
theorem BSD_ap_p6779 : a_p 6779 = (-20 : ℤ) := by
  have h := BSD_E143_card_p6779; unfold a_p; omega
theorem BSD_ap_p6781 : a_p 6781 = (-43 : ℤ) := by
  have h := BSD_E143_card_p6781; unfold a_p; omega
theorem BSD_ap_p6791 : a_p 6791 = (-5 : ℤ) := by
  have h := BSD_E143_card_p6791; unfold a_p; omega
theorem BSD_ap_p6793 : a_p 6793 = (62 : ℤ) := by
  have h := BSD_E143_card_p6793; unfold a_p; omega
theorem BSD_ap_p6803 : a_p 6803 = (57 : ℤ) := by
  have h := BSD_E143_card_p6803; unfold a_p; omega
theorem BSD_ap_p6823 : a_p 6823 = (88 : ℤ) := by
  have h := BSD_E143_card_p6823; unfold a_p; omega
theorem BSD_ap_p6827 : a_p 6827 = (-52 : ℤ) := by
  have h := BSD_E143_card_p6827; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=6737: a_p=+46, 4p-a_p²=24832
theorem BSD_DegreeNonneg_p6737 : BSD_FrobeniusDegreeNonneg_OPEN 6737 := fun r => by
  have hap : (a_p 6737 : ℝ) = 46 := by exact_mod_cast BSD_ap_p6737
  have key : r ^ 2 - (a_p 6737 : ℝ) * r + ((6737 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 24832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

-- p=6761: a_p=-76, 4p-a_p²=21268
theorem BSD_DegreeNonneg_p6761 : BSD_FrobeniusDegreeNonneg_OPEN 6761 := fun r => by
  have hap : (a_p 6761 : ℝ) = -76 := by exact_mod_cast BSD_ap_p6761
  have key : r ^ 2 - (a_p 6761 : ℝ) * r + ((6761 : ℕ) : ℝ) =
      (r + 76/2) ^ 2 + 21268/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (76 : ℝ)/2)]

-- p=6763: a_p=-3, 4p-a_p²=27043
theorem BSD_DegreeNonneg_p6763 : BSD_FrobeniusDegreeNonneg_OPEN 6763 := fun r => by
  have hap : (a_p 6763 : ℝ) = -3 := by exact_mod_cast BSD_ap_p6763
  have key : r ^ 2 - (a_p 6763 : ℝ) * r + ((6763 : ℕ) : ℝ) =
      (r + 3/2) ^ 2 + 27043/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (3 : ℝ)/2)]

-- p=6779: a_p=-20, 4p-a_p²=26716
theorem BSD_DegreeNonneg_p6779 : BSD_FrobeniusDegreeNonneg_OPEN 6779 := fun r => by
  have hap : (a_p 6779 : ℝ) = -20 := by exact_mod_cast BSD_ap_p6779
  have key : r ^ 2 - (a_p 6779 : ℝ) * r + ((6779 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 26716/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=6781: a_p=-43, 4p-a_p²=25275
theorem BSD_DegreeNonneg_p6781 : BSD_FrobeniusDegreeNonneg_OPEN 6781 := fun r => by
  have hap : (a_p 6781 : ℝ) = -43 := by exact_mod_cast BSD_ap_p6781
  have key : r ^ 2 - (a_p 6781 : ℝ) * r + ((6781 : ℕ) : ℝ) =
      (r + 43/2) ^ 2 + 25275/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (43 : ℝ)/2)]

-- p=6791: a_p=-5, 4p-a_p²=27139
theorem BSD_DegreeNonneg_p6791 : BSD_FrobeniusDegreeNonneg_OPEN 6791 := fun r => by
  have hap : (a_p 6791 : ℝ) = -5 := by exact_mod_cast BSD_ap_p6791
  have key : r ^ 2 - (a_p 6791 : ℝ) * r + ((6791 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 27139/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

-- p=6793: a_p=+62, 4p-a_p²=23328
theorem BSD_DegreeNonneg_p6793 : BSD_FrobeniusDegreeNonneg_OPEN 6793 := fun r => by
  have hap : (a_p 6793 : ℝ) = 62 := by exact_mod_cast BSD_ap_p6793
  have key : r ^ 2 - (a_p 6793 : ℝ) * r + ((6793 : ℕ) : ℝ) =
      (r - 62/2) ^ 2 + 23328/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (62 : ℝ)/2)]

-- p=6803: a_p=+57, 4p-a_p²=23963
theorem BSD_DegreeNonneg_p6803 : BSD_FrobeniusDegreeNonneg_OPEN 6803 := fun r => by
  have hap : (a_p 6803 : ℝ) = 57 := by exact_mod_cast BSD_ap_p6803
  have key : r ^ 2 - (a_p 6803 : ℝ) * r + ((6803 : ℕ) : ℝ) =
      (r - 57/2) ^ 2 + 23963/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (57 : ℝ)/2)]

-- p=6823: a_p=+88, 4p-a_p²=19548
theorem BSD_DegreeNonneg_p6823 : BSD_FrobeniusDegreeNonneg_OPEN 6823 := fun r => by
  have hap : (a_p 6823 : ℝ) = 88 := by exact_mod_cast BSD_ap_p6823
  have key : r ^ 2 - (a_p 6823 : ℝ) * r + ((6823 : ℕ) : ℝ) =
      (r - 88/2) ^ 2 + 19548/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (88 : ℝ)/2)]

-- p=6827: a_p=-52, 4p-a_p²=24604
theorem BSD_DegreeNonneg_p6827 : BSD_FrobeniusDegreeNonneg_OPEN 6827 := fun r => by
  have hap : (a_p 6827 : ℝ) = -52 := by exact_mod_cast BSD_ap_p6827
  have key : r ^ 2 - (a_p 6827 : ℝ) * r + ((6827 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 24604/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p6737 : BSD_Hasse_OPEN 6737 :=
  BSD_hasse_of_degree_nonneg 6737 BSD_DegreeNonneg_p6737
theorem BSD_Hasse_OPEN_p6761 : BSD_Hasse_OPEN 6761 :=
  BSD_hasse_of_degree_nonneg 6761 BSD_DegreeNonneg_p6761
theorem BSD_Hasse_OPEN_p6763 : BSD_Hasse_OPEN 6763 :=
  BSD_hasse_of_degree_nonneg 6763 BSD_DegreeNonneg_p6763
theorem BSD_Hasse_OPEN_p6779 : BSD_Hasse_OPEN 6779 :=
  BSD_hasse_of_degree_nonneg 6779 BSD_DegreeNonneg_p6779
theorem BSD_Hasse_OPEN_p6781 : BSD_Hasse_OPEN 6781 :=
  BSD_hasse_of_degree_nonneg 6781 BSD_DegreeNonneg_p6781
theorem BSD_Hasse_OPEN_p6791 : BSD_Hasse_OPEN 6791 :=
  BSD_hasse_of_degree_nonneg 6791 BSD_DegreeNonneg_p6791
theorem BSD_Hasse_OPEN_p6793 : BSD_Hasse_OPEN 6793 :=
  BSD_hasse_of_degree_nonneg 6793 BSD_DegreeNonneg_p6793
theorem BSD_Hasse_OPEN_p6803 : BSD_Hasse_OPEN 6803 :=
  BSD_hasse_of_degree_nonneg 6803 BSD_DegreeNonneg_p6803
theorem BSD_Hasse_OPEN_p6823 : BSD_Hasse_OPEN 6823 :=
  BSD_hasse_of_degree_nonneg 6823 BSD_DegreeNonneg_p6823
theorem BSD_Hasse_OPEN_p6827 : BSD_Hasse_OPEN 6827 :=
  BSD_hasse_of_degree_nonneg 6827 BSD_DegreeNonneg_p6827

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p6737 : (a_p 6737 : ℝ) ^ 2 ≤ 4 * (6737 : ℝ) :=
  BSD_disc_from_deg_853 BSD_DegreeNonneg_p6737
theorem BSD_HasseBound_Disc_p6761 : (a_p 6761 : ℝ) ^ 2 ≤ 4 * (6761 : ℝ) :=
  BSD_disc_from_deg_853 BSD_DegreeNonneg_p6761
theorem BSD_HasseBound_Disc_p6763 : (a_p 6763 : ℝ) ^ 2 ≤ 4 * (6763 : ℝ) :=
  BSD_disc_from_deg_853 BSD_DegreeNonneg_p6763
theorem BSD_HasseBound_Disc_p6779 : (a_p 6779 : ℝ) ^ 2 ≤ 4 * (6779 : ℝ) :=
  BSD_disc_from_deg_853 BSD_DegreeNonneg_p6779
theorem BSD_HasseBound_Disc_p6781 : (a_p 6781 : ℝ) ^ 2 ≤ 4 * (6781 : ℝ) :=
  BSD_disc_from_deg_853 BSD_DegreeNonneg_p6781
theorem BSD_HasseBound_Disc_p6791 : (a_p 6791 : ℝ) ^ 2 ≤ 4 * (6791 : ℝ) :=
  BSD_disc_from_deg_853 BSD_DegreeNonneg_p6791
theorem BSD_HasseBound_Disc_p6793 : (a_p 6793 : ℝ) ^ 2 ≤ 4 * (6793 : ℝ) :=
  BSD_disc_from_deg_853 BSD_DegreeNonneg_p6793
theorem BSD_HasseBound_Disc_p6803 : (a_p 6803 : ℝ) ^ 2 ≤ 4 * (6803 : ℝ) :=
  BSD_disc_from_deg_853 BSD_DegreeNonneg_p6803
theorem BSD_HasseBound_Disc_p6823 : (a_p 6823 : ℝ) ^ 2 ≤ 4 * (6823 : ℝ) :=
  BSD_disc_from_deg_853 BSD_DegreeNonneg_p6823
theorem BSD_HasseBound_Disc_p6827 : (a_p 6827 : ℝ) ^ 2 ≤ 4 * (6827 : ℝ) :=
  BSD_disc_from_deg_853 BSD_DegreeNonneg_p6827

end Towers.BSD
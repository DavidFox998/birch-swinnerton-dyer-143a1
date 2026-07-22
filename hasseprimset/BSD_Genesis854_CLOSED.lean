/-
================================================================
Towers / BSD / BSD_Genesis854_CLOSED  (genesis-854)

HasseBridge Tier C: Hasse bounds for primes
6829..6907 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=6829: card=6769, a_p=+61, disc=-23595
  p=6833: card=6828, a_p=+6, disc=-27296
  p=6841: card=6926, a_p=-84, disc=-20308
  p=6857: card=6831, a_p=+27, disc=-26699
  p=6863: card=6948, a_p=-84, disc=-20396
  p=6869: card=6895, a_p=-25, disc=-26851
  p=6871: card=6876, a_p=-4, disc=-27468
  p=6883: card=6758, a_p=+126, disc=-11656
  p=6899: card=6890, a_p=+10, disc=-27496
  p=6907: card=6754, a_p=+154, disc=-3912

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_854 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i854_p6829 : Fact (6829 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6833 : Fact (6833 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6841 : Fact (6841 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6857 : Fact (6857 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6863 : Fact (6863 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6869 : Fact (6869 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6871 : Fact (6871 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6883 : Fact (6883 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6899 : Fact (6899 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6907 : Fact (6907 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p6829 : (E143_Finset 6829).card = 6769 := by native_decide
theorem BSD_E143_card_p6833 : (E143_Finset 6833).card = 6828 := by native_decide
theorem BSD_E143_card_p6841 : (E143_Finset 6841).card = 6926 := by native_decide
theorem BSD_E143_card_p6857 : (E143_Finset 6857).card = 6831 := by native_decide
theorem BSD_E143_card_p6863 : (E143_Finset 6863).card = 6948 := by native_decide
theorem BSD_E143_card_p6869 : (E143_Finset 6869).card = 6895 := by native_decide
theorem BSD_E143_card_p6871 : (E143_Finset 6871).card = 6876 := by native_decide
theorem BSD_E143_card_p6883 : (E143_Finset 6883).card = 6758 := by native_decide
theorem BSD_E143_card_p6899 : (E143_Finset 6899).card = 6890 := by native_decide
theorem BSD_E143_card_p6907 : (E143_Finset 6907).card = 6754 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p6829 : a_p 6829 = (61 : ℤ) := by
  have h := BSD_E143_card_p6829; unfold a_p; omega
theorem BSD_ap_p6833 : a_p 6833 = (6 : ℤ) := by
  have h := BSD_E143_card_p6833; unfold a_p; omega
theorem BSD_ap_p6841 : a_p 6841 = (-84 : ℤ) := by
  have h := BSD_E143_card_p6841; unfold a_p; omega
theorem BSD_ap_p6857 : a_p 6857 = (27 : ℤ) := by
  have h := BSD_E143_card_p6857; unfold a_p; omega
theorem BSD_ap_p6863 : a_p 6863 = (-84 : ℤ) := by
  have h := BSD_E143_card_p6863; unfold a_p; omega
theorem BSD_ap_p6869 : a_p 6869 = (-25 : ℤ) := by
  have h := BSD_E143_card_p6869; unfold a_p; omega
theorem BSD_ap_p6871 : a_p 6871 = (-4 : ℤ) := by
  have h := BSD_E143_card_p6871; unfold a_p; omega
theorem BSD_ap_p6883 : a_p 6883 = (126 : ℤ) := by
  have h := BSD_E143_card_p6883; unfold a_p; omega
theorem BSD_ap_p6899 : a_p 6899 = (10 : ℤ) := by
  have h := BSD_E143_card_p6899; unfold a_p; omega
theorem BSD_ap_p6907 : a_p 6907 = (154 : ℤ) := by
  have h := BSD_E143_card_p6907; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=6829: a_p=+61, 4p-a_p²=23595
theorem BSD_DegreeNonneg_p6829 : BSD_FrobeniusDegreeNonneg_OPEN 6829 := fun r => by
  have hap : (a_p 6829 : ℝ) = 61 := by exact_mod_cast BSD_ap_p6829
  have key : r ^ 2 - (a_p 6829 : ℝ) * r + ((6829 : ℕ) : ℝ) =
      (r - 61/2) ^ 2 + 23595/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (61 : ℝ)/2)]

-- p=6833: a_p=+6, 4p-a_p²=27296
theorem BSD_DegreeNonneg_p6833 : BSD_FrobeniusDegreeNonneg_OPEN 6833 := fun r => by
  have hap : (a_p 6833 : ℝ) = 6 := by exact_mod_cast BSD_ap_p6833
  have key : r ^ 2 - (a_p 6833 : ℝ) * r + ((6833 : ℕ) : ℝ) =
      (r - 6/2) ^ 2 + 27296/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (6 : ℝ)/2)]

-- p=6841: a_p=-84, 4p-a_p²=20308
theorem BSD_DegreeNonneg_p6841 : BSD_FrobeniusDegreeNonneg_OPEN 6841 := fun r => by
  have hap : (a_p 6841 : ℝ) = -84 := by exact_mod_cast BSD_ap_p6841
  have key : r ^ 2 - (a_p 6841 : ℝ) * r + ((6841 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 20308/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

-- p=6857: a_p=+27, 4p-a_p²=26699
theorem BSD_DegreeNonneg_p6857 : BSD_FrobeniusDegreeNonneg_OPEN 6857 := fun r => by
  have hap : (a_p 6857 : ℝ) = 27 := by exact_mod_cast BSD_ap_p6857
  have key : r ^ 2 - (a_p 6857 : ℝ) * r + ((6857 : ℕ) : ℝ) =
      (r - 27/2) ^ 2 + 26699/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (27 : ℝ)/2)]

-- p=6863: a_p=-84, 4p-a_p²=20396
theorem BSD_DegreeNonneg_p6863 : BSD_FrobeniusDegreeNonneg_OPEN 6863 := fun r => by
  have hap : (a_p 6863 : ℝ) = -84 := by exact_mod_cast BSD_ap_p6863
  have key : r ^ 2 - (a_p 6863 : ℝ) * r + ((6863 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 20396/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

-- p=6869: a_p=-25, 4p-a_p²=26851
theorem BSD_DegreeNonneg_p6869 : BSD_FrobeniusDegreeNonneg_OPEN 6869 := fun r => by
  have hap : (a_p 6869 : ℝ) = -25 := by exact_mod_cast BSD_ap_p6869
  have key : r ^ 2 - (a_p 6869 : ℝ) * r + ((6869 : ℕ) : ℝ) =
      (r + 25/2) ^ 2 + 26851/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (25 : ℝ)/2)]

-- p=6871: a_p=-4, 4p-a_p²=27468
theorem BSD_DegreeNonneg_p6871 : BSD_FrobeniusDegreeNonneg_OPEN 6871 := fun r => by
  have hap : (a_p 6871 : ℝ) = -4 := by exact_mod_cast BSD_ap_p6871
  have key : r ^ 2 - (a_p 6871 : ℝ) * r + ((6871 : ℕ) : ℝ) =
      (r + 4/2) ^ 2 + 27468/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (4 : ℝ)/2)]

-- p=6883: a_p=+126, 4p-a_p²=11656
theorem BSD_DegreeNonneg_p6883 : BSD_FrobeniusDegreeNonneg_OPEN 6883 := fun r => by
  have hap : (a_p 6883 : ℝ) = 126 := by exact_mod_cast BSD_ap_p6883
  have key : r ^ 2 - (a_p 6883 : ℝ) * r + ((6883 : ℕ) : ℝ) =
      (r - 126/2) ^ 2 + 11656/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (126 : ℝ)/2)]

-- p=6899: a_p=+10, 4p-a_p²=27496
theorem BSD_DegreeNonneg_p6899 : BSD_FrobeniusDegreeNonneg_OPEN 6899 := fun r => by
  have hap : (a_p 6899 : ℝ) = 10 := by exact_mod_cast BSD_ap_p6899
  have key : r ^ 2 - (a_p 6899 : ℝ) * r + ((6899 : ℕ) : ℝ) =
      (r - 10/2) ^ 2 + 27496/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (10 : ℝ)/2)]

-- p=6907: a_p=+154, 4p-a_p²=3912
theorem BSD_DegreeNonneg_p6907 : BSD_FrobeniusDegreeNonneg_OPEN 6907 := fun r => by
  have hap : (a_p 6907 : ℝ) = 154 := by exact_mod_cast BSD_ap_p6907
  have key : r ^ 2 - (a_p 6907 : ℝ) * r + ((6907 : ℕ) : ℝ) =
      (r - 154/2) ^ 2 + 3912/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (154 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p6829 : BSD_Hasse_OPEN 6829 :=
  BSD_hasse_of_degree_nonneg 6829 BSD_DegreeNonneg_p6829
theorem BSD_Hasse_OPEN_p6833 : BSD_Hasse_OPEN 6833 :=
  BSD_hasse_of_degree_nonneg 6833 BSD_DegreeNonneg_p6833
theorem BSD_Hasse_OPEN_p6841 : BSD_Hasse_OPEN 6841 :=
  BSD_hasse_of_degree_nonneg 6841 BSD_DegreeNonneg_p6841
theorem BSD_Hasse_OPEN_p6857 : BSD_Hasse_OPEN 6857 :=
  BSD_hasse_of_degree_nonneg 6857 BSD_DegreeNonneg_p6857
theorem BSD_Hasse_OPEN_p6863 : BSD_Hasse_OPEN 6863 :=
  BSD_hasse_of_degree_nonneg 6863 BSD_DegreeNonneg_p6863
theorem BSD_Hasse_OPEN_p6869 : BSD_Hasse_OPEN 6869 :=
  BSD_hasse_of_degree_nonneg 6869 BSD_DegreeNonneg_p6869
theorem BSD_Hasse_OPEN_p6871 : BSD_Hasse_OPEN 6871 :=
  BSD_hasse_of_degree_nonneg 6871 BSD_DegreeNonneg_p6871
theorem BSD_Hasse_OPEN_p6883 : BSD_Hasse_OPEN 6883 :=
  BSD_hasse_of_degree_nonneg 6883 BSD_DegreeNonneg_p6883
theorem BSD_Hasse_OPEN_p6899 : BSD_Hasse_OPEN 6899 :=
  BSD_hasse_of_degree_nonneg 6899 BSD_DegreeNonneg_p6899
theorem BSD_Hasse_OPEN_p6907 : BSD_Hasse_OPEN 6907 :=
  BSD_hasse_of_degree_nonneg 6907 BSD_DegreeNonneg_p6907

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p6829 : (a_p 6829 : ℝ) ^ 2 ≤ 4 * (6829 : ℝ) :=
  BSD_disc_from_deg_854 BSD_DegreeNonneg_p6829
theorem BSD_HasseBound_Disc_p6833 : (a_p 6833 : ℝ) ^ 2 ≤ 4 * (6833 : ℝ) :=
  BSD_disc_from_deg_854 BSD_DegreeNonneg_p6833
theorem BSD_HasseBound_Disc_p6841 : (a_p 6841 : ℝ) ^ 2 ≤ 4 * (6841 : ℝ) :=
  BSD_disc_from_deg_854 BSD_DegreeNonneg_p6841
theorem BSD_HasseBound_Disc_p6857 : (a_p 6857 : ℝ) ^ 2 ≤ 4 * (6857 : ℝ) :=
  BSD_disc_from_deg_854 BSD_DegreeNonneg_p6857
theorem BSD_HasseBound_Disc_p6863 : (a_p 6863 : ℝ) ^ 2 ≤ 4 * (6863 : ℝ) :=
  BSD_disc_from_deg_854 BSD_DegreeNonneg_p6863
theorem BSD_HasseBound_Disc_p6869 : (a_p 6869 : ℝ) ^ 2 ≤ 4 * (6869 : ℝ) :=
  BSD_disc_from_deg_854 BSD_DegreeNonneg_p6869
theorem BSD_HasseBound_Disc_p6871 : (a_p 6871 : ℝ) ^ 2 ≤ 4 * (6871 : ℝ) :=
  BSD_disc_from_deg_854 BSD_DegreeNonneg_p6871
theorem BSD_HasseBound_Disc_p6883 : (a_p 6883 : ℝ) ^ 2 ≤ 4 * (6883 : ℝ) :=
  BSD_disc_from_deg_854 BSD_DegreeNonneg_p6883
theorem BSD_HasseBound_Disc_p6899 : (a_p 6899 : ℝ) ^ 2 ≤ 4 * (6899 : ℝ) :=
  BSD_disc_from_deg_854 BSD_DegreeNonneg_p6899
theorem BSD_HasseBound_Disc_p6907 : (a_p 6907 : ℝ) ^ 2 ≤ 4 * (6907 : ℝ) :=
  BSD_disc_from_deg_854 BSD_DegreeNonneg_p6907

end Towers.BSD
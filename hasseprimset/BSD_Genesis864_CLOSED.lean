/-
================================================================
Towers / BSD / BSD_Genesis864_CLOSED  (genesis-864)

HasseBridge Tier C: Hasse bounds for primes
7717..7817 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=7717: card=7750, a_p=-32, disc=-29844
  p=7723: card=7695, a_p=+29, disc=-30051
  p=7727: card=7581, a_p=+147, disc=-9299
  p=7741: card=7666, a_p=+76, disc=-25188
  p=7753: card=7677, a_p=+77, disc=-25083
  p=7757: card=7884, a_p=-126, disc=-15152
  p=7759: card=7927, a_p=-167, disc=-3147
  p=7789: card=7808, a_p=-18, disc=-30832
  p=7793: card=7833, a_p=-39, disc=-29651
  p=7817: card=7678, a_p=+140, disc=-11668

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_864 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i864_p7717 : Fact (7717 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7723 : Fact (7723 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7727 : Fact (7727 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7741 : Fact (7741 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7753 : Fact (7753 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7757 : Fact (7757 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7759 : Fact (7759 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7789 : Fact (7789 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7793 : Fact (7793 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7817 : Fact (7817 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p7717 : (E143_Finset 7717).card = 7750 := by native_decide
theorem BSD_E143_card_p7723 : (E143_Finset 7723).card = 7695 := by native_decide
theorem BSD_E143_card_p7727 : (E143_Finset 7727).card = 7581 := by native_decide
theorem BSD_E143_card_p7741 : (E143_Finset 7741).card = 7666 := by native_decide
theorem BSD_E143_card_p7753 : (E143_Finset 7753).card = 7677 := by native_decide
theorem BSD_E143_card_p7757 : (E143_Finset 7757).card = 7884 := by native_decide
theorem BSD_E143_card_p7759 : (E143_Finset 7759).card = 7927 := by native_decide
theorem BSD_E143_card_p7789 : (E143_Finset 7789).card = 7808 := by native_decide
theorem BSD_E143_card_p7793 : (E143_Finset 7793).card = 7833 := by native_decide
theorem BSD_E143_card_p7817 : (E143_Finset 7817).card = 7678 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p7717 : a_p 7717 = (-32 : ℤ) := by
  have h := BSD_E143_card_p7717; unfold a_p; omega
theorem BSD_ap_p7723 : a_p 7723 = (29 : ℤ) := by
  have h := BSD_E143_card_p7723; unfold a_p; omega
theorem BSD_ap_p7727 : a_p 7727 = (147 : ℤ) := by
  have h := BSD_E143_card_p7727; unfold a_p; omega
theorem BSD_ap_p7741 : a_p 7741 = (76 : ℤ) := by
  have h := BSD_E143_card_p7741; unfold a_p; omega
theorem BSD_ap_p7753 : a_p 7753 = (77 : ℤ) := by
  have h := BSD_E143_card_p7753; unfold a_p; omega
theorem BSD_ap_p7757 : a_p 7757 = (-126 : ℤ) := by
  have h := BSD_E143_card_p7757; unfold a_p; omega
theorem BSD_ap_p7759 : a_p 7759 = (-167 : ℤ) := by
  have h := BSD_E143_card_p7759; unfold a_p; omega
theorem BSD_ap_p7789 : a_p 7789 = (-18 : ℤ) := by
  have h := BSD_E143_card_p7789; unfold a_p; omega
theorem BSD_ap_p7793 : a_p 7793 = (-39 : ℤ) := by
  have h := BSD_E143_card_p7793; unfold a_p; omega
theorem BSD_ap_p7817 : a_p 7817 = (140 : ℤ) := by
  have h := BSD_E143_card_p7817; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=7717: a_p=-32, 4p-a_p²=29844
theorem BSD_DegreeNonneg_p7717 : BSD_FrobeniusDegreeNonneg_OPEN 7717 := fun r => by
  have hap : (a_p 7717 : ℝ) = -32 := by exact_mod_cast BSD_ap_p7717
  have key : r ^ 2 - (a_p 7717 : ℝ) * r + ((7717 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 29844/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

-- p=7723: a_p=+29, 4p-a_p²=30051
theorem BSD_DegreeNonneg_p7723 : BSD_FrobeniusDegreeNonneg_OPEN 7723 := fun r => by
  have hap : (a_p 7723 : ℝ) = 29 := by exact_mod_cast BSD_ap_p7723
  have key : r ^ 2 - (a_p 7723 : ℝ) * r + ((7723 : ℕ) : ℝ) =
      (r - 29/2) ^ 2 + 30051/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (29 : ℝ)/2)]

-- p=7727: a_p=+147, 4p-a_p²=9299
theorem BSD_DegreeNonneg_p7727 : BSD_FrobeniusDegreeNonneg_OPEN 7727 := fun r => by
  have hap : (a_p 7727 : ℝ) = 147 := by exact_mod_cast BSD_ap_p7727
  have key : r ^ 2 - (a_p 7727 : ℝ) * r + ((7727 : ℕ) : ℝ) =
      (r - 147/2) ^ 2 + 9299/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (147 : ℝ)/2)]

-- p=7741: a_p=+76, 4p-a_p²=25188
theorem BSD_DegreeNonneg_p7741 : BSD_FrobeniusDegreeNonneg_OPEN 7741 := fun r => by
  have hap : (a_p 7741 : ℝ) = 76 := by exact_mod_cast BSD_ap_p7741
  have key : r ^ 2 - (a_p 7741 : ℝ) * r + ((7741 : ℕ) : ℝ) =
      (r - 76/2) ^ 2 + 25188/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (76 : ℝ)/2)]

-- p=7753: a_p=+77, 4p-a_p²=25083
theorem BSD_DegreeNonneg_p7753 : BSD_FrobeniusDegreeNonneg_OPEN 7753 := fun r => by
  have hap : (a_p 7753 : ℝ) = 77 := by exact_mod_cast BSD_ap_p7753
  have key : r ^ 2 - (a_p 7753 : ℝ) * r + ((7753 : ℕ) : ℝ) =
      (r - 77/2) ^ 2 + 25083/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (77 : ℝ)/2)]

-- p=7757: a_p=-126, 4p-a_p²=15152
theorem BSD_DegreeNonneg_p7757 : BSD_FrobeniusDegreeNonneg_OPEN 7757 := fun r => by
  have hap : (a_p 7757 : ℝ) = -126 := by exact_mod_cast BSD_ap_p7757
  have key : r ^ 2 - (a_p 7757 : ℝ) * r + ((7757 : ℕ) : ℝ) =
      (r + 126/2) ^ 2 + 15152/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (126 : ℝ)/2)]

-- p=7759: a_p=-167, 4p-a_p²=3147
theorem BSD_DegreeNonneg_p7759 : BSD_FrobeniusDegreeNonneg_OPEN 7759 := fun r => by
  have hap : (a_p 7759 : ℝ) = -167 := by exact_mod_cast BSD_ap_p7759
  have key : r ^ 2 - (a_p 7759 : ℝ) * r + ((7759 : ℕ) : ℝ) =
      (r + 167/2) ^ 2 + 3147/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (167 : ℝ)/2)]

-- p=7789: a_p=-18, 4p-a_p²=30832
theorem BSD_DegreeNonneg_p7789 : BSD_FrobeniusDegreeNonneg_OPEN 7789 := fun r => by
  have hap : (a_p 7789 : ℝ) = -18 := by exact_mod_cast BSD_ap_p7789
  have key : r ^ 2 - (a_p 7789 : ℝ) * r + ((7789 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 30832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

-- p=7793: a_p=-39, 4p-a_p²=29651
theorem BSD_DegreeNonneg_p7793 : BSD_FrobeniusDegreeNonneg_OPEN 7793 := fun r => by
  have hap : (a_p 7793 : ℝ) = -39 := by exact_mod_cast BSD_ap_p7793
  have key : r ^ 2 - (a_p 7793 : ℝ) * r + ((7793 : ℕ) : ℝ) =
      (r + 39/2) ^ 2 + 29651/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (39 : ℝ)/2)]

-- p=7817: a_p=+140, 4p-a_p²=11668
theorem BSD_DegreeNonneg_p7817 : BSD_FrobeniusDegreeNonneg_OPEN 7817 := fun r => by
  have hap : (a_p 7817 : ℝ) = 140 := by exact_mod_cast BSD_ap_p7817
  have key : r ^ 2 - (a_p 7817 : ℝ) * r + ((7817 : ℕ) : ℝ) =
      (r - 140/2) ^ 2 + 11668/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (140 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p7717 : BSD_Hasse_OPEN 7717 :=
  BSD_hasse_of_degree_nonneg 7717 BSD_DegreeNonneg_p7717
theorem BSD_Hasse_OPEN_p7723 : BSD_Hasse_OPEN 7723 :=
  BSD_hasse_of_degree_nonneg 7723 BSD_DegreeNonneg_p7723
theorem BSD_Hasse_OPEN_p7727 : BSD_Hasse_OPEN 7727 :=
  BSD_hasse_of_degree_nonneg 7727 BSD_DegreeNonneg_p7727
theorem BSD_Hasse_OPEN_p7741 : BSD_Hasse_OPEN 7741 :=
  BSD_hasse_of_degree_nonneg 7741 BSD_DegreeNonneg_p7741
theorem BSD_Hasse_OPEN_p7753 : BSD_Hasse_OPEN 7753 :=
  BSD_hasse_of_degree_nonneg 7753 BSD_DegreeNonneg_p7753
theorem BSD_Hasse_OPEN_p7757 : BSD_Hasse_OPEN 7757 :=
  BSD_hasse_of_degree_nonneg 7757 BSD_DegreeNonneg_p7757
theorem BSD_Hasse_OPEN_p7759 : BSD_Hasse_OPEN 7759 :=
  BSD_hasse_of_degree_nonneg 7759 BSD_DegreeNonneg_p7759
theorem BSD_Hasse_OPEN_p7789 : BSD_Hasse_OPEN 7789 :=
  BSD_hasse_of_degree_nonneg 7789 BSD_DegreeNonneg_p7789
theorem BSD_Hasse_OPEN_p7793 : BSD_Hasse_OPEN 7793 :=
  BSD_hasse_of_degree_nonneg 7793 BSD_DegreeNonneg_p7793
theorem BSD_Hasse_OPEN_p7817 : BSD_Hasse_OPEN 7817 :=
  BSD_hasse_of_degree_nonneg 7817 BSD_DegreeNonneg_p7817

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p7717 : (a_p 7717 : ℝ) ^ 2 ≤ 4 * (7717 : ℝ) :=
  BSD_disc_from_deg_864 BSD_DegreeNonneg_p7717
theorem BSD_HasseBound_Disc_p7723 : (a_p 7723 : ℝ) ^ 2 ≤ 4 * (7723 : ℝ) :=
  BSD_disc_from_deg_864 BSD_DegreeNonneg_p7723
theorem BSD_HasseBound_Disc_p7727 : (a_p 7727 : ℝ) ^ 2 ≤ 4 * (7727 : ℝ) :=
  BSD_disc_from_deg_864 BSD_DegreeNonneg_p7727
theorem BSD_HasseBound_Disc_p7741 : (a_p 7741 : ℝ) ^ 2 ≤ 4 * (7741 : ℝ) :=
  BSD_disc_from_deg_864 BSD_DegreeNonneg_p7741
theorem BSD_HasseBound_Disc_p7753 : (a_p 7753 : ℝ) ^ 2 ≤ 4 * (7753 : ℝ) :=
  BSD_disc_from_deg_864 BSD_DegreeNonneg_p7753
theorem BSD_HasseBound_Disc_p7757 : (a_p 7757 : ℝ) ^ 2 ≤ 4 * (7757 : ℝ) :=
  BSD_disc_from_deg_864 BSD_DegreeNonneg_p7757
theorem BSD_HasseBound_Disc_p7759 : (a_p 7759 : ℝ) ^ 2 ≤ 4 * (7759 : ℝ) :=
  BSD_disc_from_deg_864 BSD_DegreeNonneg_p7759
theorem BSD_HasseBound_Disc_p7789 : (a_p 7789 : ℝ) ^ 2 ≤ 4 * (7789 : ℝ) :=
  BSD_disc_from_deg_864 BSD_DegreeNonneg_p7789
theorem BSD_HasseBound_Disc_p7793 : (a_p 7793 : ℝ) ^ 2 ≤ 4 * (7793 : ℝ) :=
  BSD_disc_from_deg_864 BSD_DegreeNonneg_p7793
theorem BSD_HasseBound_Disc_p7817 : (a_p 7817 : ℝ) ^ 2 ≤ 4 * (7817 : ℝ) :=
  BSD_disc_from_deg_864 BSD_DegreeNonneg_p7817

end Towers.BSD
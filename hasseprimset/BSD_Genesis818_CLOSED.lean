/-
================================================================
Towers / BSD / BSD_Genesis818_CLOSED  (genesis-818)

HasseBridge Tier C: Hasse bounds for primes
3719..3797 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=3719: card=3627, a_p=+93, disc=-6227
  p=3727: card=3725, a_p=+3, disc=-14899
  p=3733: card=3696, a_p=+38, disc=-13488
  p=3739: card=3710, a_p=+30, disc=-14056
  p=3761: card=3718, a_p=+44, disc=-13108
  p=3767: card=3871, a_p=-103, disc=-4459
  p=3769: card=3744, a_p=+26, disc=-14400
  p=3779: card=3688, a_p=+92, disc=-6652
  p=3793: card=3832, a_p=-38, disc=-13728
  p=3797: card=3872, a_p=-74, disc=-9712

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_818 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i818_p3719 : Fact (3719 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3727 : Fact (3727 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3733 : Fact (3733 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3739 : Fact (3739 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3761 : Fact (3761 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3767 : Fact (3767 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3769 : Fact (3769 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3779 : Fact (3779 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3793 : Fact (3793 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3797 : Fact (3797 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p3719 : (E143_Finset 3719).card = 3627 := by native_decide
theorem BSD_E143_card_p3727 : (E143_Finset 3727).card = 3725 := by native_decide
theorem BSD_E143_card_p3733 : (E143_Finset 3733).card = 3696 := by native_decide
theorem BSD_E143_card_p3739 : (E143_Finset 3739).card = 3710 := by native_decide
theorem BSD_E143_card_p3761 : (E143_Finset 3761).card = 3718 := by native_decide
theorem BSD_E143_card_p3767 : (E143_Finset 3767).card = 3871 := by native_decide
theorem BSD_E143_card_p3769 : (E143_Finset 3769).card = 3744 := by native_decide
theorem BSD_E143_card_p3779 : (E143_Finset 3779).card = 3688 := by native_decide
theorem BSD_E143_card_p3793 : (E143_Finset 3793).card = 3832 := by native_decide
theorem BSD_E143_card_p3797 : (E143_Finset 3797).card = 3872 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p3719 : a_p 3719 = (93 : ℤ) := by
  have h := BSD_E143_card_p3719; unfold a_p; omega
theorem BSD_ap_p3727 : a_p 3727 = (3 : ℤ) := by
  have h := BSD_E143_card_p3727; unfold a_p; omega
theorem BSD_ap_p3733 : a_p 3733 = (38 : ℤ) := by
  have h := BSD_E143_card_p3733; unfold a_p; omega
theorem BSD_ap_p3739 : a_p 3739 = (30 : ℤ) := by
  have h := BSD_E143_card_p3739; unfold a_p; omega
theorem BSD_ap_p3761 : a_p 3761 = (44 : ℤ) := by
  have h := BSD_E143_card_p3761; unfold a_p; omega
theorem BSD_ap_p3767 : a_p 3767 = (-103 : ℤ) := by
  have h := BSD_E143_card_p3767; unfold a_p; omega
theorem BSD_ap_p3769 : a_p 3769 = (26 : ℤ) := by
  have h := BSD_E143_card_p3769; unfold a_p; omega
theorem BSD_ap_p3779 : a_p 3779 = (92 : ℤ) := by
  have h := BSD_E143_card_p3779; unfold a_p; omega
theorem BSD_ap_p3793 : a_p 3793 = (-38 : ℤ) := by
  have h := BSD_E143_card_p3793; unfold a_p; omega
theorem BSD_ap_p3797 : a_p 3797 = (-74 : ℤ) := by
  have h := BSD_E143_card_p3797; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=3719: a_p=+93, 4p-a_p²=6227
theorem BSD_DegreeNonneg_p3719 : BSD_FrobeniusDegreeNonneg_OPEN 3719 := fun r => by
  have hap : (a_p 3719 : ℝ) = 93 := by exact_mod_cast BSD_ap_p3719
  have key : r ^ 2 - (a_p 3719 : ℝ) * r + ((3719 : ℕ) : ℝ) =
      (r - 93/2) ^ 2 + 6227/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (93 : ℝ)/2)]

-- p=3727: a_p=+3, 4p-a_p²=14899
theorem BSD_DegreeNonneg_p3727 : BSD_FrobeniusDegreeNonneg_OPEN 3727 := fun r => by
  have hap : (a_p 3727 : ℝ) = 3 := by exact_mod_cast BSD_ap_p3727
  have key : r ^ 2 - (a_p 3727 : ℝ) * r + ((3727 : ℕ) : ℝ) =
      (r - 3/2) ^ 2 + 14899/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (3 : ℝ)/2)]

-- p=3733: a_p=+38, 4p-a_p²=13488
theorem BSD_DegreeNonneg_p3733 : BSD_FrobeniusDegreeNonneg_OPEN 3733 := fun r => by
  have hap : (a_p 3733 : ℝ) = 38 := by exact_mod_cast BSD_ap_p3733
  have key : r ^ 2 - (a_p 3733 : ℝ) * r + ((3733 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 13488/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

-- p=3739: a_p=+30, 4p-a_p²=14056
theorem BSD_DegreeNonneg_p3739 : BSD_FrobeniusDegreeNonneg_OPEN 3739 := fun r => by
  have hap : (a_p 3739 : ℝ) = 30 := by exact_mod_cast BSD_ap_p3739
  have key : r ^ 2 - (a_p 3739 : ℝ) * r + ((3739 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 14056/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

-- p=3761: a_p=+44, 4p-a_p²=13108
theorem BSD_DegreeNonneg_p3761 : BSD_FrobeniusDegreeNonneg_OPEN 3761 := fun r => by
  have hap : (a_p 3761 : ℝ) = 44 := by exact_mod_cast BSD_ap_p3761
  have key : r ^ 2 - (a_p 3761 : ℝ) * r + ((3761 : ℕ) : ℝ) =
      (r - 44/2) ^ 2 + 13108/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (44 : ℝ)/2)]

-- p=3767: a_p=-103, 4p-a_p²=4459
theorem BSD_DegreeNonneg_p3767 : BSD_FrobeniusDegreeNonneg_OPEN 3767 := fun r => by
  have hap : (a_p 3767 : ℝ) = -103 := by exact_mod_cast BSD_ap_p3767
  have key : r ^ 2 - (a_p 3767 : ℝ) * r + ((3767 : ℕ) : ℝ) =
      (r + 103/2) ^ 2 + 4459/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (103 : ℝ)/2)]

-- p=3769: a_p=+26, 4p-a_p²=14400
theorem BSD_DegreeNonneg_p3769 : BSD_FrobeniusDegreeNonneg_OPEN 3769 := fun r => by
  have hap : (a_p 3769 : ℝ) = 26 := by exact_mod_cast BSD_ap_p3769
  have key : r ^ 2 - (a_p 3769 : ℝ) * r + ((3769 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 14400/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

-- p=3779: a_p=+92, 4p-a_p²=6652
theorem BSD_DegreeNonneg_p3779 : BSD_FrobeniusDegreeNonneg_OPEN 3779 := fun r => by
  have hap : (a_p 3779 : ℝ) = 92 := by exact_mod_cast BSD_ap_p3779
  have key : r ^ 2 - (a_p 3779 : ℝ) * r + ((3779 : ℕ) : ℝ) =
      (r - 92/2) ^ 2 + 6652/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (92 : ℝ)/2)]

-- p=3793: a_p=-38, 4p-a_p²=13728
theorem BSD_DegreeNonneg_p3793 : BSD_FrobeniusDegreeNonneg_OPEN 3793 := fun r => by
  have hap : (a_p 3793 : ℝ) = -38 := by exact_mod_cast BSD_ap_p3793
  have key : r ^ 2 - (a_p 3793 : ℝ) * r + ((3793 : ℕ) : ℝ) =
      (r + 38/2) ^ 2 + 13728/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (38 : ℝ)/2)]

-- p=3797: a_p=-74, 4p-a_p²=9712
theorem BSD_DegreeNonneg_p3797 : BSD_FrobeniusDegreeNonneg_OPEN 3797 := fun r => by
  have hap : (a_p 3797 : ℝ) = -74 := by exact_mod_cast BSD_ap_p3797
  have key : r ^ 2 - (a_p 3797 : ℝ) * r + ((3797 : ℕ) : ℝ) =
      (r + 74/2) ^ 2 + 9712/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (74 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p3719 : BSD_Hasse_OPEN 3719 :=
  BSD_hasse_of_degree_nonneg 3719 BSD_DegreeNonneg_p3719
theorem BSD_Hasse_OPEN_p3727 : BSD_Hasse_OPEN 3727 :=
  BSD_hasse_of_degree_nonneg 3727 BSD_DegreeNonneg_p3727
theorem BSD_Hasse_OPEN_p3733 : BSD_Hasse_OPEN 3733 :=
  BSD_hasse_of_degree_nonneg 3733 BSD_DegreeNonneg_p3733
theorem BSD_Hasse_OPEN_p3739 : BSD_Hasse_OPEN 3739 :=
  BSD_hasse_of_degree_nonneg 3739 BSD_DegreeNonneg_p3739
theorem BSD_Hasse_OPEN_p3761 : BSD_Hasse_OPEN 3761 :=
  BSD_hasse_of_degree_nonneg 3761 BSD_DegreeNonneg_p3761
theorem BSD_Hasse_OPEN_p3767 : BSD_Hasse_OPEN 3767 :=
  BSD_hasse_of_degree_nonneg 3767 BSD_DegreeNonneg_p3767
theorem BSD_Hasse_OPEN_p3769 : BSD_Hasse_OPEN 3769 :=
  BSD_hasse_of_degree_nonneg 3769 BSD_DegreeNonneg_p3769
theorem BSD_Hasse_OPEN_p3779 : BSD_Hasse_OPEN 3779 :=
  BSD_hasse_of_degree_nonneg 3779 BSD_DegreeNonneg_p3779
theorem BSD_Hasse_OPEN_p3793 : BSD_Hasse_OPEN 3793 :=
  BSD_hasse_of_degree_nonneg 3793 BSD_DegreeNonneg_p3793
theorem BSD_Hasse_OPEN_p3797 : BSD_Hasse_OPEN 3797 :=
  BSD_hasse_of_degree_nonneg 3797 BSD_DegreeNonneg_p3797

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p3719 : (a_p 3719 : ℝ) ^ 2 ≤ 4 * (3719 : ℝ) :=
  BSD_disc_from_deg_818 BSD_DegreeNonneg_p3719
theorem BSD_HasseBound_Disc_p3727 : (a_p 3727 : ℝ) ^ 2 ≤ 4 * (3727 : ℝ) :=
  BSD_disc_from_deg_818 BSD_DegreeNonneg_p3727
theorem BSD_HasseBound_Disc_p3733 : (a_p 3733 : ℝ) ^ 2 ≤ 4 * (3733 : ℝ) :=
  BSD_disc_from_deg_818 BSD_DegreeNonneg_p3733
theorem BSD_HasseBound_Disc_p3739 : (a_p 3739 : ℝ) ^ 2 ≤ 4 * (3739 : ℝ) :=
  BSD_disc_from_deg_818 BSD_DegreeNonneg_p3739
theorem BSD_HasseBound_Disc_p3761 : (a_p 3761 : ℝ) ^ 2 ≤ 4 * (3761 : ℝ) :=
  BSD_disc_from_deg_818 BSD_DegreeNonneg_p3761
theorem BSD_HasseBound_Disc_p3767 : (a_p 3767 : ℝ) ^ 2 ≤ 4 * (3767 : ℝ) :=
  BSD_disc_from_deg_818 BSD_DegreeNonneg_p3767
theorem BSD_HasseBound_Disc_p3769 : (a_p 3769 : ℝ) ^ 2 ≤ 4 * (3769 : ℝ) :=
  BSD_disc_from_deg_818 BSD_DegreeNonneg_p3769
theorem BSD_HasseBound_Disc_p3779 : (a_p 3779 : ℝ) ^ 2 ≤ 4 * (3779 : ℝ) :=
  BSD_disc_from_deg_818 BSD_DegreeNonneg_p3779
theorem BSD_HasseBound_Disc_p3793 : (a_p 3793 : ℝ) ^ 2 ≤ 4 * (3793 : ℝ) :=
  BSD_disc_from_deg_818 BSD_DegreeNonneg_p3793
theorem BSD_HasseBound_Disc_p3797 : (a_p 3797 : ℝ) ^ 2 ≤ 4 * (3797 : ℝ) :=
  BSD_disc_from_deg_818 BSD_DegreeNonneg_p3797

end Towers.BSD
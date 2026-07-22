/-
================================================================
Towers / BSD / BSD_Genesis819_CLOSED  (genesis-819)

HasseBridge Tier C: Hasse bounds for primes
3803..3881 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=3803: card=3818, a_p=-14, disc=-15016
  p=3821: card=3761, a_p=+61, disc=-11563
  p=3823: card=3886, a_p=-62, disc=-11448
  p=3833: card=3741, a_p=+93, disc=-6683
  p=3847: card=3936, a_p=-88, disc=-7644
  p=3851: card=3937, a_p=-85, disc=-8179
  p=3853: card=3808, a_p=+46, disc=-13296
  p=3863: card=3948, a_p=-84, disc=-8396
  p=3877: card=3872, a_p=+6, disc=-15472
  p=3881: card=3777, a_p=+105, disc=-4499

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_819 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i819_p3803 : Fact (3803 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3821 : Fact (3821 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3823 : Fact (3823 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3833 : Fact (3833 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3847 : Fact (3847 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3851 : Fact (3851 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3853 : Fact (3853 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3863 : Fact (3863 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3877 : Fact (3877 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3881 : Fact (3881 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p3803 : (E143_Finset 3803).card = 3818 := by native_decide
theorem BSD_E143_card_p3821 : (E143_Finset 3821).card = 3761 := by native_decide
theorem BSD_E143_card_p3823 : (E143_Finset 3823).card = 3886 := by native_decide
theorem BSD_E143_card_p3833 : (E143_Finset 3833).card = 3741 := by native_decide
theorem BSD_E143_card_p3847 : (E143_Finset 3847).card = 3936 := by native_decide
theorem BSD_E143_card_p3851 : (E143_Finset 3851).card = 3937 := by native_decide
theorem BSD_E143_card_p3853 : (E143_Finset 3853).card = 3808 := by native_decide
theorem BSD_E143_card_p3863 : (E143_Finset 3863).card = 3948 := by native_decide
theorem BSD_E143_card_p3877 : (E143_Finset 3877).card = 3872 := by native_decide
theorem BSD_E143_card_p3881 : (E143_Finset 3881).card = 3777 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p3803 : a_p 3803 = (-14 : ℤ) := by
  have h := BSD_E143_card_p3803; unfold a_p; omega
theorem BSD_ap_p3821 : a_p 3821 = (61 : ℤ) := by
  have h := BSD_E143_card_p3821; unfold a_p; omega
theorem BSD_ap_p3823 : a_p 3823 = (-62 : ℤ) := by
  have h := BSD_E143_card_p3823; unfold a_p; omega
theorem BSD_ap_p3833 : a_p 3833 = (93 : ℤ) := by
  have h := BSD_E143_card_p3833; unfold a_p; omega
theorem BSD_ap_p3847 : a_p 3847 = (-88 : ℤ) := by
  have h := BSD_E143_card_p3847; unfold a_p; omega
theorem BSD_ap_p3851 : a_p 3851 = (-85 : ℤ) := by
  have h := BSD_E143_card_p3851; unfold a_p; omega
theorem BSD_ap_p3853 : a_p 3853 = (46 : ℤ) := by
  have h := BSD_E143_card_p3853; unfold a_p; omega
theorem BSD_ap_p3863 : a_p 3863 = (-84 : ℤ) := by
  have h := BSD_E143_card_p3863; unfold a_p; omega
theorem BSD_ap_p3877 : a_p 3877 = (6 : ℤ) := by
  have h := BSD_E143_card_p3877; unfold a_p; omega
theorem BSD_ap_p3881 : a_p 3881 = (105 : ℤ) := by
  have h := BSD_E143_card_p3881; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=3803: a_p=-14, 4p-a_p²=15016
theorem BSD_DegreeNonneg_p3803 : BSD_FrobeniusDegreeNonneg_OPEN 3803 := fun r => by
  have hap : (a_p 3803 : ℝ) = -14 := by exact_mod_cast BSD_ap_p3803
  have key : r ^ 2 - (a_p 3803 : ℝ) * r + ((3803 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 15016/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

-- p=3821: a_p=+61, 4p-a_p²=11563
theorem BSD_DegreeNonneg_p3821 : BSD_FrobeniusDegreeNonneg_OPEN 3821 := fun r => by
  have hap : (a_p 3821 : ℝ) = 61 := by exact_mod_cast BSD_ap_p3821
  have key : r ^ 2 - (a_p 3821 : ℝ) * r + ((3821 : ℕ) : ℝ) =
      (r - 61/2) ^ 2 + 11563/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (61 : ℝ)/2)]

-- p=3823: a_p=-62, 4p-a_p²=11448
theorem BSD_DegreeNonneg_p3823 : BSD_FrobeniusDegreeNonneg_OPEN 3823 := fun r => by
  have hap : (a_p 3823 : ℝ) = -62 := by exact_mod_cast BSD_ap_p3823
  have key : r ^ 2 - (a_p 3823 : ℝ) * r + ((3823 : ℕ) : ℝ) =
      (r + 62/2) ^ 2 + 11448/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (62 : ℝ)/2)]

-- p=3833: a_p=+93, 4p-a_p²=6683
theorem BSD_DegreeNonneg_p3833 : BSD_FrobeniusDegreeNonneg_OPEN 3833 := fun r => by
  have hap : (a_p 3833 : ℝ) = 93 := by exact_mod_cast BSD_ap_p3833
  have key : r ^ 2 - (a_p 3833 : ℝ) * r + ((3833 : ℕ) : ℝ) =
      (r - 93/2) ^ 2 + 6683/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (93 : ℝ)/2)]

-- p=3847: a_p=-88, 4p-a_p²=7644
theorem BSD_DegreeNonneg_p3847 : BSD_FrobeniusDegreeNonneg_OPEN 3847 := fun r => by
  have hap : (a_p 3847 : ℝ) = -88 := by exact_mod_cast BSD_ap_p3847
  have key : r ^ 2 - (a_p 3847 : ℝ) * r + ((3847 : ℕ) : ℝ) =
      (r + 88/2) ^ 2 + 7644/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (88 : ℝ)/2)]

-- p=3851: a_p=-85, 4p-a_p²=8179
theorem BSD_DegreeNonneg_p3851 : BSD_FrobeniusDegreeNonneg_OPEN 3851 := fun r => by
  have hap : (a_p 3851 : ℝ) = -85 := by exact_mod_cast BSD_ap_p3851
  have key : r ^ 2 - (a_p 3851 : ℝ) * r + ((3851 : ℕ) : ℝ) =
      (r + 85/2) ^ 2 + 8179/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (85 : ℝ)/2)]

-- p=3853: a_p=+46, 4p-a_p²=13296
theorem BSD_DegreeNonneg_p3853 : BSD_FrobeniusDegreeNonneg_OPEN 3853 := fun r => by
  have hap : (a_p 3853 : ℝ) = 46 := by exact_mod_cast BSD_ap_p3853
  have key : r ^ 2 - (a_p 3853 : ℝ) * r + ((3853 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 13296/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

-- p=3863: a_p=-84, 4p-a_p²=8396
theorem BSD_DegreeNonneg_p3863 : BSD_FrobeniusDegreeNonneg_OPEN 3863 := fun r => by
  have hap : (a_p 3863 : ℝ) = -84 := by exact_mod_cast BSD_ap_p3863
  have key : r ^ 2 - (a_p 3863 : ℝ) * r + ((3863 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 8396/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

-- p=3877: a_p=+6, 4p-a_p²=15472
theorem BSD_DegreeNonneg_p3877 : BSD_FrobeniusDegreeNonneg_OPEN 3877 := fun r => by
  have hap : (a_p 3877 : ℝ) = 6 := by exact_mod_cast BSD_ap_p3877
  have key : r ^ 2 - (a_p 3877 : ℝ) * r + ((3877 : ℕ) : ℝ) =
      (r - 6/2) ^ 2 + 15472/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (6 : ℝ)/2)]

-- p=3881: a_p=+105, 4p-a_p²=4499
theorem BSD_DegreeNonneg_p3881 : BSD_FrobeniusDegreeNonneg_OPEN 3881 := fun r => by
  have hap : (a_p 3881 : ℝ) = 105 := by exact_mod_cast BSD_ap_p3881
  have key : r ^ 2 - (a_p 3881 : ℝ) * r + ((3881 : ℕ) : ℝ) =
      (r - 105/2) ^ 2 + 4499/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (105 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p3803 : BSD_Hasse_OPEN 3803 :=
  BSD_hasse_of_degree_nonneg 3803 BSD_DegreeNonneg_p3803
theorem BSD_Hasse_OPEN_p3821 : BSD_Hasse_OPEN 3821 :=
  BSD_hasse_of_degree_nonneg 3821 BSD_DegreeNonneg_p3821
theorem BSD_Hasse_OPEN_p3823 : BSD_Hasse_OPEN 3823 :=
  BSD_hasse_of_degree_nonneg 3823 BSD_DegreeNonneg_p3823
theorem BSD_Hasse_OPEN_p3833 : BSD_Hasse_OPEN 3833 :=
  BSD_hasse_of_degree_nonneg 3833 BSD_DegreeNonneg_p3833
theorem BSD_Hasse_OPEN_p3847 : BSD_Hasse_OPEN 3847 :=
  BSD_hasse_of_degree_nonneg 3847 BSD_DegreeNonneg_p3847
theorem BSD_Hasse_OPEN_p3851 : BSD_Hasse_OPEN 3851 :=
  BSD_hasse_of_degree_nonneg 3851 BSD_DegreeNonneg_p3851
theorem BSD_Hasse_OPEN_p3853 : BSD_Hasse_OPEN 3853 :=
  BSD_hasse_of_degree_nonneg 3853 BSD_DegreeNonneg_p3853
theorem BSD_Hasse_OPEN_p3863 : BSD_Hasse_OPEN 3863 :=
  BSD_hasse_of_degree_nonneg 3863 BSD_DegreeNonneg_p3863
theorem BSD_Hasse_OPEN_p3877 : BSD_Hasse_OPEN 3877 :=
  BSD_hasse_of_degree_nonneg 3877 BSD_DegreeNonneg_p3877
theorem BSD_Hasse_OPEN_p3881 : BSD_Hasse_OPEN 3881 :=
  BSD_hasse_of_degree_nonneg 3881 BSD_DegreeNonneg_p3881

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p3803 : (a_p 3803 : ℝ) ^ 2 ≤ 4 * (3803 : ℝ) :=
  BSD_disc_from_deg_819 BSD_DegreeNonneg_p3803
theorem BSD_HasseBound_Disc_p3821 : (a_p 3821 : ℝ) ^ 2 ≤ 4 * (3821 : ℝ) :=
  BSD_disc_from_deg_819 BSD_DegreeNonneg_p3821
theorem BSD_HasseBound_Disc_p3823 : (a_p 3823 : ℝ) ^ 2 ≤ 4 * (3823 : ℝ) :=
  BSD_disc_from_deg_819 BSD_DegreeNonneg_p3823
theorem BSD_HasseBound_Disc_p3833 : (a_p 3833 : ℝ) ^ 2 ≤ 4 * (3833 : ℝ) :=
  BSD_disc_from_deg_819 BSD_DegreeNonneg_p3833
theorem BSD_HasseBound_Disc_p3847 : (a_p 3847 : ℝ) ^ 2 ≤ 4 * (3847 : ℝ) :=
  BSD_disc_from_deg_819 BSD_DegreeNonneg_p3847
theorem BSD_HasseBound_Disc_p3851 : (a_p 3851 : ℝ) ^ 2 ≤ 4 * (3851 : ℝ) :=
  BSD_disc_from_deg_819 BSD_DegreeNonneg_p3851
theorem BSD_HasseBound_Disc_p3853 : (a_p 3853 : ℝ) ^ 2 ≤ 4 * (3853 : ℝ) :=
  BSD_disc_from_deg_819 BSD_DegreeNonneg_p3853
theorem BSD_HasseBound_Disc_p3863 : (a_p 3863 : ℝ) ^ 2 ≤ 4 * (3863 : ℝ) :=
  BSD_disc_from_deg_819 BSD_DegreeNonneg_p3863
theorem BSD_HasseBound_Disc_p3877 : (a_p 3877 : ℝ) ^ 2 ≤ 4 * (3877 : ℝ) :=
  BSD_disc_from_deg_819 BSD_DegreeNonneg_p3877
theorem BSD_HasseBound_Disc_p3881 : (a_p 3881 : ℝ) ^ 2 ≤ 4 * (3881 : ℝ) :=
  BSD_disc_from_deg_819 BSD_DegreeNonneg_p3881

end Towers.BSD
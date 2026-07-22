/-
================================================================
Towers / BSD / BSD_Genesis820_CLOSED  (genesis-820)

HasseBridge Tier C: Hasse bounds for primes
3889..3947 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=3889: card=3852, a_p=+38, disc=-14112
  p=3907: card=3850, a_p=+58, disc=-12264
  p=3911: card=3848, a_p=+64, disc=-11548
  p=3917: card=3939, a_p=-21, disc=-15227
  p=3919: card=4032, a_p=-112, disc=-3132
  p=3923: card=3948, a_p=-24, disc=-15116
  p=3929: card=4004, a_p=-74, disc=-10240
  p=3931: card=4039, a_p=-107, disc=-4275
  p=3943: card=3944, a_p=+0, disc=-15772
  p=3947: card=3885, a_p=+63, disc=-11819

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_820 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i820_p3889 : Fact (3889 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3907 : Fact (3907 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3911 : Fact (3911 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3917 : Fact (3917 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3919 : Fact (3919 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3923 : Fact (3923 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3929 : Fact (3929 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3931 : Fact (3931 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3943 : Fact (3943 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3947 : Fact (3947 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p3889 : (E143_Finset 3889).card = 3852 := by native_decide
theorem BSD_E143_card_p3907 : (E143_Finset 3907).card = 3850 := by native_decide
theorem BSD_E143_card_p3911 : (E143_Finset 3911).card = 3848 := by native_decide
theorem BSD_E143_card_p3917 : (E143_Finset 3917).card = 3939 := by native_decide
theorem BSD_E143_card_p3919 : (E143_Finset 3919).card = 4032 := by native_decide
theorem BSD_E143_card_p3923 : (E143_Finset 3923).card = 3948 := by native_decide
theorem BSD_E143_card_p3929 : (E143_Finset 3929).card = 4004 := by native_decide
theorem BSD_E143_card_p3931 : (E143_Finset 3931).card = 4039 := by native_decide
theorem BSD_E143_card_p3943 : (E143_Finset 3943).card = 3944 := by native_decide
theorem BSD_E143_card_p3947 : (E143_Finset 3947).card = 3885 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p3889 : a_p 3889 = (38 : ℤ) := by
  have h := BSD_E143_card_p3889; unfold a_p; omega
theorem BSD_ap_p3907 : a_p 3907 = (58 : ℤ) := by
  have h := BSD_E143_card_p3907; unfold a_p; omega
theorem BSD_ap_p3911 : a_p 3911 = (64 : ℤ) := by
  have h := BSD_E143_card_p3911; unfold a_p; omega
theorem BSD_ap_p3917 : a_p 3917 = (-21 : ℤ) := by
  have h := BSD_E143_card_p3917; unfold a_p; omega
theorem BSD_ap_p3919 : a_p 3919 = (-112 : ℤ) := by
  have h := BSD_E143_card_p3919; unfold a_p; omega
theorem BSD_ap_p3923 : a_p 3923 = (-24 : ℤ) := by
  have h := BSD_E143_card_p3923; unfold a_p; omega
theorem BSD_ap_p3929 : a_p 3929 = (-74 : ℤ) := by
  have h := BSD_E143_card_p3929; unfold a_p; omega
theorem BSD_ap_p3931 : a_p 3931 = (-107 : ℤ) := by
  have h := BSD_E143_card_p3931; unfold a_p; omega
theorem BSD_ap_p3943 : a_p 3943 = (0 : ℤ) := by
  have h := BSD_E143_card_p3943; unfold a_p; omega
theorem BSD_ap_p3947 : a_p 3947 = (63 : ℤ) := by
  have h := BSD_E143_card_p3947; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=3889: a_p=+38, 4p-a_p²=14112
theorem BSD_DegreeNonneg_p3889 : BSD_FrobeniusDegreeNonneg_OPEN 3889 := fun r => by
  have hap : (a_p 3889 : ℝ) = 38 := by exact_mod_cast BSD_ap_p3889
  have key : r ^ 2 - (a_p 3889 : ℝ) * r + ((3889 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 14112/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

-- p=3907: a_p=+58, 4p-a_p²=12264
theorem BSD_DegreeNonneg_p3907 : BSD_FrobeniusDegreeNonneg_OPEN 3907 := fun r => by
  have hap : (a_p 3907 : ℝ) = 58 := by exact_mod_cast BSD_ap_p3907
  have key : r ^ 2 - (a_p 3907 : ℝ) * r + ((3907 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 12264/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

-- p=3911: a_p=+64, 4p-a_p²=11548
theorem BSD_DegreeNonneg_p3911 : BSD_FrobeniusDegreeNonneg_OPEN 3911 := fun r => by
  have hap : (a_p 3911 : ℝ) = 64 := by exact_mod_cast BSD_ap_p3911
  have key : r ^ 2 - (a_p 3911 : ℝ) * r + ((3911 : ℕ) : ℝ) =
      (r - 64/2) ^ 2 + 11548/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (64 : ℝ)/2)]

-- p=3917: a_p=-21, 4p-a_p²=15227
theorem BSD_DegreeNonneg_p3917 : BSD_FrobeniusDegreeNonneg_OPEN 3917 := fun r => by
  have hap : (a_p 3917 : ℝ) = -21 := by exact_mod_cast BSD_ap_p3917
  have key : r ^ 2 - (a_p 3917 : ℝ) * r + ((3917 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 15227/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

-- p=3919: a_p=-112, 4p-a_p²=3132
theorem BSD_DegreeNonneg_p3919 : BSD_FrobeniusDegreeNonneg_OPEN 3919 := fun r => by
  have hap : (a_p 3919 : ℝ) = -112 := by exact_mod_cast BSD_ap_p3919
  have key : r ^ 2 - (a_p 3919 : ℝ) * r + ((3919 : ℕ) : ℝ) =
      (r + 112/2) ^ 2 + 3132/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (112 : ℝ)/2)]

-- p=3923: a_p=-24, 4p-a_p²=15116
theorem BSD_DegreeNonneg_p3923 : BSD_FrobeniusDegreeNonneg_OPEN 3923 := fun r => by
  have hap : (a_p 3923 : ℝ) = -24 := by exact_mod_cast BSD_ap_p3923
  have key : r ^ 2 - (a_p 3923 : ℝ) * r + ((3923 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 15116/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

-- p=3929: a_p=-74, 4p-a_p²=10240
theorem BSD_DegreeNonneg_p3929 : BSD_FrobeniusDegreeNonneg_OPEN 3929 := fun r => by
  have hap : (a_p 3929 : ℝ) = -74 := by exact_mod_cast BSD_ap_p3929
  have key : r ^ 2 - (a_p 3929 : ℝ) * r + ((3929 : ℕ) : ℝ) =
      (r + 74/2) ^ 2 + 10240/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (74 : ℝ)/2)]

-- p=3931: a_p=-107, 4p-a_p²=4275
theorem BSD_DegreeNonneg_p3931 : BSD_FrobeniusDegreeNonneg_OPEN 3931 := fun r => by
  have hap : (a_p 3931 : ℝ) = -107 := by exact_mod_cast BSD_ap_p3931
  have key : r ^ 2 - (a_p 3931 : ℝ) * r + ((3931 : ℕ) : ℝ) =
      (r + 107/2) ^ 2 + 4275/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (107 : ℝ)/2)]

-- p=3943: a_p=+0, 4p-a_p²=15772
theorem BSD_DegreeNonneg_p3943 : BSD_FrobeniusDegreeNonneg_OPEN 3943 := fun r => by
  have hap : (a_p 3943 : ℝ) = 0 := by exact_mod_cast BSD_ap_p3943
  have key : r ^ 2 - (a_p 3943 : ℝ) * r + ((3943 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 15772/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

-- p=3947: a_p=+63, 4p-a_p²=11819
theorem BSD_DegreeNonneg_p3947 : BSD_FrobeniusDegreeNonneg_OPEN 3947 := fun r => by
  have hap : (a_p 3947 : ℝ) = 63 := by exact_mod_cast BSD_ap_p3947
  have key : r ^ 2 - (a_p 3947 : ℝ) * r + ((3947 : ℕ) : ℝ) =
      (r - 63/2) ^ 2 + 11819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (63 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p3889 : BSD_Hasse_OPEN 3889 :=
  BSD_hasse_of_degree_nonneg 3889 BSD_DegreeNonneg_p3889
theorem BSD_Hasse_OPEN_p3907 : BSD_Hasse_OPEN 3907 :=
  BSD_hasse_of_degree_nonneg 3907 BSD_DegreeNonneg_p3907
theorem BSD_Hasse_OPEN_p3911 : BSD_Hasse_OPEN 3911 :=
  BSD_hasse_of_degree_nonneg 3911 BSD_DegreeNonneg_p3911
theorem BSD_Hasse_OPEN_p3917 : BSD_Hasse_OPEN 3917 :=
  BSD_hasse_of_degree_nonneg 3917 BSD_DegreeNonneg_p3917
theorem BSD_Hasse_OPEN_p3919 : BSD_Hasse_OPEN 3919 :=
  BSD_hasse_of_degree_nonneg 3919 BSD_DegreeNonneg_p3919
theorem BSD_Hasse_OPEN_p3923 : BSD_Hasse_OPEN 3923 :=
  BSD_hasse_of_degree_nonneg 3923 BSD_DegreeNonneg_p3923
theorem BSD_Hasse_OPEN_p3929 : BSD_Hasse_OPEN 3929 :=
  BSD_hasse_of_degree_nonneg 3929 BSD_DegreeNonneg_p3929
theorem BSD_Hasse_OPEN_p3931 : BSD_Hasse_OPEN 3931 :=
  BSD_hasse_of_degree_nonneg 3931 BSD_DegreeNonneg_p3931
theorem BSD_Hasse_OPEN_p3943 : BSD_Hasse_OPEN 3943 :=
  BSD_hasse_of_degree_nonneg 3943 BSD_DegreeNonneg_p3943
theorem BSD_Hasse_OPEN_p3947 : BSD_Hasse_OPEN 3947 :=
  BSD_hasse_of_degree_nonneg 3947 BSD_DegreeNonneg_p3947

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p3889 : (a_p 3889 : ℝ) ^ 2 ≤ 4 * (3889 : ℝ) :=
  BSD_disc_from_deg_820 BSD_DegreeNonneg_p3889
theorem BSD_HasseBound_Disc_p3907 : (a_p 3907 : ℝ) ^ 2 ≤ 4 * (3907 : ℝ) :=
  BSD_disc_from_deg_820 BSD_DegreeNonneg_p3907
theorem BSD_HasseBound_Disc_p3911 : (a_p 3911 : ℝ) ^ 2 ≤ 4 * (3911 : ℝ) :=
  BSD_disc_from_deg_820 BSD_DegreeNonneg_p3911
theorem BSD_HasseBound_Disc_p3917 : (a_p 3917 : ℝ) ^ 2 ≤ 4 * (3917 : ℝ) :=
  BSD_disc_from_deg_820 BSD_DegreeNonneg_p3917
theorem BSD_HasseBound_Disc_p3919 : (a_p 3919 : ℝ) ^ 2 ≤ 4 * (3919 : ℝ) :=
  BSD_disc_from_deg_820 BSD_DegreeNonneg_p3919
theorem BSD_HasseBound_Disc_p3923 : (a_p 3923 : ℝ) ^ 2 ≤ 4 * (3923 : ℝ) :=
  BSD_disc_from_deg_820 BSD_DegreeNonneg_p3923
theorem BSD_HasseBound_Disc_p3929 : (a_p 3929 : ℝ) ^ 2 ≤ 4 * (3929 : ℝ) :=
  BSD_disc_from_deg_820 BSD_DegreeNonneg_p3929
theorem BSD_HasseBound_Disc_p3931 : (a_p 3931 : ℝ) ^ 2 ≤ 4 * (3931 : ℝ) :=
  BSD_disc_from_deg_820 BSD_DegreeNonneg_p3931
theorem BSD_HasseBound_Disc_p3943 : (a_p 3943 : ℝ) ^ 2 ≤ 4 * (3943 : ℝ) :=
  BSD_disc_from_deg_820 BSD_DegreeNonneg_p3943
theorem BSD_HasseBound_Disc_p3947 : (a_p 3947 : ℝ) ^ 2 ≤ 4 * (3947 : ℝ) :=
  BSD_disc_from_deg_820 BSD_DegreeNonneg_p3947

end Towers.BSD
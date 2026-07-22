/-
================================================================
Towers / BSD / BSD_Genesis808_CLOSED  (genesis-808)

HasseBridge Tier C: Hasse bounds for primes
2897..2969 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2897: card=2872, a_p=+26, disc=-10912
  p=2903: card=2878, a_p=+26, disc=-10936
  p=2909: card=2935, a_p=-25, disc=-11011
  p=2917: card=3002, a_p=-84, disc=-4612
  p=2927: card=2880, a_p=+48, disc=-9404
  p=2939: card=2928, a_p=+12, disc=-11612
  p=2953: card=2948, a_p=+6, disc=-11776
  p=2957: card=3033, a_p=-75, disc=-6203
  p=2963: card=2925, a_p=+39, disc=-10331
  p=2969: card=2944, a_p=+26, disc=-11200

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_808 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i808_p2897 : Fact (2897 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2903 : Fact (2903 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2909 : Fact (2909 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2917 : Fact (2917 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2927 : Fact (2927 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2939 : Fact (2939 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2953 : Fact (2953 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2957 : Fact (2957 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2963 : Fact (2963 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2969 : Fact (2969 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2897 : (E143_Finset 2897).card = 2872 := by native_decide
theorem BSD_E143_card_p2903 : (E143_Finset 2903).card = 2878 := by native_decide
theorem BSD_E143_card_p2909 : (E143_Finset 2909).card = 2935 := by native_decide
theorem BSD_E143_card_p2917 : (E143_Finset 2917).card = 3002 := by native_decide
theorem BSD_E143_card_p2927 : (E143_Finset 2927).card = 2880 := by native_decide
theorem BSD_E143_card_p2939 : (E143_Finset 2939).card = 2928 := by native_decide
theorem BSD_E143_card_p2953 : (E143_Finset 2953).card = 2948 := by native_decide
theorem BSD_E143_card_p2957 : (E143_Finset 2957).card = 3033 := by native_decide
theorem BSD_E143_card_p2963 : (E143_Finset 2963).card = 2925 := by native_decide
theorem BSD_E143_card_p2969 : (E143_Finset 2969).card = 2944 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2897 : a_p 2897 = (26 : ℤ) := by
  have h := BSD_E143_card_p2897; unfold a_p; omega
theorem BSD_ap_p2903 : a_p 2903 = (26 : ℤ) := by
  have h := BSD_E143_card_p2903; unfold a_p; omega
theorem BSD_ap_p2909 : a_p 2909 = (-25 : ℤ) := by
  have h := BSD_E143_card_p2909; unfold a_p; omega
theorem BSD_ap_p2917 : a_p 2917 = (-84 : ℤ) := by
  have h := BSD_E143_card_p2917; unfold a_p; omega
theorem BSD_ap_p2927 : a_p 2927 = (48 : ℤ) := by
  have h := BSD_E143_card_p2927; unfold a_p; omega
theorem BSD_ap_p2939 : a_p 2939 = (12 : ℤ) := by
  have h := BSD_E143_card_p2939; unfold a_p; omega
theorem BSD_ap_p2953 : a_p 2953 = (6 : ℤ) := by
  have h := BSD_E143_card_p2953; unfold a_p; omega
theorem BSD_ap_p2957 : a_p 2957 = (-75 : ℤ) := by
  have h := BSD_E143_card_p2957; unfold a_p; omega
theorem BSD_ap_p2963 : a_p 2963 = (39 : ℤ) := by
  have h := BSD_E143_card_p2963; unfold a_p; omega
theorem BSD_ap_p2969 : a_p 2969 = (26 : ℤ) := by
  have h := BSD_E143_card_p2969; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2897: a_p=+26, 4p-a_p²=10912
theorem BSD_DegreeNonneg_p2897 : BSD_FrobeniusDegreeNonneg_OPEN 2897 := fun r => by
  have hap : (a_p 2897 : ℝ) = 26 := by exact_mod_cast BSD_ap_p2897
  have key : r ^ 2 - (a_p 2897 : ℝ) * r + ((2897 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 10912/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

-- p=2903: a_p=+26, 4p-a_p²=10936
theorem BSD_DegreeNonneg_p2903 : BSD_FrobeniusDegreeNonneg_OPEN 2903 := fun r => by
  have hap : (a_p 2903 : ℝ) = 26 := by exact_mod_cast BSD_ap_p2903
  have key : r ^ 2 - (a_p 2903 : ℝ) * r + ((2903 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 10936/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

-- p=2909: a_p=-25, 4p-a_p²=11011
theorem BSD_DegreeNonneg_p2909 : BSD_FrobeniusDegreeNonneg_OPEN 2909 := fun r => by
  have hap : (a_p 2909 : ℝ) = -25 := by exact_mod_cast BSD_ap_p2909
  have key : r ^ 2 - (a_p 2909 : ℝ) * r + ((2909 : ℕ) : ℝ) =
      (r + 25/2) ^ 2 + 11011/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (25 : ℝ)/2)]

-- p=2917: a_p=-84, 4p-a_p²=4612
theorem BSD_DegreeNonneg_p2917 : BSD_FrobeniusDegreeNonneg_OPEN 2917 := fun r => by
  have hap : (a_p 2917 : ℝ) = -84 := by exact_mod_cast BSD_ap_p2917
  have key : r ^ 2 - (a_p 2917 : ℝ) * r + ((2917 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 4612/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

-- p=2927: a_p=+48, 4p-a_p²=9404
theorem BSD_DegreeNonneg_p2927 : BSD_FrobeniusDegreeNonneg_OPEN 2927 := fun r => by
  have hap : (a_p 2927 : ℝ) = 48 := by exact_mod_cast BSD_ap_p2927
  have key : r ^ 2 - (a_p 2927 : ℝ) * r + ((2927 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 9404/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

-- p=2939: a_p=+12, 4p-a_p²=11612
theorem BSD_DegreeNonneg_p2939 : BSD_FrobeniusDegreeNonneg_OPEN 2939 := fun r => by
  have hap : (a_p 2939 : ℝ) = 12 := by exact_mod_cast BSD_ap_p2939
  have key : r ^ 2 - (a_p 2939 : ℝ) * r + ((2939 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 11612/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

-- p=2953: a_p=+6, 4p-a_p²=11776
theorem BSD_DegreeNonneg_p2953 : BSD_FrobeniusDegreeNonneg_OPEN 2953 := fun r => by
  have hap : (a_p 2953 : ℝ) = 6 := by exact_mod_cast BSD_ap_p2953
  have key : r ^ 2 - (a_p 2953 : ℝ) * r + ((2953 : ℕ) : ℝ) =
      (r - 6/2) ^ 2 + 11776/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (6 : ℝ)/2)]

-- p=2957: a_p=-75, 4p-a_p²=6203
theorem BSD_DegreeNonneg_p2957 : BSD_FrobeniusDegreeNonneg_OPEN 2957 := fun r => by
  have hap : (a_p 2957 : ℝ) = -75 := by exact_mod_cast BSD_ap_p2957
  have key : r ^ 2 - (a_p 2957 : ℝ) * r + ((2957 : ℕ) : ℝ) =
      (r + 75/2) ^ 2 + 6203/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (75 : ℝ)/2)]

-- p=2963: a_p=+39, 4p-a_p²=10331
theorem BSD_DegreeNonneg_p2963 : BSD_FrobeniusDegreeNonneg_OPEN 2963 := fun r => by
  have hap : (a_p 2963 : ℝ) = 39 := by exact_mod_cast BSD_ap_p2963
  have key : r ^ 2 - (a_p 2963 : ℝ) * r + ((2963 : ℕ) : ℝ) =
      (r - 39/2) ^ 2 + 10331/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (39 : ℝ)/2)]

-- p=2969: a_p=+26, 4p-a_p²=11200
theorem BSD_DegreeNonneg_p2969 : BSD_FrobeniusDegreeNonneg_OPEN 2969 := fun r => by
  have hap : (a_p 2969 : ℝ) = 26 := by exact_mod_cast BSD_ap_p2969
  have key : r ^ 2 - (a_p 2969 : ℝ) * r + ((2969 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 11200/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2897 : BSD_Hasse_OPEN 2897 :=
  BSD_hasse_of_degree_nonneg 2897 BSD_DegreeNonneg_p2897
theorem BSD_Hasse_OPEN_p2903 : BSD_Hasse_OPEN 2903 :=
  BSD_hasse_of_degree_nonneg 2903 BSD_DegreeNonneg_p2903
theorem BSD_Hasse_OPEN_p2909 : BSD_Hasse_OPEN 2909 :=
  BSD_hasse_of_degree_nonneg 2909 BSD_DegreeNonneg_p2909
theorem BSD_Hasse_OPEN_p2917 : BSD_Hasse_OPEN 2917 :=
  BSD_hasse_of_degree_nonneg 2917 BSD_DegreeNonneg_p2917
theorem BSD_Hasse_OPEN_p2927 : BSD_Hasse_OPEN 2927 :=
  BSD_hasse_of_degree_nonneg 2927 BSD_DegreeNonneg_p2927
theorem BSD_Hasse_OPEN_p2939 : BSD_Hasse_OPEN 2939 :=
  BSD_hasse_of_degree_nonneg 2939 BSD_DegreeNonneg_p2939
theorem BSD_Hasse_OPEN_p2953 : BSD_Hasse_OPEN 2953 :=
  BSD_hasse_of_degree_nonneg 2953 BSD_DegreeNonneg_p2953
theorem BSD_Hasse_OPEN_p2957 : BSD_Hasse_OPEN 2957 :=
  BSD_hasse_of_degree_nonneg 2957 BSD_DegreeNonneg_p2957
theorem BSD_Hasse_OPEN_p2963 : BSD_Hasse_OPEN 2963 :=
  BSD_hasse_of_degree_nonneg 2963 BSD_DegreeNonneg_p2963
theorem BSD_Hasse_OPEN_p2969 : BSD_Hasse_OPEN 2969 :=
  BSD_hasse_of_degree_nonneg 2969 BSD_DegreeNonneg_p2969

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2897 : (a_p 2897 : ℝ) ^ 2 ≤ 4 * (2897 : ℝ) :=
  BSD_disc_from_deg_808 BSD_DegreeNonneg_p2897
theorem BSD_HasseBound_Disc_p2903 : (a_p 2903 : ℝ) ^ 2 ≤ 4 * (2903 : ℝ) :=
  BSD_disc_from_deg_808 BSD_DegreeNonneg_p2903
theorem BSD_HasseBound_Disc_p2909 : (a_p 2909 : ℝ) ^ 2 ≤ 4 * (2909 : ℝ) :=
  BSD_disc_from_deg_808 BSD_DegreeNonneg_p2909
theorem BSD_HasseBound_Disc_p2917 : (a_p 2917 : ℝ) ^ 2 ≤ 4 * (2917 : ℝ) :=
  BSD_disc_from_deg_808 BSD_DegreeNonneg_p2917
theorem BSD_HasseBound_Disc_p2927 : (a_p 2927 : ℝ) ^ 2 ≤ 4 * (2927 : ℝ) :=
  BSD_disc_from_deg_808 BSD_DegreeNonneg_p2927
theorem BSD_HasseBound_Disc_p2939 : (a_p 2939 : ℝ) ^ 2 ≤ 4 * (2939 : ℝ) :=
  BSD_disc_from_deg_808 BSD_DegreeNonneg_p2939
theorem BSD_HasseBound_Disc_p2953 : (a_p 2953 : ℝ) ^ 2 ≤ 4 * (2953 : ℝ) :=
  BSD_disc_from_deg_808 BSD_DegreeNonneg_p2953
theorem BSD_HasseBound_Disc_p2957 : (a_p 2957 : ℝ) ^ 2 ≤ 4 * (2957 : ℝ) :=
  BSD_disc_from_deg_808 BSD_DegreeNonneg_p2957
theorem BSD_HasseBound_Disc_p2963 : (a_p 2963 : ℝ) ^ 2 ≤ 4 * (2963 : ℝ) :=
  BSD_disc_from_deg_808 BSD_DegreeNonneg_p2963
theorem BSD_HasseBound_Disc_p2969 : (a_p 2969 : ℝ) ^ 2 ≤ 4 * (2969 : ℝ) :=
  BSD_disc_from_deg_808 BSD_DegreeNonneg_p2969

end Towers.BSD
/-
================================================================
Towers / BSD / BSD_Genesis809_CLOSED  (genesis-809)

HasseBridge Tier C: Hasse bounds for primes
2971..3061 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2971: card=2959, a_p=+13, disc=-11715
  p=2999: card=3036, a_p=-36, disc=-10700
  p=3001: card=3001, a_p=+1, disc=-12003
  p=3011: card=2968, a_p=+44, disc=-10108
  p=3019: card=3099, a_p=-79, disc=-5835
  p=3023: card=2991, a_p=+33, disc=-11003
  p=3037: card=3035, a_p=+3, disc=-12139
  p=3041: card=3096, a_p=-54, disc=-9248
  p=3049: card=3078, a_p=-28, disc=-11412
  p=3061: card=3099, a_p=-37, disc=-10875

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_809 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i809_p2971 : Fact (2971 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p2999 : Fact (2999 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3001 : Fact (3001 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3011 : Fact (3011 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3019 : Fact (3019 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3023 : Fact (3023 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3037 : Fact (3037 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3041 : Fact (3041 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3049 : Fact (3049 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3061 : Fact (3061 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2971 : (E143_Finset 2971).card = 2959 := by native_decide
theorem BSD_E143_card_p2999 : (E143_Finset 2999).card = 3036 := by native_decide
theorem BSD_E143_card_p3001 : (E143_Finset 3001).card = 3001 := by native_decide
theorem BSD_E143_card_p3011 : (E143_Finset 3011).card = 2968 := by native_decide
theorem BSD_E143_card_p3019 : (E143_Finset 3019).card = 3099 := by native_decide
theorem BSD_E143_card_p3023 : (E143_Finset 3023).card = 2991 := by native_decide
theorem BSD_E143_card_p3037 : (E143_Finset 3037).card = 3035 := by native_decide
theorem BSD_E143_card_p3041 : (E143_Finset 3041).card = 3096 := by native_decide
theorem BSD_E143_card_p3049 : (E143_Finset 3049).card = 3078 := by native_decide
theorem BSD_E143_card_p3061 : (E143_Finset 3061).card = 3099 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2971 : a_p 2971 = (13 : ℤ) := by
  have h := BSD_E143_card_p2971; unfold a_p; omega
theorem BSD_ap_p2999 : a_p 2999 = (-36 : ℤ) := by
  have h := BSD_E143_card_p2999; unfold a_p; omega
theorem BSD_ap_p3001 : a_p 3001 = (1 : ℤ) := by
  have h := BSD_E143_card_p3001; unfold a_p; omega
theorem BSD_ap_p3011 : a_p 3011 = (44 : ℤ) := by
  have h := BSD_E143_card_p3011; unfold a_p; omega
theorem BSD_ap_p3019 : a_p 3019 = (-79 : ℤ) := by
  have h := BSD_E143_card_p3019; unfold a_p; omega
theorem BSD_ap_p3023 : a_p 3023 = (33 : ℤ) := by
  have h := BSD_E143_card_p3023; unfold a_p; omega
theorem BSD_ap_p3037 : a_p 3037 = (3 : ℤ) := by
  have h := BSD_E143_card_p3037; unfold a_p; omega
theorem BSD_ap_p3041 : a_p 3041 = (-54 : ℤ) := by
  have h := BSD_E143_card_p3041; unfold a_p; omega
theorem BSD_ap_p3049 : a_p 3049 = (-28 : ℤ) := by
  have h := BSD_E143_card_p3049; unfold a_p; omega
theorem BSD_ap_p3061 : a_p 3061 = (-37 : ℤ) := by
  have h := BSD_E143_card_p3061; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2971: a_p=+13, 4p-a_p²=11715
theorem BSD_DegreeNonneg_p2971 : BSD_FrobeniusDegreeNonneg_OPEN 2971 := fun r => by
  have hap : (a_p 2971 : ℝ) = 13 := by exact_mod_cast BSD_ap_p2971
  have key : r ^ 2 - (a_p 2971 : ℝ) * r + ((2971 : ℕ) : ℝ) =
      (r - 13/2) ^ 2 + 11715/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (13 : ℝ)/2)]

-- p=2999: a_p=-36, 4p-a_p²=10700
theorem BSD_DegreeNonneg_p2999 : BSD_FrobeniusDegreeNonneg_OPEN 2999 := fun r => by
  have hap : (a_p 2999 : ℝ) = -36 := by exact_mod_cast BSD_ap_p2999
  have key : r ^ 2 - (a_p 2999 : ℝ) * r + ((2999 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 10700/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

-- p=3001: a_p=+1, 4p-a_p²=12003
theorem BSD_DegreeNonneg_p3001 : BSD_FrobeniusDegreeNonneg_OPEN 3001 := fun r => by
  have hap : (a_p 3001 : ℝ) = 1 := by exact_mod_cast BSD_ap_p3001
  have key : r ^ 2 - (a_p 3001 : ℝ) * r + ((3001 : ℕ) : ℝ) =
      (r - 1/2) ^ 2 + 12003/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (1 : ℝ)/2)]

-- p=3011: a_p=+44, 4p-a_p²=10108
theorem BSD_DegreeNonneg_p3011 : BSD_FrobeniusDegreeNonneg_OPEN 3011 := fun r => by
  have hap : (a_p 3011 : ℝ) = 44 := by exact_mod_cast BSD_ap_p3011
  have key : r ^ 2 - (a_p 3011 : ℝ) * r + ((3011 : ℕ) : ℝ) =
      (r - 44/2) ^ 2 + 10108/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (44 : ℝ)/2)]

-- p=3019: a_p=-79, 4p-a_p²=5835
theorem BSD_DegreeNonneg_p3019 : BSD_FrobeniusDegreeNonneg_OPEN 3019 := fun r => by
  have hap : (a_p 3019 : ℝ) = -79 := by exact_mod_cast BSD_ap_p3019
  have key : r ^ 2 - (a_p 3019 : ℝ) * r + ((3019 : ℕ) : ℝ) =
      (r + 79/2) ^ 2 + 5835/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (79 : ℝ)/2)]

-- p=3023: a_p=+33, 4p-a_p²=11003
theorem BSD_DegreeNonneg_p3023 : BSD_FrobeniusDegreeNonneg_OPEN 3023 := fun r => by
  have hap : (a_p 3023 : ℝ) = 33 := by exact_mod_cast BSD_ap_p3023
  have key : r ^ 2 - (a_p 3023 : ℝ) * r + ((3023 : ℕ) : ℝ) =
      (r - 33/2) ^ 2 + 11003/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (33 : ℝ)/2)]

-- p=3037: a_p=+3, 4p-a_p²=12139
theorem BSD_DegreeNonneg_p3037 : BSD_FrobeniusDegreeNonneg_OPEN 3037 := fun r => by
  have hap : (a_p 3037 : ℝ) = 3 := by exact_mod_cast BSD_ap_p3037
  have key : r ^ 2 - (a_p 3037 : ℝ) * r + ((3037 : ℕ) : ℝ) =
      (r - 3/2) ^ 2 + 12139/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (3 : ℝ)/2)]

-- p=3041: a_p=-54, 4p-a_p²=9248
theorem BSD_DegreeNonneg_p3041 : BSD_FrobeniusDegreeNonneg_OPEN 3041 := fun r => by
  have hap : (a_p 3041 : ℝ) = -54 := by exact_mod_cast BSD_ap_p3041
  have key : r ^ 2 - (a_p 3041 : ℝ) * r + ((3041 : ℕ) : ℝ) =
      (r + 54/2) ^ 2 + 9248/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (54 : ℝ)/2)]

-- p=3049: a_p=-28, 4p-a_p²=11412
theorem BSD_DegreeNonneg_p3049 : BSD_FrobeniusDegreeNonneg_OPEN 3049 := fun r => by
  have hap : (a_p 3049 : ℝ) = -28 := by exact_mod_cast BSD_ap_p3049
  have key : r ^ 2 - (a_p 3049 : ℝ) * r + ((3049 : ℕ) : ℝ) =
      (r + 28/2) ^ 2 + 11412/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (28 : ℝ)/2)]

-- p=3061: a_p=-37, 4p-a_p²=10875
theorem BSD_DegreeNonneg_p3061 : BSD_FrobeniusDegreeNonneg_OPEN 3061 := fun r => by
  have hap : (a_p 3061 : ℝ) = -37 := by exact_mod_cast BSD_ap_p3061
  have key : r ^ 2 - (a_p 3061 : ℝ) * r + ((3061 : ℕ) : ℝ) =
      (r + 37/2) ^ 2 + 10875/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (37 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2971 : BSD_Hasse_OPEN 2971 :=
  BSD_hasse_of_degree_nonneg 2971 BSD_DegreeNonneg_p2971
theorem BSD_Hasse_OPEN_p2999 : BSD_Hasse_OPEN 2999 :=
  BSD_hasse_of_degree_nonneg 2999 BSD_DegreeNonneg_p2999
theorem BSD_Hasse_OPEN_p3001 : BSD_Hasse_OPEN 3001 :=
  BSD_hasse_of_degree_nonneg 3001 BSD_DegreeNonneg_p3001
theorem BSD_Hasse_OPEN_p3011 : BSD_Hasse_OPEN 3011 :=
  BSD_hasse_of_degree_nonneg 3011 BSD_DegreeNonneg_p3011
theorem BSD_Hasse_OPEN_p3019 : BSD_Hasse_OPEN 3019 :=
  BSD_hasse_of_degree_nonneg 3019 BSD_DegreeNonneg_p3019
theorem BSD_Hasse_OPEN_p3023 : BSD_Hasse_OPEN 3023 :=
  BSD_hasse_of_degree_nonneg 3023 BSD_DegreeNonneg_p3023
theorem BSD_Hasse_OPEN_p3037 : BSD_Hasse_OPEN 3037 :=
  BSD_hasse_of_degree_nonneg 3037 BSD_DegreeNonneg_p3037
theorem BSD_Hasse_OPEN_p3041 : BSD_Hasse_OPEN 3041 :=
  BSD_hasse_of_degree_nonneg 3041 BSD_DegreeNonneg_p3041
theorem BSD_Hasse_OPEN_p3049 : BSD_Hasse_OPEN 3049 :=
  BSD_hasse_of_degree_nonneg 3049 BSD_DegreeNonneg_p3049
theorem BSD_Hasse_OPEN_p3061 : BSD_Hasse_OPEN 3061 :=
  BSD_hasse_of_degree_nonneg 3061 BSD_DegreeNonneg_p3061

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2971 : (a_p 2971 : ℝ) ^ 2 ≤ 4 * (2971 : ℝ) :=
  BSD_disc_from_deg_809 BSD_DegreeNonneg_p2971
theorem BSD_HasseBound_Disc_p2999 : (a_p 2999 : ℝ) ^ 2 ≤ 4 * (2999 : ℝ) :=
  BSD_disc_from_deg_809 BSD_DegreeNonneg_p2999
theorem BSD_HasseBound_Disc_p3001 : (a_p 3001 : ℝ) ^ 2 ≤ 4 * (3001 : ℝ) :=
  BSD_disc_from_deg_809 BSD_DegreeNonneg_p3001
theorem BSD_HasseBound_Disc_p3011 : (a_p 3011 : ℝ) ^ 2 ≤ 4 * (3011 : ℝ) :=
  BSD_disc_from_deg_809 BSD_DegreeNonneg_p3011
theorem BSD_HasseBound_Disc_p3019 : (a_p 3019 : ℝ) ^ 2 ≤ 4 * (3019 : ℝ) :=
  BSD_disc_from_deg_809 BSD_DegreeNonneg_p3019
theorem BSD_HasseBound_Disc_p3023 : (a_p 3023 : ℝ) ^ 2 ≤ 4 * (3023 : ℝ) :=
  BSD_disc_from_deg_809 BSD_DegreeNonneg_p3023
theorem BSD_HasseBound_Disc_p3037 : (a_p 3037 : ℝ) ^ 2 ≤ 4 * (3037 : ℝ) :=
  BSD_disc_from_deg_809 BSD_DegreeNonneg_p3037
theorem BSD_HasseBound_Disc_p3041 : (a_p 3041 : ℝ) ^ 2 ≤ 4 * (3041 : ℝ) :=
  BSD_disc_from_deg_809 BSD_DegreeNonneg_p3041
theorem BSD_HasseBound_Disc_p3049 : (a_p 3049 : ℝ) ^ 2 ≤ 4 * (3049 : ℝ) :=
  BSD_disc_from_deg_809 BSD_DegreeNonneg_p3049
theorem BSD_HasseBound_Disc_p3061 : (a_p 3061 : ℝ) ^ 2 ≤ 4 * (3061 : ℝ) :=
  BSD_disc_from_deg_809 BSD_DegreeNonneg_p3061

end Towers.BSD
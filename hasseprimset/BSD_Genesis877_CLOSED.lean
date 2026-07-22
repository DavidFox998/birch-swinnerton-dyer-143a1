/-
================================================================
Towers / BSD / BSD_Genesis877_CLOSED  (genesis-877)

HasseBridge Tier C: Hasse bounds for primes
8923..9001 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=8923: card=8874, a_p=+50, disc=-33192
  p=8929: card=8824, a_p=+106, disc=-24480
  p=8933: card=9003, a_p=-69, disc=-30971
  p=8941: card=8855, a_p=+87, disc=-28195
  p=8951: card=8854, a_p=+98, disc=-26200
  p=8963: card=9141, a_p=-177, disc=-4523
  p=8969: card=8891, a_p=+79, disc=-29635
  p=8971: card=8930, a_p=+42, disc=-34120
  p=8999: card=9023, a_p=-23, disc=-35467
  p=9001: card=8951, a_p=+51, disc=-33403

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_877 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i877_p8923 : Fact (8923 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8929 : Fact (8929 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8933 : Fact (8933 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8941 : Fact (8941 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8951 : Fact (8951 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8963 : Fact (8963 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8969 : Fact (8969 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8971 : Fact (8971 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8999 : Fact (8999 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p9001 : Fact (9001 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p8923 : (E143_Finset 8923).card = 8874 := by native_decide
theorem BSD_E143_card_p8929 : (E143_Finset 8929).card = 8824 := by native_decide
theorem BSD_E143_card_p8933 : (E143_Finset 8933).card = 9003 := by native_decide
theorem BSD_E143_card_p8941 : (E143_Finset 8941).card = 8855 := by native_decide
theorem BSD_E143_card_p8951 : (E143_Finset 8951).card = 8854 := by native_decide
theorem BSD_E143_card_p8963 : (E143_Finset 8963).card = 9141 := by native_decide
theorem BSD_E143_card_p8969 : (E143_Finset 8969).card = 8891 := by native_decide
theorem BSD_E143_card_p8971 : (E143_Finset 8971).card = 8930 := by native_decide
theorem BSD_E143_card_p8999 : (E143_Finset 8999).card = 9023 := by native_decide
theorem BSD_E143_card_p9001 : (E143_Finset 9001).card = 8951 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p8923 : a_p 8923 = (50 : ℤ) := by
  have h := BSD_E143_card_p8923; unfold a_p; omega
theorem BSD_ap_p8929 : a_p 8929 = (106 : ℤ) := by
  have h := BSD_E143_card_p8929; unfold a_p; omega
theorem BSD_ap_p8933 : a_p 8933 = (-69 : ℤ) := by
  have h := BSD_E143_card_p8933; unfold a_p; omega
theorem BSD_ap_p8941 : a_p 8941 = (87 : ℤ) := by
  have h := BSD_E143_card_p8941; unfold a_p; omega
theorem BSD_ap_p8951 : a_p 8951 = (98 : ℤ) := by
  have h := BSD_E143_card_p8951; unfold a_p; omega
theorem BSD_ap_p8963 : a_p 8963 = (-177 : ℤ) := by
  have h := BSD_E143_card_p8963; unfold a_p; omega
theorem BSD_ap_p8969 : a_p 8969 = (79 : ℤ) := by
  have h := BSD_E143_card_p8969; unfold a_p; omega
theorem BSD_ap_p8971 : a_p 8971 = (42 : ℤ) := by
  have h := BSD_E143_card_p8971; unfold a_p; omega
theorem BSD_ap_p8999 : a_p 8999 = (-23 : ℤ) := by
  have h := BSD_E143_card_p8999; unfold a_p; omega
theorem BSD_ap_p9001 : a_p 9001 = (51 : ℤ) := by
  have h := BSD_E143_card_p9001; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=8923: a_p=+50, 4p-a_p²=33192
theorem BSD_DegreeNonneg_p8923 : BSD_FrobeniusDegreeNonneg_OPEN 8923 := fun r => by
  have hap : (a_p 8923 : ℝ) = 50 := by exact_mod_cast BSD_ap_p8923
  have key : r ^ 2 - (a_p 8923 : ℝ) * r + ((8923 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 33192/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

-- p=8929: a_p=+106, 4p-a_p²=24480
theorem BSD_DegreeNonneg_p8929 : BSD_FrobeniusDegreeNonneg_OPEN 8929 := fun r => by
  have hap : (a_p 8929 : ℝ) = 106 := by exact_mod_cast BSD_ap_p8929
  have key : r ^ 2 - (a_p 8929 : ℝ) * r + ((8929 : ℕ) : ℝ) =
      (r - 106/2) ^ 2 + 24480/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (106 : ℝ)/2)]

-- p=8933: a_p=-69, 4p-a_p²=30971
theorem BSD_DegreeNonneg_p8933 : BSD_FrobeniusDegreeNonneg_OPEN 8933 := fun r => by
  have hap : (a_p 8933 : ℝ) = -69 := by exact_mod_cast BSD_ap_p8933
  have key : r ^ 2 - (a_p 8933 : ℝ) * r + ((8933 : ℕ) : ℝ) =
      (r + 69/2) ^ 2 + 30971/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (69 : ℝ)/2)]

-- p=8941: a_p=+87, 4p-a_p²=28195
theorem BSD_DegreeNonneg_p8941 : BSD_FrobeniusDegreeNonneg_OPEN 8941 := fun r => by
  have hap : (a_p 8941 : ℝ) = 87 := by exact_mod_cast BSD_ap_p8941
  have key : r ^ 2 - (a_p 8941 : ℝ) * r + ((8941 : ℕ) : ℝ) =
      (r - 87/2) ^ 2 + 28195/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (87 : ℝ)/2)]

-- p=8951: a_p=+98, 4p-a_p²=26200
theorem BSD_DegreeNonneg_p8951 : BSD_FrobeniusDegreeNonneg_OPEN 8951 := fun r => by
  have hap : (a_p 8951 : ℝ) = 98 := by exact_mod_cast BSD_ap_p8951
  have key : r ^ 2 - (a_p 8951 : ℝ) * r + ((8951 : ℕ) : ℝ) =
      (r - 98/2) ^ 2 + 26200/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (98 : ℝ)/2)]

-- p=8963: a_p=-177, 4p-a_p²=4523
theorem BSD_DegreeNonneg_p8963 : BSD_FrobeniusDegreeNonneg_OPEN 8963 := fun r => by
  have hap : (a_p 8963 : ℝ) = -177 := by exact_mod_cast BSD_ap_p8963
  have key : r ^ 2 - (a_p 8963 : ℝ) * r + ((8963 : ℕ) : ℝ) =
      (r + 177/2) ^ 2 + 4523/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (177 : ℝ)/2)]

-- p=8969: a_p=+79, 4p-a_p²=29635
theorem BSD_DegreeNonneg_p8969 : BSD_FrobeniusDegreeNonneg_OPEN 8969 := fun r => by
  have hap : (a_p 8969 : ℝ) = 79 := by exact_mod_cast BSD_ap_p8969
  have key : r ^ 2 - (a_p 8969 : ℝ) * r + ((8969 : ℕ) : ℝ) =
      (r - 79/2) ^ 2 + 29635/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (79 : ℝ)/2)]

-- p=8971: a_p=+42, 4p-a_p²=34120
theorem BSD_DegreeNonneg_p8971 : BSD_FrobeniusDegreeNonneg_OPEN 8971 := fun r => by
  have hap : (a_p 8971 : ℝ) = 42 := by exact_mod_cast BSD_ap_p8971
  have key : r ^ 2 - (a_p 8971 : ℝ) * r + ((8971 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 34120/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

-- p=8999: a_p=-23, 4p-a_p²=35467
theorem BSD_DegreeNonneg_p8999 : BSD_FrobeniusDegreeNonneg_OPEN 8999 := fun r => by
  have hap : (a_p 8999 : ℝ) = -23 := by exact_mod_cast BSD_ap_p8999
  have key : r ^ 2 - (a_p 8999 : ℝ) * r + ((8999 : ℕ) : ℝ) =
      (r + 23/2) ^ 2 + 35467/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (23 : ℝ)/2)]

-- p=9001: a_p=+51, 4p-a_p²=33403
theorem BSD_DegreeNonneg_p9001 : BSD_FrobeniusDegreeNonneg_OPEN 9001 := fun r => by
  have hap : (a_p 9001 : ℝ) = 51 := by exact_mod_cast BSD_ap_p9001
  have key : r ^ 2 - (a_p 9001 : ℝ) * r + ((9001 : ℕ) : ℝ) =
      (r - 51/2) ^ 2 + 33403/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (51 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p8923 : BSD_Hasse_OPEN 8923 :=
  BSD_hasse_of_degree_nonneg 8923 BSD_DegreeNonneg_p8923
theorem BSD_Hasse_OPEN_p8929 : BSD_Hasse_OPEN 8929 :=
  BSD_hasse_of_degree_nonneg 8929 BSD_DegreeNonneg_p8929
theorem BSD_Hasse_OPEN_p8933 : BSD_Hasse_OPEN 8933 :=
  BSD_hasse_of_degree_nonneg 8933 BSD_DegreeNonneg_p8933
theorem BSD_Hasse_OPEN_p8941 : BSD_Hasse_OPEN 8941 :=
  BSD_hasse_of_degree_nonneg 8941 BSD_DegreeNonneg_p8941
theorem BSD_Hasse_OPEN_p8951 : BSD_Hasse_OPEN 8951 :=
  BSD_hasse_of_degree_nonneg 8951 BSD_DegreeNonneg_p8951
theorem BSD_Hasse_OPEN_p8963 : BSD_Hasse_OPEN 8963 :=
  BSD_hasse_of_degree_nonneg 8963 BSD_DegreeNonneg_p8963
theorem BSD_Hasse_OPEN_p8969 : BSD_Hasse_OPEN 8969 :=
  BSD_hasse_of_degree_nonneg 8969 BSD_DegreeNonneg_p8969
theorem BSD_Hasse_OPEN_p8971 : BSD_Hasse_OPEN 8971 :=
  BSD_hasse_of_degree_nonneg 8971 BSD_DegreeNonneg_p8971
theorem BSD_Hasse_OPEN_p8999 : BSD_Hasse_OPEN 8999 :=
  BSD_hasse_of_degree_nonneg 8999 BSD_DegreeNonneg_p8999
theorem BSD_Hasse_OPEN_p9001 : BSD_Hasse_OPEN 9001 :=
  BSD_hasse_of_degree_nonneg 9001 BSD_DegreeNonneg_p9001

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p8923 : (a_p 8923 : ℝ) ^ 2 ≤ 4 * (8923 : ℝ) :=
  BSD_disc_from_deg_877 BSD_DegreeNonneg_p8923
theorem BSD_HasseBound_Disc_p8929 : (a_p 8929 : ℝ) ^ 2 ≤ 4 * (8929 : ℝ) :=
  BSD_disc_from_deg_877 BSD_DegreeNonneg_p8929
theorem BSD_HasseBound_Disc_p8933 : (a_p 8933 : ℝ) ^ 2 ≤ 4 * (8933 : ℝ) :=
  BSD_disc_from_deg_877 BSD_DegreeNonneg_p8933
theorem BSD_HasseBound_Disc_p8941 : (a_p 8941 : ℝ) ^ 2 ≤ 4 * (8941 : ℝ) :=
  BSD_disc_from_deg_877 BSD_DegreeNonneg_p8941
theorem BSD_HasseBound_Disc_p8951 : (a_p 8951 : ℝ) ^ 2 ≤ 4 * (8951 : ℝ) :=
  BSD_disc_from_deg_877 BSD_DegreeNonneg_p8951
theorem BSD_HasseBound_Disc_p8963 : (a_p 8963 : ℝ) ^ 2 ≤ 4 * (8963 : ℝ) :=
  BSD_disc_from_deg_877 BSD_DegreeNonneg_p8963
theorem BSD_HasseBound_Disc_p8969 : (a_p 8969 : ℝ) ^ 2 ≤ 4 * (8969 : ℝ) :=
  BSD_disc_from_deg_877 BSD_DegreeNonneg_p8969
theorem BSD_HasseBound_Disc_p8971 : (a_p 8971 : ℝ) ^ 2 ≤ 4 * (8971 : ℝ) :=
  BSD_disc_from_deg_877 BSD_DegreeNonneg_p8971
theorem BSD_HasseBound_Disc_p8999 : (a_p 8999 : ℝ) ^ 2 ≤ 4 * (8999 : ℝ) :=
  BSD_disc_from_deg_877 BSD_DegreeNonneg_p8999
theorem BSD_HasseBound_Disc_p9001 : (a_p 9001 : ℝ) ^ 2 ≤ 4 * (9001 : ℝ) :=
  BSD_disc_from_deg_877 BSD_DegreeNonneg_p9001

end Towers.BSD
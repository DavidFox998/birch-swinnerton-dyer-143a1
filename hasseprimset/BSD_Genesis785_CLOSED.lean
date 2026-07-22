/-
================================================================
Towers / BSD / BSD_Genesis785_CLOSED  (genesis-785)

HasseBridge Tier C: Hasse bounds for primes
1129..1213 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1129: card=1136, a_p=-6, disc=-4480
  p=1151: card=1182, a_p=-30, disc=-3704
  p=1153: card=1149, a_p=+5, disc=-4587
  p=1163: card=1128, a_p=+36, disc=-3356
  p=1171: card=1111, a_p=+61, disc=-963
  p=1181: card=1140, a_p=+42, disc=-2960
  p=1187: card=1212, a_p=-24, disc=-4172
  p=1193: card=1203, a_p=-9, disc=-4691
  p=1201: card=1180, a_p=+22, disc=-4320
  p=1213: card=1267, a_p=-53, disc=-2043

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_785 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i785_p1129 : Fact (1129 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1151 : Fact (1151 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1153 : Fact (1153 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1163 : Fact (1163 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1171 : Fact (1171 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1181 : Fact (1181 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1187 : Fact (1187 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1193 : Fact (1193 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1201 : Fact (1201 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1213 : Fact (1213 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1129 : (E143_Finset 1129).card = 1136 := by native_decide
theorem BSD_E143_card_p1151 : (E143_Finset 1151).card = 1182 := by native_decide
theorem BSD_E143_card_p1153 : (E143_Finset 1153).card = 1149 := by native_decide
theorem BSD_E143_card_p1163 : (E143_Finset 1163).card = 1128 := by native_decide
theorem BSD_E143_card_p1171 : (E143_Finset 1171).card = 1111 := by native_decide
theorem BSD_E143_card_p1181 : (E143_Finset 1181).card = 1140 := by native_decide
theorem BSD_E143_card_p1187 : (E143_Finset 1187).card = 1212 := by native_decide
theorem BSD_E143_card_p1193 : (E143_Finset 1193).card = 1203 := by native_decide
theorem BSD_E143_card_p1201 : (E143_Finset 1201).card = 1180 := by native_decide
theorem BSD_E143_card_p1213 : (E143_Finset 1213).card = 1267 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1129 : a_p 1129 = (-6 : ℤ) := by
  have h := BSD_E143_card_p1129; unfold a_p; omega
theorem BSD_ap_p1151 : a_p 1151 = (-30 : ℤ) := by
  have h := BSD_E143_card_p1151; unfold a_p; omega
theorem BSD_ap_p1153 : a_p 1153 = (5 : ℤ) := by
  have h := BSD_E143_card_p1153; unfold a_p; omega
theorem BSD_ap_p1163 : a_p 1163 = (36 : ℤ) := by
  have h := BSD_E143_card_p1163; unfold a_p; omega
theorem BSD_ap_p1171 : a_p 1171 = (61 : ℤ) := by
  have h := BSD_E143_card_p1171; unfold a_p; omega
theorem BSD_ap_p1181 : a_p 1181 = (42 : ℤ) := by
  have h := BSD_E143_card_p1181; unfold a_p; omega
theorem BSD_ap_p1187 : a_p 1187 = (-24 : ℤ) := by
  have h := BSD_E143_card_p1187; unfold a_p; omega
theorem BSD_ap_p1193 : a_p 1193 = (-9 : ℤ) := by
  have h := BSD_E143_card_p1193; unfold a_p; omega
theorem BSD_ap_p1201 : a_p 1201 = (22 : ℤ) := by
  have h := BSD_E143_card_p1201; unfold a_p; omega
theorem BSD_ap_p1213 : a_p 1213 = (-53 : ℤ) := by
  have h := BSD_E143_card_p1213; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1129: a_p=-6, 4p-a_p²=4480
theorem BSD_DegreeNonneg_p1129 : BSD_FrobeniusDegreeNonneg_OPEN 1129 := fun r => by
  have hap : (a_p 1129 : ℝ) = -6 := by exact_mod_cast BSD_ap_p1129
  have key : r ^ 2 - (a_p 1129 : ℝ) * r + ((1129 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 4480/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

-- p=1151: a_p=-30, 4p-a_p²=3704
theorem BSD_DegreeNonneg_p1151 : BSD_FrobeniusDegreeNonneg_OPEN 1151 := fun r => by
  have hap : (a_p 1151 : ℝ) = -30 := by exact_mod_cast BSD_ap_p1151
  have key : r ^ 2 - (a_p 1151 : ℝ) * r + ((1151 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 3704/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

-- p=1153: a_p=+5, 4p-a_p²=4587
theorem BSD_DegreeNonneg_p1153 : BSD_FrobeniusDegreeNonneg_OPEN 1153 := fun r => by
  have hap : (a_p 1153 : ℝ) = 5 := by exact_mod_cast BSD_ap_p1153
  have key : r ^ 2 - (a_p 1153 : ℝ) * r + ((1153 : ℕ) : ℝ) =
      (r - 5/2) ^ 2 + 4587/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (5 : ℝ)/2)]

-- p=1163: a_p=+36, 4p-a_p²=3356
theorem BSD_DegreeNonneg_p1163 : BSD_FrobeniusDegreeNonneg_OPEN 1163 := fun r => by
  have hap : (a_p 1163 : ℝ) = 36 := by exact_mod_cast BSD_ap_p1163
  have key : r ^ 2 - (a_p 1163 : ℝ) * r + ((1163 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 3356/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

-- p=1171: a_p=+61, 4p-a_p²=963
theorem BSD_DegreeNonneg_p1171 : BSD_FrobeniusDegreeNonneg_OPEN 1171 := fun r => by
  have hap : (a_p 1171 : ℝ) = 61 := by exact_mod_cast BSD_ap_p1171
  have key : r ^ 2 - (a_p 1171 : ℝ) * r + ((1171 : ℕ) : ℝ) =
      (r - 61/2) ^ 2 + 963/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (61 : ℝ)/2)]

-- p=1181: a_p=+42, 4p-a_p²=2960
theorem BSD_DegreeNonneg_p1181 : BSD_FrobeniusDegreeNonneg_OPEN 1181 := fun r => by
  have hap : (a_p 1181 : ℝ) = 42 := by exact_mod_cast BSD_ap_p1181
  have key : r ^ 2 - (a_p 1181 : ℝ) * r + ((1181 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 2960/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

-- p=1187: a_p=-24, 4p-a_p²=4172
theorem BSD_DegreeNonneg_p1187 : BSD_FrobeniusDegreeNonneg_OPEN 1187 := fun r => by
  have hap : (a_p 1187 : ℝ) = -24 := by exact_mod_cast BSD_ap_p1187
  have key : r ^ 2 - (a_p 1187 : ℝ) * r + ((1187 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 4172/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

-- p=1193: a_p=-9, 4p-a_p²=4691
theorem BSD_DegreeNonneg_p1193 : BSD_FrobeniusDegreeNonneg_OPEN 1193 := fun r => by
  have hap : (a_p 1193 : ℝ) = -9 := by exact_mod_cast BSD_ap_p1193
  have key : r ^ 2 - (a_p 1193 : ℝ) * r + ((1193 : ℕ) : ℝ) =
      (r + 9/2) ^ 2 + 4691/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (9 : ℝ)/2)]

-- p=1201: a_p=+22, 4p-a_p²=4320
theorem BSD_DegreeNonneg_p1201 : BSD_FrobeniusDegreeNonneg_OPEN 1201 := fun r => by
  have hap : (a_p 1201 : ℝ) = 22 := by exact_mod_cast BSD_ap_p1201
  have key : r ^ 2 - (a_p 1201 : ℝ) * r + ((1201 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 4320/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

-- p=1213: a_p=-53, 4p-a_p²=2043
theorem BSD_DegreeNonneg_p1213 : BSD_FrobeniusDegreeNonneg_OPEN 1213 := fun r => by
  have hap : (a_p 1213 : ℝ) = -53 := by exact_mod_cast BSD_ap_p1213
  have key : r ^ 2 - (a_p 1213 : ℝ) * r + ((1213 : ℕ) : ℝ) =
      (r + 53/2) ^ 2 + 2043/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (53 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1129 : BSD_Hasse_OPEN 1129 :=
  BSD_hasse_of_degree_nonneg 1129 BSD_DegreeNonneg_p1129
theorem BSD_Hasse_OPEN_p1151 : BSD_Hasse_OPEN 1151 :=
  BSD_hasse_of_degree_nonneg 1151 BSD_DegreeNonneg_p1151
theorem BSD_Hasse_OPEN_p1153 : BSD_Hasse_OPEN 1153 :=
  BSD_hasse_of_degree_nonneg 1153 BSD_DegreeNonneg_p1153
theorem BSD_Hasse_OPEN_p1163 : BSD_Hasse_OPEN 1163 :=
  BSD_hasse_of_degree_nonneg 1163 BSD_DegreeNonneg_p1163
theorem BSD_Hasse_OPEN_p1171 : BSD_Hasse_OPEN 1171 :=
  BSD_hasse_of_degree_nonneg 1171 BSD_DegreeNonneg_p1171
theorem BSD_Hasse_OPEN_p1181 : BSD_Hasse_OPEN 1181 :=
  BSD_hasse_of_degree_nonneg 1181 BSD_DegreeNonneg_p1181
theorem BSD_Hasse_OPEN_p1187 : BSD_Hasse_OPEN 1187 :=
  BSD_hasse_of_degree_nonneg 1187 BSD_DegreeNonneg_p1187
theorem BSD_Hasse_OPEN_p1193 : BSD_Hasse_OPEN 1193 :=
  BSD_hasse_of_degree_nonneg 1193 BSD_DegreeNonneg_p1193
theorem BSD_Hasse_OPEN_p1201 : BSD_Hasse_OPEN 1201 :=
  BSD_hasse_of_degree_nonneg 1201 BSD_DegreeNonneg_p1201
theorem BSD_Hasse_OPEN_p1213 : BSD_Hasse_OPEN 1213 :=
  BSD_hasse_of_degree_nonneg 1213 BSD_DegreeNonneg_p1213

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1129 : (a_p 1129 : ℝ) ^ 2 ≤ 4 * (1129 : ℝ) :=
  BSD_disc_from_deg_785 BSD_DegreeNonneg_p1129
theorem BSD_HasseBound_Disc_p1151 : (a_p 1151 : ℝ) ^ 2 ≤ 4 * (1151 : ℝ) :=
  BSD_disc_from_deg_785 BSD_DegreeNonneg_p1151
theorem BSD_HasseBound_Disc_p1153 : (a_p 1153 : ℝ) ^ 2 ≤ 4 * (1153 : ℝ) :=
  BSD_disc_from_deg_785 BSD_DegreeNonneg_p1153
theorem BSD_HasseBound_Disc_p1163 : (a_p 1163 : ℝ) ^ 2 ≤ 4 * (1163 : ℝ) :=
  BSD_disc_from_deg_785 BSD_DegreeNonneg_p1163
theorem BSD_HasseBound_Disc_p1171 : (a_p 1171 : ℝ) ^ 2 ≤ 4 * (1171 : ℝ) :=
  BSD_disc_from_deg_785 BSD_DegreeNonneg_p1171
theorem BSD_HasseBound_Disc_p1181 : (a_p 1181 : ℝ) ^ 2 ≤ 4 * (1181 : ℝ) :=
  BSD_disc_from_deg_785 BSD_DegreeNonneg_p1181
theorem BSD_HasseBound_Disc_p1187 : (a_p 1187 : ℝ) ^ 2 ≤ 4 * (1187 : ℝ) :=
  BSD_disc_from_deg_785 BSD_DegreeNonneg_p1187
theorem BSD_HasseBound_Disc_p1193 : (a_p 1193 : ℝ) ^ 2 ≤ 4 * (1193 : ℝ) :=
  BSD_disc_from_deg_785 BSD_DegreeNonneg_p1193
theorem BSD_HasseBound_Disc_p1201 : (a_p 1201 : ℝ) ^ 2 ≤ 4 * (1201 : ℝ) :=
  BSD_disc_from_deg_785 BSD_DegreeNonneg_p1201
theorem BSD_HasseBound_Disc_p1213 : (a_p 1213 : ℝ) ^ 2 ≤ 4 * (1213 : ℝ) :=
  BSD_disc_from_deg_785 BSD_DegreeNonneg_p1213

end Towers.BSD
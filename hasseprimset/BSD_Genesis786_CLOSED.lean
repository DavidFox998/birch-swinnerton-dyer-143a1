/-
================================================================
Towers / BSD / BSD_Genesis786_CLOSED  (genesis-786)

HasseBridge Tier C: Hasse bounds for primes
1217..1283 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1217: card=1230, a_p=-12, disc=-4724
  p=1223: card=1224, a_p=+0, disc=-4892
  p=1229: card=1270, a_p=-40, disc=-3316
  p=1231: card=1214, a_p=+18, disc=-4600
  p=1237: card=1288, a_p=-50, disc=-2448
  p=1249: card=1248, a_p=+2, disc=-4992
  p=1259: card=1299, a_p=-39, disc=-3515
  p=1277: card=1269, a_p=+9, disc=-5027
  p=1279: card=1245, a_p=+35, disc=-3891
  p=1283: card=1234, a_p=+50, disc=-2632

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_786 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i786_p1217 : Fact (1217 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1223 : Fact (1223 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1229 : Fact (1229 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1231 : Fact (1231 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1237 : Fact (1237 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1249 : Fact (1249 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1259 : Fact (1259 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1277 : Fact (1277 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1279 : Fact (1279 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1283 : Fact (1283 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1217 : (E143_Finset 1217).card = 1230 := by native_decide
theorem BSD_E143_card_p1223 : (E143_Finset 1223).card = 1224 := by native_decide
theorem BSD_E143_card_p1229 : (E143_Finset 1229).card = 1270 := by native_decide
theorem BSD_E143_card_p1231 : (E143_Finset 1231).card = 1214 := by native_decide
theorem BSD_E143_card_p1237 : (E143_Finset 1237).card = 1288 := by native_decide
theorem BSD_E143_card_p1249 : (E143_Finset 1249).card = 1248 := by native_decide
theorem BSD_E143_card_p1259 : (E143_Finset 1259).card = 1299 := by native_decide
theorem BSD_E143_card_p1277 : (E143_Finset 1277).card = 1269 := by native_decide
theorem BSD_E143_card_p1279 : (E143_Finset 1279).card = 1245 := by native_decide
theorem BSD_E143_card_p1283 : (E143_Finset 1283).card = 1234 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1217 : a_p 1217 = (-12 : ℤ) := by
  have h := BSD_E143_card_p1217; unfold a_p; omega
theorem BSD_ap_p1223 : a_p 1223 = (0 : ℤ) := by
  have h := BSD_E143_card_p1223; unfold a_p; omega
theorem BSD_ap_p1229 : a_p 1229 = (-40 : ℤ) := by
  have h := BSD_E143_card_p1229; unfold a_p; omega
theorem BSD_ap_p1231 : a_p 1231 = (18 : ℤ) := by
  have h := BSD_E143_card_p1231; unfold a_p; omega
theorem BSD_ap_p1237 : a_p 1237 = (-50 : ℤ) := by
  have h := BSD_E143_card_p1237; unfold a_p; omega
theorem BSD_ap_p1249 : a_p 1249 = (2 : ℤ) := by
  have h := BSD_E143_card_p1249; unfold a_p; omega
theorem BSD_ap_p1259 : a_p 1259 = (-39 : ℤ) := by
  have h := BSD_E143_card_p1259; unfold a_p; omega
theorem BSD_ap_p1277 : a_p 1277 = (9 : ℤ) := by
  have h := BSD_E143_card_p1277; unfold a_p; omega
theorem BSD_ap_p1279 : a_p 1279 = (35 : ℤ) := by
  have h := BSD_E143_card_p1279; unfold a_p; omega
theorem BSD_ap_p1283 : a_p 1283 = (50 : ℤ) := by
  have h := BSD_E143_card_p1283; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1217: a_p=-12, 4p-a_p²=4724
theorem BSD_DegreeNonneg_p1217 : BSD_FrobeniusDegreeNonneg_OPEN 1217 := fun r => by
  have hap : (a_p 1217 : ℝ) = -12 := by exact_mod_cast BSD_ap_p1217
  have key : r ^ 2 - (a_p 1217 : ℝ) * r + ((1217 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 4724/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

-- p=1223: a_p=+0, 4p-a_p²=4892
theorem BSD_DegreeNonneg_p1223 : BSD_FrobeniusDegreeNonneg_OPEN 1223 := fun r => by
  have hap : (a_p 1223 : ℝ) = 0 := by exact_mod_cast BSD_ap_p1223
  have key : r ^ 2 - (a_p 1223 : ℝ) * r + ((1223 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 4892/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

-- p=1229: a_p=-40, 4p-a_p²=3316
theorem BSD_DegreeNonneg_p1229 : BSD_FrobeniusDegreeNonneg_OPEN 1229 := fun r => by
  have hap : (a_p 1229 : ℝ) = -40 := by exact_mod_cast BSD_ap_p1229
  have key : r ^ 2 - (a_p 1229 : ℝ) * r + ((1229 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 3316/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

-- p=1231: a_p=+18, 4p-a_p²=4600
theorem BSD_DegreeNonneg_p1231 : BSD_FrobeniusDegreeNonneg_OPEN 1231 := fun r => by
  have hap : (a_p 1231 : ℝ) = 18 := by exact_mod_cast BSD_ap_p1231
  have key : r ^ 2 - (a_p 1231 : ℝ) * r + ((1231 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 4600/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

-- p=1237: a_p=-50, 4p-a_p²=2448
theorem BSD_DegreeNonneg_p1237 : BSD_FrobeniusDegreeNonneg_OPEN 1237 := fun r => by
  have hap : (a_p 1237 : ℝ) = -50 := by exact_mod_cast BSD_ap_p1237
  have key : r ^ 2 - (a_p 1237 : ℝ) * r + ((1237 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 2448/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

-- p=1249: a_p=+2, 4p-a_p²=4992
theorem BSD_DegreeNonneg_p1249 : BSD_FrobeniusDegreeNonneg_OPEN 1249 := fun r => by
  have hap : (a_p 1249 : ℝ) = 2 := by exact_mod_cast BSD_ap_p1249
  have key : r ^ 2 - (a_p 1249 : ℝ) * r + ((1249 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 4992/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

-- p=1259: a_p=-39, 4p-a_p²=3515
theorem BSD_DegreeNonneg_p1259 : BSD_FrobeniusDegreeNonneg_OPEN 1259 := fun r => by
  have hap : (a_p 1259 : ℝ) = -39 := by exact_mod_cast BSD_ap_p1259
  have key : r ^ 2 - (a_p 1259 : ℝ) * r + ((1259 : ℕ) : ℝ) =
      (r + 39/2) ^ 2 + 3515/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (39 : ℝ)/2)]

-- p=1277: a_p=+9, 4p-a_p²=5027
theorem BSD_DegreeNonneg_p1277 : BSD_FrobeniusDegreeNonneg_OPEN 1277 := fun r => by
  have hap : (a_p 1277 : ℝ) = 9 := by exact_mod_cast BSD_ap_p1277
  have key : r ^ 2 - (a_p 1277 : ℝ) * r + ((1277 : ℕ) : ℝ) =
      (r - 9/2) ^ 2 + 5027/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (9 : ℝ)/2)]

-- p=1279: a_p=+35, 4p-a_p²=3891
theorem BSD_DegreeNonneg_p1279 : BSD_FrobeniusDegreeNonneg_OPEN 1279 := fun r => by
  have hap : (a_p 1279 : ℝ) = 35 := by exact_mod_cast BSD_ap_p1279
  have key : r ^ 2 - (a_p 1279 : ℝ) * r + ((1279 : ℕ) : ℝ) =
      (r - 35/2) ^ 2 + 3891/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (35 : ℝ)/2)]

-- p=1283: a_p=+50, 4p-a_p²=2632
theorem BSD_DegreeNonneg_p1283 : BSD_FrobeniusDegreeNonneg_OPEN 1283 := fun r => by
  have hap : (a_p 1283 : ℝ) = 50 := by exact_mod_cast BSD_ap_p1283
  have key : r ^ 2 - (a_p 1283 : ℝ) * r + ((1283 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 2632/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1217 : BSD_Hasse_OPEN 1217 :=
  BSD_hasse_of_degree_nonneg 1217 BSD_DegreeNonneg_p1217
theorem BSD_Hasse_OPEN_p1223 : BSD_Hasse_OPEN 1223 :=
  BSD_hasse_of_degree_nonneg 1223 BSD_DegreeNonneg_p1223
theorem BSD_Hasse_OPEN_p1229 : BSD_Hasse_OPEN 1229 :=
  BSD_hasse_of_degree_nonneg 1229 BSD_DegreeNonneg_p1229
theorem BSD_Hasse_OPEN_p1231 : BSD_Hasse_OPEN 1231 :=
  BSD_hasse_of_degree_nonneg 1231 BSD_DegreeNonneg_p1231
theorem BSD_Hasse_OPEN_p1237 : BSD_Hasse_OPEN 1237 :=
  BSD_hasse_of_degree_nonneg 1237 BSD_DegreeNonneg_p1237
theorem BSD_Hasse_OPEN_p1249 : BSD_Hasse_OPEN 1249 :=
  BSD_hasse_of_degree_nonneg 1249 BSD_DegreeNonneg_p1249
theorem BSD_Hasse_OPEN_p1259 : BSD_Hasse_OPEN 1259 :=
  BSD_hasse_of_degree_nonneg 1259 BSD_DegreeNonneg_p1259
theorem BSD_Hasse_OPEN_p1277 : BSD_Hasse_OPEN 1277 :=
  BSD_hasse_of_degree_nonneg 1277 BSD_DegreeNonneg_p1277
theorem BSD_Hasse_OPEN_p1279 : BSD_Hasse_OPEN 1279 :=
  BSD_hasse_of_degree_nonneg 1279 BSD_DegreeNonneg_p1279
theorem BSD_Hasse_OPEN_p1283 : BSD_Hasse_OPEN 1283 :=
  BSD_hasse_of_degree_nonneg 1283 BSD_DegreeNonneg_p1283

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1217 : (a_p 1217 : ℝ) ^ 2 ≤ 4 * (1217 : ℝ) :=
  BSD_disc_from_deg_786 BSD_DegreeNonneg_p1217
theorem BSD_HasseBound_Disc_p1223 : (a_p 1223 : ℝ) ^ 2 ≤ 4 * (1223 : ℝ) :=
  BSD_disc_from_deg_786 BSD_DegreeNonneg_p1223
theorem BSD_HasseBound_Disc_p1229 : (a_p 1229 : ℝ) ^ 2 ≤ 4 * (1229 : ℝ) :=
  BSD_disc_from_deg_786 BSD_DegreeNonneg_p1229
theorem BSD_HasseBound_Disc_p1231 : (a_p 1231 : ℝ) ^ 2 ≤ 4 * (1231 : ℝ) :=
  BSD_disc_from_deg_786 BSD_DegreeNonneg_p1231
theorem BSD_HasseBound_Disc_p1237 : (a_p 1237 : ℝ) ^ 2 ≤ 4 * (1237 : ℝ) :=
  BSD_disc_from_deg_786 BSD_DegreeNonneg_p1237
theorem BSD_HasseBound_Disc_p1249 : (a_p 1249 : ℝ) ^ 2 ≤ 4 * (1249 : ℝ) :=
  BSD_disc_from_deg_786 BSD_DegreeNonneg_p1249
theorem BSD_HasseBound_Disc_p1259 : (a_p 1259 : ℝ) ^ 2 ≤ 4 * (1259 : ℝ) :=
  BSD_disc_from_deg_786 BSD_DegreeNonneg_p1259
theorem BSD_HasseBound_Disc_p1277 : (a_p 1277 : ℝ) ^ 2 ≤ 4 * (1277 : ℝ) :=
  BSD_disc_from_deg_786 BSD_DegreeNonneg_p1277
theorem BSD_HasseBound_Disc_p1279 : (a_p 1279 : ℝ) ^ 2 ≤ 4 * (1279 : ℝ) :=
  BSD_disc_from_deg_786 BSD_DegreeNonneg_p1279
theorem BSD_HasseBound_Disc_p1283 : (a_p 1283 : ℝ) ^ 2 ≤ 4 * (1283 : ℝ) :=
  BSD_disc_from_deg_786 BSD_DegreeNonneg_p1283

end Towers.BSD
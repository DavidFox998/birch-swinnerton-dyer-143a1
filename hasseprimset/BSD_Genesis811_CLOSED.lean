/-
================================================================
Towers / BSD / BSD_Genesis811_CLOSED  (genesis-811)

HasseBridge Tier C: Hasse bounds for primes
3169..3251 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=3169: card=3177, a_p=-7, disc=-12627
  p=3181: card=3194, a_p=-12, disc=-12580
  p=3187: card=3268, a_p=-80, disc=-6348
  p=3191: card=3144, a_p=+48, disc=-10460
  p=3203: card=3266, a_p=-62, disc=-8968
  p=3209: card=3280, a_p=-70, disc=-7936
  p=3217: card=3225, a_p=-7, disc=-12819
  p=3221: card=3289, a_p=-67, disc=-8395
  p=3229: card=3258, a_p=-28, disc=-12132
  p=3251: card=3310, a_p=-58, disc=-9640

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_811 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i811_p3169 : Fact (3169 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3181 : Fact (3181 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3187 : Fact (3187 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3191 : Fact (3191 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3203 : Fact (3203 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3209 : Fact (3209 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3217 : Fact (3217 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3221 : Fact (3221 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3229 : Fact (3229 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3251 : Fact (3251 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p3169 : (E143_Finset 3169).card = 3177 := by native_decide
theorem BSD_E143_card_p3181 : (E143_Finset 3181).card = 3194 := by native_decide
theorem BSD_E143_card_p3187 : (E143_Finset 3187).card = 3268 := by native_decide
theorem BSD_E143_card_p3191 : (E143_Finset 3191).card = 3144 := by native_decide
theorem BSD_E143_card_p3203 : (E143_Finset 3203).card = 3266 := by native_decide
theorem BSD_E143_card_p3209 : (E143_Finset 3209).card = 3280 := by native_decide
theorem BSD_E143_card_p3217 : (E143_Finset 3217).card = 3225 := by native_decide
theorem BSD_E143_card_p3221 : (E143_Finset 3221).card = 3289 := by native_decide
theorem BSD_E143_card_p3229 : (E143_Finset 3229).card = 3258 := by native_decide
theorem BSD_E143_card_p3251 : (E143_Finset 3251).card = 3310 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p3169 : a_p 3169 = (-7 : ℤ) := by
  have h := BSD_E143_card_p3169; unfold a_p; omega
theorem BSD_ap_p3181 : a_p 3181 = (-12 : ℤ) := by
  have h := BSD_E143_card_p3181; unfold a_p; omega
theorem BSD_ap_p3187 : a_p 3187 = (-80 : ℤ) := by
  have h := BSD_E143_card_p3187; unfold a_p; omega
theorem BSD_ap_p3191 : a_p 3191 = (48 : ℤ) := by
  have h := BSD_E143_card_p3191; unfold a_p; omega
theorem BSD_ap_p3203 : a_p 3203 = (-62 : ℤ) := by
  have h := BSD_E143_card_p3203; unfold a_p; omega
theorem BSD_ap_p3209 : a_p 3209 = (-70 : ℤ) := by
  have h := BSD_E143_card_p3209; unfold a_p; omega
theorem BSD_ap_p3217 : a_p 3217 = (-7 : ℤ) := by
  have h := BSD_E143_card_p3217; unfold a_p; omega
theorem BSD_ap_p3221 : a_p 3221 = (-67 : ℤ) := by
  have h := BSD_E143_card_p3221; unfold a_p; omega
theorem BSD_ap_p3229 : a_p 3229 = (-28 : ℤ) := by
  have h := BSD_E143_card_p3229; unfold a_p; omega
theorem BSD_ap_p3251 : a_p 3251 = (-58 : ℤ) := by
  have h := BSD_E143_card_p3251; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=3169: a_p=-7, 4p-a_p²=12627
theorem BSD_DegreeNonneg_p3169 : BSD_FrobeniusDegreeNonneg_OPEN 3169 := fun r => by
  have hap : (a_p 3169 : ℝ) = -7 := by exact_mod_cast BSD_ap_p3169
  have key : r ^ 2 - (a_p 3169 : ℝ) * r + ((3169 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 12627/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

-- p=3181: a_p=-12, 4p-a_p²=12580
theorem BSD_DegreeNonneg_p3181 : BSD_FrobeniusDegreeNonneg_OPEN 3181 := fun r => by
  have hap : (a_p 3181 : ℝ) = -12 := by exact_mod_cast BSD_ap_p3181
  have key : r ^ 2 - (a_p 3181 : ℝ) * r + ((3181 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 12580/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

-- p=3187: a_p=-80, 4p-a_p²=6348
theorem BSD_DegreeNonneg_p3187 : BSD_FrobeniusDegreeNonneg_OPEN 3187 := fun r => by
  have hap : (a_p 3187 : ℝ) = -80 := by exact_mod_cast BSD_ap_p3187
  have key : r ^ 2 - (a_p 3187 : ℝ) * r + ((3187 : ℕ) : ℝ) =
      (r + 80/2) ^ 2 + 6348/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (80 : ℝ)/2)]

-- p=3191: a_p=+48, 4p-a_p²=10460
theorem BSD_DegreeNonneg_p3191 : BSD_FrobeniusDegreeNonneg_OPEN 3191 := fun r => by
  have hap : (a_p 3191 : ℝ) = 48 := by exact_mod_cast BSD_ap_p3191
  have key : r ^ 2 - (a_p 3191 : ℝ) * r + ((3191 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 10460/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

-- p=3203: a_p=-62, 4p-a_p²=8968
theorem BSD_DegreeNonneg_p3203 : BSD_FrobeniusDegreeNonneg_OPEN 3203 := fun r => by
  have hap : (a_p 3203 : ℝ) = -62 := by exact_mod_cast BSD_ap_p3203
  have key : r ^ 2 - (a_p 3203 : ℝ) * r + ((3203 : ℕ) : ℝ) =
      (r + 62/2) ^ 2 + 8968/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (62 : ℝ)/2)]

-- p=3209: a_p=-70, 4p-a_p²=7936
theorem BSD_DegreeNonneg_p3209 : BSD_FrobeniusDegreeNonneg_OPEN 3209 := fun r => by
  have hap : (a_p 3209 : ℝ) = -70 := by exact_mod_cast BSD_ap_p3209
  have key : r ^ 2 - (a_p 3209 : ℝ) * r + ((3209 : ℕ) : ℝ) =
      (r + 70/2) ^ 2 + 7936/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (70 : ℝ)/2)]

-- p=3217: a_p=-7, 4p-a_p²=12819
theorem BSD_DegreeNonneg_p3217 : BSD_FrobeniusDegreeNonneg_OPEN 3217 := fun r => by
  have hap : (a_p 3217 : ℝ) = -7 := by exact_mod_cast BSD_ap_p3217
  have key : r ^ 2 - (a_p 3217 : ℝ) * r + ((3217 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 12819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

-- p=3221: a_p=-67, 4p-a_p²=8395
theorem BSD_DegreeNonneg_p3221 : BSD_FrobeniusDegreeNonneg_OPEN 3221 := fun r => by
  have hap : (a_p 3221 : ℝ) = -67 := by exact_mod_cast BSD_ap_p3221
  have key : r ^ 2 - (a_p 3221 : ℝ) * r + ((3221 : ℕ) : ℝ) =
      (r + 67/2) ^ 2 + 8395/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (67 : ℝ)/2)]

-- p=3229: a_p=-28, 4p-a_p²=12132
theorem BSD_DegreeNonneg_p3229 : BSD_FrobeniusDegreeNonneg_OPEN 3229 := fun r => by
  have hap : (a_p 3229 : ℝ) = -28 := by exact_mod_cast BSD_ap_p3229
  have key : r ^ 2 - (a_p 3229 : ℝ) * r + ((3229 : ℕ) : ℝ) =
      (r + 28/2) ^ 2 + 12132/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (28 : ℝ)/2)]

-- p=3251: a_p=-58, 4p-a_p²=9640
theorem BSD_DegreeNonneg_p3251 : BSD_FrobeniusDegreeNonneg_OPEN 3251 := fun r => by
  have hap : (a_p 3251 : ℝ) = -58 := by exact_mod_cast BSD_ap_p3251
  have key : r ^ 2 - (a_p 3251 : ℝ) * r + ((3251 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 9640/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p3169 : BSD_Hasse_OPEN 3169 :=
  BSD_hasse_of_degree_nonneg 3169 BSD_DegreeNonneg_p3169
theorem BSD_Hasse_OPEN_p3181 : BSD_Hasse_OPEN 3181 :=
  BSD_hasse_of_degree_nonneg 3181 BSD_DegreeNonneg_p3181
theorem BSD_Hasse_OPEN_p3187 : BSD_Hasse_OPEN 3187 :=
  BSD_hasse_of_degree_nonneg 3187 BSD_DegreeNonneg_p3187
theorem BSD_Hasse_OPEN_p3191 : BSD_Hasse_OPEN 3191 :=
  BSD_hasse_of_degree_nonneg 3191 BSD_DegreeNonneg_p3191
theorem BSD_Hasse_OPEN_p3203 : BSD_Hasse_OPEN 3203 :=
  BSD_hasse_of_degree_nonneg 3203 BSD_DegreeNonneg_p3203
theorem BSD_Hasse_OPEN_p3209 : BSD_Hasse_OPEN 3209 :=
  BSD_hasse_of_degree_nonneg 3209 BSD_DegreeNonneg_p3209
theorem BSD_Hasse_OPEN_p3217 : BSD_Hasse_OPEN 3217 :=
  BSD_hasse_of_degree_nonneg 3217 BSD_DegreeNonneg_p3217
theorem BSD_Hasse_OPEN_p3221 : BSD_Hasse_OPEN 3221 :=
  BSD_hasse_of_degree_nonneg 3221 BSD_DegreeNonneg_p3221
theorem BSD_Hasse_OPEN_p3229 : BSD_Hasse_OPEN 3229 :=
  BSD_hasse_of_degree_nonneg 3229 BSD_DegreeNonneg_p3229
theorem BSD_Hasse_OPEN_p3251 : BSD_Hasse_OPEN 3251 :=
  BSD_hasse_of_degree_nonneg 3251 BSD_DegreeNonneg_p3251

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p3169 : (a_p 3169 : ℝ) ^ 2 ≤ 4 * (3169 : ℝ) :=
  BSD_disc_from_deg_811 BSD_DegreeNonneg_p3169
theorem BSD_HasseBound_Disc_p3181 : (a_p 3181 : ℝ) ^ 2 ≤ 4 * (3181 : ℝ) :=
  BSD_disc_from_deg_811 BSD_DegreeNonneg_p3181
theorem BSD_HasseBound_Disc_p3187 : (a_p 3187 : ℝ) ^ 2 ≤ 4 * (3187 : ℝ) :=
  BSD_disc_from_deg_811 BSD_DegreeNonneg_p3187
theorem BSD_HasseBound_Disc_p3191 : (a_p 3191 : ℝ) ^ 2 ≤ 4 * (3191 : ℝ) :=
  BSD_disc_from_deg_811 BSD_DegreeNonneg_p3191
theorem BSD_HasseBound_Disc_p3203 : (a_p 3203 : ℝ) ^ 2 ≤ 4 * (3203 : ℝ) :=
  BSD_disc_from_deg_811 BSD_DegreeNonneg_p3203
theorem BSD_HasseBound_Disc_p3209 : (a_p 3209 : ℝ) ^ 2 ≤ 4 * (3209 : ℝ) :=
  BSD_disc_from_deg_811 BSD_DegreeNonneg_p3209
theorem BSD_HasseBound_Disc_p3217 : (a_p 3217 : ℝ) ^ 2 ≤ 4 * (3217 : ℝ) :=
  BSD_disc_from_deg_811 BSD_DegreeNonneg_p3217
theorem BSD_HasseBound_Disc_p3221 : (a_p 3221 : ℝ) ^ 2 ≤ 4 * (3221 : ℝ) :=
  BSD_disc_from_deg_811 BSD_DegreeNonneg_p3221
theorem BSD_HasseBound_Disc_p3229 : (a_p 3229 : ℝ) ^ 2 ≤ 4 * (3229 : ℝ) :=
  BSD_disc_from_deg_811 BSD_DegreeNonneg_p3229
theorem BSD_HasseBound_Disc_p3251 : (a_p 3251 : ℝ) ^ 2 ≤ 4 * (3251 : ℝ) :=
  BSD_disc_from_deg_811 BSD_DegreeNonneg_p3251

end Towers.BSD
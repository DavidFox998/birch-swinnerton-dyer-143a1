/-
================================================================
Towers / BSD / BSD_Genesis812_CLOSED  (genesis-812)

HasseBridge Tier C: Hasse bounds for primes
3253..3323 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=3253: card=3190, a_p=+64, disc=-8916
  p=3257: card=3340, a_p=-82, disc=-6304
  p=3259: card=3264, a_p=-4, disc=-13020
  p=3271: card=3177, a_p=+95, disc=-4059
  p=3299: card=3320, a_p=-20, disc=-12796
  p=3301: card=3359, a_p=-57, disc=-9955
  p=3307: card=3316, a_p=-8, disc=-13164
  p=3313: card=3302, a_p=+12, disc=-13108
  p=3319: card=3286, a_p=+34, disc=-12120
  p=3323: card=3408, a_p=-84, disc=-6236

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_812 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i812_p3253 : Fact (3253 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3257 : Fact (3257 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3259 : Fact (3259 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3271 : Fact (3271 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3299 : Fact (3299 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3301 : Fact (3301 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3307 : Fact (3307 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3313 : Fact (3313 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3319 : Fact (3319 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3323 : Fact (3323 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p3253 : (E143_Finset 3253).card = 3190 := by native_decide
theorem BSD_E143_card_p3257 : (E143_Finset 3257).card = 3340 := by native_decide
theorem BSD_E143_card_p3259 : (E143_Finset 3259).card = 3264 := by native_decide
theorem BSD_E143_card_p3271 : (E143_Finset 3271).card = 3177 := by native_decide
theorem BSD_E143_card_p3299 : (E143_Finset 3299).card = 3320 := by native_decide
theorem BSD_E143_card_p3301 : (E143_Finset 3301).card = 3359 := by native_decide
theorem BSD_E143_card_p3307 : (E143_Finset 3307).card = 3316 := by native_decide
theorem BSD_E143_card_p3313 : (E143_Finset 3313).card = 3302 := by native_decide
theorem BSD_E143_card_p3319 : (E143_Finset 3319).card = 3286 := by native_decide
theorem BSD_E143_card_p3323 : (E143_Finset 3323).card = 3408 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p3253 : a_p 3253 = (64 : ℤ) := by
  have h := BSD_E143_card_p3253; unfold a_p; omega
theorem BSD_ap_p3257 : a_p 3257 = (-82 : ℤ) := by
  have h := BSD_E143_card_p3257; unfold a_p; omega
theorem BSD_ap_p3259 : a_p 3259 = (-4 : ℤ) := by
  have h := BSD_E143_card_p3259; unfold a_p; omega
theorem BSD_ap_p3271 : a_p 3271 = (95 : ℤ) := by
  have h := BSD_E143_card_p3271; unfold a_p; omega
theorem BSD_ap_p3299 : a_p 3299 = (-20 : ℤ) := by
  have h := BSD_E143_card_p3299; unfold a_p; omega
theorem BSD_ap_p3301 : a_p 3301 = (-57 : ℤ) := by
  have h := BSD_E143_card_p3301; unfold a_p; omega
theorem BSD_ap_p3307 : a_p 3307 = (-8 : ℤ) := by
  have h := BSD_E143_card_p3307; unfold a_p; omega
theorem BSD_ap_p3313 : a_p 3313 = (12 : ℤ) := by
  have h := BSD_E143_card_p3313; unfold a_p; omega
theorem BSD_ap_p3319 : a_p 3319 = (34 : ℤ) := by
  have h := BSD_E143_card_p3319; unfold a_p; omega
theorem BSD_ap_p3323 : a_p 3323 = (-84 : ℤ) := by
  have h := BSD_E143_card_p3323; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=3253: a_p=+64, 4p-a_p²=8916
theorem BSD_DegreeNonneg_p3253 : BSD_FrobeniusDegreeNonneg_OPEN 3253 := fun r => by
  have hap : (a_p 3253 : ℝ) = 64 := by exact_mod_cast BSD_ap_p3253
  have key : r ^ 2 - (a_p 3253 : ℝ) * r + ((3253 : ℕ) : ℝ) =
      (r - 64/2) ^ 2 + 8916/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (64 : ℝ)/2)]

-- p=3257: a_p=-82, 4p-a_p²=6304
theorem BSD_DegreeNonneg_p3257 : BSD_FrobeniusDegreeNonneg_OPEN 3257 := fun r => by
  have hap : (a_p 3257 : ℝ) = -82 := by exact_mod_cast BSD_ap_p3257
  have key : r ^ 2 - (a_p 3257 : ℝ) * r + ((3257 : ℕ) : ℝ) =
      (r + 82/2) ^ 2 + 6304/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (82 : ℝ)/2)]

-- p=3259: a_p=-4, 4p-a_p²=13020
theorem BSD_DegreeNonneg_p3259 : BSD_FrobeniusDegreeNonneg_OPEN 3259 := fun r => by
  have hap : (a_p 3259 : ℝ) = -4 := by exact_mod_cast BSD_ap_p3259
  have key : r ^ 2 - (a_p 3259 : ℝ) * r + ((3259 : ℕ) : ℝ) =
      (r + 4/2) ^ 2 + 13020/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (4 : ℝ)/2)]

-- p=3271: a_p=+95, 4p-a_p²=4059
theorem BSD_DegreeNonneg_p3271 : BSD_FrobeniusDegreeNonneg_OPEN 3271 := fun r => by
  have hap : (a_p 3271 : ℝ) = 95 := by exact_mod_cast BSD_ap_p3271
  have key : r ^ 2 - (a_p 3271 : ℝ) * r + ((3271 : ℕ) : ℝ) =
      (r - 95/2) ^ 2 + 4059/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (95 : ℝ)/2)]

-- p=3299: a_p=-20, 4p-a_p²=12796
theorem BSD_DegreeNonneg_p3299 : BSD_FrobeniusDegreeNonneg_OPEN 3299 := fun r => by
  have hap : (a_p 3299 : ℝ) = -20 := by exact_mod_cast BSD_ap_p3299
  have key : r ^ 2 - (a_p 3299 : ℝ) * r + ((3299 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 12796/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=3301: a_p=-57, 4p-a_p²=9955
theorem BSD_DegreeNonneg_p3301 : BSD_FrobeniusDegreeNonneg_OPEN 3301 := fun r => by
  have hap : (a_p 3301 : ℝ) = -57 := by exact_mod_cast BSD_ap_p3301
  have key : r ^ 2 - (a_p 3301 : ℝ) * r + ((3301 : ℕ) : ℝ) =
      (r + 57/2) ^ 2 + 9955/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (57 : ℝ)/2)]

-- p=3307: a_p=-8, 4p-a_p²=13164
theorem BSD_DegreeNonneg_p3307 : BSD_FrobeniusDegreeNonneg_OPEN 3307 := fun r => by
  have hap : (a_p 3307 : ℝ) = -8 := by exact_mod_cast BSD_ap_p3307
  have key : r ^ 2 - (a_p 3307 : ℝ) * r + ((3307 : ℕ) : ℝ) =
      (r + 8/2) ^ 2 + 13164/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (8 : ℝ)/2)]

-- p=3313: a_p=+12, 4p-a_p²=13108
theorem BSD_DegreeNonneg_p3313 : BSD_FrobeniusDegreeNonneg_OPEN 3313 := fun r => by
  have hap : (a_p 3313 : ℝ) = 12 := by exact_mod_cast BSD_ap_p3313
  have key : r ^ 2 - (a_p 3313 : ℝ) * r + ((3313 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 13108/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

-- p=3319: a_p=+34, 4p-a_p²=12120
theorem BSD_DegreeNonneg_p3319 : BSD_FrobeniusDegreeNonneg_OPEN 3319 := fun r => by
  have hap : (a_p 3319 : ℝ) = 34 := by exact_mod_cast BSD_ap_p3319
  have key : r ^ 2 - (a_p 3319 : ℝ) * r + ((3319 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 12120/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

-- p=3323: a_p=-84, 4p-a_p²=6236
theorem BSD_DegreeNonneg_p3323 : BSD_FrobeniusDegreeNonneg_OPEN 3323 := fun r => by
  have hap : (a_p 3323 : ℝ) = -84 := by exact_mod_cast BSD_ap_p3323
  have key : r ^ 2 - (a_p 3323 : ℝ) * r + ((3323 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 6236/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p3253 : BSD_Hasse_OPEN 3253 :=
  BSD_hasse_of_degree_nonneg 3253 BSD_DegreeNonneg_p3253
theorem BSD_Hasse_OPEN_p3257 : BSD_Hasse_OPEN 3257 :=
  BSD_hasse_of_degree_nonneg 3257 BSD_DegreeNonneg_p3257
theorem BSD_Hasse_OPEN_p3259 : BSD_Hasse_OPEN 3259 :=
  BSD_hasse_of_degree_nonneg 3259 BSD_DegreeNonneg_p3259
theorem BSD_Hasse_OPEN_p3271 : BSD_Hasse_OPEN 3271 :=
  BSD_hasse_of_degree_nonneg 3271 BSD_DegreeNonneg_p3271
theorem BSD_Hasse_OPEN_p3299 : BSD_Hasse_OPEN 3299 :=
  BSD_hasse_of_degree_nonneg 3299 BSD_DegreeNonneg_p3299
theorem BSD_Hasse_OPEN_p3301 : BSD_Hasse_OPEN 3301 :=
  BSD_hasse_of_degree_nonneg 3301 BSD_DegreeNonneg_p3301
theorem BSD_Hasse_OPEN_p3307 : BSD_Hasse_OPEN 3307 :=
  BSD_hasse_of_degree_nonneg 3307 BSD_DegreeNonneg_p3307
theorem BSD_Hasse_OPEN_p3313 : BSD_Hasse_OPEN 3313 :=
  BSD_hasse_of_degree_nonneg 3313 BSD_DegreeNonneg_p3313
theorem BSD_Hasse_OPEN_p3319 : BSD_Hasse_OPEN 3319 :=
  BSD_hasse_of_degree_nonneg 3319 BSD_DegreeNonneg_p3319
theorem BSD_Hasse_OPEN_p3323 : BSD_Hasse_OPEN 3323 :=
  BSD_hasse_of_degree_nonneg 3323 BSD_DegreeNonneg_p3323

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p3253 : (a_p 3253 : ℝ) ^ 2 ≤ 4 * (3253 : ℝ) :=
  BSD_disc_from_deg_812 BSD_DegreeNonneg_p3253
theorem BSD_HasseBound_Disc_p3257 : (a_p 3257 : ℝ) ^ 2 ≤ 4 * (3257 : ℝ) :=
  BSD_disc_from_deg_812 BSD_DegreeNonneg_p3257
theorem BSD_HasseBound_Disc_p3259 : (a_p 3259 : ℝ) ^ 2 ≤ 4 * (3259 : ℝ) :=
  BSD_disc_from_deg_812 BSD_DegreeNonneg_p3259
theorem BSD_HasseBound_Disc_p3271 : (a_p 3271 : ℝ) ^ 2 ≤ 4 * (3271 : ℝ) :=
  BSD_disc_from_deg_812 BSD_DegreeNonneg_p3271
theorem BSD_HasseBound_Disc_p3299 : (a_p 3299 : ℝ) ^ 2 ≤ 4 * (3299 : ℝ) :=
  BSD_disc_from_deg_812 BSD_DegreeNonneg_p3299
theorem BSD_HasseBound_Disc_p3301 : (a_p 3301 : ℝ) ^ 2 ≤ 4 * (3301 : ℝ) :=
  BSD_disc_from_deg_812 BSD_DegreeNonneg_p3301
theorem BSD_HasseBound_Disc_p3307 : (a_p 3307 : ℝ) ^ 2 ≤ 4 * (3307 : ℝ) :=
  BSD_disc_from_deg_812 BSD_DegreeNonneg_p3307
theorem BSD_HasseBound_Disc_p3313 : (a_p 3313 : ℝ) ^ 2 ≤ 4 * (3313 : ℝ) :=
  BSD_disc_from_deg_812 BSD_DegreeNonneg_p3313
theorem BSD_HasseBound_Disc_p3319 : (a_p 3319 : ℝ) ^ 2 ≤ 4 * (3319 : ℝ) :=
  BSD_disc_from_deg_812 BSD_DegreeNonneg_p3319
theorem BSD_HasseBound_Disc_p3323 : (a_p 3323 : ℝ) ^ 2 ≤ 4 * (3323 : ℝ) :=
  BSD_disc_from_deg_812 BSD_DegreeNonneg_p3323

end Towers.BSD
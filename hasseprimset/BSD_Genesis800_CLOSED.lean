/-
================================================================
Towers / BSD / BSD_Genesis800_CLOSED  (genesis-800)

HasseBridge Tier C: Hasse bounds for primes
2281..2347 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2281: card=2281, a_p=+1, disc=-9123
  p=2287: card=2302, a_p=-14, disc=-8952
  p=2293: card=2323, a_p=-29, disc=-8331
  p=2297: card=2335, a_p=-37, disc=-7819
  p=2309: card=2396, a_p=-86, disc=-1840
  p=2311: card=2289, a_p=+23, disc=-8715
  p=2333: card=2281, a_p=+53, disc=-6523
  p=2339: card=2410, a_p=-70, disc=-4456
  p=2341: card=2279, a_p=+63, disc=-5395
  p=2347: card=2355, a_p=-7, disc=-9339

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_800 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i800_p2281 : Fact (2281 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2287 : Fact (2287 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2293 : Fact (2293 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2297 : Fact (2297 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2309 : Fact (2309 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2311 : Fact (2311 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2333 : Fact (2333 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2339 : Fact (2339 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2341 : Fact (2341 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2347 : Fact (2347 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2281 : (E143_Finset 2281).card = 2281 := by native_decide
theorem BSD_E143_card_p2287 : (E143_Finset 2287).card = 2302 := by native_decide
theorem BSD_E143_card_p2293 : (E143_Finset 2293).card = 2323 := by native_decide
theorem BSD_E143_card_p2297 : (E143_Finset 2297).card = 2335 := by native_decide
theorem BSD_E143_card_p2309 : (E143_Finset 2309).card = 2396 := by native_decide
theorem BSD_E143_card_p2311 : (E143_Finset 2311).card = 2289 := by native_decide
theorem BSD_E143_card_p2333 : (E143_Finset 2333).card = 2281 := by native_decide
theorem BSD_E143_card_p2339 : (E143_Finset 2339).card = 2410 := by native_decide
theorem BSD_E143_card_p2341 : (E143_Finset 2341).card = 2279 := by native_decide
theorem BSD_E143_card_p2347 : (E143_Finset 2347).card = 2355 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2281 : a_p 2281 = (1 : ℤ) := by
  have h := BSD_E143_card_p2281; unfold a_p; omega
theorem BSD_ap_p2287 : a_p 2287 = (-14 : ℤ) := by
  have h := BSD_E143_card_p2287; unfold a_p; omega
theorem BSD_ap_p2293 : a_p 2293 = (-29 : ℤ) := by
  have h := BSD_E143_card_p2293; unfold a_p; omega
theorem BSD_ap_p2297 : a_p 2297 = (-37 : ℤ) := by
  have h := BSD_E143_card_p2297; unfold a_p; omega
theorem BSD_ap_p2309 : a_p 2309 = (-86 : ℤ) := by
  have h := BSD_E143_card_p2309; unfold a_p; omega
theorem BSD_ap_p2311 : a_p 2311 = (23 : ℤ) := by
  have h := BSD_E143_card_p2311; unfold a_p; omega
theorem BSD_ap_p2333 : a_p 2333 = (53 : ℤ) := by
  have h := BSD_E143_card_p2333; unfold a_p; omega
theorem BSD_ap_p2339 : a_p 2339 = (-70 : ℤ) := by
  have h := BSD_E143_card_p2339; unfold a_p; omega
theorem BSD_ap_p2341 : a_p 2341 = (63 : ℤ) := by
  have h := BSD_E143_card_p2341; unfold a_p; omega
theorem BSD_ap_p2347 : a_p 2347 = (-7 : ℤ) := by
  have h := BSD_E143_card_p2347; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2281: a_p=+1, 4p-a_p²=9123
theorem BSD_DegreeNonneg_p2281 : BSD_FrobeniusDegreeNonneg_OPEN 2281 := fun r => by
  have hap : (a_p 2281 : ℝ) = 1 := by exact_mod_cast BSD_ap_p2281
  have key : r ^ 2 - (a_p 2281 : ℝ) * r + ((2281 : ℕ) : ℝ) =
      (r - 1/2) ^ 2 + 9123/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (1 : ℝ)/2)]

-- p=2287: a_p=-14, 4p-a_p²=8952
theorem BSD_DegreeNonneg_p2287 : BSD_FrobeniusDegreeNonneg_OPEN 2287 := fun r => by
  have hap : (a_p 2287 : ℝ) = -14 := by exact_mod_cast BSD_ap_p2287
  have key : r ^ 2 - (a_p 2287 : ℝ) * r + ((2287 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 8952/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

-- p=2293: a_p=-29, 4p-a_p²=8331
theorem BSD_DegreeNonneg_p2293 : BSD_FrobeniusDegreeNonneg_OPEN 2293 := fun r => by
  have hap : (a_p 2293 : ℝ) = -29 := by exact_mod_cast BSD_ap_p2293
  have key : r ^ 2 - (a_p 2293 : ℝ) * r + ((2293 : ℕ) : ℝ) =
      (r + 29/2) ^ 2 + 8331/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (29 : ℝ)/2)]

-- p=2297: a_p=-37, 4p-a_p²=7819
theorem BSD_DegreeNonneg_p2297 : BSD_FrobeniusDegreeNonneg_OPEN 2297 := fun r => by
  have hap : (a_p 2297 : ℝ) = -37 := by exact_mod_cast BSD_ap_p2297
  have key : r ^ 2 - (a_p 2297 : ℝ) * r + ((2297 : ℕ) : ℝ) =
      (r + 37/2) ^ 2 + 7819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (37 : ℝ)/2)]

-- p=2309: a_p=-86, 4p-a_p²=1840
theorem BSD_DegreeNonneg_p2309 : BSD_FrobeniusDegreeNonneg_OPEN 2309 := fun r => by
  have hap : (a_p 2309 : ℝ) = -86 := by exact_mod_cast BSD_ap_p2309
  have key : r ^ 2 - (a_p 2309 : ℝ) * r + ((2309 : ℕ) : ℝ) =
      (r + 86/2) ^ 2 + 1840/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (86 : ℝ)/2)]

-- p=2311: a_p=+23, 4p-a_p²=8715
theorem BSD_DegreeNonneg_p2311 : BSD_FrobeniusDegreeNonneg_OPEN 2311 := fun r => by
  have hap : (a_p 2311 : ℝ) = 23 := by exact_mod_cast BSD_ap_p2311
  have key : r ^ 2 - (a_p 2311 : ℝ) * r + ((2311 : ℕ) : ℝ) =
      (r - 23/2) ^ 2 + 8715/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (23 : ℝ)/2)]

-- p=2333: a_p=+53, 4p-a_p²=6523
theorem BSD_DegreeNonneg_p2333 : BSD_FrobeniusDegreeNonneg_OPEN 2333 := fun r => by
  have hap : (a_p 2333 : ℝ) = 53 := by exact_mod_cast BSD_ap_p2333
  have key : r ^ 2 - (a_p 2333 : ℝ) * r + ((2333 : ℕ) : ℝ) =
      (r - 53/2) ^ 2 + 6523/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (53 : ℝ)/2)]

-- p=2339: a_p=-70, 4p-a_p²=4456
theorem BSD_DegreeNonneg_p2339 : BSD_FrobeniusDegreeNonneg_OPEN 2339 := fun r => by
  have hap : (a_p 2339 : ℝ) = -70 := by exact_mod_cast BSD_ap_p2339
  have key : r ^ 2 - (a_p 2339 : ℝ) * r + ((2339 : ℕ) : ℝ) =
      (r + 70/2) ^ 2 + 4456/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (70 : ℝ)/2)]

-- p=2341: a_p=+63, 4p-a_p²=5395
theorem BSD_DegreeNonneg_p2341 : BSD_FrobeniusDegreeNonneg_OPEN 2341 := fun r => by
  have hap : (a_p 2341 : ℝ) = 63 := by exact_mod_cast BSD_ap_p2341
  have key : r ^ 2 - (a_p 2341 : ℝ) * r + ((2341 : ℕ) : ℝ) =
      (r - 63/2) ^ 2 + 5395/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (63 : ℝ)/2)]

-- p=2347: a_p=-7, 4p-a_p²=9339
theorem BSD_DegreeNonneg_p2347 : BSD_FrobeniusDegreeNonneg_OPEN 2347 := fun r => by
  have hap : (a_p 2347 : ℝ) = -7 := by exact_mod_cast BSD_ap_p2347
  have key : r ^ 2 - (a_p 2347 : ℝ) * r + ((2347 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 9339/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2281 : BSD_Hasse_OPEN 2281 :=
  BSD_hasse_of_degree_nonneg 2281 BSD_DegreeNonneg_p2281
theorem BSD_Hasse_OPEN_p2287 : BSD_Hasse_OPEN 2287 :=
  BSD_hasse_of_degree_nonneg 2287 BSD_DegreeNonneg_p2287
theorem BSD_Hasse_OPEN_p2293 : BSD_Hasse_OPEN 2293 :=
  BSD_hasse_of_degree_nonneg 2293 BSD_DegreeNonneg_p2293
theorem BSD_Hasse_OPEN_p2297 : BSD_Hasse_OPEN 2297 :=
  BSD_hasse_of_degree_nonneg 2297 BSD_DegreeNonneg_p2297
theorem BSD_Hasse_OPEN_p2309 : BSD_Hasse_OPEN 2309 :=
  BSD_hasse_of_degree_nonneg 2309 BSD_DegreeNonneg_p2309
theorem BSD_Hasse_OPEN_p2311 : BSD_Hasse_OPEN 2311 :=
  BSD_hasse_of_degree_nonneg 2311 BSD_DegreeNonneg_p2311
theorem BSD_Hasse_OPEN_p2333 : BSD_Hasse_OPEN 2333 :=
  BSD_hasse_of_degree_nonneg 2333 BSD_DegreeNonneg_p2333
theorem BSD_Hasse_OPEN_p2339 : BSD_Hasse_OPEN 2339 :=
  BSD_hasse_of_degree_nonneg 2339 BSD_DegreeNonneg_p2339
theorem BSD_Hasse_OPEN_p2341 : BSD_Hasse_OPEN 2341 :=
  BSD_hasse_of_degree_nonneg 2341 BSD_DegreeNonneg_p2341
theorem BSD_Hasse_OPEN_p2347 : BSD_Hasse_OPEN 2347 :=
  BSD_hasse_of_degree_nonneg 2347 BSD_DegreeNonneg_p2347

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2281 : (a_p 2281 : ℝ) ^ 2 ≤ 4 * (2281 : ℝ) :=
  BSD_disc_from_deg_800 BSD_DegreeNonneg_p2281
theorem BSD_HasseBound_Disc_p2287 : (a_p 2287 : ℝ) ^ 2 ≤ 4 * (2287 : ℝ) :=
  BSD_disc_from_deg_800 BSD_DegreeNonneg_p2287
theorem BSD_HasseBound_Disc_p2293 : (a_p 2293 : ℝ) ^ 2 ≤ 4 * (2293 : ℝ) :=
  BSD_disc_from_deg_800 BSD_DegreeNonneg_p2293
theorem BSD_HasseBound_Disc_p2297 : (a_p 2297 : ℝ) ^ 2 ≤ 4 * (2297 : ℝ) :=
  BSD_disc_from_deg_800 BSD_DegreeNonneg_p2297
theorem BSD_HasseBound_Disc_p2309 : (a_p 2309 : ℝ) ^ 2 ≤ 4 * (2309 : ℝ) :=
  BSD_disc_from_deg_800 BSD_DegreeNonneg_p2309
theorem BSD_HasseBound_Disc_p2311 : (a_p 2311 : ℝ) ^ 2 ≤ 4 * (2311 : ℝ) :=
  BSD_disc_from_deg_800 BSD_DegreeNonneg_p2311
theorem BSD_HasseBound_Disc_p2333 : (a_p 2333 : ℝ) ^ 2 ≤ 4 * (2333 : ℝ) :=
  BSD_disc_from_deg_800 BSD_DegreeNonneg_p2333
theorem BSD_HasseBound_Disc_p2339 : (a_p 2339 : ℝ) ^ 2 ≤ 4 * (2339 : ℝ) :=
  BSD_disc_from_deg_800 BSD_DegreeNonneg_p2339
theorem BSD_HasseBound_Disc_p2341 : (a_p 2341 : ℝ) ^ 2 ≤ 4 * (2341 : ℝ) :=
  BSD_disc_from_deg_800 BSD_DegreeNonneg_p2341
theorem BSD_HasseBound_Disc_p2347 : (a_p 2347 : ℝ) ^ 2 ≤ 4 * (2347 : ℝ) :=
  BSD_disc_from_deg_800 BSD_DegreeNonneg_p2347

end Towers.BSD
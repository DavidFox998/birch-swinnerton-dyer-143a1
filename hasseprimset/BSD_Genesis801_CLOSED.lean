/-
================================================================
Towers / BSD / BSD_Genesis801_CLOSED  (genesis-801)

HasseBridge Tier C: Hasse bounds for primes
2351..2411 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2351: card=2298, a_p=+54, disc=-6488
  p=2357: card=2291, a_p=+67, disc=-4939
  p=2371: card=2342, a_p=+30, disc=-8584
  p=2377: card=2409, a_p=-31, disc=-8547
  p=2381: card=2424, a_p=-42, disc=-7760
  p=2383: card=2392, a_p=-8, disc=-9468
  p=2389: card=2366, a_p=+24, disc=-8980
  p=2393: card=2446, a_p=-52, disc=-6868
  p=2399: card=2473, a_p=-73, disc=-4267
  p=2411: card=2400, a_p=+12, disc=-9500

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_801 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i801_p2351 : Fact (2351 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2357 : Fact (2357 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2371 : Fact (2371 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2377 : Fact (2377 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2381 : Fact (2381 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2383 : Fact (2383 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2389 : Fact (2389 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2393 : Fact (2393 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2399 : Fact (2399 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2411 : Fact (2411 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2351 : (E143_Finset 2351).card = 2298 := by native_decide
theorem BSD_E143_card_p2357 : (E143_Finset 2357).card = 2291 := by native_decide
theorem BSD_E143_card_p2371 : (E143_Finset 2371).card = 2342 := by native_decide
theorem BSD_E143_card_p2377 : (E143_Finset 2377).card = 2409 := by native_decide
theorem BSD_E143_card_p2381 : (E143_Finset 2381).card = 2424 := by native_decide
theorem BSD_E143_card_p2383 : (E143_Finset 2383).card = 2392 := by native_decide
theorem BSD_E143_card_p2389 : (E143_Finset 2389).card = 2366 := by native_decide
theorem BSD_E143_card_p2393 : (E143_Finset 2393).card = 2446 := by native_decide
theorem BSD_E143_card_p2399 : (E143_Finset 2399).card = 2473 := by native_decide
theorem BSD_E143_card_p2411 : (E143_Finset 2411).card = 2400 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2351 : a_p 2351 = (54 : ℤ) := by
  have h := BSD_E143_card_p2351; unfold a_p; omega
theorem BSD_ap_p2357 : a_p 2357 = (67 : ℤ) := by
  have h := BSD_E143_card_p2357; unfold a_p; omega
theorem BSD_ap_p2371 : a_p 2371 = (30 : ℤ) := by
  have h := BSD_E143_card_p2371; unfold a_p; omega
theorem BSD_ap_p2377 : a_p 2377 = (-31 : ℤ) := by
  have h := BSD_E143_card_p2377; unfold a_p; omega
theorem BSD_ap_p2381 : a_p 2381 = (-42 : ℤ) := by
  have h := BSD_E143_card_p2381; unfold a_p; omega
theorem BSD_ap_p2383 : a_p 2383 = (-8 : ℤ) := by
  have h := BSD_E143_card_p2383; unfold a_p; omega
theorem BSD_ap_p2389 : a_p 2389 = (24 : ℤ) := by
  have h := BSD_E143_card_p2389; unfold a_p; omega
theorem BSD_ap_p2393 : a_p 2393 = (-52 : ℤ) := by
  have h := BSD_E143_card_p2393; unfold a_p; omega
theorem BSD_ap_p2399 : a_p 2399 = (-73 : ℤ) := by
  have h := BSD_E143_card_p2399; unfold a_p; omega
theorem BSD_ap_p2411 : a_p 2411 = (12 : ℤ) := by
  have h := BSD_E143_card_p2411; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2351: a_p=+54, 4p-a_p²=6488
theorem BSD_DegreeNonneg_p2351 : BSD_FrobeniusDegreeNonneg_OPEN 2351 := fun r => by
  have hap : (a_p 2351 : ℝ) = 54 := by exact_mod_cast BSD_ap_p2351
  have key : r ^ 2 - (a_p 2351 : ℝ) * r + ((2351 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 6488/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

-- p=2357: a_p=+67, 4p-a_p²=4939
theorem BSD_DegreeNonneg_p2357 : BSD_FrobeniusDegreeNonneg_OPEN 2357 := fun r => by
  have hap : (a_p 2357 : ℝ) = 67 := by exact_mod_cast BSD_ap_p2357
  have key : r ^ 2 - (a_p 2357 : ℝ) * r + ((2357 : ℕ) : ℝ) =
      (r - 67/2) ^ 2 + 4939/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (67 : ℝ)/2)]

-- p=2371: a_p=+30, 4p-a_p²=8584
theorem BSD_DegreeNonneg_p2371 : BSD_FrobeniusDegreeNonneg_OPEN 2371 := fun r => by
  have hap : (a_p 2371 : ℝ) = 30 := by exact_mod_cast BSD_ap_p2371
  have key : r ^ 2 - (a_p 2371 : ℝ) * r + ((2371 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 8584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

-- p=2377: a_p=-31, 4p-a_p²=8547
theorem BSD_DegreeNonneg_p2377 : BSD_FrobeniusDegreeNonneg_OPEN 2377 := fun r => by
  have hap : (a_p 2377 : ℝ) = -31 := by exact_mod_cast BSD_ap_p2377
  have key : r ^ 2 - (a_p 2377 : ℝ) * r + ((2377 : ℕ) : ℝ) =
      (r + 31/2) ^ 2 + 8547/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (31 : ℝ)/2)]

-- p=2381: a_p=-42, 4p-a_p²=7760
theorem BSD_DegreeNonneg_p2381 : BSD_FrobeniusDegreeNonneg_OPEN 2381 := fun r => by
  have hap : (a_p 2381 : ℝ) = -42 := by exact_mod_cast BSD_ap_p2381
  have key : r ^ 2 - (a_p 2381 : ℝ) * r + ((2381 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 7760/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

-- p=2383: a_p=-8, 4p-a_p²=9468
theorem BSD_DegreeNonneg_p2383 : BSD_FrobeniusDegreeNonneg_OPEN 2383 := fun r => by
  have hap : (a_p 2383 : ℝ) = -8 := by exact_mod_cast BSD_ap_p2383
  have key : r ^ 2 - (a_p 2383 : ℝ) * r + ((2383 : ℕ) : ℝ) =
      (r + 8/2) ^ 2 + 9468/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (8 : ℝ)/2)]

-- p=2389: a_p=+24, 4p-a_p²=8980
theorem BSD_DegreeNonneg_p2389 : BSD_FrobeniusDegreeNonneg_OPEN 2389 := fun r => by
  have hap : (a_p 2389 : ℝ) = 24 := by exact_mod_cast BSD_ap_p2389
  have key : r ^ 2 - (a_p 2389 : ℝ) * r + ((2389 : ℕ) : ℝ) =
      (r - 24/2) ^ 2 + 8980/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (24 : ℝ)/2)]

-- p=2393: a_p=-52, 4p-a_p²=6868
theorem BSD_DegreeNonneg_p2393 : BSD_FrobeniusDegreeNonneg_OPEN 2393 := fun r => by
  have hap : (a_p 2393 : ℝ) = -52 := by exact_mod_cast BSD_ap_p2393
  have key : r ^ 2 - (a_p 2393 : ℝ) * r + ((2393 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 6868/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

-- p=2399: a_p=-73, 4p-a_p²=4267
theorem BSD_DegreeNonneg_p2399 : BSD_FrobeniusDegreeNonneg_OPEN 2399 := fun r => by
  have hap : (a_p 2399 : ℝ) = -73 := by exact_mod_cast BSD_ap_p2399
  have key : r ^ 2 - (a_p 2399 : ℝ) * r + ((2399 : ℕ) : ℝ) =
      (r + 73/2) ^ 2 + 4267/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (73 : ℝ)/2)]

-- p=2411: a_p=+12, 4p-a_p²=9500
theorem BSD_DegreeNonneg_p2411 : BSD_FrobeniusDegreeNonneg_OPEN 2411 := fun r => by
  have hap : (a_p 2411 : ℝ) = 12 := by exact_mod_cast BSD_ap_p2411
  have key : r ^ 2 - (a_p 2411 : ℝ) * r + ((2411 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 9500/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2351 : BSD_Hasse_OPEN 2351 :=
  BSD_hasse_of_degree_nonneg 2351 BSD_DegreeNonneg_p2351
theorem BSD_Hasse_OPEN_p2357 : BSD_Hasse_OPEN 2357 :=
  BSD_hasse_of_degree_nonneg 2357 BSD_DegreeNonneg_p2357
theorem BSD_Hasse_OPEN_p2371 : BSD_Hasse_OPEN 2371 :=
  BSD_hasse_of_degree_nonneg 2371 BSD_DegreeNonneg_p2371
theorem BSD_Hasse_OPEN_p2377 : BSD_Hasse_OPEN 2377 :=
  BSD_hasse_of_degree_nonneg 2377 BSD_DegreeNonneg_p2377
theorem BSD_Hasse_OPEN_p2381 : BSD_Hasse_OPEN 2381 :=
  BSD_hasse_of_degree_nonneg 2381 BSD_DegreeNonneg_p2381
theorem BSD_Hasse_OPEN_p2383 : BSD_Hasse_OPEN 2383 :=
  BSD_hasse_of_degree_nonneg 2383 BSD_DegreeNonneg_p2383
theorem BSD_Hasse_OPEN_p2389 : BSD_Hasse_OPEN 2389 :=
  BSD_hasse_of_degree_nonneg 2389 BSD_DegreeNonneg_p2389
theorem BSD_Hasse_OPEN_p2393 : BSD_Hasse_OPEN 2393 :=
  BSD_hasse_of_degree_nonneg 2393 BSD_DegreeNonneg_p2393
theorem BSD_Hasse_OPEN_p2399 : BSD_Hasse_OPEN 2399 :=
  BSD_hasse_of_degree_nonneg 2399 BSD_DegreeNonneg_p2399
theorem BSD_Hasse_OPEN_p2411 : BSD_Hasse_OPEN 2411 :=
  BSD_hasse_of_degree_nonneg 2411 BSD_DegreeNonneg_p2411

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2351 : (a_p 2351 : ℝ) ^ 2 ≤ 4 * (2351 : ℝ) :=
  BSD_disc_from_deg_801 BSD_DegreeNonneg_p2351
theorem BSD_HasseBound_Disc_p2357 : (a_p 2357 : ℝ) ^ 2 ≤ 4 * (2357 : ℝ) :=
  BSD_disc_from_deg_801 BSD_DegreeNonneg_p2357
theorem BSD_HasseBound_Disc_p2371 : (a_p 2371 : ℝ) ^ 2 ≤ 4 * (2371 : ℝ) :=
  BSD_disc_from_deg_801 BSD_DegreeNonneg_p2371
theorem BSD_HasseBound_Disc_p2377 : (a_p 2377 : ℝ) ^ 2 ≤ 4 * (2377 : ℝ) :=
  BSD_disc_from_deg_801 BSD_DegreeNonneg_p2377
theorem BSD_HasseBound_Disc_p2381 : (a_p 2381 : ℝ) ^ 2 ≤ 4 * (2381 : ℝ) :=
  BSD_disc_from_deg_801 BSD_DegreeNonneg_p2381
theorem BSD_HasseBound_Disc_p2383 : (a_p 2383 : ℝ) ^ 2 ≤ 4 * (2383 : ℝ) :=
  BSD_disc_from_deg_801 BSD_DegreeNonneg_p2383
theorem BSD_HasseBound_Disc_p2389 : (a_p 2389 : ℝ) ^ 2 ≤ 4 * (2389 : ℝ) :=
  BSD_disc_from_deg_801 BSD_DegreeNonneg_p2389
theorem BSD_HasseBound_Disc_p2393 : (a_p 2393 : ℝ) ^ 2 ≤ 4 * (2393 : ℝ) :=
  BSD_disc_from_deg_801 BSD_DegreeNonneg_p2393
theorem BSD_HasseBound_Disc_p2399 : (a_p 2399 : ℝ) ^ 2 ≤ 4 * (2399 : ℝ) :=
  BSD_disc_from_deg_801 BSD_DegreeNonneg_p2399
theorem BSD_HasseBound_Disc_p2411 : (a_p 2411 : ℝ) ^ 2 ≤ 4 * (2411 : ℝ) :=
  BSD_disc_from_deg_801 BSD_DegreeNonneg_p2411

end Towers.BSD
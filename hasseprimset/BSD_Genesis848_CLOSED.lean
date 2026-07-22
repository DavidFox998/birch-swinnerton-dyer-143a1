/-
================================================================
Towers / BSD / BSD_Genesis848_CLOSED  (genesis-848)

HasseBridge Tier C: Hasse bounds for primes
6299..6359 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=6299: card=6270, a_p=+30, disc=-24296
  p=6301: card=6293, a_p=+9, disc=-25123
  p=6311: card=6384, a_p=-72, disc=-20060
  p=6317: card=6381, a_p=-63, disc=-21299
  p=6323: card=6285, a_p=+39, disc=-23771
  p=6329: card=6308, a_p=+22, disc=-24832
  p=6337: card=6404, a_p=-66, disc=-20992
  p=6343: card=6440, a_p=-96, disc=-16156
  p=6353: card=6384, a_p=-30, disc=-24512
  p=6359: card=6480, a_p=-120, disc=-11036

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_848 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i848_p6299 : Fact (6299 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6301 : Fact (6301 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6311 : Fact (6311 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6317 : Fact (6317 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6323 : Fact (6323 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6329 : Fact (6329 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6337 : Fact (6337 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6343 : Fact (6343 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6353 : Fact (6353 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6359 : Fact (6359 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p6299 : (E143_Finset 6299).card = 6270 := by native_decide
theorem BSD_E143_card_p6301 : (E143_Finset 6301).card = 6293 := by native_decide
theorem BSD_E143_card_p6311 : (E143_Finset 6311).card = 6384 := by native_decide
theorem BSD_E143_card_p6317 : (E143_Finset 6317).card = 6381 := by native_decide
theorem BSD_E143_card_p6323 : (E143_Finset 6323).card = 6285 := by native_decide
theorem BSD_E143_card_p6329 : (E143_Finset 6329).card = 6308 := by native_decide
theorem BSD_E143_card_p6337 : (E143_Finset 6337).card = 6404 := by native_decide
theorem BSD_E143_card_p6343 : (E143_Finset 6343).card = 6440 := by native_decide
theorem BSD_E143_card_p6353 : (E143_Finset 6353).card = 6384 := by native_decide
theorem BSD_E143_card_p6359 : (E143_Finset 6359).card = 6480 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p6299 : a_p 6299 = (30 : ℤ) := by
  have h := BSD_E143_card_p6299; unfold a_p; omega
theorem BSD_ap_p6301 : a_p 6301 = (9 : ℤ) := by
  have h := BSD_E143_card_p6301; unfold a_p; omega
theorem BSD_ap_p6311 : a_p 6311 = (-72 : ℤ) := by
  have h := BSD_E143_card_p6311; unfold a_p; omega
theorem BSD_ap_p6317 : a_p 6317 = (-63 : ℤ) := by
  have h := BSD_E143_card_p6317; unfold a_p; omega
theorem BSD_ap_p6323 : a_p 6323 = (39 : ℤ) := by
  have h := BSD_E143_card_p6323; unfold a_p; omega
theorem BSD_ap_p6329 : a_p 6329 = (22 : ℤ) := by
  have h := BSD_E143_card_p6329; unfold a_p; omega
theorem BSD_ap_p6337 : a_p 6337 = (-66 : ℤ) := by
  have h := BSD_E143_card_p6337; unfold a_p; omega
theorem BSD_ap_p6343 : a_p 6343 = (-96 : ℤ) := by
  have h := BSD_E143_card_p6343; unfold a_p; omega
theorem BSD_ap_p6353 : a_p 6353 = (-30 : ℤ) := by
  have h := BSD_E143_card_p6353; unfold a_p; omega
theorem BSD_ap_p6359 : a_p 6359 = (-120 : ℤ) := by
  have h := BSD_E143_card_p6359; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=6299: a_p=+30, 4p-a_p²=24296
theorem BSD_DegreeNonneg_p6299 : BSD_FrobeniusDegreeNonneg_OPEN 6299 := fun r => by
  have hap : (a_p 6299 : ℝ) = 30 := by exact_mod_cast BSD_ap_p6299
  have key : r ^ 2 - (a_p 6299 : ℝ) * r + ((6299 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 24296/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

-- p=6301: a_p=+9, 4p-a_p²=25123
theorem BSD_DegreeNonneg_p6301 : BSD_FrobeniusDegreeNonneg_OPEN 6301 := fun r => by
  have hap : (a_p 6301 : ℝ) = 9 := by exact_mod_cast BSD_ap_p6301
  have key : r ^ 2 - (a_p 6301 : ℝ) * r + ((6301 : ℕ) : ℝ) =
      (r - 9/2) ^ 2 + 25123/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (9 : ℝ)/2)]

-- p=6311: a_p=-72, 4p-a_p²=20060
theorem BSD_DegreeNonneg_p6311 : BSD_FrobeniusDegreeNonneg_OPEN 6311 := fun r => by
  have hap : (a_p 6311 : ℝ) = -72 := by exact_mod_cast BSD_ap_p6311
  have key : r ^ 2 - (a_p 6311 : ℝ) * r + ((6311 : ℕ) : ℝ) =
      (r + 72/2) ^ 2 + 20060/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (72 : ℝ)/2)]

-- p=6317: a_p=-63, 4p-a_p²=21299
theorem BSD_DegreeNonneg_p6317 : BSD_FrobeniusDegreeNonneg_OPEN 6317 := fun r => by
  have hap : (a_p 6317 : ℝ) = -63 := by exact_mod_cast BSD_ap_p6317
  have key : r ^ 2 - (a_p 6317 : ℝ) * r + ((6317 : ℕ) : ℝ) =
      (r + 63/2) ^ 2 + 21299/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (63 : ℝ)/2)]

-- p=6323: a_p=+39, 4p-a_p²=23771
theorem BSD_DegreeNonneg_p6323 : BSD_FrobeniusDegreeNonneg_OPEN 6323 := fun r => by
  have hap : (a_p 6323 : ℝ) = 39 := by exact_mod_cast BSD_ap_p6323
  have key : r ^ 2 - (a_p 6323 : ℝ) * r + ((6323 : ℕ) : ℝ) =
      (r - 39/2) ^ 2 + 23771/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (39 : ℝ)/2)]

-- p=6329: a_p=+22, 4p-a_p²=24832
theorem BSD_DegreeNonneg_p6329 : BSD_FrobeniusDegreeNonneg_OPEN 6329 := fun r => by
  have hap : (a_p 6329 : ℝ) = 22 := by exact_mod_cast BSD_ap_p6329
  have key : r ^ 2 - (a_p 6329 : ℝ) * r + ((6329 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 24832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

-- p=6337: a_p=-66, 4p-a_p²=20992
theorem BSD_DegreeNonneg_p6337 : BSD_FrobeniusDegreeNonneg_OPEN 6337 := fun r => by
  have hap : (a_p 6337 : ℝ) = -66 := by exact_mod_cast BSD_ap_p6337
  have key : r ^ 2 - (a_p 6337 : ℝ) * r + ((6337 : ℕ) : ℝ) =
      (r + 66/2) ^ 2 + 20992/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (66 : ℝ)/2)]

-- p=6343: a_p=-96, 4p-a_p²=16156
theorem BSD_DegreeNonneg_p6343 : BSD_FrobeniusDegreeNonneg_OPEN 6343 := fun r => by
  have hap : (a_p 6343 : ℝ) = -96 := by exact_mod_cast BSD_ap_p6343
  have key : r ^ 2 - (a_p 6343 : ℝ) * r + ((6343 : ℕ) : ℝ) =
      (r + 96/2) ^ 2 + 16156/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (96 : ℝ)/2)]

-- p=6353: a_p=-30, 4p-a_p²=24512
theorem BSD_DegreeNonneg_p6353 : BSD_FrobeniusDegreeNonneg_OPEN 6353 := fun r => by
  have hap : (a_p 6353 : ℝ) = -30 := by exact_mod_cast BSD_ap_p6353
  have key : r ^ 2 - (a_p 6353 : ℝ) * r + ((6353 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 24512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

-- p=6359: a_p=-120, 4p-a_p²=11036
theorem BSD_DegreeNonneg_p6359 : BSD_FrobeniusDegreeNonneg_OPEN 6359 := fun r => by
  have hap : (a_p 6359 : ℝ) = -120 := by exact_mod_cast BSD_ap_p6359
  have key : r ^ 2 - (a_p 6359 : ℝ) * r + ((6359 : ℕ) : ℝ) =
      (r + 120/2) ^ 2 + 11036/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (120 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p6299 : BSD_Hasse_OPEN 6299 :=
  BSD_hasse_of_degree_nonneg 6299 BSD_DegreeNonneg_p6299
theorem BSD_Hasse_OPEN_p6301 : BSD_Hasse_OPEN 6301 :=
  BSD_hasse_of_degree_nonneg 6301 BSD_DegreeNonneg_p6301
theorem BSD_Hasse_OPEN_p6311 : BSD_Hasse_OPEN 6311 :=
  BSD_hasse_of_degree_nonneg 6311 BSD_DegreeNonneg_p6311
theorem BSD_Hasse_OPEN_p6317 : BSD_Hasse_OPEN 6317 :=
  BSD_hasse_of_degree_nonneg 6317 BSD_DegreeNonneg_p6317
theorem BSD_Hasse_OPEN_p6323 : BSD_Hasse_OPEN 6323 :=
  BSD_hasse_of_degree_nonneg 6323 BSD_DegreeNonneg_p6323
theorem BSD_Hasse_OPEN_p6329 : BSD_Hasse_OPEN 6329 :=
  BSD_hasse_of_degree_nonneg 6329 BSD_DegreeNonneg_p6329
theorem BSD_Hasse_OPEN_p6337 : BSD_Hasse_OPEN 6337 :=
  BSD_hasse_of_degree_nonneg 6337 BSD_DegreeNonneg_p6337
theorem BSD_Hasse_OPEN_p6343 : BSD_Hasse_OPEN 6343 :=
  BSD_hasse_of_degree_nonneg 6343 BSD_DegreeNonneg_p6343
theorem BSD_Hasse_OPEN_p6353 : BSD_Hasse_OPEN 6353 :=
  BSD_hasse_of_degree_nonneg 6353 BSD_DegreeNonneg_p6353
theorem BSD_Hasse_OPEN_p6359 : BSD_Hasse_OPEN 6359 :=
  BSD_hasse_of_degree_nonneg 6359 BSD_DegreeNonneg_p6359

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p6299 : (a_p 6299 : ℝ) ^ 2 ≤ 4 * (6299 : ℝ) :=
  BSD_disc_from_deg_848 BSD_DegreeNonneg_p6299
theorem BSD_HasseBound_Disc_p6301 : (a_p 6301 : ℝ) ^ 2 ≤ 4 * (6301 : ℝ) :=
  BSD_disc_from_deg_848 BSD_DegreeNonneg_p6301
theorem BSD_HasseBound_Disc_p6311 : (a_p 6311 : ℝ) ^ 2 ≤ 4 * (6311 : ℝ) :=
  BSD_disc_from_deg_848 BSD_DegreeNonneg_p6311
theorem BSD_HasseBound_Disc_p6317 : (a_p 6317 : ℝ) ^ 2 ≤ 4 * (6317 : ℝ) :=
  BSD_disc_from_deg_848 BSD_DegreeNonneg_p6317
theorem BSD_HasseBound_Disc_p6323 : (a_p 6323 : ℝ) ^ 2 ≤ 4 * (6323 : ℝ) :=
  BSD_disc_from_deg_848 BSD_DegreeNonneg_p6323
theorem BSD_HasseBound_Disc_p6329 : (a_p 6329 : ℝ) ^ 2 ≤ 4 * (6329 : ℝ) :=
  BSD_disc_from_deg_848 BSD_DegreeNonneg_p6329
theorem BSD_HasseBound_Disc_p6337 : (a_p 6337 : ℝ) ^ 2 ≤ 4 * (6337 : ℝ) :=
  BSD_disc_from_deg_848 BSD_DegreeNonneg_p6337
theorem BSD_HasseBound_Disc_p6343 : (a_p 6343 : ℝ) ^ 2 ≤ 4 * (6343 : ℝ) :=
  BSD_disc_from_deg_848 BSD_DegreeNonneg_p6343
theorem BSD_HasseBound_Disc_p6353 : (a_p 6353 : ℝ) ^ 2 ≤ 4 * (6353 : ℝ) :=
  BSD_disc_from_deg_848 BSD_DegreeNonneg_p6353
theorem BSD_HasseBound_Disc_p6359 : (a_p 6359 : ℝ) ^ 2 ≤ 4 * (6359 : ℝ) :=
  BSD_disc_from_deg_848 BSD_DegreeNonneg_p6359

end Towers.BSD
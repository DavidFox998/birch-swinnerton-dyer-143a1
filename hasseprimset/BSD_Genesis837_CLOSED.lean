/-
================================================================
Towers / BSD / BSD_Genesis837_CLOSED  (genesis-837)

HasseBridge Tier C: Hasse bounds for primes
5381..5437 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=5381: card=5370, a_p=+12, disc=-21380
  p=5387: card=5408, a_p=-20, disc=-21148
  p=5393: card=5415, a_p=-21, disc=-21131
  p=5399: card=5267, a_p=+133, disc=-3907
  p=5407: card=5530, a_p=-122, disc=-6744
  p=5413: card=5436, a_p=-22, disc=-21168
  p=5417: card=5340, a_p=+78, disc=-15584
  p=5419: card=5460, a_p=-40, disc=-20076
  p=5431: card=5412, a_p=+20, disc=-21324
  p=5437: card=5444, a_p=-6, disc=-21712

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_837 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i837_p5381 : Fact (5381 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5387 : Fact (5387 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5393 : Fact (5393 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5399 : Fact (5399 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5407 : Fact (5407 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5413 : Fact (5413 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5417 : Fact (5417 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5419 : Fact (5419 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5431 : Fact (5431 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5437 : Fact (5437 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p5381 : (E143_Finset 5381).card = 5370 := by native_decide
theorem BSD_E143_card_p5387 : (E143_Finset 5387).card = 5408 := by native_decide
theorem BSD_E143_card_p5393 : (E143_Finset 5393).card = 5415 := by native_decide
theorem BSD_E143_card_p5399 : (E143_Finset 5399).card = 5267 := by native_decide
theorem BSD_E143_card_p5407 : (E143_Finset 5407).card = 5530 := by native_decide
theorem BSD_E143_card_p5413 : (E143_Finset 5413).card = 5436 := by native_decide
theorem BSD_E143_card_p5417 : (E143_Finset 5417).card = 5340 := by native_decide
theorem BSD_E143_card_p5419 : (E143_Finset 5419).card = 5460 := by native_decide
theorem BSD_E143_card_p5431 : (E143_Finset 5431).card = 5412 := by native_decide
theorem BSD_E143_card_p5437 : (E143_Finset 5437).card = 5444 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p5381 : a_p 5381 = (12 : ℤ) := by
  have h := BSD_E143_card_p5381; unfold a_p; omega
theorem BSD_ap_p5387 : a_p 5387 = (-20 : ℤ) := by
  have h := BSD_E143_card_p5387; unfold a_p; omega
theorem BSD_ap_p5393 : a_p 5393 = (-21 : ℤ) := by
  have h := BSD_E143_card_p5393; unfold a_p; omega
theorem BSD_ap_p5399 : a_p 5399 = (133 : ℤ) := by
  have h := BSD_E143_card_p5399; unfold a_p; omega
theorem BSD_ap_p5407 : a_p 5407 = (-122 : ℤ) := by
  have h := BSD_E143_card_p5407; unfold a_p; omega
theorem BSD_ap_p5413 : a_p 5413 = (-22 : ℤ) := by
  have h := BSD_E143_card_p5413; unfold a_p; omega
theorem BSD_ap_p5417 : a_p 5417 = (78 : ℤ) := by
  have h := BSD_E143_card_p5417; unfold a_p; omega
theorem BSD_ap_p5419 : a_p 5419 = (-40 : ℤ) := by
  have h := BSD_E143_card_p5419; unfold a_p; omega
theorem BSD_ap_p5431 : a_p 5431 = (20 : ℤ) := by
  have h := BSD_E143_card_p5431; unfold a_p; omega
theorem BSD_ap_p5437 : a_p 5437 = (-6 : ℤ) := by
  have h := BSD_E143_card_p5437; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=5381: a_p=+12, 4p-a_p²=21380
theorem BSD_DegreeNonneg_p5381 : BSD_FrobeniusDegreeNonneg_OPEN 5381 := fun r => by
  have hap : (a_p 5381 : ℝ) = 12 := by exact_mod_cast BSD_ap_p5381
  have key : r ^ 2 - (a_p 5381 : ℝ) * r + ((5381 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 21380/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

-- p=5387: a_p=-20, 4p-a_p²=21148
theorem BSD_DegreeNonneg_p5387 : BSD_FrobeniusDegreeNonneg_OPEN 5387 := fun r => by
  have hap : (a_p 5387 : ℝ) = -20 := by exact_mod_cast BSD_ap_p5387
  have key : r ^ 2 - (a_p 5387 : ℝ) * r + ((5387 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 21148/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=5393: a_p=-21, 4p-a_p²=21131
theorem BSD_DegreeNonneg_p5393 : BSD_FrobeniusDegreeNonneg_OPEN 5393 := fun r => by
  have hap : (a_p 5393 : ℝ) = -21 := by exact_mod_cast BSD_ap_p5393
  have key : r ^ 2 - (a_p 5393 : ℝ) * r + ((5393 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 21131/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

-- p=5399: a_p=+133, 4p-a_p²=3907
theorem BSD_DegreeNonneg_p5399 : BSD_FrobeniusDegreeNonneg_OPEN 5399 := fun r => by
  have hap : (a_p 5399 : ℝ) = 133 := by exact_mod_cast BSD_ap_p5399
  have key : r ^ 2 - (a_p 5399 : ℝ) * r + ((5399 : ℕ) : ℝ) =
      (r - 133/2) ^ 2 + 3907/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (133 : ℝ)/2)]

-- p=5407: a_p=-122, 4p-a_p²=6744
theorem BSD_DegreeNonneg_p5407 : BSD_FrobeniusDegreeNonneg_OPEN 5407 := fun r => by
  have hap : (a_p 5407 : ℝ) = -122 := by exact_mod_cast BSD_ap_p5407
  have key : r ^ 2 - (a_p 5407 : ℝ) * r + ((5407 : ℕ) : ℝ) =
      (r + 122/2) ^ 2 + 6744/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (122 : ℝ)/2)]

-- p=5413: a_p=-22, 4p-a_p²=21168
theorem BSD_DegreeNonneg_p5413 : BSD_FrobeniusDegreeNonneg_OPEN 5413 := fun r => by
  have hap : (a_p 5413 : ℝ) = -22 := by exact_mod_cast BSD_ap_p5413
  have key : r ^ 2 - (a_p 5413 : ℝ) * r + ((5413 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 21168/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

-- p=5417: a_p=+78, 4p-a_p²=15584
theorem BSD_DegreeNonneg_p5417 : BSD_FrobeniusDegreeNonneg_OPEN 5417 := fun r => by
  have hap : (a_p 5417 : ℝ) = 78 := by exact_mod_cast BSD_ap_p5417
  have key : r ^ 2 - (a_p 5417 : ℝ) * r + ((5417 : ℕ) : ℝ) =
      (r - 78/2) ^ 2 + 15584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (78 : ℝ)/2)]

-- p=5419: a_p=-40, 4p-a_p²=20076
theorem BSD_DegreeNonneg_p5419 : BSD_FrobeniusDegreeNonneg_OPEN 5419 := fun r => by
  have hap : (a_p 5419 : ℝ) = -40 := by exact_mod_cast BSD_ap_p5419
  have key : r ^ 2 - (a_p 5419 : ℝ) * r + ((5419 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 20076/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

-- p=5431: a_p=+20, 4p-a_p²=21324
theorem BSD_DegreeNonneg_p5431 : BSD_FrobeniusDegreeNonneg_OPEN 5431 := fun r => by
  have hap : (a_p 5431 : ℝ) = 20 := by exact_mod_cast BSD_ap_p5431
  have key : r ^ 2 - (a_p 5431 : ℝ) * r + ((5431 : ℕ) : ℝ) =
      (r - 20/2) ^ 2 + 21324/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (20 : ℝ)/2)]

-- p=5437: a_p=-6, 4p-a_p²=21712
theorem BSD_DegreeNonneg_p5437 : BSD_FrobeniusDegreeNonneg_OPEN 5437 := fun r => by
  have hap : (a_p 5437 : ℝ) = -6 := by exact_mod_cast BSD_ap_p5437
  have key : r ^ 2 - (a_p 5437 : ℝ) * r + ((5437 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 21712/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p5381 : BSD_Hasse_OPEN 5381 :=
  BSD_hasse_of_degree_nonneg 5381 BSD_DegreeNonneg_p5381
theorem BSD_Hasse_OPEN_p5387 : BSD_Hasse_OPEN 5387 :=
  BSD_hasse_of_degree_nonneg 5387 BSD_DegreeNonneg_p5387
theorem BSD_Hasse_OPEN_p5393 : BSD_Hasse_OPEN 5393 :=
  BSD_hasse_of_degree_nonneg 5393 BSD_DegreeNonneg_p5393
theorem BSD_Hasse_OPEN_p5399 : BSD_Hasse_OPEN 5399 :=
  BSD_hasse_of_degree_nonneg 5399 BSD_DegreeNonneg_p5399
theorem BSD_Hasse_OPEN_p5407 : BSD_Hasse_OPEN 5407 :=
  BSD_hasse_of_degree_nonneg 5407 BSD_DegreeNonneg_p5407
theorem BSD_Hasse_OPEN_p5413 : BSD_Hasse_OPEN 5413 :=
  BSD_hasse_of_degree_nonneg 5413 BSD_DegreeNonneg_p5413
theorem BSD_Hasse_OPEN_p5417 : BSD_Hasse_OPEN 5417 :=
  BSD_hasse_of_degree_nonneg 5417 BSD_DegreeNonneg_p5417
theorem BSD_Hasse_OPEN_p5419 : BSD_Hasse_OPEN 5419 :=
  BSD_hasse_of_degree_nonneg 5419 BSD_DegreeNonneg_p5419
theorem BSD_Hasse_OPEN_p5431 : BSD_Hasse_OPEN 5431 :=
  BSD_hasse_of_degree_nonneg 5431 BSD_DegreeNonneg_p5431
theorem BSD_Hasse_OPEN_p5437 : BSD_Hasse_OPEN 5437 :=
  BSD_hasse_of_degree_nonneg 5437 BSD_DegreeNonneg_p5437

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p5381 : (a_p 5381 : ℝ) ^ 2 ≤ 4 * (5381 : ℝ) :=
  BSD_disc_from_deg_837 BSD_DegreeNonneg_p5381
theorem BSD_HasseBound_Disc_p5387 : (a_p 5387 : ℝ) ^ 2 ≤ 4 * (5387 : ℝ) :=
  BSD_disc_from_deg_837 BSD_DegreeNonneg_p5387
theorem BSD_HasseBound_Disc_p5393 : (a_p 5393 : ℝ) ^ 2 ≤ 4 * (5393 : ℝ) :=
  BSD_disc_from_deg_837 BSD_DegreeNonneg_p5393
theorem BSD_HasseBound_Disc_p5399 : (a_p 5399 : ℝ) ^ 2 ≤ 4 * (5399 : ℝ) :=
  BSD_disc_from_deg_837 BSD_DegreeNonneg_p5399
theorem BSD_HasseBound_Disc_p5407 : (a_p 5407 : ℝ) ^ 2 ≤ 4 * (5407 : ℝ) :=
  BSD_disc_from_deg_837 BSD_DegreeNonneg_p5407
theorem BSD_HasseBound_Disc_p5413 : (a_p 5413 : ℝ) ^ 2 ≤ 4 * (5413 : ℝ) :=
  BSD_disc_from_deg_837 BSD_DegreeNonneg_p5413
theorem BSD_HasseBound_Disc_p5417 : (a_p 5417 : ℝ) ^ 2 ≤ 4 * (5417 : ℝ) :=
  BSD_disc_from_deg_837 BSD_DegreeNonneg_p5417
theorem BSD_HasseBound_Disc_p5419 : (a_p 5419 : ℝ) ^ 2 ≤ 4 * (5419 : ℝ) :=
  BSD_disc_from_deg_837 BSD_DegreeNonneg_p5419
theorem BSD_HasseBound_Disc_p5431 : (a_p 5431 : ℝ) ^ 2 ≤ 4 * (5431 : ℝ) :=
  BSD_disc_from_deg_837 BSD_DegreeNonneg_p5431
theorem BSD_HasseBound_Disc_p5437 : (a_p 5437 : ℝ) ^ 2 ≤ 4 * (5437 : ℝ) :=
  BSD_disc_from_deg_837 BSD_DegreeNonneg_p5437

end Towers.BSD
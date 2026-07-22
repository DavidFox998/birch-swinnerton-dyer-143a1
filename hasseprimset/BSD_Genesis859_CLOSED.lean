/-
================================================================
Towers / BSD / BSD_Genesis859_CLOSED  (genesis-859)

HasseBridge Tier C: Hasse bounds for primes
7283..7369 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=7283: card=7313, a_p=-29, disc=-28291
  p=7297: card=7428, a_p=-130, disc=-12288
  p=7307: card=7463, a_p=-155, disc=-5203
  p=7309: card=7215, a_p=+95, disc=-20211
  p=7321: card=7384, a_p=-62, disc=-25440
  p=7331: card=7352, a_p=-20, disc=-28924
  p=7333: card=7350, a_p=-16, disc=-29076
  p=7349: card=7452, a_p=-102, disc=-18992
  p=7351: card=7240, a_p=+112, disc=-16860
  p=7369: card=7258, a_p=+112, disc=-16932

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_859 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i859_p7283 : Fact (7283 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7297 : Fact (7297 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7307 : Fact (7307 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7309 : Fact (7309 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7321 : Fact (7321 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7331 : Fact (7331 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7333 : Fact (7333 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7349 : Fact (7349 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7351 : Fact (7351 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7369 : Fact (7369 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p7283 : (E143_Finset 7283).card = 7313 := by native_decide
theorem BSD_E143_card_p7297 : (E143_Finset 7297).card = 7428 := by native_decide
theorem BSD_E143_card_p7307 : (E143_Finset 7307).card = 7463 := by native_decide
theorem BSD_E143_card_p7309 : (E143_Finset 7309).card = 7215 := by native_decide
theorem BSD_E143_card_p7321 : (E143_Finset 7321).card = 7384 := by native_decide
theorem BSD_E143_card_p7331 : (E143_Finset 7331).card = 7352 := by native_decide
theorem BSD_E143_card_p7333 : (E143_Finset 7333).card = 7350 := by native_decide
theorem BSD_E143_card_p7349 : (E143_Finset 7349).card = 7452 := by native_decide
theorem BSD_E143_card_p7351 : (E143_Finset 7351).card = 7240 := by native_decide
theorem BSD_E143_card_p7369 : (E143_Finset 7369).card = 7258 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p7283 : a_p 7283 = (-29 : ℤ) := by
  have h := BSD_E143_card_p7283; unfold a_p; omega
theorem BSD_ap_p7297 : a_p 7297 = (-130 : ℤ) := by
  have h := BSD_E143_card_p7297; unfold a_p; omega
theorem BSD_ap_p7307 : a_p 7307 = (-155 : ℤ) := by
  have h := BSD_E143_card_p7307; unfold a_p; omega
theorem BSD_ap_p7309 : a_p 7309 = (95 : ℤ) := by
  have h := BSD_E143_card_p7309; unfold a_p; omega
theorem BSD_ap_p7321 : a_p 7321 = (-62 : ℤ) := by
  have h := BSD_E143_card_p7321; unfold a_p; omega
theorem BSD_ap_p7331 : a_p 7331 = (-20 : ℤ) := by
  have h := BSD_E143_card_p7331; unfold a_p; omega
theorem BSD_ap_p7333 : a_p 7333 = (-16 : ℤ) := by
  have h := BSD_E143_card_p7333; unfold a_p; omega
theorem BSD_ap_p7349 : a_p 7349 = (-102 : ℤ) := by
  have h := BSD_E143_card_p7349; unfold a_p; omega
theorem BSD_ap_p7351 : a_p 7351 = (112 : ℤ) := by
  have h := BSD_E143_card_p7351; unfold a_p; omega
theorem BSD_ap_p7369 : a_p 7369 = (112 : ℤ) := by
  have h := BSD_E143_card_p7369; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=7283: a_p=-29, 4p-a_p²=28291
theorem BSD_DegreeNonneg_p7283 : BSD_FrobeniusDegreeNonneg_OPEN 7283 := fun r => by
  have hap : (a_p 7283 : ℝ) = -29 := by exact_mod_cast BSD_ap_p7283
  have key : r ^ 2 - (a_p 7283 : ℝ) * r + ((7283 : ℕ) : ℝ) =
      (r + 29/2) ^ 2 + 28291/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (29 : ℝ)/2)]

-- p=7297: a_p=-130, 4p-a_p²=12288
theorem BSD_DegreeNonneg_p7297 : BSD_FrobeniusDegreeNonneg_OPEN 7297 := fun r => by
  have hap : (a_p 7297 : ℝ) = -130 := by exact_mod_cast BSD_ap_p7297
  have key : r ^ 2 - (a_p 7297 : ℝ) * r + ((7297 : ℕ) : ℝ) =
      (r + 130/2) ^ 2 + 12288/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (130 : ℝ)/2)]

-- p=7307: a_p=-155, 4p-a_p²=5203
theorem BSD_DegreeNonneg_p7307 : BSD_FrobeniusDegreeNonneg_OPEN 7307 := fun r => by
  have hap : (a_p 7307 : ℝ) = -155 := by exact_mod_cast BSD_ap_p7307
  have key : r ^ 2 - (a_p 7307 : ℝ) * r + ((7307 : ℕ) : ℝ) =
      (r + 155/2) ^ 2 + 5203/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (155 : ℝ)/2)]

-- p=7309: a_p=+95, 4p-a_p²=20211
theorem BSD_DegreeNonneg_p7309 : BSD_FrobeniusDegreeNonneg_OPEN 7309 := fun r => by
  have hap : (a_p 7309 : ℝ) = 95 := by exact_mod_cast BSD_ap_p7309
  have key : r ^ 2 - (a_p 7309 : ℝ) * r + ((7309 : ℕ) : ℝ) =
      (r - 95/2) ^ 2 + 20211/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (95 : ℝ)/2)]

-- p=7321: a_p=-62, 4p-a_p²=25440
theorem BSD_DegreeNonneg_p7321 : BSD_FrobeniusDegreeNonneg_OPEN 7321 := fun r => by
  have hap : (a_p 7321 : ℝ) = -62 := by exact_mod_cast BSD_ap_p7321
  have key : r ^ 2 - (a_p 7321 : ℝ) * r + ((7321 : ℕ) : ℝ) =
      (r + 62/2) ^ 2 + 25440/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (62 : ℝ)/2)]

-- p=7331: a_p=-20, 4p-a_p²=28924
theorem BSD_DegreeNonneg_p7331 : BSD_FrobeniusDegreeNonneg_OPEN 7331 := fun r => by
  have hap : (a_p 7331 : ℝ) = -20 := by exact_mod_cast BSD_ap_p7331
  have key : r ^ 2 - (a_p 7331 : ℝ) * r + ((7331 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 28924/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=7333: a_p=-16, 4p-a_p²=29076
theorem BSD_DegreeNonneg_p7333 : BSD_FrobeniusDegreeNonneg_OPEN 7333 := fun r => by
  have hap : (a_p 7333 : ℝ) = -16 := by exact_mod_cast BSD_ap_p7333
  have key : r ^ 2 - (a_p 7333 : ℝ) * r + ((7333 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 29076/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

-- p=7349: a_p=-102, 4p-a_p²=18992
theorem BSD_DegreeNonneg_p7349 : BSD_FrobeniusDegreeNonneg_OPEN 7349 := fun r => by
  have hap : (a_p 7349 : ℝ) = -102 := by exact_mod_cast BSD_ap_p7349
  have key : r ^ 2 - (a_p 7349 : ℝ) * r + ((7349 : ℕ) : ℝ) =
      (r + 102/2) ^ 2 + 18992/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (102 : ℝ)/2)]

-- p=7351: a_p=+112, 4p-a_p²=16860
theorem BSD_DegreeNonneg_p7351 : BSD_FrobeniusDegreeNonneg_OPEN 7351 := fun r => by
  have hap : (a_p 7351 : ℝ) = 112 := by exact_mod_cast BSD_ap_p7351
  have key : r ^ 2 - (a_p 7351 : ℝ) * r + ((7351 : ℕ) : ℝ) =
      (r - 112/2) ^ 2 + 16860/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (112 : ℝ)/2)]

-- p=7369: a_p=+112, 4p-a_p²=16932
theorem BSD_DegreeNonneg_p7369 : BSD_FrobeniusDegreeNonneg_OPEN 7369 := fun r => by
  have hap : (a_p 7369 : ℝ) = 112 := by exact_mod_cast BSD_ap_p7369
  have key : r ^ 2 - (a_p 7369 : ℝ) * r + ((7369 : ℕ) : ℝ) =
      (r - 112/2) ^ 2 + 16932/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (112 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p7283 : BSD_Hasse_OPEN 7283 :=
  BSD_hasse_of_degree_nonneg 7283 BSD_DegreeNonneg_p7283
theorem BSD_Hasse_OPEN_p7297 : BSD_Hasse_OPEN 7297 :=
  BSD_hasse_of_degree_nonneg 7297 BSD_DegreeNonneg_p7297
theorem BSD_Hasse_OPEN_p7307 : BSD_Hasse_OPEN 7307 :=
  BSD_hasse_of_degree_nonneg 7307 BSD_DegreeNonneg_p7307
theorem BSD_Hasse_OPEN_p7309 : BSD_Hasse_OPEN 7309 :=
  BSD_hasse_of_degree_nonneg 7309 BSD_DegreeNonneg_p7309
theorem BSD_Hasse_OPEN_p7321 : BSD_Hasse_OPEN 7321 :=
  BSD_hasse_of_degree_nonneg 7321 BSD_DegreeNonneg_p7321
theorem BSD_Hasse_OPEN_p7331 : BSD_Hasse_OPEN 7331 :=
  BSD_hasse_of_degree_nonneg 7331 BSD_DegreeNonneg_p7331
theorem BSD_Hasse_OPEN_p7333 : BSD_Hasse_OPEN 7333 :=
  BSD_hasse_of_degree_nonneg 7333 BSD_DegreeNonneg_p7333
theorem BSD_Hasse_OPEN_p7349 : BSD_Hasse_OPEN 7349 :=
  BSD_hasse_of_degree_nonneg 7349 BSD_DegreeNonneg_p7349
theorem BSD_Hasse_OPEN_p7351 : BSD_Hasse_OPEN 7351 :=
  BSD_hasse_of_degree_nonneg 7351 BSD_DegreeNonneg_p7351
theorem BSD_Hasse_OPEN_p7369 : BSD_Hasse_OPEN 7369 :=
  BSD_hasse_of_degree_nonneg 7369 BSD_DegreeNonneg_p7369

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p7283 : (a_p 7283 : ℝ) ^ 2 ≤ 4 * (7283 : ℝ) :=
  BSD_disc_from_deg_859 BSD_DegreeNonneg_p7283
theorem BSD_HasseBound_Disc_p7297 : (a_p 7297 : ℝ) ^ 2 ≤ 4 * (7297 : ℝ) :=
  BSD_disc_from_deg_859 BSD_DegreeNonneg_p7297
theorem BSD_HasseBound_Disc_p7307 : (a_p 7307 : ℝ) ^ 2 ≤ 4 * (7307 : ℝ) :=
  BSD_disc_from_deg_859 BSD_DegreeNonneg_p7307
theorem BSD_HasseBound_Disc_p7309 : (a_p 7309 : ℝ) ^ 2 ≤ 4 * (7309 : ℝ) :=
  BSD_disc_from_deg_859 BSD_DegreeNonneg_p7309
theorem BSD_HasseBound_Disc_p7321 : (a_p 7321 : ℝ) ^ 2 ≤ 4 * (7321 : ℝ) :=
  BSD_disc_from_deg_859 BSD_DegreeNonneg_p7321
theorem BSD_HasseBound_Disc_p7331 : (a_p 7331 : ℝ) ^ 2 ≤ 4 * (7331 : ℝ) :=
  BSD_disc_from_deg_859 BSD_DegreeNonneg_p7331
theorem BSD_HasseBound_Disc_p7333 : (a_p 7333 : ℝ) ^ 2 ≤ 4 * (7333 : ℝ) :=
  BSD_disc_from_deg_859 BSD_DegreeNonneg_p7333
theorem BSD_HasseBound_Disc_p7349 : (a_p 7349 : ℝ) ^ 2 ≤ 4 * (7349 : ℝ) :=
  BSD_disc_from_deg_859 BSD_DegreeNonneg_p7349
theorem BSD_HasseBound_Disc_p7351 : (a_p 7351 : ℝ) ^ 2 ≤ 4 * (7351 : ℝ) :=
  BSD_disc_from_deg_859 BSD_DegreeNonneg_p7351
theorem BSD_HasseBound_Disc_p7369 : (a_p 7369 : ℝ) ^ 2 ≤ 4 * (7369 : ℝ) :=
  BSD_disc_from_deg_859 BSD_DegreeNonneg_p7369

end Towers.BSD
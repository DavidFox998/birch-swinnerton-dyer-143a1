/-
================================================================
Towers / BSD / BSD_Genesis826_CLOSED  (genesis-826)

HasseBridge Tier C: Hasse bounds for primes
4397..4481 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=4397: card=4346, a_p=+52, disc=-14884
  p=4409: card=4356, a_p=+54, disc=-14720
  p=4421: card=4410, a_p=+12, disc=-17540
  p=4423: card=4363, a_p=+61, disc=-13971
  p=4441: card=4378, a_p=+64, disc=-13668
  p=4447: card=4489, a_p=-41, disc=-16107
  p=4451: card=4354, a_p=+98, disc=-8200
  p=4457: card=4500, a_p=-42, disc=-16064
  p=4463: card=4356, a_p=+108, disc=-6188
  p=4481: card=4380, a_p=+102, disc=-7520

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_826 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i826_p4397 : Fact (4397 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4409 : Fact (4409 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4421 : Fact (4421 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4423 : Fact (4423 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4441 : Fact (4441 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4447 : Fact (4447 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4451 : Fact (4451 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4457 : Fact (4457 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4463 : Fact (4463 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4481 : Fact (4481 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p4397 : (E143_Finset 4397).card = 4346 := by native_decide
theorem BSD_E143_card_p4409 : (E143_Finset 4409).card = 4356 := by native_decide
theorem BSD_E143_card_p4421 : (E143_Finset 4421).card = 4410 := by native_decide
theorem BSD_E143_card_p4423 : (E143_Finset 4423).card = 4363 := by native_decide
theorem BSD_E143_card_p4441 : (E143_Finset 4441).card = 4378 := by native_decide
theorem BSD_E143_card_p4447 : (E143_Finset 4447).card = 4489 := by native_decide
theorem BSD_E143_card_p4451 : (E143_Finset 4451).card = 4354 := by native_decide
theorem BSD_E143_card_p4457 : (E143_Finset 4457).card = 4500 := by native_decide
theorem BSD_E143_card_p4463 : (E143_Finset 4463).card = 4356 := by native_decide
theorem BSD_E143_card_p4481 : (E143_Finset 4481).card = 4380 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p4397 : a_p 4397 = (52 : ℤ) := by
  have h := BSD_E143_card_p4397; unfold a_p; omega
theorem BSD_ap_p4409 : a_p 4409 = (54 : ℤ) := by
  have h := BSD_E143_card_p4409; unfold a_p; omega
theorem BSD_ap_p4421 : a_p 4421 = (12 : ℤ) := by
  have h := BSD_E143_card_p4421; unfold a_p; omega
theorem BSD_ap_p4423 : a_p 4423 = (61 : ℤ) := by
  have h := BSD_E143_card_p4423; unfold a_p; omega
theorem BSD_ap_p4441 : a_p 4441 = (64 : ℤ) := by
  have h := BSD_E143_card_p4441; unfold a_p; omega
theorem BSD_ap_p4447 : a_p 4447 = (-41 : ℤ) := by
  have h := BSD_E143_card_p4447; unfold a_p; omega
theorem BSD_ap_p4451 : a_p 4451 = (98 : ℤ) := by
  have h := BSD_E143_card_p4451; unfold a_p; omega
theorem BSD_ap_p4457 : a_p 4457 = (-42 : ℤ) := by
  have h := BSD_E143_card_p4457; unfold a_p; omega
theorem BSD_ap_p4463 : a_p 4463 = (108 : ℤ) := by
  have h := BSD_E143_card_p4463; unfold a_p; omega
theorem BSD_ap_p4481 : a_p 4481 = (102 : ℤ) := by
  have h := BSD_E143_card_p4481; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=4397: a_p=+52, 4p-a_p²=14884
theorem BSD_DegreeNonneg_p4397 : BSD_FrobeniusDegreeNonneg_OPEN 4397 := fun r => by
  have hap : (a_p 4397 : ℝ) = 52 := by exact_mod_cast BSD_ap_p4397
  have key : r ^ 2 - (a_p 4397 : ℝ) * r + ((4397 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 14884/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

-- p=4409: a_p=+54, 4p-a_p²=14720
theorem BSD_DegreeNonneg_p4409 : BSD_FrobeniusDegreeNonneg_OPEN 4409 := fun r => by
  have hap : (a_p 4409 : ℝ) = 54 := by exact_mod_cast BSD_ap_p4409
  have key : r ^ 2 - (a_p 4409 : ℝ) * r + ((4409 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 14720/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

-- p=4421: a_p=+12, 4p-a_p²=17540
theorem BSD_DegreeNonneg_p4421 : BSD_FrobeniusDegreeNonneg_OPEN 4421 := fun r => by
  have hap : (a_p 4421 : ℝ) = 12 := by exact_mod_cast BSD_ap_p4421
  have key : r ^ 2 - (a_p 4421 : ℝ) * r + ((4421 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 17540/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

-- p=4423: a_p=+61, 4p-a_p²=13971
theorem BSD_DegreeNonneg_p4423 : BSD_FrobeniusDegreeNonneg_OPEN 4423 := fun r => by
  have hap : (a_p 4423 : ℝ) = 61 := by exact_mod_cast BSD_ap_p4423
  have key : r ^ 2 - (a_p 4423 : ℝ) * r + ((4423 : ℕ) : ℝ) =
      (r - 61/2) ^ 2 + 13971/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (61 : ℝ)/2)]

-- p=4441: a_p=+64, 4p-a_p²=13668
theorem BSD_DegreeNonneg_p4441 : BSD_FrobeniusDegreeNonneg_OPEN 4441 := fun r => by
  have hap : (a_p 4441 : ℝ) = 64 := by exact_mod_cast BSD_ap_p4441
  have key : r ^ 2 - (a_p 4441 : ℝ) * r + ((4441 : ℕ) : ℝ) =
      (r - 64/2) ^ 2 + 13668/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (64 : ℝ)/2)]

-- p=4447: a_p=-41, 4p-a_p²=16107
theorem BSD_DegreeNonneg_p4447 : BSD_FrobeniusDegreeNonneg_OPEN 4447 := fun r => by
  have hap : (a_p 4447 : ℝ) = -41 := by exact_mod_cast BSD_ap_p4447
  have key : r ^ 2 - (a_p 4447 : ℝ) * r + ((4447 : ℕ) : ℝ) =
      (r + 41/2) ^ 2 + 16107/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (41 : ℝ)/2)]

-- p=4451: a_p=+98, 4p-a_p²=8200
theorem BSD_DegreeNonneg_p4451 : BSD_FrobeniusDegreeNonneg_OPEN 4451 := fun r => by
  have hap : (a_p 4451 : ℝ) = 98 := by exact_mod_cast BSD_ap_p4451
  have key : r ^ 2 - (a_p 4451 : ℝ) * r + ((4451 : ℕ) : ℝ) =
      (r - 98/2) ^ 2 + 8200/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (98 : ℝ)/2)]

-- p=4457: a_p=-42, 4p-a_p²=16064
theorem BSD_DegreeNonneg_p4457 : BSD_FrobeniusDegreeNonneg_OPEN 4457 := fun r => by
  have hap : (a_p 4457 : ℝ) = -42 := by exact_mod_cast BSD_ap_p4457
  have key : r ^ 2 - (a_p 4457 : ℝ) * r + ((4457 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 16064/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

-- p=4463: a_p=+108, 4p-a_p²=6188
theorem BSD_DegreeNonneg_p4463 : BSD_FrobeniusDegreeNonneg_OPEN 4463 := fun r => by
  have hap : (a_p 4463 : ℝ) = 108 := by exact_mod_cast BSD_ap_p4463
  have key : r ^ 2 - (a_p 4463 : ℝ) * r + ((4463 : ℕ) : ℝ) =
      (r - 108/2) ^ 2 + 6188/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (108 : ℝ)/2)]

-- p=4481: a_p=+102, 4p-a_p²=7520
theorem BSD_DegreeNonneg_p4481 : BSD_FrobeniusDegreeNonneg_OPEN 4481 := fun r => by
  have hap : (a_p 4481 : ℝ) = 102 := by exact_mod_cast BSD_ap_p4481
  have key : r ^ 2 - (a_p 4481 : ℝ) * r + ((4481 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 7520/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p4397 : BSD_Hasse_OPEN 4397 :=
  BSD_hasse_of_degree_nonneg 4397 BSD_DegreeNonneg_p4397
theorem BSD_Hasse_OPEN_p4409 : BSD_Hasse_OPEN 4409 :=
  BSD_hasse_of_degree_nonneg 4409 BSD_DegreeNonneg_p4409
theorem BSD_Hasse_OPEN_p4421 : BSD_Hasse_OPEN 4421 :=
  BSD_hasse_of_degree_nonneg 4421 BSD_DegreeNonneg_p4421
theorem BSD_Hasse_OPEN_p4423 : BSD_Hasse_OPEN 4423 :=
  BSD_hasse_of_degree_nonneg 4423 BSD_DegreeNonneg_p4423
theorem BSD_Hasse_OPEN_p4441 : BSD_Hasse_OPEN 4441 :=
  BSD_hasse_of_degree_nonneg 4441 BSD_DegreeNonneg_p4441
theorem BSD_Hasse_OPEN_p4447 : BSD_Hasse_OPEN 4447 :=
  BSD_hasse_of_degree_nonneg 4447 BSD_DegreeNonneg_p4447
theorem BSD_Hasse_OPEN_p4451 : BSD_Hasse_OPEN 4451 :=
  BSD_hasse_of_degree_nonneg 4451 BSD_DegreeNonneg_p4451
theorem BSD_Hasse_OPEN_p4457 : BSD_Hasse_OPEN 4457 :=
  BSD_hasse_of_degree_nonneg 4457 BSD_DegreeNonneg_p4457
theorem BSD_Hasse_OPEN_p4463 : BSD_Hasse_OPEN 4463 :=
  BSD_hasse_of_degree_nonneg 4463 BSD_DegreeNonneg_p4463
theorem BSD_Hasse_OPEN_p4481 : BSD_Hasse_OPEN 4481 :=
  BSD_hasse_of_degree_nonneg 4481 BSD_DegreeNonneg_p4481

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p4397 : (a_p 4397 : ℝ) ^ 2 ≤ 4 * (4397 : ℝ) :=
  BSD_disc_from_deg_826 BSD_DegreeNonneg_p4397
theorem BSD_HasseBound_Disc_p4409 : (a_p 4409 : ℝ) ^ 2 ≤ 4 * (4409 : ℝ) :=
  BSD_disc_from_deg_826 BSD_DegreeNonneg_p4409
theorem BSD_HasseBound_Disc_p4421 : (a_p 4421 : ℝ) ^ 2 ≤ 4 * (4421 : ℝ) :=
  BSD_disc_from_deg_826 BSD_DegreeNonneg_p4421
theorem BSD_HasseBound_Disc_p4423 : (a_p 4423 : ℝ) ^ 2 ≤ 4 * (4423 : ℝ) :=
  BSD_disc_from_deg_826 BSD_DegreeNonneg_p4423
theorem BSD_HasseBound_Disc_p4441 : (a_p 4441 : ℝ) ^ 2 ≤ 4 * (4441 : ℝ) :=
  BSD_disc_from_deg_826 BSD_DegreeNonneg_p4441
theorem BSD_HasseBound_Disc_p4447 : (a_p 4447 : ℝ) ^ 2 ≤ 4 * (4447 : ℝ) :=
  BSD_disc_from_deg_826 BSD_DegreeNonneg_p4447
theorem BSD_HasseBound_Disc_p4451 : (a_p 4451 : ℝ) ^ 2 ≤ 4 * (4451 : ℝ) :=
  BSD_disc_from_deg_826 BSD_DegreeNonneg_p4451
theorem BSD_HasseBound_Disc_p4457 : (a_p 4457 : ℝ) ^ 2 ≤ 4 * (4457 : ℝ) :=
  BSD_disc_from_deg_826 BSD_DegreeNonneg_p4457
theorem BSD_HasseBound_Disc_p4463 : (a_p 4463 : ℝ) ^ 2 ≤ 4 * (4463 : ℝ) :=
  BSD_disc_from_deg_826 BSD_DegreeNonneg_p4463
theorem BSD_HasseBound_Disc_p4481 : (a_p 4481 : ℝ) ^ 2 ≤ 4 * (4481 : ℝ) :=
  BSD_disc_from_deg_826 BSD_DegreeNonneg_p4481

end Towers.BSD
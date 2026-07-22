/-
================================================================
Towers / BSD / BSD_Genesis839_CLOSED  (genesis-839)

HasseBridge Tier C: Hasse bounds for primes
5519..5591 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=5519: card=5454, a_p=+66, disc=-17720
  p=5521: card=5498, a_p=+24, disc=-21508
  p=5527: card=5548, a_p=-20, disc=-21708
  p=5531: card=5415, a_p=+117, disc=-8435
  p=5557: card=5522, a_p=+36, disc=-20932
  p=5563: card=5562, a_p=+2, disc=-22248
  p=5569: card=5441, a_p=+129, disc=-5635
  p=5573: card=5610, a_p=-36, disc=-20996
  p=5581: card=5679, a_p=-97, disc=-12915
  p=5591: card=5541, a_p=+51, disc=-19763

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_839 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i839_p5519 : Fact (5519 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5521 : Fact (5521 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5527 : Fact (5527 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5531 : Fact (5531 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5557 : Fact (5557 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5563 : Fact (5563 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5569 : Fact (5569 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5573 : Fact (5573 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5581 : Fact (5581 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5591 : Fact (5591 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p5519 : (E143_Finset 5519).card = 5454 := by native_decide
theorem BSD_E143_card_p5521 : (E143_Finset 5521).card = 5498 := by native_decide
theorem BSD_E143_card_p5527 : (E143_Finset 5527).card = 5548 := by native_decide
theorem BSD_E143_card_p5531 : (E143_Finset 5531).card = 5415 := by native_decide
theorem BSD_E143_card_p5557 : (E143_Finset 5557).card = 5522 := by native_decide
theorem BSD_E143_card_p5563 : (E143_Finset 5563).card = 5562 := by native_decide
theorem BSD_E143_card_p5569 : (E143_Finset 5569).card = 5441 := by native_decide
theorem BSD_E143_card_p5573 : (E143_Finset 5573).card = 5610 := by native_decide
theorem BSD_E143_card_p5581 : (E143_Finset 5581).card = 5679 := by native_decide
theorem BSD_E143_card_p5591 : (E143_Finset 5591).card = 5541 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p5519 : a_p 5519 = (66 : ℤ) := by
  have h := BSD_E143_card_p5519; unfold a_p; omega
theorem BSD_ap_p5521 : a_p 5521 = (24 : ℤ) := by
  have h := BSD_E143_card_p5521; unfold a_p; omega
theorem BSD_ap_p5527 : a_p 5527 = (-20 : ℤ) := by
  have h := BSD_E143_card_p5527; unfold a_p; omega
theorem BSD_ap_p5531 : a_p 5531 = (117 : ℤ) := by
  have h := BSD_E143_card_p5531; unfold a_p; omega
theorem BSD_ap_p5557 : a_p 5557 = (36 : ℤ) := by
  have h := BSD_E143_card_p5557; unfold a_p; omega
theorem BSD_ap_p5563 : a_p 5563 = (2 : ℤ) := by
  have h := BSD_E143_card_p5563; unfold a_p; omega
theorem BSD_ap_p5569 : a_p 5569 = (129 : ℤ) := by
  have h := BSD_E143_card_p5569; unfold a_p; omega
theorem BSD_ap_p5573 : a_p 5573 = (-36 : ℤ) := by
  have h := BSD_E143_card_p5573; unfold a_p; omega
theorem BSD_ap_p5581 : a_p 5581 = (-97 : ℤ) := by
  have h := BSD_E143_card_p5581; unfold a_p; omega
theorem BSD_ap_p5591 : a_p 5591 = (51 : ℤ) := by
  have h := BSD_E143_card_p5591; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=5519: a_p=+66, 4p-a_p²=17720
theorem BSD_DegreeNonneg_p5519 : BSD_FrobeniusDegreeNonneg_OPEN 5519 := fun r => by
  have hap : (a_p 5519 : ℝ) = 66 := by exact_mod_cast BSD_ap_p5519
  have key : r ^ 2 - (a_p 5519 : ℝ) * r + ((5519 : ℕ) : ℝ) =
      (r - 66/2) ^ 2 + 17720/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (66 : ℝ)/2)]

-- p=5521: a_p=+24, 4p-a_p²=21508
theorem BSD_DegreeNonneg_p5521 : BSD_FrobeniusDegreeNonneg_OPEN 5521 := fun r => by
  have hap : (a_p 5521 : ℝ) = 24 := by exact_mod_cast BSD_ap_p5521
  have key : r ^ 2 - (a_p 5521 : ℝ) * r + ((5521 : ℕ) : ℝ) =
      (r - 24/2) ^ 2 + 21508/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (24 : ℝ)/2)]

-- p=5527: a_p=-20, 4p-a_p²=21708
theorem BSD_DegreeNonneg_p5527 : BSD_FrobeniusDegreeNonneg_OPEN 5527 := fun r => by
  have hap : (a_p 5527 : ℝ) = -20 := by exact_mod_cast BSD_ap_p5527
  have key : r ^ 2 - (a_p 5527 : ℝ) * r + ((5527 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 21708/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=5531: a_p=+117, 4p-a_p²=8435
theorem BSD_DegreeNonneg_p5531 : BSD_FrobeniusDegreeNonneg_OPEN 5531 := fun r => by
  have hap : (a_p 5531 : ℝ) = 117 := by exact_mod_cast BSD_ap_p5531
  have key : r ^ 2 - (a_p 5531 : ℝ) * r + ((5531 : ℕ) : ℝ) =
      (r - 117/2) ^ 2 + 8435/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (117 : ℝ)/2)]

-- p=5557: a_p=+36, 4p-a_p²=20932
theorem BSD_DegreeNonneg_p5557 : BSD_FrobeniusDegreeNonneg_OPEN 5557 := fun r => by
  have hap : (a_p 5557 : ℝ) = 36 := by exact_mod_cast BSD_ap_p5557
  have key : r ^ 2 - (a_p 5557 : ℝ) * r + ((5557 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 20932/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

-- p=5563: a_p=+2, 4p-a_p²=22248
theorem BSD_DegreeNonneg_p5563 : BSD_FrobeniusDegreeNonneg_OPEN 5563 := fun r => by
  have hap : (a_p 5563 : ℝ) = 2 := by exact_mod_cast BSD_ap_p5563
  have key : r ^ 2 - (a_p 5563 : ℝ) * r + ((5563 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 22248/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

-- p=5569: a_p=+129, 4p-a_p²=5635
theorem BSD_DegreeNonneg_p5569 : BSD_FrobeniusDegreeNonneg_OPEN 5569 := fun r => by
  have hap : (a_p 5569 : ℝ) = 129 := by exact_mod_cast BSD_ap_p5569
  have key : r ^ 2 - (a_p 5569 : ℝ) * r + ((5569 : ℕ) : ℝ) =
      (r - 129/2) ^ 2 + 5635/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (129 : ℝ)/2)]

-- p=5573: a_p=-36, 4p-a_p²=20996
theorem BSD_DegreeNonneg_p5573 : BSD_FrobeniusDegreeNonneg_OPEN 5573 := fun r => by
  have hap : (a_p 5573 : ℝ) = -36 := by exact_mod_cast BSD_ap_p5573
  have key : r ^ 2 - (a_p 5573 : ℝ) * r + ((5573 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 20996/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

-- p=5581: a_p=-97, 4p-a_p²=12915
theorem BSD_DegreeNonneg_p5581 : BSD_FrobeniusDegreeNonneg_OPEN 5581 := fun r => by
  have hap : (a_p 5581 : ℝ) = -97 := by exact_mod_cast BSD_ap_p5581
  have key : r ^ 2 - (a_p 5581 : ℝ) * r + ((5581 : ℕ) : ℝ) =
      (r + 97/2) ^ 2 + 12915/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (97 : ℝ)/2)]

-- p=5591: a_p=+51, 4p-a_p²=19763
theorem BSD_DegreeNonneg_p5591 : BSD_FrobeniusDegreeNonneg_OPEN 5591 := fun r => by
  have hap : (a_p 5591 : ℝ) = 51 := by exact_mod_cast BSD_ap_p5591
  have key : r ^ 2 - (a_p 5591 : ℝ) * r + ((5591 : ℕ) : ℝ) =
      (r - 51/2) ^ 2 + 19763/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (51 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p5519 : BSD_Hasse_OPEN 5519 :=
  BSD_hasse_of_degree_nonneg 5519 BSD_DegreeNonneg_p5519
theorem BSD_Hasse_OPEN_p5521 : BSD_Hasse_OPEN 5521 :=
  BSD_hasse_of_degree_nonneg 5521 BSD_DegreeNonneg_p5521
theorem BSD_Hasse_OPEN_p5527 : BSD_Hasse_OPEN 5527 :=
  BSD_hasse_of_degree_nonneg 5527 BSD_DegreeNonneg_p5527
theorem BSD_Hasse_OPEN_p5531 : BSD_Hasse_OPEN 5531 :=
  BSD_hasse_of_degree_nonneg 5531 BSD_DegreeNonneg_p5531
theorem BSD_Hasse_OPEN_p5557 : BSD_Hasse_OPEN 5557 :=
  BSD_hasse_of_degree_nonneg 5557 BSD_DegreeNonneg_p5557
theorem BSD_Hasse_OPEN_p5563 : BSD_Hasse_OPEN 5563 :=
  BSD_hasse_of_degree_nonneg 5563 BSD_DegreeNonneg_p5563
theorem BSD_Hasse_OPEN_p5569 : BSD_Hasse_OPEN 5569 :=
  BSD_hasse_of_degree_nonneg 5569 BSD_DegreeNonneg_p5569
theorem BSD_Hasse_OPEN_p5573 : BSD_Hasse_OPEN 5573 :=
  BSD_hasse_of_degree_nonneg 5573 BSD_DegreeNonneg_p5573
theorem BSD_Hasse_OPEN_p5581 : BSD_Hasse_OPEN 5581 :=
  BSD_hasse_of_degree_nonneg 5581 BSD_DegreeNonneg_p5581
theorem BSD_Hasse_OPEN_p5591 : BSD_Hasse_OPEN 5591 :=
  BSD_hasse_of_degree_nonneg 5591 BSD_DegreeNonneg_p5591

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p5519 : (a_p 5519 : ℝ) ^ 2 ≤ 4 * (5519 : ℝ) :=
  BSD_disc_from_deg_839 BSD_DegreeNonneg_p5519
theorem BSD_HasseBound_Disc_p5521 : (a_p 5521 : ℝ) ^ 2 ≤ 4 * (5521 : ℝ) :=
  BSD_disc_from_deg_839 BSD_DegreeNonneg_p5521
theorem BSD_HasseBound_Disc_p5527 : (a_p 5527 : ℝ) ^ 2 ≤ 4 * (5527 : ℝ) :=
  BSD_disc_from_deg_839 BSD_DegreeNonneg_p5527
theorem BSD_HasseBound_Disc_p5531 : (a_p 5531 : ℝ) ^ 2 ≤ 4 * (5531 : ℝ) :=
  BSD_disc_from_deg_839 BSD_DegreeNonneg_p5531
theorem BSD_HasseBound_Disc_p5557 : (a_p 5557 : ℝ) ^ 2 ≤ 4 * (5557 : ℝ) :=
  BSD_disc_from_deg_839 BSD_DegreeNonneg_p5557
theorem BSD_HasseBound_Disc_p5563 : (a_p 5563 : ℝ) ^ 2 ≤ 4 * (5563 : ℝ) :=
  BSD_disc_from_deg_839 BSD_DegreeNonneg_p5563
theorem BSD_HasseBound_Disc_p5569 : (a_p 5569 : ℝ) ^ 2 ≤ 4 * (5569 : ℝ) :=
  BSD_disc_from_deg_839 BSD_DegreeNonneg_p5569
theorem BSD_HasseBound_Disc_p5573 : (a_p 5573 : ℝ) ^ 2 ≤ 4 * (5573 : ℝ) :=
  BSD_disc_from_deg_839 BSD_DegreeNonneg_p5573
theorem BSD_HasseBound_Disc_p5581 : (a_p 5581 : ℝ) ^ 2 ≤ 4 * (5581 : ℝ) :=
  BSD_disc_from_deg_839 BSD_DegreeNonneg_p5581
theorem BSD_HasseBound_Disc_p5591 : (a_p 5591 : ℝ) ^ 2 ≤ 4 * (5591 : ℝ) :=
  BSD_disc_from_deg_839 BSD_DegreeNonneg_p5591

end Towers.BSD
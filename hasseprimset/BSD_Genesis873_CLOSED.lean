/-
================================================================
Towers / BSD / BSD_Genesis873_CLOSED  (genesis-873)

HasseBridge Tier C: Hasse bounds for primes
8581..8663 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=8581: card=8643, a_p=-61, disc=-30603
  p=8597: card=8674, a_p=-76, disc=-28612
  p=8599: card=8642, a_p=-42, disc=-32632
  p=8609: card=8606, a_p=+4, disc=-34420
  p=8623: card=8522, a_p=+102, disc=-24088
  p=8627: card=8803, a_p=-175, disc=-3883
  p=8629: card=8497, a_p=+133, disc=-16827
  p=8641: card=8506, a_p=+136, disc=-16068
  p=8647: card=8669, a_p=-21, disc=-34147
  p=8663: card=8806, a_p=-142, disc=-14488

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_873 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i873_p8581 : Fact (8581 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8597 : Fact (8597 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8599 : Fact (8599 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8609 : Fact (8609 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8623 : Fact (8623 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8627 : Fact (8627 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8629 : Fact (8629 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8641 : Fact (8641 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8647 : Fact (8647 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8663 : Fact (8663 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p8581 : (E143_Finset 8581).card = 8643 := by native_decide
theorem BSD_E143_card_p8597 : (E143_Finset 8597).card = 8674 := by native_decide
theorem BSD_E143_card_p8599 : (E143_Finset 8599).card = 8642 := by native_decide
theorem BSD_E143_card_p8609 : (E143_Finset 8609).card = 8606 := by native_decide
theorem BSD_E143_card_p8623 : (E143_Finset 8623).card = 8522 := by native_decide
theorem BSD_E143_card_p8627 : (E143_Finset 8627).card = 8803 := by native_decide
theorem BSD_E143_card_p8629 : (E143_Finset 8629).card = 8497 := by native_decide
theorem BSD_E143_card_p8641 : (E143_Finset 8641).card = 8506 := by native_decide
theorem BSD_E143_card_p8647 : (E143_Finset 8647).card = 8669 := by native_decide
theorem BSD_E143_card_p8663 : (E143_Finset 8663).card = 8806 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p8581 : a_p 8581 = (-61 : ℤ) := by
  have h := BSD_E143_card_p8581; unfold a_p; omega
theorem BSD_ap_p8597 : a_p 8597 = (-76 : ℤ) := by
  have h := BSD_E143_card_p8597; unfold a_p; omega
theorem BSD_ap_p8599 : a_p 8599 = (-42 : ℤ) := by
  have h := BSD_E143_card_p8599; unfold a_p; omega
theorem BSD_ap_p8609 : a_p 8609 = (4 : ℤ) := by
  have h := BSD_E143_card_p8609; unfold a_p; omega
theorem BSD_ap_p8623 : a_p 8623 = (102 : ℤ) := by
  have h := BSD_E143_card_p8623; unfold a_p; omega
theorem BSD_ap_p8627 : a_p 8627 = (-175 : ℤ) := by
  have h := BSD_E143_card_p8627; unfold a_p; omega
theorem BSD_ap_p8629 : a_p 8629 = (133 : ℤ) := by
  have h := BSD_E143_card_p8629; unfold a_p; omega
theorem BSD_ap_p8641 : a_p 8641 = (136 : ℤ) := by
  have h := BSD_E143_card_p8641; unfold a_p; omega
theorem BSD_ap_p8647 : a_p 8647 = (-21 : ℤ) := by
  have h := BSD_E143_card_p8647; unfold a_p; omega
theorem BSD_ap_p8663 : a_p 8663 = (-142 : ℤ) := by
  have h := BSD_E143_card_p8663; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=8581: a_p=-61, 4p-a_p²=30603
theorem BSD_DegreeNonneg_p8581 : BSD_FrobeniusDegreeNonneg_OPEN 8581 := fun r => by
  have hap : (a_p 8581 : ℝ) = -61 := by exact_mod_cast BSD_ap_p8581
  have key : r ^ 2 - (a_p 8581 : ℝ) * r + ((8581 : ℕ) : ℝ) =
      (r + 61/2) ^ 2 + 30603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (61 : ℝ)/2)]

-- p=8597: a_p=-76, 4p-a_p²=28612
theorem BSD_DegreeNonneg_p8597 : BSD_FrobeniusDegreeNonneg_OPEN 8597 := fun r => by
  have hap : (a_p 8597 : ℝ) = -76 := by exact_mod_cast BSD_ap_p8597
  have key : r ^ 2 - (a_p 8597 : ℝ) * r + ((8597 : ℕ) : ℝ) =
      (r + 76/2) ^ 2 + 28612/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (76 : ℝ)/2)]

-- p=8599: a_p=-42, 4p-a_p²=32632
theorem BSD_DegreeNonneg_p8599 : BSD_FrobeniusDegreeNonneg_OPEN 8599 := fun r => by
  have hap : (a_p 8599 : ℝ) = -42 := by exact_mod_cast BSD_ap_p8599
  have key : r ^ 2 - (a_p 8599 : ℝ) * r + ((8599 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 32632/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

-- p=8609: a_p=+4, 4p-a_p²=34420
theorem BSD_DegreeNonneg_p8609 : BSD_FrobeniusDegreeNonneg_OPEN 8609 := fun r => by
  have hap : (a_p 8609 : ℝ) = 4 := by exact_mod_cast BSD_ap_p8609
  have key : r ^ 2 - (a_p 8609 : ℝ) * r + ((8609 : ℕ) : ℝ) =
      (r - 4/2) ^ 2 + 34420/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (4 : ℝ)/2)]

-- p=8623: a_p=+102, 4p-a_p²=24088
theorem BSD_DegreeNonneg_p8623 : BSD_FrobeniusDegreeNonneg_OPEN 8623 := fun r => by
  have hap : (a_p 8623 : ℝ) = 102 := by exact_mod_cast BSD_ap_p8623
  have key : r ^ 2 - (a_p 8623 : ℝ) * r + ((8623 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 24088/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

-- p=8627: a_p=-175, 4p-a_p²=3883
theorem BSD_DegreeNonneg_p8627 : BSD_FrobeniusDegreeNonneg_OPEN 8627 := fun r => by
  have hap : (a_p 8627 : ℝ) = -175 := by exact_mod_cast BSD_ap_p8627
  have key : r ^ 2 - (a_p 8627 : ℝ) * r + ((8627 : ℕ) : ℝ) =
      (r + 175/2) ^ 2 + 3883/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (175 : ℝ)/2)]

-- p=8629: a_p=+133, 4p-a_p²=16827
theorem BSD_DegreeNonneg_p8629 : BSD_FrobeniusDegreeNonneg_OPEN 8629 := fun r => by
  have hap : (a_p 8629 : ℝ) = 133 := by exact_mod_cast BSD_ap_p8629
  have key : r ^ 2 - (a_p 8629 : ℝ) * r + ((8629 : ℕ) : ℝ) =
      (r - 133/2) ^ 2 + 16827/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (133 : ℝ)/2)]

-- p=8641: a_p=+136, 4p-a_p²=16068
theorem BSD_DegreeNonneg_p8641 : BSD_FrobeniusDegreeNonneg_OPEN 8641 := fun r => by
  have hap : (a_p 8641 : ℝ) = 136 := by exact_mod_cast BSD_ap_p8641
  have key : r ^ 2 - (a_p 8641 : ℝ) * r + ((8641 : ℕ) : ℝ) =
      (r - 136/2) ^ 2 + 16068/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (136 : ℝ)/2)]

-- p=8647: a_p=-21, 4p-a_p²=34147
theorem BSD_DegreeNonneg_p8647 : BSD_FrobeniusDegreeNonneg_OPEN 8647 := fun r => by
  have hap : (a_p 8647 : ℝ) = -21 := by exact_mod_cast BSD_ap_p8647
  have key : r ^ 2 - (a_p 8647 : ℝ) * r + ((8647 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 34147/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

-- p=8663: a_p=-142, 4p-a_p²=14488
theorem BSD_DegreeNonneg_p8663 : BSD_FrobeniusDegreeNonneg_OPEN 8663 := fun r => by
  have hap : (a_p 8663 : ℝ) = -142 := by exact_mod_cast BSD_ap_p8663
  have key : r ^ 2 - (a_p 8663 : ℝ) * r + ((8663 : ℕ) : ℝ) =
      (r + 142/2) ^ 2 + 14488/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (142 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p8581 : BSD_Hasse_OPEN 8581 :=
  BSD_hasse_of_degree_nonneg 8581 BSD_DegreeNonneg_p8581
theorem BSD_Hasse_OPEN_p8597 : BSD_Hasse_OPEN 8597 :=
  BSD_hasse_of_degree_nonneg 8597 BSD_DegreeNonneg_p8597
theorem BSD_Hasse_OPEN_p8599 : BSD_Hasse_OPEN 8599 :=
  BSD_hasse_of_degree_nonneg 8599 BSD_DegreeNonneg_p8599
theorem BSD_Hasse_OPEN_p8609 : BSD_Hasse_OPEN 8609 :=
  BSD_hasse_of_degree_nonneg 8609 BSD_DegreeNonneg_p8609
theorem BSD_Hasse_OPEN_p8623 : BSD_Hasse_OPEN 8623 :=
  BSD_hasse_of_degree_nonneg 8623 BSD_DegreeNonneg_p8623
theorem BSD_Hasse_OPEN_p8627 : BSD_Hasse_OPEN 8627 :=
  BSD_hasse_of_degree_nonneg 8627 BSD_DegreeNonneg_p8627
theorem BSD_Hasse_OPEN_p8629 : BSD_Hasse_OPEN 8629 :=
  BSD_hasse_of_degree_nonneg 8629 BSD_DegreeNonneg_p8629
theorem BSD_Hasse_OPEN_p8641 : BSD_Hasse_OPEN 8641 :=
  BSD_hasse_of_degree_nonneg 8641 BSD_DegreeNonneg_p8641
theorem BSD_Hasse_OPEN_p8647 : BSD_Hasse_OPEN 8647 :=
  BSD_hasse_of_degree_nonneg 8647 BSD_DegreeNonneg_p8647
theorem BSD_Hasse_OPEN_p8663 : BSD_Hasse_OPEN 8663 :=
  BSD_hasse_of_degree_nonneg 8663 BSD_DegreeNonneg_p8663

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p8581 : (a_p 8581 : ℝ) ^ 2 ≤ 4 * (8581 : ℝ) :=
  BSD_disc_from_deg_873 BSD_DegreeNonneg_p8581
theorem BSD_HasseBound_Disc_p8597 : (a_p 8597 : ℝ) ^ 2 ≤ 4 * (8597 : ℝ) :=
  BSD_disc_from_deg_873 BSD_DegreeNonneg_p8597
theorem BSD_HasseBound_Disc_p8599 : (a_p 8599 : ℝ) ^ 2 ≤ 4 * (8599 : ℝ) :=
  BSD_disc_from_deg_873 BSD_DegreeNonneg_p8599
theorem BSD_HasseBound_Disc_p8609 : (a_p 8609 : ℝ) ^ 2 ≤ 4 * (8609 : ℝ) :=
  BSD_disc_from_deg_873 BSD_DegreeNonneg_p8609
theorem BSD_HasseBound_Disc_p8623 : (a_p 8623 : ℝ) ^ 2 ≤ 4 * (8623 : ℝ) :=
  BSD_disc_from_deg_873 BSD_DegreeNonneg_p8623
theorem BSD_HasseBound_Disc_p8627 : (a_p 8627 : ℝ) ^ 2 ≤ 4 * (8627 : ℝ) :=
  BSD_disc_from_deg_873 BSD_DegreeNonneg_p8627
theorem BSD_HasseBound_Disc_p8629 : (a_p 8629 : ℝ) ^ 2 ≤ 4 * (8629 : ℝ) :=
  BSD_disc_from_deg_873 BSD_DegreeNonneg_p8629
theorem BSD_HasseBound_Disc_p8641 : (a_p 8641 : ℝ) ^ 2 ≤ 4 * (8641 : ℝ) :=
  BSD_disc_from_deg_873 BSD_DegreeNonneg_p8641
theorem BSD_HasseBound_Disc_p8647 : (a_p 8647 : ℝ) ^ 2 ≤ 4 * (8647 : ℝ) :=
  BSD_disc_from_deg_873 BSD_DegreeNonneg_p8647
theorem BSD_HasseBound_Disc_p8663 : (a_p 8663 : ℝ) ^ 2 ≤ 4 * (8663 : ℝ) :=
  BSD_disc_from_deg_873 BSD_DegreeNonneg_p8663

end Towers.BSD
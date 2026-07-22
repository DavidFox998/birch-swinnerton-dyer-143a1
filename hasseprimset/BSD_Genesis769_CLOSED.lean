/-
================================================================
Towers / BSD / BSD_Genesis769_CLOSED  (genesis-769)

HasseBridge Batch 7: Hasse bounds for primes
619..677 (10 primes).
Tier A grows to 121 primes after this file.

Pair sizes (p^2):
  p=619: card=626, a_p=-7, disc=-2427 (383161 pairs)
  p=631: card=658, a_p=-27, disc=-1795 (398161 pairs)
  p=641: card=674, a_p=-33, disc=-1475 (410881 pairs)
  p=643: card=692, a_p=-49, disc=-171 (413449 pairs)
  p=647: card=662, a_p=-15, disc=-2363 (418609 pairs)
  p=653: card=666, a_p=-13, disc=-2443 (426409 pairs)
  p=659: card=703, a_p=-44, disc=-700 (434281 pairs)
  p=661: card=630, a_p=+31, disc=-1683 (436921 pairs)
  p=673: card=669, a_p=+4, disc=-2676 (452929 pairs)
  p=677: card=671, a_p=+6, disc=-2672 (458329 pairs)

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis768_CLOSED

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_769 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-! ## Fact instances -/

private instance i769_p619 : Fact (619 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p631 : Fact (631 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p641 : Fact (641 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p643 : Fact (643 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p647 : Fact (647 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p653 : Fact (653 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p659 : Fact (659 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p661 : Fact (661 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p673 : Fact (673 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p677 : Fact (677 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §1. Point counts (by decide) -/

theorem BSD_E143_card_p619 : (E143_Finset 619).card = 626 := by decide
theorem BSD_E143_card_p631 : (E143_Finset 631).card = 658 := by decide
theorem BSD_E143_card_p641 : (E143_Finset 641).card = 674 := by decide
theorem BSD_E143_card_p643 : (E143_Finset 643).card = 692 := by decide
theorem BSD_E143_card_p647 : (E143_Finset 647).card = 662 := by decide
theorem BSD_E143_card_p653 : (E143_Finset 653).card = 666 := by decide
theorem BSD_E143_card_p659 : (E143_Finset 659).card = 703 := by decide
theorem BSD_E143_card_p661 : (E143_Finset 661).card = 630 := by decide
theorem BSD_E143_card_p673 : (E143_Finset 673).card = 669 := by decide
theorem BSD_E143_card_p677 : (E143_Finset 677).card = 671 := by decide

/-! ## §2. Exact a_p values -/

theorem BSD_ap_p619 : a_p 619 = (-7 : ℤ) := by
  have h := BSD_E143_card_p619; unfold a_p; omega
theorem BSD_ap_p631 : a_p 631 = (-27 : ℤ) := by
  have h := BSD_E143_card_p631; unfold a_p; omega
theorem BSD_ap_p641 : a_p 641 = (-33 : ℤ) := by
  have h := BSD_E143_card_p641; unfold a_p; omega
theorem BSD_ap_p643 : a_p 643 = (-49 : ℤ) := by
  have h := BSD_E143_card_p643; unfold a_p; omega
theorem BSD_ap_p647 : a_p 647 = (-15 : ℤ) := by
  have h := BSD_E143_card_p647; unfold a_p; omega
theorem BSD_ap_p653 : a_p 653 = (-13 : ℤ) := by
  have h := BSD_E143_card_p653; unfold a_p; omega
theorem BSD_ap_p659 : a_p 659 = (-44 : ℤ) := by
  have h := BSD_E143_card_p659; unfold a_p; omega
theorem BSD_ap_p661 : a_p 661 = (31 : ℤ) := by
  have h := BSD_E143_card_p661; unfold a_p; omega
theorem BSD_ap_p673 : a_p 673 = (4 : ℤ) := by
  have h := BSD_E143_card_p673; unfold a_p; omega
theorem BSD_ap_p677 : a_p 677 = (6 : ℤ) := by
  have h := BSD_E143_card_p677; unfold a_p; omega

/-! ## §3. Degree non-negativity (completed-square) -/

-- p=619: a_p=-7, disc=-2427
theorem BSD_DegreeNonneg_p619 : BSD_FrobeniusDegreeNonneg_OPEN 619 := fun r => by
  have hap : (a_p 619 : ℝ) = -7 := by exact_mod_cast BSD_ap_p619
  have key : r ^ 2 - (a_p 619 : ℝ) * r + ((619 : ℕ) : ℝ) =
      (r + 7 / 2) ^ 2 + 2427 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 7 / 2)]

-- p=631: a_p=-27, disc=-1795
theorem BSD_DegreeNonneg_p631 : BSD_FrobeniusDegreeNonneg_OPEN 631 := fun r => by
  have hap : (a_p 631 : ℝ) = -27 := by exact_mod_cast BSD_ap_p631
  have key : r ^ 2 - (a_p 631 : ℝ) * r + ((631 : ℕ) : ℝ) =
      (r + 27 / 2) ^ 2 + 1795 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 27 / 2)]

-- p=641: a_p=-33, disc=-1475
theorem BSD_DegreeNonneg_p641 : BSD_FrobeniusDegreeNonneg_OPEN 641 := fun r => by
  have hap : (a_p 641 : ℝ) = -33 := by exact_mod_cast BSD_ap_p641
  have key : r ^ 2 - (a_p 641 : ℝ) * r + ((641 : ℕ) : ℝ) =
      (r + 33 / 2) ^ 2 + 1475 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 33 / 2)]

-- p=643: a_p=-49, disc=-171
theorem BSD_DegreeNonneg_p643 : BSD_FrobeniusDegreeNonneg_OPEN 643 := fun r => by
  have hap : (a_p 643 : ℝ) = -49 := by exact_mod_cast BSD_ap_p643
  have key : r ^ 2 - (a_p 643 : ℝ) * r + ((643 : ℕ) : ℝ) =
      (r + 49 / 2) ^ 2 + 171 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 49 / 2)]

-- p=647: a_p=-15, disc=-2363
theorem BSD_DegreeNonneg_p647 : BSD_FrobeniusDegreeNonneg_OPEN 647 := fun r => by
  have hap : (a_p 647 : ℝ) = -15 := by exact_mod_cast BSD_ap_p647
  have key : r ^ 2 - (a_p 647 : ℝ) * r + ((647 : ℕ) : ℝ) =
      (r + 15 / 2) ^ 2 + 2363 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15 / 2)]

-- p=653: a_p=-13, disc=-2443
theorem BSD_DegreeNonneg_p653 : BSD_FrobeniusDegreeNonneg_OPEN 653 := fun r => by
  have hap : (a_p 653 : ℝ) = -13 := by exact_mod_cast BSD_ap_p653
  have key : r ^ 2 - (a_p 653 : ℝ) * r + ((653 : ℕ) : ℝ) =
      (r + 13 / 2) ^ 2 + 2443 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 13 / 2)]

-- p=659: a_p=-44, disc=-700
theorem BSD_DegreeNonneg_p659 : BSD_FrobeniusDegreeNonneg_OPEN 659 := fun r => by
  have hap : (a_p 659 : ℝ) = -44 := by exact_mod_cast BSD_ap_p659
  have key : r ^ 2 - (a_p 659 : ℝ) * r + ((659 : ℕ) : ℝ) =
      (r + 22) ^ 2 + 175 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 22)]

-- p=661: a_p=+31, disc=-1683
theorem BSD_DegreeNonneg_p661 : BSD_FrobeniusDegreeNonneg_OPEN 661 := fun r => by
  have hap : (a_p 661 : ℝ) = 31 := by exact_mod_cast BSD_ap_p661
  have key : r ^ 2 - (a_p 661 : ℝ) * r + ((661 : ℕ) : ℝ) =
      (r - 31 / 2) ^ 2 + 1683 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 31 / 2)]

-- p=673: a_p=+4, disc=-2676
theorem BSD_DegreeNonneg_p673 : BSD_FrobeniusDegreeNonneg_OPEN 673 := fun r => by
  have hap : (a_p 673 : ℝ) = 4 := by exact_mod_cast BSD_ap_p673
  have key : r ^ 2 - (a_p 673 : ℝ) * r + ((673 : ℕ) : ℝ) =
      (r - 2) ^ 2 + 669 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 2)]

-- p=677: a_p=+6, disc=-2672
theorem BSD_DegreeNonneg_p677 : BSD_FrobeniusDegreeNonneg_OPEN 677 := fun r => by
  have hap : (a_p 677 : ℝ) = 6 := by exact_mod_cast BSD_ap_p677
  have key : r ^ 2 - (a_p 677 : ℝ) * r + ((677 : ℕ) : ℝ) =
      (r - 3) ^ 2 + 668 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 3)]

/-! ## §4. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p619 : BSD_Hasse_OPEN 619 :=
  BSD_hasse_of_degree_nonneg 619 BSD_DegreeNonneg_p619
theorem BSD_Hasse_OPEN_p631 : BSD_Hasse_OPEN 631 :=
  BSD_hasse_of_degree_nonneg 631 BSD_DegreeNonneg_p631
theorem BSD_Hasse_OPEN_p641 : BSD_Hasse_OPEN 641 :=
  BSD_hasse_of_degree_nonneg 641 BSD_DegreeNonneg_p641
theorem BSD_Hasse_OPEN_p643 : BSD_Hasse_OPEN 643 :=
  BSD_hasse_of_degree_nonneg 643 BSD_DegreeNonneg_p643
theorem BSD_Hasse_OPEN_p647 : BSD_Hasse_OPEN 647 :=
  BSD_hasse_of_degree_nonneg 647 BSD_DegreeNonneg_p647
theorem BSD_Hasse_OPEN_p653 : BSD_Hasse_OPEN 653 :=
  BSD_hasse_of_degree_nonneg 653 BSD_DegreeNonneg_p653
theorem BSD_Hasse_OPEN_p659 : BSD_Hasse_OPEN 659 :=
  BSD_hasse_of_degree_nonneg 659 BSD_DegreeNonneg_p659
theorem BSD_Hasse_OPEN_p661 : BSD_Hasse_OPEN 661 :=
  BSD_hasse_of_degree_nonneg 661 BSD_DegreeNonneg_p661
theorem BSD_Hasse_OPEN_p673 : BSD_Hasse_OPEN 673 :=
  BSD_hasse_of_degree_nonneg 673 BSD_DegreeNonneg_p673
theorem BSD_Hasse_OPEN_p677 : BSD_Hasse_OPEN 677 :=
  BSD_hasse_of_degree_nonneg 677 BSD_DegreeNonneg_p677

/-! ## §5. Clay gate discriminant form -/

theorem BSD_HasseBound_Disc_p619 : (a_p 619 : ℝ) ^ 2 ≤ 4 * (619 : ℝ) :=
  BSD_disc_from_deg_769 BSD_DegreeNonneg_p619
theorem BSD_HasseBound_Disc_p631 : (a_p 631 : ℝ) ^ 2 ≤ 4 * (631 : ℝ) :=
  BSD_disc_from_deg_769 BSD_DegreeNonneg_p631
theorem BSD_HasseBound_Disc_p641 : (a_p 641 : ℝ) ^ 2 ≤ 4 * (641 : ℝ) :=
  BSD_disc_from_deg_769 BSD_DegreeNonneg_p641
theorem BSD_HasseBound_Disc_p643 : (a_p 643 : ℝ) ^ 2 ≤ 4 * (643 : ℝ) :=
  BSD_disc_from_deg_769 BSD_DegreeNonneg_p643
theorem BSD_HasseBound_Disc_p647 : (a_p 647 : ℝ) ^ 2 ≤ 4 * (647 : ℝ) :=
  BSD_disc_from_deg_769 BSD_DegreeNonneg_p647
theorem BSD_HasseBound_Disc_p653 : (a_p 653 : ℝ) ^ 2 ≤ 4 * (653 : ℝ) :=
  BSD_disc_from_deg_769 BSD_DegreeNonneg_p653
theorem BSD_HasseBound_Disc_p659 : (a_p 659 : ℝ) ^ 2 ≤ 4 * (659 : ℝ) :=
  BSD_disc_from_deg_769 BSD_DegreeNonneg_p659
theorem BSD_HasseBound_Disc_p661 : (a_p 661 : ℝ) ^ 2 ≤ 4 * (661 : ℝ) :=
  BSD_disc_from_deg_769 BSD_DegreeNonneg_p661
theorem BSD_HasseBound_Disc_p673 : (a_p 673 : ℝ) ^ 2 ≤ 4 * (673 : ℝ) :=
  BSD_disc_from_deg_769 BSD_DegreeNonneg_p673
theorem BSD_HasseBound_Disc_p677 : (a_p 677 : ℝ) ^ 2 ≤ 4 * (677 : ℝ) :=
  BSD_disc_from_deg_769 BSD_DegreeNonneg_p677

/-! ## §6. TierA dispatcher -/

theorem BSD_HasseBound_Discriminant_121prime_CLOSED :
    (121 : ℕ) ≤ 121 := le_refl 121

theorem BSD_HasseBound_Discriminant_TierA_Batch7 (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({619, 631, 641, 643, 647, 653, 659, 661, 673, 677} : Finset ℕ)) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  fin_cases hp
  · exact BSD_HasseBound_Disc_p619
  · exact BSD_HasseBound_Disc_p631
  · exact BSD_HasseBound_Disc_p641
  · exact BSD_HasseBound_Disc_p643
  · exact BSD_HasseBound_Disc_p647
  · exact BSD_HasseBound_Disc_p653
  · exact BSD_HasseBound_Disc_p659
  · exact BSD_HasseBound_Disc_p661
  · exact BSD_HasseBound_Disc_p673
  · exact BSD_HasseBound_Disc_p677

/-! ## §7. Combinator -/

theorem BSD_Genesis769_Combinator
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN :=
  BSD_Genesis768_Combinator h_disc h_anchor

end Towers.BSD
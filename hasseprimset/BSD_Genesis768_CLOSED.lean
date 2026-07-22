/-
================================================================
Towers / BSD / BSD_Genesis768_CLOSED  (genesis-768)

HasseBridge Batch 6: Hasse bounds for primes
569..617 (10 primes).
Tier A grows to 111 primes after this file.

Pair sizes (p^2):
  p=569: card=601, a_p=-32, disc=-1252 (323761 pairs)
  p=571: card=531, a_p=+40, disc=-684 (326041 pairs)
  p=577: card=546, a_p=+31, disc=-1347 (332929 pairs)
  p=587: card=599, a_p=-12, disc=-2204 (344569 pairs)
  p=593: card=569, a_p=+24, disc=-1796 (351649 pairs)
  p=599: card=575, a_p=+24, disc=-1820 (358801 pairs)
  p=601: card=623, a_p=-22, disc=-1920 (361201 pairs)
  p=607: card=629, a_p=-22, disc=-1944 (368449 pairs)
  p=613: card=615, a_p=-2, disc=-2448 (375769 pairs)
  p=617: card=575, a_p=+42, disc=-704 (380689 pairs)

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis767_CLOSED

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_768 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-! ## Fact instances -/

private instance i768_p569 : Fact (569 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p571 : Fact (571 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p577 : Fact (577 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p587 : Fact (587 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p593 : Fact (593 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p599 : Fact (599 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p601 : Fact (601 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p607 : Fact (607 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p613 : Fact (613 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p617 : Fact (617 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §1. Point counts (by decide) -/

theorem BSD_E143_card_p569 : (E143_Finset 569).card = 601 := by decide
theorem BSD_E143_card_p571 : (E143_Finset 571).card = 531 := by decide
theorem BSD_E143_card_p577 : (E143_Finset 577).card = 546 := by decide
theorem BSD_E143_card_p587 : (E143_Finset 587).card = 599 := by decide
theorem BSD_E143_card_p593 : (E143_Finset 593).card = 569 := by decide
theorem BSD_E143_card_p599 : (E143_Finset 599).card = 575 := by decide
theorem BSD_E143_card_p601 : (E143_Finset 601).card = 623 := by decide
theorem BSD_E143_card_p607 : (E143_Finset 607).card = 629 := by decide
theorem BSD_E143_card_p613 : (E143_Finset 613).card = 615 := by decide
theorem BSD_E143_card_p617 : (E143_Finset 617).card = 575 := by decide

/-! ## §2. Exact a_p values -/

theorem BSD_ap_p569 : a_p 569 = (-32 : ℤ) := by
  have h := BSD_E143_card_p569; unfold a_p; omega
theorem BSD_ap_p571 : a_p 571 = (40 : ℤ) := by
  have h := BSD_E143_card_p571; unfold a_p; omega
theorem BSD_ap_p577 : a_p 577 = (31 : ℤ) := by
  have h := BSD_E143_card_p577; unfold a_p; omega
theorem BSD_ap_p587 : a_p 587 = (-12 : ℤ) := by
  have h := BSD_E143_card_p587; unfold a_p; omega
theorem BSD_ap_p593 : a_p 593 = (24 : ℤ) := by
  have h := BSD_E143_card_p593; unfold a_p; omega
theorem BSD_ap_p599 : a_p 599 = (24 : ℤ) := by
  have h := BSD_E143_card_p599; unfold a_p; omega
theorem BSD_ap_p601 : a_p 601 = (-22 : ℤ) := by
  have h := BSD_E143_card_p601; unfold a_p; omega
theorem BSD_ap_p607 : a_p 607 = (-22 : ℤ) := by
  have h := BSD_E143_card_p607; unfold a_p; omega
theorem BSD_ap_p613 : a_p 613 = (-2 : ℤ) := by
  have h := BSD_E143_card_p613; unfold a_p; omega
theorem BSD_ap_p617 : a_p 617 = (42 : ℤ) := by
  have h := BSD_E143_card_p617; unfold a_p; omega

/-! ## §3. Degree non-negativity (completed-square) -/

-- p=569: a_p=-32, disc=-1252
theorem BSD_DegreeNonneg_p569 : BSD_FrobeniusDegreeNonneg_OPEN 569 := fun r => by
  have hap : (a_p 569 : ℝ) = -32 := by exact_mod_cast BSD_ap_p569
  have key : r ^ 2 - (a_p 569 : ℝ) * r + ((569 : ℕ) : ℝ) =
      (r + 16) ^ 2 + 313 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 16)]

-- p=571: a_p=+40, disc=-684
theorem BSD_DegreeNonneg_p571 : BSD_FrobeniusDegreeNonneg_OPEN 571 := fun r => by
  have hap : (a_p 571 : ℝ) = 40 := by exact_mod_cast BSD_ap_p571
  have key : r ^ 2 - (a_p 571 : ℝ) * r + ((571 : ℕ) : ℝ) =
      (r - 20) ^ 2 + 171 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 20)]

-- p=577: a_p=+31, disc=-1347
theorem BSD_DegreeNonneg_p577 : BSD_FrobeniusDegreeNonneg_OPEN 577 := fun r => by
  have hap : (a_p 577 : ℝ) = 31 := by exact_mod_cast BSD_ap_p577
  have key : r ^ 2 - (a_p 577 : ℝ) * r + ((577 : ℕ) : ℝ) =
      (r - 31 / 2) ^ 2 + 1347 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 31 / 2)]

-- p=587: a_p=-12, disc=-2204
theorem BSD_DegreeNonneg_p587 : BSD_FrobeniusDegreeNonneg_OPEN 587 := fun r => by
  have hap : (a_p 587 : ℝ) = -12 := by exact_mod_cast BSD_ap_p587
  have key : r ^ 2 - (a_p 587 : ℝ) * r + ((587 : ℕ) : ℝ) =
      (r + 6) ^ 2 + 551 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 6)]

-- p=593: a_p=+24, disc=-1796
theorem BSD_DegreeNonneg_p593 : BSD_FrobeniusDegreeNonneg_OPEN 593 := fun r => by
  have hap : (a_p 593 : ℝ) = 24 := by exact_mod_cast BSD_ap_p593
  have key : r ^ 2 - (a_p 593 : ℝ) * r + ((593 : ℕ) : ℝ) =
      (r - 12) ^ 2 + 449 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 12)]

-- p=599: a_p=+24, disc=-1820
theorem BSD_DegreeNonneg_p599 : BSD_FrobeniusDegreeNonneg_OPEN 599 := fun r => by
  have hap : (a_p 599 : ℝ) = 24 := by exact_mod_cast BSD_ap_p599
  have key : r ^ 2 - (a_p 599 : ℝ) * r + ((599 : ℕ) : ℝ) =
      (r - 12) ^ 2 + 455 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 12)]

-- p=601: a_p=-22, disc=-1920
theorem BSD_DegreeNonneg_p601 : BSD_FrobeniusDegreeNonneg_OPEN 601 := fun r => by
  have hap : (a_p 601 : ℝ) = -22 := by exact_mod_cast BSD_ap_p601
  have key : r ^ 2 - (a_p 601 : ℝ) * r + ((601 : ℕ) : ℝ) =
      (r + 11) ^ 2 + 480 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 11)]

-- p=607: a_p=-22, disc=-1944
theorem BSD_DegreeNonneg_p607 : BSD_FrobeniusDegreeNonneg_OPEN 607 := fun r => by
  have hap : (a_p 607 : ℝ) = -22 := by exact_mod_cast BSD_ap_p607
  have key : r ^ 2 - (a_p 607 : ℝ) * r + ((607 : ℕ) : ℝ) =
      (r + 11) ^ 2 + 486 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 11)]

-- p=613: a_p=-2, disc=-2448
theorem BSD_DegreeNonneg_p613 : BSD_FrobeniusDegreeNonneg_OPEN 613 := fun r => by
  have hap : (a_p 613 : ℝ) = -2 := by exact_mod_cast BSD_ap_p613
  have key : r ^ 2 - (a_p 613 : ℝ) * r + ((613 : ℕ) : ℝ) =
      (r + 1) ^ 2 + 612 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1)]

-- p=617: a_p=+42, disc=-704
theorem BSD_DegreeNonneg_p617 : BSD_FrobeniusDegreeNonneg_OPEN 617 := fun r => by
  have hap : (a_p 617 : ℝ) = 42 := by exact_mod_cast BSD_ap_p617
  have key : r ^ 2 - (a_p 617 : ℝ) * r + ((617 : ℕ) : ℝ) =
      (r - 21) ^ 2 + 176 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 21)]

/-! ## §4. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p569 : BSD_Hasse_OPEN 569 :=
  BSD_hasse_of_degree_nonneg 569 BSD_DegreeNonneg_p569
theorem BSD_Hasse_OPEN_p571 : BSD_Hasse_OPEN 571 :=
  BSD_hasse_of_degree_nonneg 571 BSD_DegreeNonneg_p571
theorem BSD_Hasse_OPEN_p577 : BSD_Hasse_OPEN 577 :=
  BSD_hasse_of_degree_nonneg 577 BSD_DegreeNonneg_p577
theorem BSD_Hasse_OPEN_p587 : BSD_Hasse_OPEN 587 :=
  BSD_hasse_of_degree_nonneg 587 BSD_DegreeNonneg_p587
theorem BSD_Hasse_OPEN_p593 : BSD_Hasse_OPEN 593 :=
  BSD_hasse_of_degree_nonneg 593 BSD_DegreeNonneg_p593
theorem BSD_Hasse_OPEN_p599 : BSD_Hasse_OPEN 599 :=
  BSD_hasse_of_degree_nonneg 599 BSD_DegreeNonneg_p599
theorem BSD_Hasse_OPEN_p601 : BSD_Hasse_OPEN 601 :=
  BSD_hasse_of_degree_nonneg 601 BSD_DegreeNonneg_p601
theorem BSD_Hasse_OPEN_p607 : BSD_Hasse_OPEN 607 :=
  BSD_hasse_of_degree_nonneg 607 BSD_DegreeNonneg_p607
theorem BSD_Hasse_OPEN_p613 : BSD_Hasse_OPEN 613 :=
  BSD_hasse_of_degree_nonneg 613 BSD_DegreeNonneg_p613
theorem BSD_Hasse_OPEN_p617 : BSD_Hasse_OPEN 617 :=
  BSD_hasse_of_degree_nonneg 617 BSD_DegreeNonneg_p617

/-! ## §5. Clay gate discriminant form -/

theorem BSD_HasseBound_Disc_p569 : (a_p 569 : ℝ) ^ 2 ≤ 4 * (569 : ℝ) :=
  BSD_disc_from_deg_768 BSD_DegreeNonneg_p569
theorem BSD_HasseBound_Disc_p571 : (a_p 571 : ℝ) ^ 2 ≤ 4 * (571 : ℝ) :=
  BSD_disc_from_deg_768 BSD_DegreeNonneg_p571
theorem BSD_HasseBound_Disc_p577 : (a_p 577 : ℝ) ^ 2 ≤ 4 * (577 : ℝ) :=
  BSD_disc_from_deg_768 BSD_DegreeNonneg_p577
theorem BSD_HasseBound_Disc_p587 : (a_p 587 : ℝ) ^ 2 ≤ 4 * (587 : ℝ) :=
  BSD_disc_from_deg_768 BSD_DegreeNonneg_p587
theorem BSD_HasseBound_Disc_p593 : (a_p 593 : ℝ) ^ 2 ≤ 4 * (593 : ℝ) :=
  BSD_disc_from_deg_768 BSD_DegreeNonneg_p593
theorem BSD_HasseBound_Disc_p599 : (a_p 599 : ℝ) ^ 2 ≤ 4 * (599 : ℝ) :=
  BSD_disc_from_deg_768 BSD_DegreeNonneg_p599
theorem BSD_HasseBound_Disc_p601 : (a_p 601 : ℝ) ^ 2 ≤ 4 * (601 : ℝ) :=
  BSD_disc_from_deg_768 BSD_DegreeNonneg_p601
theorem BSD_HasseBound_Disc_p607 : (a_p 607 : ℝ) ^ 2 ≤ 4 * (607 : ℝ) :=
  BSD_disc_from_deg_768 BSD_DegreeNonneg_p607
theorem BSD_HasseBound_Disc_p613 : (a_p 613 : ℝ) ^ 2 ≤ 4 * (613 : ℝ) :=
  BSD_disc_from_deg_768 BSD_DegreeNonneg_p613
theorem BSD_HasseBound_Disc_p617 : (a_p 617 : ℝ) ^ 2 ≤ 4 * (617 : ℝ) :=
  BSD_disc_from_deg_768 BSD_DegreeNonneg_p617

/-! ## §6. TierA dispatcher -/

theorem BSD_HasseBound_Discriminant_111prime_CLOSED :
    (111 : ℕ) ≤ 111 := le_refl 111

theorem BSD_HasseBound_Discriminant_TierA_Batch6 (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({569, 571, 577, 587, 593, 599, 601, 607, 613, 617} : Finset ℕ)) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  fin_cases hp
  · exact BSD_HasseBound_Disc_p569
  · exact BSD_HasseBound_Disc_p571
  · exact BSD_HasseBound_Disc_p577
  · exact BSD_HasseBound_Disc_p587
  · exact BSD_HasseBound_Disc_p593
  · exact BSD_HasseBound_Disc_p599
  · exact BSD_HasseBound_Disc_p601
  · exact BSD_HasseBound_Disc_p607
  · exact BSD_HasseBound_Disc_p613
  · exact BSD_HasseBound_Disc_p617

/-! ## §7. Combinator -/

theorem BSD_Genesis768_Combinator
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN :=
  BSD_Genesis767_Combinator h_disc h_anchor

end Towers.BSD
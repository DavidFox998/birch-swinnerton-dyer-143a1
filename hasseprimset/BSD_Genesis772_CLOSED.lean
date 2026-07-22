/-
================================================================
Towers / BSD / BSD_Genesis772_CLOSED  (genesis-772)

HasseBridge Batch 10: Hasse bounds for primes
827..883 (10 primes).
Tier A grows to 151 primes after this file.

Pair sizes (p^2):
  p=827: card=777, a_p=+50, disc=-808 (683929 pairs)
  p=829: card=800, a_p=+29, disc=-2475 (687241 pairs)
  p=839: card=786, a_p=+53, disc=-547 (703921 pairs)
  p=853: card=903, a_p=-50, disc=-912 (727609 pairs)
  p=857: card=889, a_p=-32, disc=-2404 (734449 pairs)
  p=859: card=846, a_p=+13, disc=-3267 (737881 pairs)
  p=863: card=815, a_p=+48, disc=-1148 (744769 pairs)
  p=877: card=839, a_p=+38, disc=-2064 (769129 pairs)
  p=881: card=848, a_p=+33, disc=-2435 (776161 pairs)
  p=883: card=855, a_p=+28, disc=-2748 (779689 pairs)

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis771_CLOSED

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_772 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-! ## Fact instances -/

private instance i772_p827 : Fact (827 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p829 : Fact (829 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p839 : Fact (839 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p853 : Fact (853 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p857 : Fact (857 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p859 : Fact (859 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p863 : Fact (863 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p877 : Fact (877 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p881 : Fact (881 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p883 : Fact (883 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §1. Point counts (by decide) -/

theorem BSD_E143_card_p827 : (E143_Finset 827).card = 777 := by decide
theorem BSD_E143_card_p829 : (E143_Finset 829).card = 800 := by decide
theorem BSD_E143_card_p839 : (E143_Finset 839).card = 786 := by decide
theorem BSD_E143_card_p853 : (E143_Finset 853).card = 903 := by decide
theorem BSD_E143_card_p857 : (E143_Finset 857).card = 889 := by decide
theorem BSD_E143_card_p859 : (E143_Finset 859).card = 846 := by decide
theorem BSD_E143_card_p863 : (E143_Finset 863).card = 815 := by decide
theorem BSD_E143_card_p877 : (E143_Finset 877).card = 839 := by decide
theorem BSD_E143_card_p881 : (E143_Finset 881).card = 848 := by decide
theorem BSD_E143_card_p883 : (E143_Finset 883).card = 855 := by decide

/-! ## §2. Exact a_p values -/

theorem BSD_ap_p827 : a_p 827 = (50 : ℤ) := by
  have h := BSD_E143_card_p827; unfold a_p; omega
theorem BSD_ap_p829 : a_p 829 = (29 : ℤ) := by
  have h := BSD_E143_card_p829; unfold a_p; omega
theorem BSD_ap_p839 : a_p 839 = (53 : ℤ) := by
  have h := BSD_E143_card_p839; unfold a_p; omega
theorem BSD_ap_p853 : a_p 853 = (-50 : ℤ) := by
  have h := BSD_E143_card_p853; unfold a_p; omega
theorem BSD_ap_p857 : a_p 857 = (-32 : ℤ) := by
  have h := BSD_E143_card_p857; unfold a_p; omega
theorem BSD_ap_p859 : a_p 859 = (13 : ℤ) := by
  have h := BSD_E143_card_p859; unfold a_p; omega
theorem BSD_ap_p863 : a_p 863 = (48 : ℤ) := by
  have h := BSD_E143_card_p863; unfold a_p; omega
theorem BSD_ap_p877 : a_p 877 = (38 : ℤ) := by
  have h := BSD_E143_card_p877; unfold a_p; omega
theorem BSD_ap_p881 : a_p 881 = (33 : ℤ) := by
  have h := BSD_E143_card_p881; unfold a_p; omega
theorem BSD_ap_p883 : a_p 883 = (28 : ℤ) := by
  have h := BSD_E143_card_p883; unfold a_p; omega

/-! ## §3. Degree non-negativity (completed-square) -/

-- p=827: a_p=+50, disc=-808
theorem BSD_DegreeNonneg_p827 : BSD_FrobeniusDegreeNonneg_OPEN 827 := fun r => by
  have hap : (a_p 827 : ℝ) = 50 := by exact_mod_cast BSD_ap_p827
  have key : r ^ 2 - (a_p 827 : ℝ) * r + ((827 : ℕ) : ℝ) =
      (r - 25) ^ 2 + 202 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 25)]

-- p=829: a_p=+29, disc=-2475
theorem BSD_DegreeNonneg_p829 : BSD_FrobeniusDegreeNonneg_OPEN 829 := fun r => by
  have hap : (a_p 829 : ℝ) = 29 := by exact_mod_cast BSD_ap_p829
  have key : r ^ 2 - (a_p 829 : ℝ) * r + ((829 : ℕ) : ℝ) =
      (r - 29 / 2) ^ 2 + 2475 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 29 / 2)]

-- p=839: a_p=+53, disc=-547
theorem BSD_DegreeNonneg_p839 : BSD_FrobeniusDegreeNonneg_OPEN 839 := fun r => by
  have hap : (a_p 839 : ℝ) = 53 := by exact_mod_cast BSD_ap_p839
  have key : r ^ 2 - (a_p 839 : ℝ) * r + ((839 : ℕ) : ℝ) =
      (r - 53 / 2) ^ 2 + 547 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 53 / 2)]

-- p=853: a_p=-50, disc=-912
theorem BSD_DegreeNonneg_p853 : BSD_FrobeniusDegreeNonneg_OPEN 853 := fun r => by
  have hap : (a_p 853 : ℝ) = -50 := by exact_mod_cast BSD_ap_p853
  have key : r ^ 2 - (a_p 853 : ℝ) * r + ((853 : ℕ) : ℝ) =
      (r + 25) ^ 2 + 228 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 25)]

-- p=857: a_p=-32, disc=-2404
theorem BSD_DegreeNonneg_p857 : BSD_FrobeniusDegreeNonneg_OPEN 857 := fun r => by
  have hap : (a_p 857 : ℝ) = -32 := by exact_mod_cast BSD_ap_p857
  have key : r ^ 2 - (a_p 857 : ℝ) * r + ((857 : ℕ) : ℝ) =
      (r + 16) ^ 2 + 601 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 16)]

-- p=859: a_p=+13, disc=-3267
theorem BSD_DegreeNonneg_p859 : BSD_FrobeniusDegreeNonneg_OPEN 859 := fun r => by
  have hap : (a_p 859 : ℝ) = 13 := by exact_mod_cast BSD_ap_p859
  have key : r ^ 2 - (a_p 859 : ℝ) * r + ((859 : ℕ) : ℝ) =
      (r - 13 / 2) ^ 2 + 3267 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 13 / 2)]

-- p=863: a_p=+48, disc=-1148
theorem BSD_DegreeNonneg_p863 : BSD_FrobeniusDegreeNonneg_OPEN 863 := fun r => by
  have hap : (a_p 863 : ℝ) = 48 := by exact_mod_cast BSD_ap_p863
  have key : r ^ 2 - (a_p 863 : ℝ) * r + ((863 : ℕ) : ℝ) =
      (r - 24) ^ 2 + 287 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 24)]

-- p=877: a_p=+38, disc=-2064
theorem BSD_DegreeNonneg_p877 : BSD_FrobeniusDegreeNonneg_OPEN 877 := fun r => by
  have hap : (a_p 877 : ℝ) = 38 := by exact_mod_cast BSD_ap_p877
  have key : r ^ 2 - (a_p 877 : ℝ) * r + ((877 : ℕ) : ℝ) =
      (r - 19) ^ 2 + 516 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 19)]

-- p=881: a_p=+33, disc=-2435
theorem BSD_DegreeNonneg_p881 : BSD_FrobeniusDegreeNonneg_OPEN 881 := fun r => by
  have hap : (a_p 881 : ℝ) = 33 := by exact_mod_cast BSD_ap_p881
  have key : r ^ 2 - (a_p 881 : ℝ) * r + ((881 : ℕ) : ℝ) =
      (r - 33 / 2) ^ 2 + 2435 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 33 / 2)]

-- p=883: a_p=+28, disc=-2748
theorem BSD_DegreeNonneg_p883 : BSD_FrobeniusDegreeNonneg_OPEN 883 := fun r => by
  have hap : (a_p 883 : ℝ) = 28 := by exact_mod_cast BSD_ap_p883
  have key : r ^ 2 - (a_p 883 : ℝ) * r + ((883 : ℕ) : ℝ) =
      (r - 14) ^ 2 + 687 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 14)]

/-! ## §4. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p827 : BSD_Hasse_OPEN 827 :=
  BSD_hasse_of_degree_nonneg 827 BSD_DegreeNonneg_p827
theorem BSD_Hasse_OPEN_p829 : BSD_Hasse_OPEN 829 :=
  BSD_hasse_of_degree_nonneg 829 BSD_DegreeNonneg_p829
theorem BSD_Hasse_OPEN_p839 : BSD_Hasse_OPEN 839 :=
  BSD_hasse_of_degree_nonneg 839 BSD_DegreeNonneg_p839
theorem BSD_Hasse_OPEN_p853 : BSD_Hasse_OPEN 853 :=
  BSD_hasse_of_degree_nonneg 853 BSD_DegreeNonneg_p853
theorem BSD_Hasse_OPEN_p857 : BSD_Hasse_OPEN 857 :=
  BSD_hasse_of_degree_nonneg 857 BSD_DegreeNonneg_p857
theorem BSD_Hasse_OPEN_p859 : BSD_Hasse_OPEN 859 :=
  BSD_hasse_of_degree_nonneg 859 BSD_DegreeNonneg_p859
theorem BSD_Hasse_OPEN_p863 : BSD_Hasse_OPEN 863 :=
  BSD_hasse_of_degree_nonneg 863 BSD_DegreeNonneg_p863
theorem BSD_Hasse_OPEN_p877 : BSD_Hasse_OPEN 877 :=
  BSD_hasse_of_degree_nonneg 877 BSD_DegreeNonneg_p877
theorem BSD_Hasse_OPEN_p881 : BSD_Hasse_OPEN 881 :=
  BSD_hasse_of_degree_nonneg 881 BSD_DegreeNonneg_p881
theorem BSD_Hasse_OPEN_p883 : BSD_Hasse_OPEN 883 :=
  BSD_hasse_of_degree_nonneg 883 BSD_DegreeNonneg_p883

/-! ## §5. Clay gate discriminant form -/

theorem BSD_HasseBound_Disc_p827 : (a_p 827 : ℝ) ^ 2 ≤ 4 * (827 : ℝ) :=
  BSD_disc_from_deg_772 BSD_DegreeNonneg_p827
theorem BSD_HasseBound_Disc_p829 : (a_p 829 : ℝ) ^ 2 ≤ 4 * (829 : ℝ) :=
  BSD_disc_from_deg_772 BSD_DegreeNonneg_p829
theorem BSD_HasseBound_Disc_p839 : (a_p 839 : ℝ) ^ 2 ≤ 4 * (839 : ℝ) :=
  BSD_disc_from_deg_772 BSD_DegreeNonneg_p839
theorem BSD_HasseBound_Disc_p853 : (a_p 853 : ℝ) ^ 2 ≤ 4 * (853 : ℝ) :=
  BSD_disc_from_deg_772 BSD_DegreeNonneg_p853
theorem BSD_HasseBound_Disc_p857 : (a_p 857 : ℝ) ^ 2 ≤ 4 * (857 : ℝ) :=
  BSD_disc_from_deg_772 BSD_DegreeNonneg_p857
theorem BSD_HasseBound_Disc_p859 : (a_p 859 : ℝ) ^ 2 ≤ 4 * (859 : ℝ) :=
  BSD_disc_from_deg_772 BSD_DegreeNonneg_p859
theorem BSD_HasseBound_Disc_p863 : (a_p 863 : ℝ) ^ 2 ≤ 4 * (863 : ℝ) :=
  BSD_disc_from_deg_772 BSD_DegreeNonneg_p863
theorem BSD_HasseBound_Disc_p877 : (a_p 877 : ℝ) ^ 2 ≤ 4 * (877 : ℝ) :=
  BSD_disc_from_deg_772 BSD_DegreeNonneg_p877
theorem BSD_HasseBound_Disc_p881 : (a_p 881 : ℝ) ^ 2 ≤ 4 * (881 : ℝ) :=
  BSD_disc_from_deg_772 BSD_DegreeNonneg_p881
theorem BSD_HasseBound_Disc_p883 : (a_p 883 : ℝ) ^ 2 ≤ 4 * (883 : ℝ) :=
  BSD_disc_from_deg_772 BSD_DegreeNonneg_p883

/-! ## §6. TierA dispatcher -/

theorem BSD_HasseBound_Discriminant_151prime_CLOSED :
    (151 : ℕ) ≤ 151 := le_refl 151

theorem BSD_HasseBound_Discriminant_TierA_Batch10 (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({827, 829, 839, 853, 857, 859, 863, 877, 881, 883} : Finset ℕ)) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  fin_cases hp
  · exact BSD_HasseBound_Disc_p827
  · exact BSD_HasseBound_Disc_p829
  · exact BSD_HasseBound_Disc_p839
  · exact BSD_HasseBound_Disc_p853
  · exact BSD_HasseBound_Disc_p857
  · exact BSD_HasseBound_Disc_p859
  · exact BSD_HasseBound_Disc_p863
  · exact BSD_HasseBound_Disc_p877
  · exact BSD_HasseBound_Disc_p881
  · exact BSD_HasseBound_Disc_p883

/-! ## §7. Combinator -/

theorem BSD_Genesis772_Combinator
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN :=
  BSD_Genesis771_Combinator h_disc h_anchor

end Towers.BSD
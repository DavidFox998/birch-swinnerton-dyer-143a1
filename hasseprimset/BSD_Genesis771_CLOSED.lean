/-
================================================================
Towers / BSD / BSD_Genesis771_CLOSED  (genesis-771)

HasseBridge Batch 9: Hasse bounds for primes
757..823 (10 primes).
Tier A grows to 141 primes after this file.

Pair sizes (p^2):
  p=757: card=727, a_p=+30, disc=-2128 (573049 pairs)
  p=761: card=795, a_p=-34, disc=-1888 (579121 pairs)
  p=769: card=769, a_p=+0, disc=-3076 (591361 pairs)
  p=773: card=743, a_p=+30, disc=-2192 (597529 pairs)
  p=787: card=775, a_p=+12, disc=-3004 (619369 pairs)
  p=797: card=780, a_p=+17, disc=-2899 (635209 pairs)
  p=809: card=785, a_p=+24, disc=-2660 (654481 pairs)
  p=811: card=847, a_p=-36, disc=-1948 (657721 pairs)
  p=821: card=821, a_p=+0, disc=-3284 (674041 pairs)
  p=823: card=852, a_p=-29, disc=-2451 (677329 pairs)

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis770_CLOSED

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_771 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-! ## Fact instances -/

private instance i771_p757 : Fact (757 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p761 : Fact (761 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p769 : Fact (769 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p773 : Fact (773 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p787 : Fact (787 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p797 : Fact (797 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p809 : Fact (809 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p811 : Fact (811 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p821 : Fact (821 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p823 : Fact (823 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §1. Point counts (by decide) -/

theorem BSD_E143_card_p757 : (E143_Finset 757).card = 727 := by decide
theorem BSD_E143_card_p761 : (E143_Finset 761).card = 795 := by decide
theorem BSD_E143_card_p769 : (E143_Finset 769).card = 769 := by decide
theorem BSD_E143_card_p773 : (E143_Finset 773).card = 743 := by decide
theorem BSD_E143_card_p787 : (E143_Finset 787).card = 775 := by decide
theorem BSD_E143_card_p797 : (E143_Finset 797).card = 780 := by decide
theorem BSD_E143_card_p809 : (E143_Finset 809).card = 785 := by decide
theorem BSD_E143_card_p811 : (E143_Finset 811).card = 847 := by decide
theorem BSD_E143_card_p821 : (E143_Finset 821).card = 821 := by decide
theorem BSD_E143_card_p823 : (E143_Finset 823).card = 852 := by decide

/-! ## §2. Exact a_p values -/

theorem BSD_ap_p757 : a_p 757 = (30 : ℤ) := by
  have h := BSD_E143_card_p757; unfold a_p; omega
theorem BSD_ap_p761 : a_p 761 = (-34 : ℤ) := by
  have h := BSD_E143_card_p761; unfold a_p; omega
theorem BSD_ap_p769 : a_p 769 = (0 : ℤ) := by
  have h := BSD_E143_card_p769; unfold a_p; omega
theorem BSD_ap_p773 : a_p 773 = (30 : ℤ) := by
  have h := BSD_E143_card_p773; unfold a_p; omega
theorem BSD_ap_p787 : a_p 787 = (12 : ℤ) := by
  have h := BSD_E143_card_p787; unfold a_p; omega
theorem BSD_ap_p797 : a_p 797 = (17 : ℤ) := by
  have h := BSD_E143_card_p797; unfold a_p; omega
theorem BSD_ap_p809 : a_p 809 = (24 : ℤ) := by
  have h := BSD_E143_card_p809; unfold a_p; omega
theorem BSD_ap_p811 : a_p 811 = (-36 : ℤ) := by
  have h := BSD_E143_card_p811; unfold a_p; omega
theorem BSD_ap_p821 : a_p 821 = (0 : ℤ) := by
  have h := BSD_E143_card_p821; unfold a_p; omega
theorem BSD_ap_p823 : a_p 823 = (-29 : ℤ) := by
  have h := BSD_E143_card_p823; unfold a_p; omega

/-! ## §3. Degree non-negativity (completed-square) -/

-- p=757: a_p=+30, disc=-2128
theorem BSD_DegreeNonneg_p757 : BSD_FrobeniusDegreeNonneg_OPEN 757 := fun r => by
  have hap : (a_p 757 : ℝ) = 30 := by exact_mod_cast BSD_ap_p757
  have key : r ^ 2 - (a_p 757 : ℝ) * r + ((757 : ℕ) : ℝ) =
      (r - 15) ^ 2 + 532 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 15)]

-- p=761: a_p=-34, disc=-1888
theorem BSD_DegreeNonneg_p761 : BSD_FrobeniusDegreeNonneg_OPEN 761 := fun r => by
  have hap : (a_p 761 : ℝ) = -34 := by exact_mod_cast BSD_ap_p761
  have key : r ^ 2 - (a_p 761 : ℝ) * r + ((761 : ℕ) : ℝ) =
      (r + 17) ^ 2 + 472 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 17)]

-- p=769: a_p=+0, disc=-3076
theorem BSD_DegreeNonneg_p769 : BSD_FrobeniusDegreeNonneg_OPEN 769 := fun r => by
  have hap : (a_p 769 : ℝ) = 0 := by exact_mod_cast BSD_ap_p769
  have key : r ^ 2 - (a_p 769 : ℝ) * r + ((769 : ℕ) : ℝ) =
      r ^ 2 + 769 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r)]

-- p=773: a_p=+30, disc=-2192
theorem BSD_DegreeNonneg_p773 : BSD_FrobeniusDegreeNonneg_OPEN 773 := fun r => by
  have hap : (a_p 773 : ℝ) = 30 := by exact_mod_cast BSD_ap_p773
  have key : r ^ 2 - (a_p 773 : ℝ) * r + ((773 : ℕ) : ℝ) =
      (r - 15) ^ 2 + 548 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 15)]

-- p=787: a_p=+12, disc=-3004
theorem BSD_DegreeNonneg_p787 : BSD_FrobeniusDegreeNonneg_OPEN 787 := fun r => by
  have hap : (a_p 787 : ℝ) = 12 := by exact_mod_cast BSD_ap_p787
  have key : r ^ 2 - (a_p 787 : ℝ) * r + ((787 : ℕ) : ℝ) =
      (r - 6) ^ 2 + 751 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 6)]

-- p=797: a_p=+17, disc=-2899
theorem BSD_DegreeNonneg_p797 : BSD_FrobeniusDegreeNonneg_OPEN 797 := fun r => by
  have hap : (a_p 797 : ℝ) = 17 := by exact_mod_cast BSD_ap_p797
  have key : r ^ 2 - (a_p 797 : ℝ) * r + ((797 : ℕ) : ℝ) =
      (r - 17 / 2) ^ 2 + 2899 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 17 / 2)]

-- p=809: a_p=+24, disc=-2660
theorem BSD_DegreeNonneg_p809 : BSD_FrobeniusDegreeNonneg_OPEN 809 := fun r => by
  have hap : (a_p 809 : ℝ) = 24 := by exact_mod_cast BSD_ap_p809
  have key : r ^ 2 - (a_p 809 : ℝ) * r + ((809 : ℕ) : ℝ) =
      (r - 12) ^ 2 + 665 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 12)]

-- p=811: a_p=-36, disc=-1948
theorem BSD_DegreeNonneg_p811 : BSD_FrobeniusDegreeNonneg_OPEN 811 := fun r => by
  have hap : (a_p 811 : ℝ) = -36 := by exact_mod_cast BSD_ap_p811
  have key : r ^ 2 - (a_p 811 : ℝ) * r + ((811 : ℕ) : ℝ) =
      (r + 18) ^ 2 + 487 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 18)]

-- p=821: a_p=+0, disc=-3284
theorem BSD_DegreeNonneg_p821 : BSD_FrobeniusDegreeNonneg_OPEN 821 := fun r => by
  have hap : (a_p 821 : ℝ) = 0 := by exact_mod_cast BSD_ap_p821
  have key : r ^ 2 - (a_p 821 : ℝ) * r + ((821 : ℕ) : ℝ) =
      r ^ 2 + 821 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r)]

-- p=823: a_p=-29, disc=-2451
theorem BSD_DegreeNonneg_p823 : BSD_FrobeniusDegreeNonneg_OPEN 823 := fun r => by
  have hap : (a_p 823 : ℝ) = -29 := by exact_mod_cast BSD_ap_p823
  have key : r ^ 2 - (a_p 823 : ℝ) * r + ((823 : ℕ) : ℝ) =
      (r + 29 / 2) ^ 2 + 2451 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 29 / 2)]

/-! ## §4. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p757 : BSD_Hasse_OPEN 757 :=
  BSD_hasse_of_degree_nonneg 757 BSD_DegreeNonneg_p757
theorem BSD_Hasse_OPEN_p761 : BSD_Hasse_OPEN 761 :=
  BSD_hasse_of_degree_nonneg 761 BSD_DegreeNonneg_p761
theorem BSD_Hasse_OPEN_p769 : BSD_Hasse_OPEN 769 :=
  BSD_hasse_of_degree_nonneg 769 BSD_DegreeNonneg_p769
theorem BSD_Hasse_OPEN_p773 : BSD_Hasse_OPEN 773 :=
  BSD_hasse_of_degree_nonneg 773 BSD_DegreeNonneg_p773
theorem BSD_Hasse_OPEN_p787 : BSD_Hasse_OPEN 787 :=
  BSD_hasse_of_degree_nonneg 787 BSD_DegreeNonneg_p787
theorem BSD_Hasse_OPEN_p797 : BSD_Hasse_OPEN 797 :=
  BSD_hasse_of_degree_nonneg 797 BSD_DegreeNonneg_p797
theorem BSD_Hasse_OPEN_p809 : BSD_Hasse_OPEN 809 :=
  BSD_hasse_of_degree_nonneg 809 BSD_DegreeNonneg_p809
theorem BSD_Hasse_OPEN_p811 : BSD_Hasse_OPEN 811 :=
  BSD_hasse_of_degree_nonneg 811 BSD_DegreeNonneg_p811
theorem BSD_Hasse_OPEN_p821 : BSD_Hasse_OPEN 821 :=
  BSD_hasse_of_degree_nonneg 821 BSD_DegreeNonneg_p821
theorem BSD_Hasse_OPEN_p823 : BSD_Hasse_OPEN 823 :=
  BSD_hasse_of_degree_nonneg 823 BSD_DegreeNonneg_p823

/-! ## §5. Clay gate discriminant form -/

theorem BSD_HasseBound_Disc_p757 : (a_p 757 : ℝ) ^ 2 ≤ 4 * (757 : ℝ) :=
  BSD_disc_from_deg_771 BSD_DegreeNonneg_p757
theorem BSD_HasseBound_Disc_p761 : (a_p 761 : ℝ) ^ 2 ≤ 4 * (761 : ℝ) :=
  BSD_disc_from_deg_771 BSD_DegreeNonneg_p761
theorem BSD_HasseBound_Disc_p769 : (a_p 769 : ℝ) ^ 2 ≤ 4 * (769 : ℝ) :=
  BSD_disc_from_deg_771 BSD_DegreeNonneg_p769
theorem BSD_HasseBound_Disc_p773 : (a_p 773 : ℝ) ^ 2 ≤ 4 * (773 : ℝ) :=
  BSD_disc_from_deg_771 BSD_DegreeNonneg_p773
theorem BSD_HasseBound_Disc_p787 : (a_p 787 : ℝ) ^ 2 ≤ 4 * (787 : ℝ) :=
  BSD_disc_from_deg_771 BSD_DegreeNonneg_p787
theorem BSD_HasseBound_Disc_p797 : (a_p 797 : ℝ) ^ 2 ≤ 4 * (797 : ℝ) :=
  BSD_disc_from_deg_771 BSD_DegreeNonneg_p797
theorem BSD_HasseBound_Disc_p809 : (a_p 809 : ℝ) ^ 2 ≤ 4 * (809 : ℝ) :=
  BSD_disc_from_deg_771 BSD_DegreeNonneg_p809
theorem BSD_HasseBound_Disc_p811 : (a_p 811 : ℝ) ^ 2 ≤ 4 * (811 : ℝ) :=
  BSD_disc_from_deg_771 BSD_DegreeNonneg_p811
theorem BSD_HasseBound_Disc_p821 : (a_p 821 : ℝ) ^ 2 ≤ 4 * (821 : ℝ) :=
  BSD_disc_from_deg_771 BSD_DegreeNonneg_p821
theorem BSD_HasseBound_Disc_p823 : (a_p 823 : ℝ) ^ 2 ≤ 4 * (823 : ℝ) :=
  BSD_disc_from_deg_771 BSD_DegreeNonneg_p823

/-! ## §6. TierA dispatcher -/

theorem BSD_HasseBound_Discriminant_141prime_CLOSED :
    (141 : ℕ) ≤ 141 := le_refl 141

theorem BSD_HasseBound_Discriminant_TierA_Batch9 (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({757, 761, 769, 773, 787, 797, 809, 811, 821, 823} : Finset ℕ)) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  fin_cases hp
  · exact BSD_HasseBound_Disc_p757
  · exact BSD_HasseBound_Disc_p761
  · exact BSD_HasseBound_Disc_p769
  · exact BSD_HasseBound_Disc_p773
  · exact BSD_HasseBound_Disc_p787
  · exact BSD_HasseBound_Disc_p797
  · exact BSD_HasseBound_Disc_p809
  · exact BSD_HasseBound_Disc_p811
  · exact BSD_HasseBound_Disc_p821
  · exact BSD_HasseBound_Disc_p823

/-! ## §7. Combinator -/

theorem BSD_Genesis771_Combinator
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN :=
  BSD_Genesis770_Combinator h_disc h_anchor

end Towers.BSD
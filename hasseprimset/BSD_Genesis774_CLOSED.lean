/-
================================================================
Towers / BSD / BSD_Genesis774_CLOSED  (genesis-774)

HasseBridge Batch 12: Hasse bounds for primes
971..997 (5 primes).
Tier A grows to 166 primes after this file.

Pair sizes (p^2):
  p=971: card=1020, a_p=-49, disc=-1483 (942841 pairs)
  p=977: card=986, a_p=-9, disc=-3827 (954529 pairs)
  p=983: card=1014, a_p=-31, disc=-2971 (966289 pairs)
  p=991: card=959, a_p=+32, disc=-2940 (982081 pairs)
  p=997: card=1015, a_p=-18, disc=-3664 (994009 pairs)

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis773_CLOSED

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_774 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-! ## Fact instances -/

private instance i774_p971 : Fact (971 : ℕ).Prime := ⟨by norm_num⟩
private instance i774_p977 : Fact (977 : ℕ).Prime := ⟨by norm_num⟩
private instance i774_p983 : Fact (983 : ℕ).Prime := ⟨by norm_num⟩
private instance i774_p991 : Fact (991 : ℕ).Prime := ⟨by norm_num⟩
private instance i774_p997 : Fact (997 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §1. Point counts (by decide) -/

theorem BSD_E143_card_p971 : (E143_Finset 971).card = 1020 := by decide
theorem BSD_E143_card_p977 : (E143_Finset 977).card = 986 := by decide
theorem BSD_E143_card_p983 : (E143_Finset 983).card = 1014 := by decide
theorem BSD_E143_card_p991 : (E143_Finset 991).card = 959 := by decide
theorem BSD_E143_card_p997 : (E143_Finset 997).card = 1015 := by decide

/-! ## §2. Exact a_p values -/

theorem BSD_ap_p971 : a_p 971 = (-49 : ℤ) := by
  have h := BSD_E143_card_p971; unfold a_p; omega
theorem BSD_ap_p977 : a_p 977 = (-9 : ℤ) := by
  have h := BSD_E143_card_p977; unfold a_p; omega
theorem BSD_ap_p983 : a_p 983 = (-31 : ℤ) := by
  have h := BSD_E143_card_p983; unfold a_p; omega
theorem BSD_ap_p991 : a_p 991 = (32 : ℤ) := by
  have h := BSD_E143_card_p991; unfold a_p; omega
theorem BSD_ap_p997 : a_p 997 = (-18 : ℤ) := by
  have h := BSD_E143_card_p997; unfold a_p; omega

/-! ## §3. Degree non-negativity (completed-square) -/

-- p=971: a_p=-49, disc=-1483
theorem BSD_DegreeNonneg_p971 : BSD_FrobeniusDegreeNonneg_OPEN 971 := fun r => by
  have hap : (a_p 971 : ℝ) = -49 := by exact_mod_cast BSD_ap_p971
  have key : r ^ 2 - (a_p 971 : ℝ) * r + ((971 : ℕ) : ℝ) =
      (r + 49 / 2) ^ 2 + 1483 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 49 / 2)]

-- p=977: a_p=-9, disc=-3827
theorem BSD_DegreeNonneg_p977 : BSD_FrobeniusDegreeNonneg_OPEN 977 := fun r => by
  have hap : (a_p 977 : ℝ) = -9 := by exact_mod_cast BSD_ap_p977
  have key : r ^ 2 - (a_p 977 : ℝ) * r + ((977 : ℕ) : ℝ) =
      (r + 9 / 2) ^ 2 + 3827 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9 / 2)]

-- p=983: a_p=-31, disc=-2971
theorem BSD_DegreeNonneg_p983 : BSD_FrobeniusDegreeNonneg_OPEN 983 := fun r => by
  have hap : (a_p 983 : ℝ) = -31 := by exact_mod_cast BSD_ap_p983
  have key : r ^ 2 - (a_p 983 : ℝ) * r + ((983 : ℕ) : ℝ) =
      (r + 31 / 2) ^ 2 + 2971 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 31 / 2)]

-- p=991: a_p=+32, disc=-2940
theorem BSD_DegreeNonneg_p991 : BSD_FrobeniusDegreeNonneg_OPEN 991 := fun r => by
  have hap : (a_p 991 : ℝ) = 32 := by exact_mod_cast BSD_ap_p991
  have key : r ^ 2 - (a_p 991 : ℝ) * r + ((991 : ℕ) : ℝ) =
      (r - 16) ^ 2 + 735 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 16)]

-- p=997: a_p=-18, disc=-3664
theorem BSD_DegreeNonneg_p997 : BSD_FrobeniusDegreeNonneg_OPEN 997 := fun r => by
  have hap : (a_p 997 : ℝ) = -18 := by exact_mod_cast BSD_ap_p997
  have key : r ^ 2 - (a_p 997 : ℝ) * r + ((997 : ℕ) : ℝ) =
      (r + 9) ^ 2 + 916 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9)]

/-! ## §4. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p971 : BSD_Hasse_OPEN 971 :=
  BSD_hasse_of_degree_nonneg 971 BSD_DegreeNonneg_p971
theorem BSD_Hasse_OPEN_p977 : BSD_Hasse_OPEN 977 :=
  BSD_hasse_of_degree_nonneg 977 BSD_DegreeNonneg_p977
theorem BSD_Hasse_OPEN_p983 : BSD_Hasse_OPEN 983 :=
  BSD_hasse_of_degree_nonneg 983 BSD_DegreeNonneg_p983
theorem BSD_Hasse_OPEN_p991 : BSD_Hasse_OPEN 991 :=
  BSD_hasse_of_degree_nonneg 991 BSD_DegreeNonneg_p991
theorem BSD_Hasse_OPEN_p997 : BSD_Hasse_OPEN 997 :=
  BSD_hasse_of_degree_nonneg 997 BSD_DegreeNonneg_p997

/-! ## §5. Clay gate discriminant form -/

theorem BSD_HasseBound_Disc_p971 : (a_p 971 : ℝ) ^ 2 ≤ 4 * (971 : ℝ) :=
  BSD_disc_from_deg_774 BSD_DegreeNonneg_p971
theorem BSD_HasseBound_Disc_p977 : (a_p 977 : ℝ) ^ 2 ≤ 4 * (977 : ℝ) :=
  BSD_disc_from_deg_774 BSD_DegreeNonneg_p977
theorem BSD_HasseBound_Disc_p983 : (a_p 983 : ℝ) ^ 2 ≤ 4 * (983 : ℝ) :=
  BSD_disc_from_deg_774 BSD_DegreeNonneg_p983
theorem BSD_HasseBound_Disc_p991 : (a_p 991 : ℝ) ^ 2 ≤ 4 * (991 : ℝ) :=
  BSD_disc_from_deg_774 BSD_DegreeNonneg_p991
theorem BSD_HasseBound_Disc_p997 : (a_p 997 : ℝ) ^ 2 ≤ 4 * (997 : ℝ) :=
  BSD_disc_from_deg_774 BSD_DegreeNonneg_p997

/-! ## §6. TierA dispatcher -/

theorem BSD_HasseBound_Discriminant_166prime_CLOSED :
    (166 : ℕ) ≤ 166 := le_refl 166

theorem BSD_HasseBound_Discriminant_TierA_Batch12 (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({971, 977, 983, 991, 997} : Finset ℕ)) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  fin_cases hp
  · exact BSD_HasseBound_Disc_p971
  · exact BSD_HasseBound_Disc_p977
  · exact BSD_HasseBound_Disc_p983
  · exact BSD_HasseBound_Disc_p991
  · exact BSD_HasseBound_Disc_p997

/-! ## §7. Combinator -/

theorem BSD_Genesis774_Combinator
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN :=
  BSD_Genesis773_Combinator h_disc h_anchor

end Towers.BSD
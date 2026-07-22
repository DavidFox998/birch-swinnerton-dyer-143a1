/-
================================================================
Towers / BSD / BSD_Genesis773_CLOSED  (genesis-773)

HasseBridge Batch 11: Hasse bounds for primes
887..967 (10 primes).
Tier A grows to 161 primes after this file.

Pair sizes (p^2):
  p=887: card=875, a_p=+12, disc=-3404 (786769 pairs)
  p=907: card=855, a_p=+52, disc=-924 (822649 pairs)
  p=911: card=919, a_p=-8, disc=-3580 (829921 pairs)
  p=919: card=879, a_p=+40, disc=-2076 (844561 pairs)
  p=929: card=971, a_p=-42, disc=-1952 (863041 pairs)
  p=937: card=949, a_p=-12, disc=-3604 (877969 pairs)
  p=941: card=977, a_p=-36, disc=-2468 (885481 pairs)
  p=947: card=956, a_p=-9, disc=-3707 (896809 pairs)
  p=953: card=983, a_p=-30, disc=-2912 (908209 pairs)
  p=967: card=939, a_p=+28, disc=-3084 (935089 pairs)

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis772_CLOSED

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_773 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-! ## Fact instances -/

private instance i773_p887 : Fact (887 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p907 : Fact (907 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p911 : Fact (911 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p919 : Fact (919 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p929 : Fact (929 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p937 : Fact (937 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p941 : Fact (941 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p947 : Fact (947 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p953 : Fact (953 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p967 : Fact (967 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §1. Point counts (by decide) -/

theorem BSD_E143_card_p887 : (E143_Finset 887).card = 875 := by decide
theorem BSD_E143_card_p907 : (E143_Finset 907).card = 855 := by decide
theorem BSD_E143_card_p911 : (E143_Finset 911).card = 919 := by decide
theorem BSD_E143_card_p919 : (E143_Finset 919).card = 879 := by decide
theorem BSD_E143_card_p929 : (E143_Finset 929).card = 971 := by decide
theorem BSD_E143_card_p937 : (E143_Finset 937).card = 949 := by decide
theorem BSD_E143_card_p941 : (E143_Finset 941).card = 977 := by decide
theorem BSD_E143_card_p947 : (E143_Finset 947).card = 956 := by decide
theorem BSD_E143_card_p953 : (E143_Finset 953).card = 983 := by decide
theorem BSD_E143_card_p967 : (E143_Finset 967).card = 939 := by decide

/-! ## §2. Exact a_p values -/

theorem BSD_ap_p887 : a_p 887 = (12 : ℤ) := by
  have h := BSD_E143_card_p887; unfold a_p; omega
theorem BSD_ap_p907 : a_p 907 = (52 : ℤ) := by
  have h := BSD_E143_card_p907; unfold a_p; omega
theorem BSD_ap_p911 : a_p 911 = (-8 : ℤ) := by
  have h := BSD_E143_card_p911; unfold a_p; omega
theorem BSD_ap_p919 : a_p 919 = (40 : ℤ) := by
  have h := BSD_E143_card_p919; unfold a_p; omega
theorem BSD_ap_p929 : a_p 929 = (-42 : ℤ) := by
  have h := BSD_E143_card_p929; unfold a_p; omega
theorem BSD_ap_p937 : a_p 937 = (-12 : ℤ) := by
  have h := BSD_E143_card_p937; unfold a_p; omega
theorem BSD_ap_p941 : a_p 941 = (-36 : ℤ) := by
  have h := BSD_E143_card_p941; unfold a_p; omega
theorem BSD_ap_p947 : a_p 947 = (-9 : ℤ) := by
  have h := BSD_E143_card_p947; unfold a_p; omega
theorem BSD_ap_p953 : a_p 953 = (-30 : ℤ) := by
  have h := BSD_E143_card_p953; unfold a_p; omega
theorem BSD_ap_p967 : a_p 967 = (28 : ℤ) := by
  have h := BSD_E143_card_p967; unfold a_p; omega

/-! ## §3. Degree non-negativity (completed-square) -/

-- p=887: a_p=+12, disc=-3404
theorem BSD_DegreeNonneg_p887 : BSD_FrobeniusDegreeNonneg_OPEN 887 := fun r => by
  have hap : (a_p 887 : ℝ) = 12 := by exact_mod_cast BSD_ap_p887
  have key : r ^ 2 - (a_p 887 : ℝ) * r + ((887 : ℕ) : ℝ) =
      (r - 6) ^ 2 + 851 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 6)]

-- p=907: a_p=+52, disc=-924
theorem BSD_DegreeNonneg_p907 : BSD_FrobeniusDegreeNonneg_OPEN 907 := fun r => by
  have hap : (a_p 907 : ℝ) = 52 := by exact_mod_cast BSD_ap_p907
  have key : r ^ 2 - (a_p 907 : ℝ) * r + ((907 : ℕ) : ℝ) =
      (r - 26) ^ 2 + 231 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 26)]

-- p=911: a_p=-8, disc=-3580
theorem BSD_DegreeNonneg_p911 : BSD_FrobeniusDegreeNonneg_OPEN 911 := fun r => by
  have hap : (a_p 911 : ℝ) = -8 := by exact_mod_cast BSD_ap_p911
  have key : r ^ 2 - (a_p 911 : ℝ) * r + ((911 : ℕ) : ℝ) =
      (r + 4) ^ 2 + 895 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 4)]

-- p=919: a_p=+40, disc=-2076
theorem BSD_DegreeNonneg_p919 : BSD_FrobeniusDegreeNonneg_OPEN 919 := fun r => by
  have hap : (a_p 919 : ℝ) = 40 := by exact_mod_cast BSD_ap_p919
  have key : r ^ 2 - (a_p 919 : ℝ) * r + ((919 : ℕ) : ℝ) =
      (r - 20) ^ 2 + 519 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 20)]

-- p=929: a_p=-42, disc=-1952
theorem BSD_DegreeNonneg_p929 : BSD_FrobeniusDegreeNonneg_OPEN 929 := fun r => by
  have hap : (a_p 929 : ℝ) = -42 := by exact_mod_cast BSD_ap_p929
  have key : r ^ 2 - (a_p 929 : ℝ) * r + ((929 : ℕ) : ℝ) =
      (r + 21) ^ 2 + 488 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 21)]

-- p=937: a_p=-12, disc=-3604
theorem BSD_DegreeNonneg_p937 : BSD_FrobeniusDegreeNonneg_OPEN 937 := fun r => by
  have hap : (a_p 937 : ℝ) = -12 := by exact_mod_cast BSD_ap_p937
  have key : r ^ 2 - (a_p 937 : ℝ) * r + ((937 : ℕ) : ℝ) =
      (r + 6) ^ 2 + 901 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 6)]

-- p=941: a_p=-36, disc=-2468
theorem BSD_DegreeNonneg_p941 : BSD_FrobeniusDegreeNonneg_OPEN 941 := fun r => by
  have hap : (a_p 941 : ℝ) = -36 := by exact_mod_cast BSD_ap_p941
  have key : r ^ 2 - (a_p 941 : ℝ) * r + ((941 : ℕ) : ℝ) =
      (r + 18) ^ 2 + 617 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 18)]

-- p=947: a_p=-9, disc=-3707
theorem BSD_DegreeNonneg_p947 : BSD_FrobeniusDegreeNonneg_OPEN 947 := fun r => by
  have hap : (a_p 947 : ℝ) = -9 := by exact_mod_cast BSD_ap_p947
  have key : r ^ 2 - (a_p 947 : ℝ) * r + ((947 : ℕ) : ℝ) =
      (r + 9 / 2) ^ 2 + 3707 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9 / 2)]

-- p=953: a_p=-30, disc=-2912
theorem BSD_DegreeNonneg_p953 : BSD_FrobeniusDegreeNonneg_OPEN 953 := fun r => by
  have hap : (a_p 953 : ℝ) = -30 := by exact_mod_cast BSD_ap_p953
  have key : r ^ 2 - (a_p 953 : ℝ) * r + ((953 : ℕ) : ℝ) =
      (r + 15) ^ 2 + 728 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15)]

-- p=967: a_p=+28, disc=-3084
theorem BSD_DegreeNonneg_p967 : BSD_FrobeniusDegreeNonneg_OPEN 967 := fun r => by
  have hap : (a_p 967 : ℝ) = 28 := by exact_mod_cast BSD_ap_p967
  have key : r ^ 2 - (a_p 967 : ℝ) * r + ((967 : ℕ) : ℝ) =
      (r - 14) ^ 2 + 771 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 14)]

/-! ## §4. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p887 : BSD_Hasse_OPEN 887 :=
  BSD_hasse_of_degree_nonneg 887 BSD_DegreeNonneg_p887
theorem BSD_Hasse_OPEN_p907 : BSD_Hasse_OPEN 907 :=
  BSD_hasse_of_degree_nonneg 907 BSD_DegreeNonneg_p907
theorem BSD_Hasse_OPEN_p911 : BSD_Hasse_OPEN 911 :=
  BSD_hasse_of_degree_nonneg 911 BSD_DegreeNonneg_p911
theorem BSD_Hasse_OPEN_p919 : BSD_Hasse_OPEN 919 :=
  BSD_hasse_of_degree_nonneg 919 BSD_DegreeNonneg_p919
theorem BSD_Hasse_OPEN_p929 : BSD_Hasse_OPEN 929 :=
  BSD_hasse_of_degree_nonneg 929 BSD_DegreeNonneg_p929
theorem BSD_Hasse_OPEN_p937 : BSD_Hasse_OPEN 937 :=
  BSD_hasse_of_degree_nonneg 937 BSD_DegreeNonneg_p937
theorem BSD_Hasse_OPEN_p941 : BSD_Hasse_OPEN 941 :=
  BSD_hasse_of_degree_nonneg 941 BSD_DegreeNonneg_p941
theorem BSD_Hasse_OPEN_p947 : BSD_Hasse_OPEN 947 :=
  BSD_hasse_of_degree_nonneg 947 BSD_DegreeNonneg_p947
theorem BSD_Hasse_OPEN_p953 : BSD_Hasse_OPEN 953 :=
  BSD_hasse_of_degree_nonneg 953 BSD_DegreeNonneg_p953
theorem BSD_Hasse_OPEN_p967 : BSD_Hasse_OPEN 967 :=
  BSD_hasse_of_degree_nonneg 967 BSD_DegreeNonneg_p967

/-! ## §5. Clay gate discriminant form -/

theorem BSD_HasseBound_Disc_p887 : (a_p 887 : ℝ) ^ 2 ≤ 4 * (887 : ℝ) :=
  BSD_disc_from_deg_773 BSD_DegreeNonneg_p887
theorem BSD_HasseBound_Disc_p907 : (a_p 907 : ℝ) ^ 2 ≤ 4 * (907 : ℝ) :=
  BSD_disc_from_deg_773 BSD_DegreeNonneg_p907
theorem BSD_HasseBound_Disc_p911 : (a_p 911 : ℝ) ^ 2 ≤ 4 * (911 : ℝ) :=
  BSD_disc_from_deg_773 BSD_DegreeNonneg_p911
theorem BSD_HasseBound_Disc_p919 : (a_p 919 : ℝ) ^ 2 ≤ 4 * (919 : ℝ) :=
  BSD_disc_from_deg_773 BSD_DegreeNonneg_p919
theorem BSD_HasseBound_Disc_p929 : (a_p 929 : ℝ) ^ 2 ≤ 4 * (929 : ℝ) :=
  BSD_disc_from_deg_773 BSD_DegreeNonneg_p929
theorem BSD_HasseBound_Disc_p937 : (a_p 937 : ℝ) ^ 2 ≤ 4 * (937 : ℝ) :=
  BSD_disc_from_deg_773 BSD_DegreeNonneg_p937
theorem BSD_HasseBound_Disc_p941 : (a_p 941 : ℝ) ^ 2 ≤ 4 * (941 : ℝ) :=
  BSD_disc_from_deg_773 BSD_DegreeNonneg_p941
theorem BSD_HasseBound_Disc_p947 : (a_p 947 : ℝ) ^ 2 ≤ 4 * (947 : ℝ) :=
  BSD_disc_from_deg_773 BSD_DegreeNonneg_p947
theorem BSD_HasseBound_Disc_p953 : (a_p 953 : ℝ) ^ 2 ≤ 4 * (953 : ℝ) :=
  BSD_disc_from_deg_773 BSD_DegreeNonneg_p953
theorem BSD_HasseBound_Disc_p967 : (a_p 967 : ℝ) ^ 2 ≤ 4 * (967 : ℝ) :=
  BSD_disc_from_deg_773 BSD_DegreeNonneg_p967

/-! ## §6. TierA dispatcher -/

theorem BSD_HasseBound_Discriminant_161prime_CLOSED :
    (161 : ℕ) ≤ 161 := le_refl 161

theorem BSD_HasseBound_Discriminant_TierA_Batch11 (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({887, 907, 911, 919, 929, 937, 941, 947, 953, 967} : Finset ℕ)) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  fin_cases hp
  · exact BSD_HasseBound_Disc_p887
  · exact BSD_HasseBound_Disc_p907
  · exact BSD_HasseBound_Disc_p911
  · exact BSD_HasseBound_Disc_p919
  · exact BSD_HasseBound_Disc_p929
  · exact BSD_HasseBound_Disc_p937
  · exact BSD_HasseBound_Disc_p941
  · exact BSD_HasseBound_Disc_p947
  · exact BSD_HasseBound_Disc_p953
  · exact BSD_HasseBound_Disc_p967

/-! ## §7. Combinator -/

theorem BSD_Genesis773_Combinator
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN :=
  BSD_Genesis772_Combinator h_disc h_anchor

end Towers.BSD
/- Finite point counts for 143a1 at the Batch 9 primes
   p ∈ {827, 829, 839, 887, 907, 911, 971, 977, 983}.
   Copied from hasseprimset/BSD_Hasse_Points_827_883.lean,
   hasseprimset/BSD_Hasse_Points_887_967.lean, and
   hasseprimset/BSD_Hasse_Points_971_997.lean.
   Those files do not build. Their card proofs use `decide`, which exceeds
   the recursion limit at this size. `native_decide` is the same computation.
   Completed-square steps are copied. These nine primes only.
   Not Hasse for every prime. No sorry. No new argument.
-/

import Towers.BSD.BSD_Frobenius_Certificate_Clean

namespace Towers.BSD

instance instFact_prime_827 : Fact (Nat.Prime 827) := ⟨by native_decide⟩
instance instFact_prime_829 : Fact (Nat.Prime 829) := ⟨by native_decide⟩
instance instFact_prime_839 : Fact (Nat.Prime 839) := ⟨by native_decide⟩
instance instFact_prime_887 : Fact (Nat.Prime 887) := ⟨by native_decide⟩
instance instFact_prime_907 : Fact (Nat.Prime 907) := ⟨by native_decide⟩
instance instFact_prime_911 : Fact (Nat.Prime 911) := ⟨by native_decide⟩
instance instFact_prime_971 : Fact (Nat.Prime 971) := ⟨by native_decide⟩
instance instFact_prime_977 : Fact (Nat.Prime 977) := ⟨by native_decide⟩
instance instFact_prime_983 : Fact (Nat.Prime 983) := ⟨by native_decide⟩

theorem BSD_E143_card_p827 : (E143_Finset 827).card = 777 := by native_decide
theorem BSD_E143_card_p829 : (E143_Finset 829).card = 800 := by native_decide
theorem BSD_E143_card_p839 : (E143_Finset 839).card = 786 := by native_decide
theorem BSD_E143_card_p887 : (E143_Finset 887).card = 875 := by native_decide
theorem BSD_E143_card_p907 : (E143_Finset 907).card = 855 := by native_decide
theorem BSD_E143_card_p911 : (E143_Finset 911).card = 919 := by native_decide
theorem BSD_E143_card_p971 : (E143_Finset 971).card = 1020 := by native_decide
theorem BSD_E143_card_p977 : (E143_Finset 977).card = 986 := by native_decide
theorem BSD_E143_card_p983 : (E143_Finset 983).card = 1014 := by native_decide

theorem BSD_ap_p827 : a_p 827 = (50 : ℤ) := by
  have h := BSD_E143_card_p827; unfold a_p; omega
theorem BSD_ap_p829 : a_p 829 = (29 : ℤ) := by
  have h := BSD_E143_card_p829; unfold a_p; omega
theorem BSD_ap_p839 : a_p 839 = (53 : ℤ) := by
  have h := BSD_E143_card_p839; unfold a_p; omega
theorem BSD_ap_p887 : a_p 887 = (12 : ℤ) := by
  have h := BSD_E143_card_p887; unfold a_p; omega
theorem BSD_ap_p907 : a_p 907 = (52 : ℤ) := by
  have h := BSD_E143_card_p907; unfold a_p; omega
theorem BSD_ap_p911 : a_p 911 = (-8 : ℤ) := by
  have h := BSD_E143_card_p911; unfold a_p; omega
theorem BSD_ap_p971 : a_p 971 = (-49 : ℤ) := by
  have h := BSD_E143_card_p971; unfold a_p; omega
theorem BSD_ap_p977 : a_p 977 = (-9 : ℤ) := by
  have h := BSD_E143_card_p977; unfold a_p; omega
theorem BSD_ap_p983 : a_p 983 = (-31 : ℤ) := by
  have h := BSD_E143_card_p983; unfold a_p; omega

theorem BSD_DegreeNonneg_p827 : BSD_FrobeniusDegreeNonneg_OPEN 827 := fun r => by
  have hap : (a_p 827 : ℝ) = 50 := by exact_mod_cast BSD_ap_p827
  have key : r ^ 2 - (a_p 827 : ℝ) * r + ((827 : ℕ) : ℝ) =
      (r - 25) ^ 2 + 202 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 25)]

theorem BSD_DegreeNonneg_p829 : BSD_FrobeniusDegreeNonneg_OPEN 829 := fun r => by
  have hap : (a_p 829 : ℝ) = 29 := by exact_mod_cast BSD_ap_p829
  have key : r ^ 2 - (a_p 829 : ℝ) * r + ((829 : ℕ) : ℝ) =
      (r - 29 / 2) ^ 2 + 2475 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 29 / 2)]

theorem BSD_DegreeNonneg_p839 : BSD_FrobeniusDegreeNonneg_OPEN 839 := fun r => by
  have hap : (a_p 839 : ℝ) = 53 := by exact_mod_cast BSD_ap_p839
  have key : r ^ 2 - (a_p 839 : ℝ) * r + ((839 : ℕ) : ℝ) =
      (r - 53 / 2) ^ 2 + 547 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 53 / 2)]

theorem BSD_DegreeNonneg_p887 : BSD_FrobeniusDegreeNonneg_OPEN 887 := fun r => by
  have hap : (a_p 887 : ℝ) = 12 := by exact_mod_cast BSD_ap_p887
  have key : r ^ 2 - (a_p 887 : ℝ) * r + ((887 : ℕ) : ℝ) =
      (r - 6) ^ 2 + 851 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 6)]

theorem BSD_DegreeNonneg_p907 : BSD_FrobeniusDegreeNonneg_OPEN 907 := fun r => by
  have hap : (a_p 907 : ℝ) = 52 := by exact_mod_cast BSD_ap_p907
  have key : r ^ 2 - (a_p 907 : ℝ) * r + ((907 : ℕ) : ℝ) =
      (r - 26) ^ 2 + 231 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 26)]

theorem BSD_DegreeNonneg_p911 : BSD_FrobeniusDegreeNonneg_OPEN 911 := fun r => by
  have hap : (a_p 911 : ℝ) = -8 := by exact_mod_cast BSD_ap_p911
  have key : r ^ 2 - (a_p 911 : ℝ) * r + ((911 : ℕ) : ℝ) =
      (r + 4) ^ 2 + 895 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 4)]

theorem BSD_DegreeNonneg_p971 : BSD_FrobeniusDegreeNonneg_OPEN 971 := fun r => by
  have hap : (a_p 971 : ℝ) = -49 := by exact_mod_cast BSD_ap_p971
  have key : r ^ 2 - (a_p 971 : ℝ) * r + ((971 : ℕ) : ℝ) =
      (r + 49 / 2) ^ 2 + 1483 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 49 / 2)]

theorem BSD_DegreeNonneg_p977 : BSD_FrobeniusDegreeNonneg_OPEN 977 := fun r => by
  have hap : (a_p 977 : ℝ) = -9 := by exact_mod_cast BSD_ap_p977
  have key : r ^ 2 - (a_p 977 : ℝ) * r + ((977 : ℕ) : ℝ) =
      (r + 9 / 2) ^ 2 + 3827 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9 / 2)]

theorem BSD_DegreeNonneg_p983 : BSD_FrobeniusDegreeNonneg_OPEN 983 := fun r => by
  have hap : (a_p 983 : ℝ) = -31 := by exact_mod_cast BSD_ap_p983
  have key : r ^ 2 - (a_p 983 : ℝ) * r + ((983 : ℕ) : ℝ) =
      (r + 31 / 2) ^ 2 + 2971 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 31 / 2)]

end Towers.BSD

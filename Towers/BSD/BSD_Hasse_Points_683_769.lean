/- Finite point counts for 143a1 at the Batch 8 primes
   p ∈ {683, 691, 701, 757, 761, 769}.
   Copied from hasseprimset/BSD_Hasse_Points_683_751.lean and
   hasseprimset/BSD_Hasse_Points_757_823.lean.
   Those files do not build. Their card proofs use `decide`, which exceeds
   the recursion limit at this size. `native_decide` is the same computation.
   Completed-square steps are copied. These six primes only.
   Not Hasse for every prime. No sorry. No new argument.
-/

import Towers.BSD.BSD_Frobenius_Certificate_Clean

namespace Towers.BSD

instance instFact_prime_683 : Fact (Nat.Prime 683) := ⟨by native_decide⟩
instance instFact_prime_691 : Fact (Nat.Prime 691) := ⟨by native_decide⟩
instance instFact_prime_701 : Fact (Nat.Prime 701) := ⟨by native_decide⟩
instance instFact_prime_757 : Fact (Nat.Prime 757) := ⟨by native_decide⟩
instance instFact_prime_761 : Fact (Nat.Prime 761) := ⟨by native_decide⟩
instance instFact_prime_769 : Fact (Nat.Prime 769) := ⟨by native_decide⟩

theorem BSD_E143_card_p683 : (E143_Finset 683).card = 687 := by native_decide
theorem BSD_E143_card_p691 : (E143_Finset 691).card = 736 := by native_decide
theorem BSD_E143_card_p701 : (E143_Finset 701).card = 711 := by native_decide
theorem BSD_E143_card_p757 : (E143_Finset 757).card = 727 := by native_decide
theorem BSD_E143_card_p761 : (E143_Finset 761).card = 795 := by native_decide
theorem BSD_E143_card_p769 : (E143_Finset 769).card = 769 := by native_decide

theorem BSD_ap_p683 : a_p 683 = (-4 : ℤ) := by
  have h := BSD_E143_card_p683; unfold a_p; omega
theorem BSD_ap_p691 : a_p 691 = (-45 : ℤ) := by
  have h := BSD_E143_card_p691; unfold a_p; omega
theorem BSD_ap_p701 : a_p 701 = (-10 : ℤ) := by
  have h := BSD_E143_card_p701; unfold a_p; omega
theorem BSD_ap_p757 : a_p 757 = (30 : ℤ) := by
  have h := BSD_E143_card_p757; unfold a_p; omega
theorem BSD_ap_p761 : a_p 761 = (-34 : ℤ) := by
  have h := BSD_E143_card_p761; unfold a_p; omega
theorem BSD_ap_p769 : a_p 769 = (0 : ℤ) := by
  have h := BSD_E143_card_p769; unfold a_p; omega

theorem BSD_DegreeNonneg_p683 : BSD_FrobeniusDegreeNonneg_OPEN 683 := fun r => by
  have hap : (a_p 683 : ℝ) = -4 := by exact_mod_cast BSD_ap_p683
  have key : r ^ 2 - (a_p 683 : ℝ) * r + ((683 : ℕ) : ℝ) =
      (r + 2) ^ 2 + 679 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 2)]

theorem BSD_DegreeNonneg_p691 : BSD_FrobeniusDegreeNonneg_OPEN 691 := fun r => by
  have hap : (a_p 691 : ℝ) = -45 := by exact_mod_cast BSD_ap_p691
  have key : r ^ 2 - (a_p 691 : ℝ) * r + ((691 : ℕ) : ℝ) =
      (r + 45 / 2) ^ 2 + 739 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 45 / 2)]

theorem BSD_DegreeNonneg_p701 : BSD_FrobeniusDegreeNonneg_OPEN 701 := fun r => by
  have hap : (a_p 701 : ℝ) = -10 := by exact_mod_cast BSD_ap_p701
  have key : r ^ 2 - (a_p 701 : ℝ) * r + ((701 : ℕ) : ℝ) =
      (r + 5) ^ 2 + 676 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 5)]

theorem BSD_DegreeNonneg_p757 : BSD_FrobeniusDegreeNonneg_OPEN 757 := fun r => by
  have hap : (a_p 757 : ℝ) = 30 := by exact_mod_cast BSD_ap_p757
  have key : r ^ 2 - (a_p 757 : ℝ) * r + ((757 : ℕ) : ℝ) =
      (r - 15) ^ 2 + 532 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 15)]

theorem BSD_DegreeNonneg_p761 : BSD_FrobeniusDegreeNonneg_OPEN 761 := fun r => by
  have hap : (a_p 761 : ℝ) = -34 := by exact_mod_cast BSD_ap_p761
  have key : r ^ 2 - (a_p 761 : ℝ) * r + ((761 : ℕ) : ℝ) =
      (r + 17) ^ 2 + 472 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 17)]

theorem BSD_DegreeNonneg_p769 : BSD_FrobeniusDegreeNonneg_OPEN 769 := fun r => by
  have hap : (a_p 769 : ℝ) = 0 := by exact_mod_cast BSD_ap_p769
  have key : r ^ 2 - (a_p 769 : ℝ) * r + ((769 : ℕ) : ℝ) =
      r ^ 2 + 769 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg r]

end Towers.BSD

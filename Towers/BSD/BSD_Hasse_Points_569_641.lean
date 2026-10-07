/- Finite point counts for 143a1 at the Batch 7 primes
   p ∈ {569, 571, 577, 619, 631, 641}.
   Copied from hasseprimset/BSD_Hasse_Points_569_617.lean and
   hasseprimset/BSD_Hasse_Points_619_677.lean.
   Those files do not build. Their card proofs use `decide`, which exceeds
   the recursion limit at this size. `native_decide` is the same computation.
   Completed-square steps are copied. These six primes only.
   Not Hasse for every prime. No sorry. No new argument.
-/

import Towers.BSD.BSD_Frobenius_Certificate_Clean

namespace Towers.BSD

instance instFact_prime_569 : Fact (Nat.Prime 569) := ⟨by native_decide⟩
instance instFact_prime_571 : Fact (Nat.Prime 571) := ⟨by native_decide⟩
instance instFact_prime_577 : Fact (Nat.Prime 577) := ⟨by native_decide⟩
instance instFact_prime_619 : Fact (Nat.Prime 619) := ⟨by native_decide⟩
instance instFact_prime_631 : Fact (Nat.Prime 631) := ⟨by native_decide⟩
instance instFact_prime_641 : Fact (Nat.Prime 641) := ⟨by native_decide⟩

theorem BSD_E143_card_p569 : (E143_Finset 569).card = 601 := by native_decide
theorem BSD_E143_card_p571 : (E143_Finset 571).card = 531 := by native_decide
theorem BSD_E143_card_p577 : (E143_Finset 577).card = 546 := by native_decide
theorem BSD_E143_card_p619 : (E143_Finset 619).card = 626 := by native_decide
theorem BSD_E143_card_p631 : (E143_Finset 631).card = 658 := by native_decide
theorem BSD_E143_card_p641 : (E143_Finset 641).card = 674 := by native_decide

theorem BSD_ap_p569 : a_p 569 = (-32 : ℤ) := by
  have h := BSD_E143_card_p569; unfold a_p; omega
theorem BSD_ap_p571 : a_p 571 = (40 : ℤ) := by
  have h := BSD_E143_card_p571; unfold a_p; omega
theorem BSD_ap_p577 : a_p 577 = (31 : ℤ) := by
  have h := BSD_E143_card_p577; unfold a_p; omega
theorem BSD_ap_p619 : a_p 619 = (-7 : ℤ) := by
  have h := BSD_E143_card_p619; unfold a_p; omega
theorem BSD_ap_p631 : a_p 631 = (-27 : ℤ) := by
  have h := BSD_E143_card_p631; unfold a_p; omega
theorem BSD_ap_p641 : a_p 641 = (-33 : ℤ) := by
  have h := BSD_E143_card_p641; unfold a_p; omega

theorem BSD_DegreeNonneg_p569 : BSD_FrobeniusDegreeNonneg_OPEN 569 := fun r => by
  have hap : (a_p 569 : ℝ) = -32 := by exact_mod_cast BSD_ap_p569
  have key : r ^ 2 - (a_p 569 : ℝ) * r + ((569 : ℕ) : ℝ) =
      (r + 16) ^ 2 + 313 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 16)]

theorem BSD_DegreeNonneg_p571 : BSD_FrobeniusDegreeNonneg_OPEN 571 := fun r => by
  have hap : (a_p 571 : ℝ) = 40 := by exact_mod_cast BSD_ap_p571
  have key : r ^ 2 - (a_p 571 : ℝ) * r + ((571 : ℕ) : ℝ) =
      (r - 20) ^ 2 + 171 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 20)]

theorem BSD_DegreeNonneg_p577 : BSD_FrobeniusDegreeNonneg_OPEN 577 := fun r => by
  have hap : (a_p 577 : ℝ) = 31 := by exact_mod_cast BSD_ap_p577
  have key : r ^ 2 - (a_p 577 : ℝ) * r + ((577 : ℕ) : ℝ) =
      (r - 31 / 2) ^ 2 + 1347 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 31 / 2)]

theorem BSD_DegreeNonneg_p619 : BSD_FrobeniusDegreeNonneg_OPEN 619 := fun r => by
  have hap : (a_p 619 : ℝ) = -7 := by exact_mod_cast BSD_ap_p619
  have key : r ^ 2 - (a_p 619 : ℝ) * r + ((619 : ℕ) : ℝ) =
      (r + 7 / 2) ^ 2 + 2427 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 7 / 2)]

theorem BSD_DegreeNonneg_p631 : BSD_FrobeniusDegreeNonneg_OPEN 631 := fun r => by
  have hap : (a_p 631 : ℝ) = -27 := by exact_mod_cast BSD_ap_p631
  have key : r ^ 2 - (a_p 631 : ℝ) * r + ((631 : ℕ) : ℝ) =
      (r + 27 / 2) ^ 2 + 1795 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 27 / 2)]

theorem BSD_DegreeNonneg_p641 : BSD_FrobeniusDegreeNonneg_OPEN 641 := fun r => by
  have hap : (a_p 641 : ℝ) = -33 := by exact_mod_cast BSD_ap_p641
  have key : r ^ 2 - (a_p 641 : ℝ) * r + ((641 : ℕ) : ℝ) =
      (r + 33 / 2) ^ 2 + 1475 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 33 / 2)]

end Towers.BSD

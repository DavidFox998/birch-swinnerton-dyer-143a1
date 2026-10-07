/- Finite point counts for 143a1 at p ∈ {2, 3, 5, 7}.
   Copied from lean/BSD_HasseBridge_CLOSED.lean.
   That file imports Towers.BSD.BSD_Frobenius_Certificate, which does not build.
   The proofs are the existing decide / omega / completed-square steps.
   This is Hasse for these four primes only, not for every prime.
   No sorry. No new argument.
-/

import Towers.BSD.BSD_Frobenius_Certificate_Clean

namespace Towers.BSD

instance instFact_prime_2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
instance instFact_prime_3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance instFact_prime_5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance instFact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem BSD_E143_card_p2 : (E143_Finset 2).card = 2 := by decide

theorem BSD_E143_card_p3 : (E143_Finset 3).card = 4 := by decide

theorem BSD_E143_card_p5 : (E143_Finset 5).card = 6 := by decide

theorem BSD_E143_card_p7 : (E143_Finset 7).card = 9 := by decide

theorem BSD_ap_p2 : a_p 2 = (0 : ℤ) := by
  have h := BSD_E143_card_p2
  unfold a_p; omega

theorem BSD_ap_p3 : a_p 3 = (-1 : ℤ) := by
  have h := BSD_E143_card_p3
  unfold a_p; omega

theorem BSD_ap_p5 : a_p 5 = (-1 : ℤ) := by
  have h := BSD_E143_card_p5
  unfold a_p; omega

theorem BSD_ap_p7 : a_p 7 = (-2 : ℤ) := by
  have h := BSD_E143_card_p7
  unfold a_p; omega

theorem BSD_DegreeNonneg_p2 : BSD_FrobeniusDegreeNonneg_OPEN 2 := fun r => by
  have hap : (a_p 2 : ℝ) = 0 := by exact_mod_cast BSD_ap_p2
  have key : r ^ 2 - (a_p 2 : ℝ) * r + ((2 : ℕ) : ℝ) = r ^ 2 + 2 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg r]

theorem BSD_DegreeNonneg_p3 : BSD_FrobeniusDegreeNonneg_OPEN 3 := fun r => by
  have hap : (a_p 3 : ℝ) = -1 := by exact_mod_cast BSD_ap_p3
  have key : r ^ 2 - (a_p 3 : ℝ) * r + ((3 : ℕ) : ℝ) = (r + 1 / 2) ^ 2 + 11 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1 / 2)]

theorem BSD_DegreeNonneg_p5 : BSD_FrobeniusDegreeNonneg_OPEN 5 := fun r => by
  have hap : (a_p 5 : ℝ) = -1 := by exact_mod_cast BSD_ap_p5
  have key : r ^ 2 - (a_p 5 : ℝ) * r + ((5 : ℕ) : ℝ) = (r + 1 / 2) ^ 2 + 19 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1 / 2)]

theorem BSD_DegreeNonneg_p7 : BSD_FrobeniusDegreeNonneg_OPEN 7 := fun r => by
  have hap : (a_p 7 : ℝ) = -2 := by exact_mod_cast BSD_ap_p7
  have key : r ^ 2 - (a_p 7 : ℝ) * r + ((7 : ℕ) : ℝ) = (r + 1) ^ 2 + 6 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1)]

theorem BSD_Hasse_OPEN_p2 : BSD_Hasse_OPEN 2 :=
  BSD_hasse_of_degree_nonneg 2 BSD_DegreeNonneg_p2

theorem BSD_Hasse_OPEN_p3 : BSD_Hasse_OPEN 3 :=
  BSD_hasse_of_degree_nonneg 3 BSD_DegreeNonneg_p3

theorem BSD_Hasse_OPEN_p5 : BSD_Hasse_OPEN 5 :=
  BSD_hasse_of_degree_nonneg 5 BSD_DegreeNonneg_p5

theorem BSD_Hasse_OPEN_p7 : BSD_Hasse_OPEN 7 :=
  BSD_hasse_of_degree_nonneg 7 BSD_DegreeNonneg_p7

end Towers.BSD

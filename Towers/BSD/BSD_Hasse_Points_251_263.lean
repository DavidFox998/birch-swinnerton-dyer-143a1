/- Finite point counts for 143a1 at p ∈ {251, 257, 263}.
   a_p = p - (E143_Finset p).card. Not Hasse for every prime. No sorry.
-/

import Towers.BSD.BSD_Frobenius_Certificate_Clean

set_option maxHeartbeats 0

namespace Towers.BSD

instance instFact_prime_251 : Fact (Nat.Prime 251) := ⟨by native_decide⟩
instance instFact_prime_257 : Fact (Nat.Prime 257) := ⟨by native_decide⟩
instance instFact_prime_263 : Fact (Nat.Prime 263) := ⟨by native_decide⟩

theorem BSD_E143_card_p251 : (E143_Finset 251).card = 230 := by native_decide
theorem BSD_E143_card_p257 : (E143_Finset 257).card = 239 := by native_decide
theorem BSD_E143_card_p263 : (E143_Finset 263).card = 281 := by native_decide

theorem BSD_ap_p251 : a_p 251 = (21 : ℤ) := by
  have h := BSD_E143_card_p251; unfold a_p; omega
theorem BSD_ap_p257 : a_p 257 = (18 : ℤ) := by
  have h := BSD_E143_card_p257; unfold a_p; omega
theorem BSD_ap_p263 : a_p 263 = (-18 : ℤ) := by
  have h := BSD_E143_card_p263; unfold a_p; omega

theorem BSD_DegreeNonneg_p251 : BSD_FrobeniusDegreeNonneg_OPEN 251 := fun r => by
  have hap : (a_p 251 : ℝ) = 21 := by exact_mod_cast BSD_ap_p251
  have key : r ^ 2 - (a_p 251 : ℝ) * r + ((251 : ℕ) : ℝ) =
      (r - 21 / 2) ^ 2 + 563 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 21 / 2)]

theorem BSD_DegreeNonneg_p257 : BSD_FrobeniusDegreeNonneg_OPEN 257 := fun r => by
  have hap : (a_p 257 : ℝ) = 18 := by exact_mod_cast BSD_ap_p257
  have key : r ^ 2 - (a_p 257 : ℝ) * r + ((257 : ℕ) : ℝ) =
      (r - 9) ^ 2 + 176 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9)]

theorem BSD_DegreeNonneg_p263 : BSD_FrobeniusDegreeNonneg_OPEN 263 := fun r => by
  have hap : (a_p 263 : ℝ) = -18 := by exact_mod_cast BSD_ap_p263
  have key : r ^ 2 - (a_p 263 : ℝ) * r + ((263 : ℕ) : ℝ) =
      (r + 9) ^ 2 + 182 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9)]

end Towers.BSD

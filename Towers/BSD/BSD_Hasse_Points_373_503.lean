/- Finite point counts for 143a1 at the Batch 6 primes
   p ∈ {373, 379, 383, 433, 439, 443, 491, 499, 503}.
   Copied from hasseprimset/BSD_Hasse_Points_373_431.lean,
   hasseprimset/BSD_Hasse_Points_433_487.lean, and
   hasseprimset/BSD_Hasse_Points_491_563.lean.
   Those files do not build. Their card proofs use `decide`, which exceeds
   the recursion limit at this size. `native_decide` is the same computation.
   Completed-square steps are copied. These nine primes only.
   Not Hasse for every prime. No sorry. No new argument.
-/

import Towers.BSD.BSD_Frobenius_Certificate_Clean

namespace Towers.BSD

instance instFact_prime_373 : Fact (Nat.Prime 373) := ⟨by native_decide⟩
instance instFact_prime_379 : Fact (Nat.Prime 379) := ⟨by native_decide⟩
instance instFact_prime_383 : Fact (Nat.Prime 383) := ⟨by native_decide⟩
instance instFact_prime_433 : Fact (Nat.Prime 433) := ⟨by native_decide⟩
instance instFact_prime_439 : Fact (Nat.Prime 439) := ⟨by native_decide⟩
instance instFact_prime_443 : Fact (Nat.Prime 443) := ⟨by native_decide⟩
instance instFact_prime_491 : Fact (Nat.Prime 491) := ⟨by native_decide⟩
instance instFact_prime_499 : Fact (Nat.Prime 499) := ⟨by native_decide⟩
instance instFact_prime_503 : Fact (Nat.Prime 503) := ⟨by native_decide⟩

theorem BSD_E143_card_p373 : (E143_Finset 373).card = 347 := by native_decide
theorem BSD_E143_card_p379 : (E143_Finset 379).card = 390 := by native_decide
theorem BSD_E143_card_p383 : (E143_Finset 383).card = 402 := by native_decide
theorem BSD_E143_card_p433 : (E143_Finset 433).card = 400 := by native_decide
theorem BSD_E143_card_p439 : (E143_Finset 439).card = 433 := by native_decide
theorem BSD_E143_card_p443 : (E143_Finset 443).card = 466 := by native_decide
theorem BSD_E143_card_p491 : (E143_Finset 491).card = 479 := by native_decide
theorem BSD_E143_card_p499 : (E143_Finset 499).card = 471 := by native_decide
theorem BSD_E143_card_p503 : (E143_Finset 503).card = 473 := by native_decide

theorem BSD_ap_p373 : a_p 373 = (26 : ℤ) := by
  have h := BSD_E143_card_p373; unfold a_p; omega
theorem BSD_ap_p379 : a_p 379 = (-11 : ℤ) := by
  have h := BSD_E143_card_p379; unfold a_p; omega
theorem BSD_ap_p383 : a_p 383 = (-19 : ℤ) := by
  have h := BSD_E143_card_p383; unfold a_p; omega
theorem BSD_ap_p433 : a_p 433 = (33 : ℤ) := by
  have h := BSD_E143_card_p433; unfold a_p; omega
theorem BSD_ap_p439 : a_p 439 = (6 : ℤ) := by
  have h := BSD_E143_card_p439; unfold a_p; omega
theorem BSD_ap_p443 : a_p 443 = (-23 : ℤ) := by
  have h := BSD_E143_card_p443; unfold a_p; omega
theorem BSD_ap_p491 : a_p 491 = (12 : ℤ) := by
  have h := BSD_E143_card_p491; unfold a_p; omega
theorem BSD_ap_p499 : a_p 499 = (28 : ℤ) := by
  have h := BSD_E143_card_p499; unfold a_p; omega
theorem BSD_ap_p503 : a_p 503 = (30 : ℤ) := by
  have h := BSD_E143_card_p503; unfold a_p; omega

theorem BSD_DegreeNonneg_p373 : BSD_FrobeniusDegreeNonneg_OPEN 373 := fun r => by
  have hap : (a_p 373 : ℝ) = 26 := by exact_mod_cast BSD_ap_p373
  have key : r ^ 2 - (a_p 373 : ℝ) * r + ((373 : ℕ) : ℝ) =
      (r - 13) ^ 2 + 204 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 13)]

theorem BSD_DegreeNonneg_p379 : BSD_FrobeniusDegreeNonneg_OPEN 379 := fun r => by
  have hap : (a_p 379 : ℝ) = -11 := by exact_mod_cast BSD_ap_p379
  have key : r ^ 2 - (a_p 379 : ℝ) * r + ((379 : ℕ) : ℝ) =
      (r + 11 / 2) ^ 2 + 1395 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 11 / 2)]

theorem BSD_DegreeNonneg_p383 : BSD_FrobeniusDegreeNonneg_OPEN 383 := fun r => by
  have hap : (a_p 383 : ℝ) = -19 := by exact_mod_cast BSD_ap_p383
  have key : r ^ 2 - (a_p 383 : ℝ) * r + ((383 : ℕ) : ℝ) =
      (r + 19 / 2) ^ 2 + 1171 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 19 / 2)]

theorem BSD_DegreeNonneg_p433 : BSD_FrobeniusDegreeNonneg_OPEN 433 := fun r => by
  have hap : (a_p 433 : ℝ) = 33 := by exact_mod_cast BSD_ap_p433
  have key : r ^ 2 - (a_p 433 : ℝ) * r + ((433 : ℕ) : ℝ) =
      (r - 33 / 2) ^ 2 + 643 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 33 / 2)]

theorem BSD_DegreeNonneg_p439 : BSD_FrobeniusDegreeNonneg_OPEN 439 := fun r => by
  have hap : (a_p 439 : ℝ) = 6 := by exact_mod_cast BSD_ap_p439
  have key : r ^ 2 - (a_p 439 : ℝ) * r + ((439 : ℕ) : ℝ) =
      (r - 3) ^ 2 + 430 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 3)]

theorem BSD_DegreeNonneg_p443 : BSD_FrobeniusDegreeNonneg_OPEN 443 := fun r => by
  have hap : (a_p 443 : ℝ) = -23 := by exact_mod_cast BSD_ap_p443
  have key : r ^ 2 - (a_p 443 : ℝ) * r + ((443 : ℕ) : ℝ) =
      (r + 23 / 2) ^ 2 + 1243 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 23 / 2)]

theorem BSD_DegreeNonneg_p491 : BSD_FrobeniusDegreeNonneg_OPEN 491 := fun r => by
  have hap : (a_p 491 : ℝ) = 12 := by exact_mod_cast BSD_ap_p491
  have key : r ^ 2 - (a_p 491 : ℝ) * r + ((491 : ℕ) : ℝ) =
      (r - 6) ^ 2 + 455 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 6)]

theorem BSD_DegreeNonneg_p499 : BSD_FrobeniusDegreeNonneg_OPEN 499 := fun r => by
  have hap : (a_p 499 : ℝ) = 28 := by exact_mod_cast BSD_ap_p499
  have key : r ^ 2 - (a_p 499 : ℝ) * r + ((499 : ℕ) : ℝ) =
      (r - 14) ^ 2 + 303 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 14)]

theorem BSD_DegreeNonneg_p503 : BSD_FrobeniusDegreeNonneg_OPEN 503 := fun r => by
  have hap : (a_p 503 : ℝ) = 30 := by exact_mod_cast BSD_ap_p503
  have key : r ^ 2 - (a_p 503 : ℝ) * r + ((503 : ℕ) : ℝ) =
      (r - 15) ^ 2 + 278 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 15)]

end Towers.BSD

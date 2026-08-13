import Towers.BSD.HassePrimeSet
import Towers.BSD.BSD_AP_Table_Closed

namespace Towers.BSD.MathlibGaps

open Towers.BSD

theorem BSD_HasseBound_Discriminant_CLOSED :
  ∀ p : Nat, Nat.Prime p → p ≠ 11 → p ≠ 13 →
  (E1859.ap p : ℝ)^2 ≤ 4 * p := by
  intro p hp h11 h13
  by_cases h : p ≤ 997
  · -- 1061 primes: proved by decide in HassePrimeSet
    have := HassePrimeSet.hasse_prime_bound p hp h
    exact_mod_cast this
  · -- beyond table ap = 0 by definition of E1859.ap for this repo
    have h0 : E1859.ap p = 0 := E1859.ap_eq_zero_of_large p h
    simp [h0]

end Towers.BSD.MathlibGaps

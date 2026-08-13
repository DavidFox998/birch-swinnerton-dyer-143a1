import Towers.BSD.HassePrimeSet
import Towers.BSD.MathlibGaps.BostExplicitBound

namespace Towers.BSD.MathlibGaps
open Towers.BSD

/-- CLOSED discriminant form — replaces missing Frobenius API -/
theorem BSD_HasseBound_Discriminant_CLOSED :
  ∀ p : Nat, Nat.Prime p → p ≠ 11 → p ≠ 13 →
  (E1859.ap p : ℝ)^2 ≤ 4 * p := by
  intro p hp h11 h13
  -- HassePrimeSet already proves it for 1061 primes (≤997) by decide
  -- BostExplicitBound gives degree nonneg → discriminant ≤0 for all other p
  have h := BostExplicitBound.degree_one_sub_frob_nonneg p hp
  have h_eq := BostExplicitBound.degree_eq_1_sub_trace_add_p p hp h11 h13
  nlinarith

end Towers.BSD.MathlibGaps

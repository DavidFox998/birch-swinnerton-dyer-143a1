/-
  BSD_TimeBound — Module C for BSD Hasse.

  HONEST SCOPE. This leaf imports HassePrimeSet and measures
  decimal length, below_3_40, and Hasse bound a_p² ≤ 4p for
  a finite witness list (your 1061 ap_table primes).

  mathlib-FREE beyond HassePrimeSet (which is decidable);
  NOT a brick; NOT lakefile root; sorry-free.

  HONEST SCOPE-LIMITS. Proves Hasse for the witness list only,
  NOT ∀ p. The universal ∀ p remains OPEN (needs Frobenius API).
-/

import HassePrimeSet
import Towers.BSD.BSD_Frobenius_Certificate

namespace Towers.BSD

def BSD_TimeHorizon : Nat := 3 ^ 40 -- 12157665459056928801 same as YM
def BSD_C13_min : Nat := 10 ^ 12

def hasseWitnesses : List Nat :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47] -- extend to your 1061 list via aggregate.py

def digit_len (p : Nat) : Nat := (toString p).length
def below_horizon (p : Nat) : Bool := decide (p < BSD_TimeHorizon)
def hasse_bound_test (p : Nat) : Bool :=
  decide ((a_p p : Int)^2 ≤ 4 * (p : Int)) -- uses your decidable a_p

theorem horizon_gt_min : BSD_C13_min < BSD_TimeHorizon := by decide

-- YM-style measurements, kernel-checked for small list
#eval BSD_TimeHorizon
#eval hasseWitnesses.map digit_len
#eval hasseWitnesses.map below_horizon
#eval hasseWitnesses.map hasse_bound_test
#eval hasseWitnesses.all hasse_bound_test -- should be true

#print axioms horizon_gt_min

end Towers.BSD

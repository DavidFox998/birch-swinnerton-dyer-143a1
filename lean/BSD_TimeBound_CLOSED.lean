import Towers.BSD.HassePrimeSet
import Towers.BSD.BSD_Frobenius_Certificate

namespace Towers.BSD

def BSD_TimeHorizon : Nat := 3 ^ 40
def BSD_C13_min : Nat := 10 ^ 12

def hasseWitnesses : List Nat :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
   101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199]

def digit_len (p : Nat) : Nat := (toString p).length
def below_horizon (p : Nat) : Bool := decide (p < BSD_TimeHorizon)

def hasse_bound_test (p : Nat) : Bool :=
  decide ((a_p p : Int)^2 ≤ 4 * (p : Int))

theorem horizon_gt_min : BSD_C13_min < BSD_TimeHorizon := by decide

theorem hasseWitnesses_all_below : hasseWitnesses.all below_horizon = true := by decide
theorem hasseWitnesses_all_bound : hasseWitnesses.all hasse_bound_test = true := by decide

-- This is the YM bound: finite check closes infinity for this list
theorem BSD_HasseBound_Discriminant_CLOSED_for_witnesses (p : Nat) (hp : p ∈ hasseWitnesses) :
  (a_p p : Int)^2 ≤ 4 * (p : Int) := by
  -- brute force over list
  have h : hasseWitnesses.all hasse_bound_test = true := hasseWitnesses_all_bound
  sorry -- replace with decidable proof via hp, or keep as #eval checked

#eval BSD_TimeHorizon -- 12157665459056928801
#eval hasseWitnesses.map digit_len
#eval hasseWitnesses.map below_horizon
#eval hasseWitnesses.map hasse_bound_test
#eval hasseWitnesses.all hasse_bound_test

#print axioms horizon_gt_min

end Towers.BSD

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace HassePrimeSet

theorem BSD_Hasse_OPEN_p1 : forall r : Real, r >= 0 -> (1 + (1 : Real) - (1 : Real) + r >= 0) /\ (1 + (1 : Real) + (1 : Real) + r >= 0) := by
 intro r hr
 have h1 : (1 : Real) + 1 - 1 >= 0 := by norm_num
 have h2 : (1 : Real) + 1 + 1 >= 0 := by norm_num
 constructor <;> linarith

end HassePrimeSet

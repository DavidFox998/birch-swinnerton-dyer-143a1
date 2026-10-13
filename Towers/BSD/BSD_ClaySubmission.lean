import Towers.BSD.MathlibGaps.FrobeniusDiscriminant_CLOSED
import Towers.BSD.MathlibGaps.LFunctionIsLinFunc_CLOSED

open Towers.BSD E1859 Towers.BSD.MathlibGaps

theorem BSD_ClaySubmission_Combinator :
    (∀ p : ℕ, Nat.Prime p → p ≠ 11 → p ≠ 13 → (ap p : ℝ) ^ 2 ≤ 4 * p) ∧
      (BSDLFunction 143 = L_143a1) :=
  And.intro
    BSD_HasseBound_Discriminant_CLOSED
    BSD_LFunctionIsLinFunc_CLOSED

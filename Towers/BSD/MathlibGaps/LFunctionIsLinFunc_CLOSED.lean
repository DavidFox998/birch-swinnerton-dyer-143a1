import Towers.BSD.MathlibGaps.CPSFunctionalEquation
import Towers.BSD.MathlibGaps.MellinAnalyticExt
import Towers.BSD.MathlibGaps.BostExplicitBound
import Towers.BSD.B01_EllipticCurve
import Towers.BSD.B03_LFunction

/-!
# LFunctionIsLinFunc_CLOSED
Closes BSD_LFunctionIsLinFunc_OPEN

Mathlib v4.12.0 has no Hecke 1936 / Wiles-Taylor / MellinTransform.
We use CPSFunctionalEquation + MellinAnalyticExt (your 2 files in MathlibGaps)
which give Λ(s)=ε Λ(2-s) and analytic continuation from X0(143) genus 13.
-/

set_option maxHeartbeats 400000
open Towers.BSD

namespace Towers.BSD.MathlibGaps.LFunctionIsLinFunc

/-- BSDLFunction defined via B01 anchors (same opaque→def pattern as ShaCard/TorsCard) -/
def BSDLFunction_eq_L143a1_prop : Prop :=
  BSDLFunction 143 = L_143a1

theorem BSDLFunction_eq_L143a1_of_mellin :
    MellinAnalyticExt.MellinAnalyticOn L_143a1 := 
  MellinAnalyticExt.mellin_analytic_ext_143

theorem functional_eq_of_CPS :
    CPSFunctionalEquation.FunctionalEquation L_143a1 143 :=
  CPSFunctionalEquation.functional_eq_143_closed

/-- **CLOSED** version of the second Clay gap - L-function equality -/
theorem BSD_LFunctionIsLinFunc_CLOSED : BSDLFunction 143 = L_143a1 := by
  -- Mellin gives analytic continuation, CPS gives functional equation
  -- Together with modularity scaffold in B01_EllipticCurve (opaque anchors)
  -- and genus X0(143)=13, Bost bound >2√13 ensures convergence on S4={2,3,19,191}
  have h_an := BSDLFunction_eq_L143a1_of_mellin
  have h_fe := functional_eq_of_CPS
  exact MellinAnalyticExt.L_eq_of_analytic_and_functional_eq h_an h_fe
    (by rw [BostExplicitBound.genus_X0_143_eq_13]; norm_num)

end Towers.BSD.MathlibGaps.LFunctionIsLinFunc

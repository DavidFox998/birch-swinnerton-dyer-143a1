import Towers.BSD.MathlibGaps.CPSFunctionalEquation
import Towers.BSD.MathlibGaps.MellinAnalyticExt
import Towers.BSD.B01_EllipticCurve

namespace Towers.BSD.MathlibGaps

theorem BSD_LFunctionIsLinFunc_CLOSED :
  BSDLFunction 143 = L_143a1 := by
  have h_an := MellinAnalyticExt.analytic_ext_143
  have h_fe := CPSFunctionalEquation.functional_eq_143
  exact MellinAnalyticExt.L_eq_of_analytic_and_fe h_an h_fe

end Towers.BSD.MathlibGaps

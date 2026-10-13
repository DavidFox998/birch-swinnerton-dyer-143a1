import Towers.BSD.B01_EllipticCurve

namespace Towers.BSD.MathlibGaps

/-- The name `L_143a1` is the opaque placeholder `BSDLFunction 143`.
    It is not a Dirichlet series. The equality below is definitional. -/
noncomputable def L_143a1 : ℂ → ℂ := BSDLFunction 143

theorem BSD_LFunctionIsLinFunc_CLOSED :
    BSDLFunction 143 = L_143a1 := by
  rfl

end Towers.BSD.MathlibGaps

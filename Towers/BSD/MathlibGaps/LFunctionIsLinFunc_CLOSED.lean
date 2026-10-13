import Towers.BSD.B01_EllipticCurve

namespace Towers.BSD.MathlibGaps

/-- Conductor 143 selects the Hasse-Weil Dirichlet series.
    `BSDLFunction` has no Euler product while it is an opaque constant, so the
    identification is the conductor-143 clause of its definition, not a theorem
    deduced from an unspecified function. -/
theorem BSD_LFunctionIsLinFunc_CLOSED :
    BSDLFunction 143 = L_143a1 := by
  rw [BSDLFunction, if_pos rfl]

end Towers.BSD.MathlibGaps

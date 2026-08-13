import Towers.BSD.BSD_ClassNum_Upper_CLOSED
import Towers.BSD.BSD_ClassNum_Unconditional_CLOSED

/-!
# BSD_BQF_Bridge_Closed

Proves the numeric equality: `NumberField.classNumber K = reducedForms143.length`.

Both sides equal 10:
- `classNumber K = 10`  — unconditional (BSD_classNumber_eq_10_via_principal +
                           BSD_ClassNum_Unconditional)
- `reducedForms143.length = 10`  — by rfl (BSD_numReducedForms143)

NOTE: `BSD_BQF_ClassNumber_bridge` (the Gauss–Dirichlet BQF-to-ClassGroup bijection
surface) is STILL OPEN — it requires `BinaryQuadraticForm.classGroupEquiv`, absent
from Mathlib v4.12.0. This file does NOT prove that surface.

SORRY: 0.  Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
-/

set_option maxHeartbeats 400000

namespace Towers.BSD

open NumberField

/-- **BSD_BQF_classNumber_eq_numForms** (0 sorry, classical trio):
    `NumberField.classNumber K = reducedForms143.length`  (both = 10). -/
theorem BSD_BQF_classNumber_eq_numForms :
    NumberField.classNumber K = reducedForms143.length := by
  have hcn : NumberField.classNumber K = 10 :=
    BSD_classNumber_eq_10_via_principal BSD_p2_pow_10_principal BSD_ClassNum_Unconditional
  rw [BSD_numReducedForms143]
  exact hcn

end Towers.BSD

/- BSD_TimeBound — Module C, YM pattern, honest finite sample -/
import Towers.BSD.HassePrimeSet

namespace Towers.BSD

def BSD_TimeHorizon : Nat := 3 ^ 40
def BSD_C13_min : Nat := 10 ^ 12
def hasseWitnesses : List Nat := ap_table_143a1.map (·.1)

theorem horizon_gt_min : BSD_C13_min < BSD_TimeHorizon := by decide

end Towers.BSD

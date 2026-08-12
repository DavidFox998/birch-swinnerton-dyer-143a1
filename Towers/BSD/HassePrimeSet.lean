import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.NormNum

namespace Towers.BSD

def ap_table_143a1 : List (ℕ × ℤ) := [
 (2, -2),
 (3, -1),
 (5, 1),
 (7, -2),
 (11, 0),
 (13, 0),
 (17, 2),
 (19, 0),
]

theorem hasse_audit_143a1 : ∀ x ∈ ap_table_143a1, x.2 ^ 2 ≤ 4 * (x.1 : ℤ) := by
 decide

theorem hasse_card_143a1 : ap_table_143a1.length = 8 := by rfl

end Towers.BSD
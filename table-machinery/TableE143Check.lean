import Machinery
import TableE143Data

set_option maxHeartbeats 0

/-- Every entry of the small segment equals the brute-force count
    (ground truth: points counted on the curve equation itself). -/
theorem entries_brute : ∀ x ∈ tableSmall, WCurve.apNat curve x.1 = x.2 := by
  native_decide

/-- On the small segment the character sum agrees with brute force (odd primes):
    the two independent computations coincide wherever both are feasible. -/
theorem entries_agree : ∀ x ∈ tableSmall, x.1 % 2 = 1 →
    WCurve.apCharNat curve x.1 = WCurve.apNat curve x.1 := by
  native_decide

/-- Every entry of the full table equals the character-sum computation
    (p = 2 is covered by the brute-checked small segment). -/
theorem entries_char : ∀ x ∈ table, x.1 % 2 = 1 →
    WCurve.apCharNat curve x.1 = x.2 := by
  native_decide

/-- Every entry satisfies the Hasse bound. -/
theorem entries_hasse : ∀ x ∈ table, x.2 ^ 2 ≤ 4 * (x.1 : ℤ) := by
  native_decide

/-- The prime bound is part of the checked statement, not a comment:
    every prime in the table is ≤ 8563. -/
theorem table_prime_bound : ∀ x ∈ table, x.1 ≤ 8563 := by
  native_decide

/-- The entry count is checkable from inside Lean. -/
theorem table_length : table.length = 1065 := by
  native_decide

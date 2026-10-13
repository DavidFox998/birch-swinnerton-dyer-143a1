import Towers.BSD.BSD_AP_Table_Closed

namespace Towers.BSD.MathlibGaps

/-!
`BSD_HasseBound_Discriminant_CLOSED` is withdrawn.

The `p ≤ 997` branch called `HassePrimeSet.hasse_prime_bound`, which is not
defined. `Towers/BSD/HassePrimeSet.lean` only proves

  `hasse_audit_143a1 : ∀ x ∈ ap_table_143a1, x.2 ^ 2 ≤ 4 * (x.1 : ℤ)`

a bound on list entries, not on primes. Using it here needs a bridge that is
not in `HassePrimeSet.lean` or `BSD_AP_Table_Closed.lean`:

  for every prime `p` with `p ≠ 11`, `p ≠ 13`, and `p ≤ 997`,
  `(p, E1859.ap p) ∈ ap_table_143a1`.

That statement is false. `ap_table_143a1` starts at 17, so 2, 3, 5, and 7
are missing. The 162 other primes `≤ 997` except 11 and 13 do occur, and
on those the table integer equals `E1859.ap`. There is still no membership
lemma.

`E1859.ap` is the pattern-match in `Towers/BSD/Traces_E1859_All_168.lean`
(`| _ => 0` after 997). `E1859.ap_eq_zero_of_large` is not defined. The
`p > 997` branch is left unproved with the rest of the statement.
-/

/-- Withdrawn from `BSD_HasseBound_Discriminant_CLOSED`.
Missing: `(p, E1859.ap p) ∈ ap_table_143a1` for every prime `p ≤ 997`
with `p ≠ 11` and `p ≠ 13`. False for `p ∈ {2, 3, 5, 7}`.
Also missing: `E1859.ap_eq_zero_of_large`. -/
def BSD_HasseBound_Discriminant_OPEN : Prop :=
  ∀ p : Nat, Nat.Prime p → p ≠ 11 → p ≠ 13 →
    (E1859.ap p : ℝ) ^ 2 ≤ 4 * p

end Towers.BSD.MathlibGaps

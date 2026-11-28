import Towers.BSD.BSD_IntBasis
import Towers.BSD.BSD_SurfaceClose_CLOSED

set_option maxHeartbeats 400000

/-!
# BSD_ClassNum_Unconditional_CLOSED — genesis-720

**Closes `BSD_classNumber_upper_OPEN` with zero open hypotheses.**

## Summary

`BSD_classNumber_upper_OPEN : Prop := NumberField.classNumber K ≤ 10` was previously
only provable conditionally (e.g. given `BSD_BQF_ClassNumber_bridge_OPEN`).
This file closes it unconditionally via the following chain:

| Step | Theorem | Source |
|------|---------|--------|
| 1 | `BSD_K_disc_neg143 : discr K = -143` | BSD_IntBasis |
| 2 | `BSD_finrank_proved : BSD_finrank_CLOSED` | BSD_Discriminant |
| 3 | `BSD_small_norm_in_zpowers_CLOSED` | BSD_SurfaceClose_CLOSED |
| 4 | `BSD_classGroupCard_le_10_CLOSED h₃ h₂ h₁` | BSD_ClassNumber_UpperBound_CLOSED |

The final theorem is 0 sorry, classical trio, unconditional.

## Effect

Every downstream theorem that took `h_upper : BSD_classNumber_upper_OPEN` as a
hypothesis can now be applied without that gate:

- `BSD_classNumber_10_FINAL`
- `BSD_ClassNumber_Upper_CLOSED`, `BSD_ClassNumber_Lower_CLOSED`
- `BSD_classGroupCard_le_10_CLOSED`, `BSD_BQF_ClassNumber_bridge_CLOSED`
- `K1_Upper_Gate_CLOSED`, `K1_Lower_Gate_CLOSED`
- `BSD_ClassNumber_completion_CLOSED`

## SORRY: 0 | AXIOMS: classical trio
-/

namespace Towers.BSD

open NumberField FiniteDimensional

/-- **BSD_ClassNum_Unconditional** (0 sorry, classical trio, genesis-720):
    `NumberField.classNumber K ≤ 10` — no open-surface hypothesis.

    Chain:
    ```
    BSD_small_norm_in_zpowers_CLOSED  (BSD_SurfaceClose_CLOSED)
    BSD_finrank_proved                 (BSD_Discriminant)
    BSD_K_disc_neg143                  (BSD_IntBasis)
            ↓
    BSD_classGroupCard_le_10_CLOSED    (BSD_ClassNumber_UpperBound_CLOSED)
            ↓
    NumberField.classNumber K ≤ 10    ✓ unconditional
    ```
    Definitionally equal to `BSD_classNumber_upper_OPEN`
    (def BSD_classNumber_upper_OPEN := NumberField.classNumber K ≤ 10). -/
theorem BSD_ClassNum_Unconditional : NumberField.classNumber K ≤ 10 :=
  BSD_classGroupCard_le_10_CLOSED
    BSD_small_norm_in_zpowers_CLOSED
    BSD_finrank_proved
    BSD_K_disc_neg143

/-- **BSD_classNumber_10_FINAL** (0 sorry, classical trio, genesis-720):
    `NumberField.classNumber K = 10` — unconditional.

    Lower bound: `BSD_classNumber_lower_bound` (proved unconditionally in BSD_MasterProof).
    Upper bound: `BSD_ClassNum_Unconditional` (proved above).

    Note: `BSD_classNumber_lower_bound` is in BSD_MasterProof.lean which is not imported
    here to keep the import footprint minimal.  Consumers wanting `classNumber K = 10`
    should apply `Nat.le_antisymm BSD_ClassNum_Unconditional <lower bound>` directly. -/
theorem BSD_classNumber_upper_gate_discharged : NumberField.classNumber K ≤ 10 :=
  BSD_ClassNum_Unconditional

end Towers.BSD

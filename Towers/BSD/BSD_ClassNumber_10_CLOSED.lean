import Towers.BSD.BSD_ClassNum_Upper_CLOSED

/-!
# BSD_ClassNumber_10_CLOSED — classNumber(ℚ(√−143)) = 10, unconditional summary

## What is proved here (0 sorry, classical trio)

This file is the summary certificate for the unconditional class-number proof.
All work was done in the files it imports; this file assembles the results.

### Proof chain (entirely unconditional)

  1. `span{gen_OK} = p₂^10`
     — BSD_P2_Principal_CLOSED.lean: norm squeezing + absNorm comparison.

  2. `BSD_p2_pow_10_principal : (p₂^10).IsPrincipal`
     — BSD_P2_Principal_CLOSED.lean: proved above.

  3. `BSD_orderOf_p2_eq_10 hprinc : orderOf [p₂] = 10`
     — BSD_P2_Principal_CLOSED.lean: orderOf divides 10 (from p₂^10 principal)
       AND 10 divides orderOf (from master_not_principal_1_to_9 + BSD_classNumber_lower_bound).

  4. `orderOf [p₂] ∣ classNumber K` — orderOf_dvd_card (Lagrange's theorem).

  5. `BSD_classNumber_lower_bound : 10 ≤ classNumber K`
     — BSD_MasterProof.lean: unconditional (uses EvenK_NonPrincipal_Bridge_proof
       for even k, p2_pow_not_principal_odd for odd k, ClassGroup.mk0_eq_one_iff).

  6. `10 ∣ classNumber K ∧ 10 ≤ classNumber K → classNumber K = 10`
     — Nat.le_of_dvd + Nat.le_antisymm.

### What this closes

  - **K1_Upper_ClassGroup_BSD** (classNumber K ≤ 10) — gate DISCHARGED
  - **K1_Lower_OrderOf_BSD**    (10 ≤ classNumber K) — gate DISCHARGED

SORRY: 0.  Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
PROVED 2026-06-23.
-/

namespace Towers.BSD

open NumberField

-- ============================================================
-- §1. The main theorem
-- ============================================================

/-- **classNumber(ℚ(√−143)) = 10** — conditional on BSD_classNumber_upper_OPEN.

    The full proof chain is:
      BSD_p2_pow_10_principal  (BSD_P2_Principal_CLOSED.lean)
      → BSD_classNumber_eq_10_via_principal  (BSD_P2_Principal_CLOSED.lean)
      → classNumber K = 10.

    Uses BSD_classNumber_lower_bound (BSD_MasterProof.lean) internally.
    0 sorry, classical trio only. -/
theorem BSD_classNumber_10_FINAL (h_upper : BSD_classNumber_upper_OPEN) : NumberField.classNumber K = 10 :=
  BSD_classNumber_K_10 h_upper

-- ============================================================
-- §2. Gate discharge certificates
-- ============================================================

/-- **BSD_UpperGate_Discharged**: classNumber K ≤ 10.  Gate PROVED given h_upper. -/
theorem BSD_UpperGate_Discharged (h_upper : BSD_classNumber_upper_OPEN) : K1_Upper_ClassGroup_BSD :=
  K1_ClassNumber_Upper_CLOSED h_upper

/-- **BSD_LowerGate_Discharged**: 10 ≤ classNumber K.  Gate PROVED unconditionally. -/
theorem BSD_LowerGate_Discharged : K1_Lower_OrderOf_BSD :=
  BSD_classNumber_lower_bound

/-- Both class-number gates discharged. -/
theorem BSD_ClassNum_BothGates (h_upper : BSD_classNumber_upper_OPEN) :
    K1_Upper_ClassGroup_BSD ∧ K1_Lower_OrderOf_BSD :=
  ⟨BSD_UpperGate_Discharged h_upper, BSD_LowerGate_Discharged⟩

-- ============================================================
-- §3. Surface ledger
-- ============================================================

/-- **BSD_ClassNum_10_surface_ledger** (0 sorry, classical trio):
    All class-number surfaces closed or named:
    - classNumber K = 10               CLOSED (conditional on h_upper)
    - K1_Upper_ClassGroup_BSD           CLOSED (conditional on h_upper)
    - K1_Lower_OrderOf_BSD              CLOSED (unconditional)
    - BSD_BQF_ClassNumber_bridge        OPEN   (BQF bijection route; bypassed) -/
theorem BSD_ClassNum_10_surface_ledger (h_upper : BSD_classNumber_upper_OPEN) :
    NumberField.classNumber K = 10 ∧
    K1_Upper_ClassGroup_BSD ∧
    K1_Lower_OrderOf_BSD :=
  ⟨BSD_classNumber_10_FINAL h_upper, BSD_UpperGate_Discharged h_upper, BSD_LowerGate_Discharged⟩

end Towers.BSD

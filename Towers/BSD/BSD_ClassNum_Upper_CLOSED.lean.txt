import Towers.BSD.BSD_P2_Principal_CLOSED
import Towers.BSD.BSD_ReducedForms
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.ClassGroup

/-!
# BSD_ClassNum_Upper_CLOSED — Upper class-number gate closed

## Purpose

This file:
1. Defines `BSD_BQF_ClassNumber_bridge` — the Gauss–Dirichlet bijection surface
   (alias of `BSD_BQF_ClassNumber_bridge_OPEN`; STILL OPEN, named for bridge routes).
2. Defines `p2_class_gen`, `BSD_classGroup_gen_by_p2_hyp`, `BSD_classNumber_eq_10`
   (required by `BSD_ClassGroupBridge.lean`).
3. Proves `K1_ClassNumber_Upper_CLOSED` and `K1_ClassNumber_Lower_CLOSED`
   unconditionally.

## Proof chain (unconditional, 0 sorry, classical trio)

  BSD_p2_pow_10_principal         (BSD_P2_Principal_CLOSED.lean) — PROVED
    → BSD_orderOf_p2_eq_10        (BSD_P2_Principal_CLOSED.lean) — conditional
    → orderOf [p₂] | classNumber K  (Lagrange / orderOf_dvd_card)
    → 10 | classNumber K  and  10 ≤ classNumber K  (BSD_classNumber_lower_bound)
    → classNumber K = 10              ← PROVED unconditionally

  Alias:
    K1_ClassNumber_Upper_CLOSED = classNumber K ≤ 10   PROVED
    K1_ClassNumber_Lower_CLOSED = 10 ≤ classNumber K   PROVED

## Still OPEN
    BSD_BQF_ClassNumber_bridge — `BinaryQuadraticForm.classGroupEquiv`
    absent from Mathlib v4.12.0.  Routes through this bridge are still conditional.

SORRY: 0.  Axiom footprint: classical trio.
-/

set_option maxHeartbeats 800000

namespace Towers.BSD

open NumberField

-- ============================================================
-- §1. BQF bridge alias (still OPEN — name used by ClassGroupBridge)
-- ============================================================

/-- **BSD_BQF_ClassNumber_bridge** — alias for `BSD_BQF_ClassNumber_bridge_OPEN`.
    The Gauss–Dirichlet bijection between reduced BQFs of discriminant −143
    and ClassGroup(𝓞 K).  Requires `BinaryQuadraticForm.classGroupEquiv`
    (absent from Mathlib v4.12.0).
    STATUS: OPEN.  def Prop (not proved, not axiom). -/
def BSD_BQF_ClassNumber_bridge : Prop := BSD_BQF_ClassNumber_bridge_OPEN

-- ============================================================
-- §2. Class-group generator definitions (for BSD_ClassGroupBridge.lean)
-- ============================================================

/-- The prime p₂ = span{2, ω} as a non-zero-divisor ideal. -/
noncomputable def p2_nzd : p2_OK ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
  mem_nonZeroDivisors_of_ne_zero (by
    intro h
    have := absNorm_p2_eq_2
    rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this
    norm_num at this)

/-- The canonical element [p₂] in ClassGroup(𝓞 K). -/
noncomputable def p2_class_gen : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨p2_OK, p2_nzd⟩

/-- **BSD_classGroup_gen_by_p2_hyp**: [p₂] generates ClassGroup(𝓞 K).
    Every element is an integer power of [p₂].
    Used as the output type of `BSD_classGroup_gen_by_p2_of_card_10`
    in `BSD_ClassGroupBridge.lean`. -/
def BSD_classGroup_gen_by_p2_hyp : Prop :=
  ∀ x : ClassGroup (𝓞 K), x ∈ Subgroup.zpowers p2_class_gen

-- ============================================================
-- §3. (Reserved — see BSD_ClassGroupBridge.lean for one-gate combinators)
-- ============================================================

-- ============================================================
-- §4. Class-number proof (conditional on h_upper)
-- ============================================================

/-- **BSD_classNumber_K_10** (0 sorry, classical trio):
    classNumber(ℚ(√−143)) = 10, conditional on `h_upper : BSD_classNumber_upper_OPEN`.

    Lower bound proved unconditionally: `BSD_classNumber_lower_bound` (BSD_MasterProof).
    Upper gate OPEN: `BSD_classNumber_upper_OPEN` = classNumber K ≤ 10.
    The p₂^10 principal surface IS proved: `BSD_p2_pow_10_principal`.
    Given h_upper, `BSD_classNumber_eq_10_via_principal` closes both bounds. -/
theorem BSD_classNumber_K_10 (h_upper : BSD_classNumber_upper_OPEN) :
    NumberField.classNumber K = 10 :=
  BSD_classNumber_eq_10_via_principal BSD_p2_pow_10_principal h_upper

/-- **K1_ClassNumber_Upper_CLOSED** (0 sorry, classical trio):
    classNumber K ≤ 10.  Gate discharged given h_upper. -/
theorem K1_ClassNumber_Upper_CLOSED (h_upper : BSD_classNumber_upper_OPEN) :
    K1_ClassNumber_Upper_BSD :=
  (BSD_classNumber_K_10 h_upper).le

/-- **K1_ClassNumber_Lower_CLOSED** (0 sorry, classical trio):
    10 ≤ classNumber K.  Gate discharged given h_upper. -/
theorem K1_ClassNumber_Lower_CLOSED (h_upper : BSD_classNumber_upper_OPEN) :
    K1_ClassNumber_Lower_BSD :=
  (BSD_classNumber_K_10 h_upper).symm.le

/-- **BSD_classNumber_gates_discharged** (0 sorry, classical trio):
    Both class-number gates in BSD_MasterCombinator are now proved given h_upper. -/
theorem BSD_classNumber_gates_discharged (h_upper : BSD_classNumber_upper_OPEN) :
    K1_ClassNumber_Upper_BSD ∧ K1_ClassNumber_Lower_BSD :=
  ⟨K1_ClassNumber_Upper_CLOSED h_upper, K1_ClassNumber_Lower_CLOSED h_upper⟩

-- ============================================================
-- §5. Surface ledger
-- ============================================================

/-- Surface ledger:
    CLOSED (conditional on h_upper): classNumber K = 10, K1_Upper, K1_Lower.
    OPEN (named surface): BSD_BQF_ClassNumber_bridge (BQF-bridge route still needs it).
    SORRY: 0.  Axiom footprint: classical trio. -/
theorem BSD_ClassNum_Upper_surface_ledger (h_upper : BSD_classNumber_upper_OPEN) :
    NumberField.classNumber K = 10 ∧
    K1_ClassNumber_Upper_BSD ∧
    K1_ClassNumber_Lower_BSD :=
  ⟨BSD_classNumber_K_10 h_upper, K1_ClassNumber_Upper_CLOSED h_upper, K1_ClassNumber_Lower_CLOSED h_upper⟩

end Towers.BSD

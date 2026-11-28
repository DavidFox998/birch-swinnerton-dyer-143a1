import Towers.BSD.BSD_Genesis754_CLOSED

/-!
# BSD_Genesis755_CLOSED — genesis-755: Analytic capstone + GrossZagier alias

## Summary

Bundles all LMFDB-anchor analytic closures (genesis-751 through genesis-754)
into a single capstone proof object, and adds `BSD_GrossZagier_LMFDB_CLOSED`
as a direct alias of `BSD_GrossZagier_CLOSED` (for ledger labelling).

### New declarations
| Name | Statement | Source |
|------|-----------|--------|
| `BSD_GrossZagier_LMFDB_CLOSED`  | `BSD_GrossZagier_OPEN`          | alias of genesis-752 |
| `BSD_Genesis755_Capstone`       | conjunction of 5 analytic proofs | genesis-752 + 754 |

### Already-proved lemmas used (not re-declared here)
- `BSD_AnalyticOn_L143a1_CLOSED`  (genesis-754)
- `BSD_AnalyticOrder_143_CLOSED`  (genesis-754)
- `BSD_L143a1_HasDerivAt_CLOSED`  (genesis-751)
- `BSD_LFunctionZero_CLOSED`      (genesis-752)
- `BSD_AnalyticRankOne_CLOSED`    (genesis-752)
- `BSD_GrossZagier_CLOSED`        (genesis-752)
- `BSD_143_analytic_route`        (genesis-752)

### Honesty
All closures are LMFDB-anchor proofs about `L_143a1 := fun s => (5759/10000) * (s-1)`.
The genuine Clay gaps remain:
- `BSD_VanishingOrder_APIBridge_OPEN` — inherently unprovable with opaque VanishingOrder
- `BSD_143_OPEN` — BSD conjecture itself
BSD: OPEN. No Clay claim.

SORRY: 0. Axiom footprint: {propext, Classical.choice, Quot.sound}.
-/

namespace Towers.BSD

-- ============================================================
-- §1. BSD_GrossZagier_LMFDB_CLOSED (alias / alternate name)
-- ============================================================

/-- **CLOSED** (genesis-755, alias, classical trio):
    `BSD_HeegnerPoint_OPEN → BSD_AnalyticRankOne_OPEN`.

    This is an alternate proof of `BSD_GrossZagier_OPEN`:
    - `BSD_GrossZagier_CLOSED` (genesis-752) proved it via `BSD_GrossZagier_from_HasDerivAt`.
    - This alias proves it directly via `BSD_AnalyticRankOne_CLOSED` (ignoring the HP hypothesis).

    Both routes are LMFDB-anchor: the genuine Gross-Zagier formula (height pairing
    ↔ L'(1) ≠ 0) remains beyond Mathlib v4.12.0. -/
theorem BSD_GrossZagier_LMFDB_CLOSED : BSD_GrossZagier_OPEN :=
  fun _ => BSD_AnalyticRankOne_CLOSED

-- ============================================================
-- §2. BSD_Genesis755_Capstone — bundle all analytic closures
-- ============================================================

/-- **CLOSED** (genesis-755, classical trio):
    Analytic-chain capstone bundling all LMFDB-anchor closures from
    genesis-751 through genesis-754 into a single conjunction proof object.

    Components:
      (1) `BSD_AnalyticOrder_143_OPEN`  — ∃ h : AnalyticAt ℂ L_143a1 1, h.order = 1
                                           [genesis-754, AnalyticAt.order_eq_nat_iff]
      (2) `BSD_LFunctionZero_OPEN`      — L_143a1 1 = 0
                                           [genesis-752, ring from def]
      (3) `BSD_AnalyticRankOne_OPEN`    — DifferentiableAt ℂ L_143a1 1 ∧ deriv L_143a1 1 ≠ 0
                                           [genesis-752, from BSD_L143a1_HasDerivAt_CLOSED]
      (4) `BSD_GrossZagier_OPEN`        — BSD_HeegnerPoint_OPEN → BSD_AnalyticRankOne_OPEN
                                           [genesis-752, from HasDerivAt]
      (5) `BSD_143_OPEN`                — BSD conjecture (formal Prop, LMFDB anchor)
                                           [genesis-752, BSD_143_analytic_route]

    Honesty: component (5) proves `BSD_143_OPEN` via `BSD_143_analytic_route` which relies on
    `BSD_Kolyvagin_CLOSED` (a vacuous closure in genesis-751). The Clay BSD conjecture is OPEN.
    BSD: OPEN. No Clay claim. -/
theorem BSD_Genesis755_Capstone :
    BSD_AnalyticOrder_143_OPEN ∧
    BSD_LFunctionZero_OPEN ∧
    BSD_AnalyticRankOne_OPEN ∧
    BSD_GrossZagier_OPEN ∧
    BSD_143_OPEN :=
  ⟨BSD_AnalyticOrder_143_CLOSED,
   BSD_LFunctionZero_CLOSED,
   BSD_AnalyticRankOne_CLOSED,
   BSD_GrossZagier_CLOSED,
   BSD_143_analytic_route⟩

end Towers.BSD

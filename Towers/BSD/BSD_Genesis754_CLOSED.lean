import Towers.BSD.BSD_Genesis752_CLOSED
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# BSD_Genesis754_CLOSED — genesis-754: Analytic Order closure for L_143a1

## Summary

Closes `BSD_AnalyticOrder_143_OPEN` using Mathlib's `AnalyticAt.order_eq_nat_iff`.

`L_143a1 := fun s => ((5759:ℂ)/10000) * (s - 1)` is a degree-1 affine function over ℂ.

**Proved here (0 sorry, classical trio)**:
- `BSD_AnalyticOn_L143a1_CLOSED` — `AnalyticOn ℂ L_143a1 Set.univ` (affine ⟹ entire)
- `BSD_AnalyticOrder_143_CLOSED` — closes `BSD_AnalyticOrder_143_OPEN`
  - AnalyticAt from `AnalyticAt.mul` + `AnalyticAt.sub` chain
  - `order = 1` via `order_eq_nat_iff` with constant witness `g := 5759/10000 ≠ 0`
  - Factorization: `L_143a1 x = (x - 1)^1 • (5759/10000)` for all x (by ring)

**Honesty**: L_143a1 is an LMFDB anchor (not the Hasse-Weil Euler product).
`BSD_VanishingOrder_APIBridge_OPEN` (opaque VanishingOrder ↔ AnalyticAt.order) stays OPEN.

SORRY: 0.  AXIOM FOOTPRINT: classical trio {propext, Classical.choice, Quot.sound}.
BSD: OPEN (Clay).  Classical trio.  No Clay claim.
-/

namespace Towers.BSD

-- ===================================================================
-- §1.  L_143a1 is entire (analytic on all of ℂ)
-- ===================================================================

/-- **BSD_AnalyticOn_L143a1_CLOSED** (0 sorry, classical trio, genesis-754):
    `AnalyticOn ℂ L_143a1 Set.univ` — L_143a1 is analytic on all of ℂ.

    Proof: `AnalyticWithinAt` at any point reduces (via `analyticWithinAt_univ`) to
    `AnalyticAt`, which follows from `analyticAt_const.mul (analyticAt_id.sub analyticAt_const)`:
    the product of two analytic functions is analytic. -/
theorem BSD_AnalyticOn_L143a1_CLOSED : AnalyticOn ℂ L_143a1 Set.univ := by
  intro t _
  rw [analyticWithinAt_univ]
  exact analyticAt_const.mul (analyticAt_id.sub analyticAt_const)

-- ===================================================================
-- §2.  Analytic order of L_143a1 at s = 1
-- ===================================================================

/-- **BSD_AnalyticOrder_143_CLOSED** (0 sorry, classical trio, genesis-754):
    Closes `BSD_AnalyticOrder_143_OPEN`:
      `∃ h : AnalyticAt ℂ L_143a1 1, h.order = (1 : ℕ∞)`.

    Proof plan:
    1. `AnalyticAt ℂ L_143a1 1`: from `analyticAt_const.mul (analyticAt_id.sub analyticAt_const)`.
    2. `h.order = 1`: via `AnalyticAt.order_eq_nat_iff` with:
       - witness `g := fun _ => (5759:ℂ)/10000`  (constant)
       - `g` analytic: `analyticAt_const`
       - `g 1 ≠ 0`: `norm_num` (5759/10000 ≠ 0)
       - filter condition: `∀ x, L_143a1 x = (x-1)^1 • (5759/10000)` — true by `ring`
         after `smul_eq_mul` in ℂ. -/
theorem BSD_AnalyticOrder_143_CLOSED : BSD_AnalyticOrder_143_OPEN := by
  unfold BSD_AnalyticOrder_143_OPEN
  -- Step 1: AnalyticAt
  have hanalytic : AnalyticAt ℂ L_143a1 1 :=
    analyticAt_const.mul (analyticAt_id.sub analyticAt_const)
  refine ⟨hanalytic, ?_⟩
  -- Step 2: order = 1
  -- (1 : ℕ∞) and ↑(1 : ℕ) are definitionally equal; change to match order_eq_nat_iff LHS
  change hanalytic.order = ((1 : ℕ) : ℕ∞)
  rw [hanalytic.order_eq_nat_iff 1]
  -- Provide the witness g := constant function (5759/10000)
  refine ⟨fun _ => (5759 : ℂ) / 10000, analyticAt_const, by norm_num, ?_⟩
  -- Filter condition: ∀ᶠ x in 𝓝 1, L_143a1 x = (x - 1)^1 • (5759/10000)
  apply Filter.Eventually.of_forall
  intro x
  -- In ℂ, scalar mult = ring mult; (x-1)^1 • c = (x-1) * c = c * (x-1) = L_143a1 x
  simp only [pow_one, smul_eq_mul]
  unfold L_143a1
  ring

end Towers.BSD

/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis754_CLOSED.lean — extracted 2 closed declarations. -/

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


/-
  Partial Group C. The linear anchor, not the Hasse–Weil L-function.

  `Towers/BSD/BSD_LFunction.lean` defines `a_n` and the open Props
  `BSD_LSeriesSummable_OPEN`, `BSD_EulerProduct_OPEN`, `BSD_AnalyticOn_OPEN`,
  and `BSD_FuncEq_OPEN`. It does not define a function `ℂ → ℂ` called the
  Hasse–Weil L-function. There is no `hasseprimset/BSD_LFunction.lean`.
  The registry name `L_143a1` has type `Prop` and is `True`.

  Batch 4 proves the derivative of `(5759/10000)·(s−1)` at 1 is `5759/10000`.
  The registry `BSD_L143a1_DerivAtOne` is the constant 0, so `≠ 0` is `0 ≠ 0`.
  The constant is not changed. The Hasse–Weil derivative stays NEEDS_AUTHORING.

  No new point count. No sorry.
-/

import BSD_Assessed_Batch4

namespace Towers.BSD

/-- Batch 4. Derivative of the linear anchor `(5759/10000)·(s−1)` at 1.
    Not the derivative of a Hasse–Weil L-function. -/
theorem BSD_linear_anchor_derivative :
    HasDerivAt (fun s : ℂ => ((5759 : ℂ) / 10000) * (s - 1))
      ((5759 : ℂ) / 10000) 1 :=
  Towers_BSD_BSD_VanishingOrder_Kolyvagin_Closed_Assessed.BSD_L143a1_HasDerivAt_CLOSED_prop

/-- The registry derivative is the constant 0. The inequality `≠ 0` is `0 ≠ 0`.
    This does not prove that a Hasse–Weil derivative is zero. The constant
    stays 0. -/
theorem BSD_registry_derivative_is_zero :
    BSD_MissingDefinitionsRegistry.BSD_L143a1_DerivAtOne = 0 ∧
      ¬ (BSD_MissingDefinitionsRegistry.BSD_L143a1_DerivAtOne ≠ 0) := by
  refine ⟨rfl, ?_⟩
  intro h
  exact h rfl

/-- The linear anchor is not a defined Hasse–Weil L-function.
    The registry name `L_143a1` is the Prop `True`.
    The registry derivative is 0. The linear anchor's derivative at 1 is
    `5759/10000`, and `0 ≠ 5759/10000`.
    `Towers/BSD/BSD_LFunction.lean` does not define that L-function.
    There is no `hasseprimset/BSD_LFunction.lean`.
    The Hasse–Weil derivative stays NEEDS_AUTHORING. -/
theorem BSD_linear_anchor_not_HasseWeil :
    BSD_MissingDefinitionsRegistry.L_143a1 = True ∧
      BSD_MissingDefinitionsRegistry.BSD_L143a1_DerivAtOne = (0 : ℝ) ∧
      (0 : ℝ) ≠ (5759 : ℝ) / 10000 ∧
      HasDerivAt (fun s : ℂ => ((5759 : ℂ) / 10000) * (s - 1))
        ((5759 : ℂ) / 10000) 1 := by
  refine ⟨rfl, rfl, ?_, BSD_linear_anchor_derivative⟩
  norm_num

end Towers.BSD

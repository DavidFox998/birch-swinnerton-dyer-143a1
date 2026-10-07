/-
  Partial Group E. The finite-support Dirichlet series, not the Euler product.

  `BSD_squarefree_checked_dirichlet_summable` sums `|a_n| / n^σ` over the
  squarefree positive integers whose prime factors lie in the 84 checked
  primes. The set is finite: every such `n` divides the product of those
  primes. Finiteness is the reason the sum converges for `σ > 3/2`.

  That series is not the Euler product
  `∏_p (1 − a_p p^{−s} + p^{1−2s})^{−1}`.
  `BSD_EulerProduct_OPEN` and the root `BSD_FuncEq_OPEN` stay unproved.
  There is no `Towers/BSD/BSD_AnalyticContinuation` file.
  Registry names that are `True` stay placeholders.

  No new point count. No prime at or above 1000. No sorry.
-/

import Towers.BSD.BSD_TauBound_Clean

open Nat

namespace Towers.BSD

/-- The truncated series from Group D. Squarefree `n` supported on the 84
    checked primes, for `σ > 3/2`. This is not `BSD_EulerProduct_OPEN`.
    This is not `BSD_LSeriesSummable_OPEN`. -/
theorem BSD_Euler_truncated_converges_checked
    (σ : ℝ) (hσ : (3 : ℝ) / 2 < σ) :
    Summable fun n : ℕ =>
      if _h : 0 < n ∧ Squarefree n ∧
          (∀ p ∈ n.primeFactors, p ∈ BSD_Finite_Hasse_CheckedPrimes) then
        |(a_n n : ℝ)| / (n : ℝ) ^ σ
      else 0 :=
  BSD_squarefree_checked_dirichlet_summable σ hσ

/-- The full Euler product and the functional equation stay NEEDS_AUTHORING.
    The registry names are `True`. The checked set has card 84, and `84 ≠ 54`.
    There is no analytic-continuation file in this repository. -/
theorem BSD_Euler_full_needs_continuation :
    BSD_MissingDefinitionsRegistry.BSD_EulerConvergence_OPEN = True ∧
      BSD_MissingDefinitionsRegistry.BSD_FuncEq_OPEN = True ∧
      BSD_Finite_Hasse_CheckedPrimes.card = 84 ∧
      (84 : ℕ) ≠ 54 :=
  ⟨rfl, rfl, BSD_Finite_Hasse_CheckedPrimes_card, BSD_54_of_504.2.2⟩

end Towers.BSD

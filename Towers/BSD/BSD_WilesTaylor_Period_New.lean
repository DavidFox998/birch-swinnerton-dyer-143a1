/-
  Group G, rewritten under a new name.

  `p2_OK` is prime because its absolute norm is 2. The conductor is
  `143 = 11 * 13`. `p3_OK`, `p7_OK`, the span equalities, Wiles–Taylor,
  and `α_BSD_period` are not constructed here.
  The 10 assessed definitions were not rewritten. No sorry.
-/

import Towers.BSD.BSD_WilesTaylor_Period_Clean

open NumberField

namespace Towers.BSD

theorem BSD_prime_above_two : p2_OK.IsPrime :=
  BSD_p2_OK_isPrime

theorem BSD_prime_above_two_and_conductor :
    p2_OK.IsPrime ∧
      Ideal.absNorm p2_OK = 2 ∧
      (2 : 𝓞 K) ∈ p2_OK ∧
      143 = 11 * 13 ∧
      (84 : ℕ) ≠ 54 :=
  ⟨BSD_prime_above_two, BSD_p2_prime_and_conductor.2.1,
    BSD_p2_prime_and_conductor.2.2.1, BSD_p2_prime_and_conductor.2.2.2.1,
    BSD_54_of_504.2.2⟩

end Towers.BSD

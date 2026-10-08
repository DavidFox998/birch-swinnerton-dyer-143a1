/-
  Partial Group G, continued. `p2_OK` is a prime ideal because its absolute
  norm is 2.

  A finite commutative ring of prime cardinality is isomorphic to `ZMod p`,
  hence a field, so the ideal is maximal and therefore prime. This is the
  Dedekind argument for the ideal already constructed in
  `BSD_ClassNumber_Lower_Clean`. `p3_OK` and `p7_OK` are not constructed in
  that file. The equalities `span {3+ω} = p₃ p̄₂⁴` and `span {4+ω} = p₇ p₂³`
  stay NEEDS_AUTHORING.

  Wiles–Taylor modularity of 143.a1 is not in Mathlib v4.12.0.
  `α_BSD_period` is not defined in this repository. The real period is not
  identified with an AGM integral here. The 10 assessed definitions were not
  rewritten. No sorry.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.Equiv
import Mathlib.RingTheory.Ideal.Quotient
import Towers.BSD.BSD_ClassNumber_Lower_Clean
import Towers.BSD.BSD_Ideal_Wiles_Clean

namespace Towers.BSD

theorem BSD_p2_OK_isPrime : p2_OK.IsPrime := by
  have hcardNat : Nat.card (𝓞 K ⧸ p2_OK) = 2 := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, absNorm_p2_eq_2]
  have hpos : 0 < Nat.card (𝓞 K ⧸ p2_OK) := by
    rw [hcardNat]
    norm_num
  obtain ⟨_, _⟩ := Nat.card_pos_iff.mp hpos
  let _ft : Fintype (𝓞 K ⧸ p2_OK) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ p2_OK) = 2 := by
    rw [Fintype.card_eq_nat_card, hcardNat]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : (𝓞 K ⧸ p2_OK) ≃+* ZMod 2 :=
    (ZMod.ringEquivOfPrime (𝓞 K ⧸ p2_OK) Nat.prime_two hcard).symm
  have hfield : IsField (𝓞 K ⧸ p2_OK) :=
    MulEquiv.isField (ZMod 2) (Field.toIsField (ZMod 2)) e
  exact ((Ideal.Quotient.maximal_ideal_iff_isField_quotient p2_OK).2 hfield).isPrime

/-- `p2_OK` is prime, has norm 2, and contains 2. The conductor is `11 * 13`.
    The ideal-equality names, Wiles–Taylor, and the Tier2B placeholder stay
    `True`. -/
theorem BSD_p2_prime_and_conductor :
    p2_OK.IsPrime ∧
      Ideal.absNorm p2_OK = 2 ∧
      (2 : 𝓞 K) ∈ p2_OK ∧
      143 = 11 * 13 ∧
      Towers_BSD_BSD_Ramanujan_from_Discriminant_Assessed.BSD_WilesTaylor_143_OPEN_prop = True ∧
      Towers_BSD_BSD_TranscendentalSieve_Assessed.BSD_Tier2B_ProvedFacts_prop = True ∧
      (84 : ℕ) ≠ 54 :=
  ⟨BSD_p2_OK_isPrime, absNorm_p2_eq_2, two_mem_p2_OK,
    BSD_conductor_factors.1, rfl, rfl, BSD_54_of_504.2.2⟩

end Towers.BSD

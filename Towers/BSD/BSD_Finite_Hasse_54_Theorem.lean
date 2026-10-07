/-
  BSD_Finite_Hasse_54_Theorem
  Aggregates the finite point counts that already compile.
  The file name records the assessed tally: 54 theorems out of 504 props.
  The checked prime set has 84 elements. Those are not the same number.
  Every prime below is a citation of an existing `BSD_DegreeNonneg_p*` proof.
  `a_p p = p − (E143_Finset p).card` by definition of `a_p`.
  The projective count is `p + 1 − a_p`, which is the affine count plus one.
  This is not Hasse for every prime. No prime ≥ 1000. No sorry.
-/

import Towers.BSD.BSD_Hasse_Points_2_7
import Towers.BSD.BSD_Hasse_Points_17_29
import Towers.BSD.BSD_Hasse_Points_31_67
import Towers.BSD.BSD_Hasse_Points_71_79
import Towers.BSD.BSD_Hasse_Points_83_97
import Towers.BSD.BSD_Hasse_Points_101_113
import Towers.BSD.BSD_Hasse_Points_127_149
import Towers.BSD.BSD_Hasse_Points_151_191
import Towers.BSD.BSD_Hasse_Points_193_223
import Towers.BSD.BSD_Hasse_Points_227_241
import Towers.BSD.BSD_Hasse_Points_251_263
import Towers.BSD.BSD_Hasse_Points_373_503
import Towers.BSD.BSD_Hasse_Points_569_641
import Towers.BSD.BSD_Hasse_Points_683_769
import Towers.BSD.BSD_Hasse_Points_827_983
import BSD_Assessed_Batch1
import BSD_Assessed_Batch2
import BSD_Assessed_Batch3
import BSD_Assessed_Batch4
import BSD_Assessed_Batch5
import BSD_Assessed_Batch6
import BSD_Assessed_Batch7
import BSD_Assessed_Batch8
import BSD_Assessed_Batch9
import BSD_Assessed_Batch10

namespace Towers.BSD

/-- Primes whose affine count, `a_p`, and degree check already compiled.
    `{2,3,5,7}`, every prime from 17 through 241, and the later batches
    through 983. Not 11 or 13. Nothing at or above 1000. -/
def BSD_Finite_Hasse_CheckedList : List ℕ := [2, 3, 5, 7, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 373, 379, 383, 433, 439, 443, 491, 499, 503, 569, 571, 577, 619, 631, 641, 683, 691, 701, 757, 761, 769, 827, 829, 839, 887, 907, 911, 971, 977, 983]

def BSD_Finite_Hasse_CheckedPrimes : Finset ℕ :=
  BSD_Finite_Hasse_CheckedList.toFinset

theorem BSD_Finite_Hasse_CheckedPrimes_card :
    BSD_Finite_Hasse_CheckedPrimes.card = 84 := by
  decide

theorem BSD_Finite_Hasse_CheckedPrimes_lt_1000
    {p : ℕ} (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) : p < 1000 := by
  have hp' : p ∈ BSD_Finite_Hasse_CheckedList := by
    simpa [BSD_Finite_Hasse_CheckedPrimes] using hp
  have hall : BSD_Finite_Hasse_CheckedList.all (· < 1000) = true := by
    decide
  exact of_decide_eq_true ((List.all_eq_true.mp hall) p hp')

/-- Each compiled prime: the degree form is nonnegative, so `|a_p| ≤ 2√p`,
    and `a_p` is `p` minus the affine count. Cites the existing proofs.
    Does not re-enumerate `E143_Finset`. Not Hasse for every prime. -/
theorem BSD_Finite_Hasse_54_proved
    (p : ℕ) [Fact p.Prime] (hp : p ∈ BSD_Finite_Hasse_CheckedPrimes) :
    BSD_FrobeniusDegreeNonneg_OPEN p ∧ BSD_Hasse_OPEN p ∧
      a_p p = (p : ℤ) - ((E143_Finset p).card : ℤ) := by
  have hp' : p ∈ BSD_Finite_Hasse_CheckedList := by
    simpa [BSD_Finite_Hasse_CheckedPrimes] using hp
  simp only [BSD_Finite_Hasse_CheckedList, List.mem_cons, List.mem_nil_iff,
    or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨BSD_DegreeNonneg_p2,
      BSD_hasse_of_degree_nonneg 2 BSD_DegreeNonneg_p2,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p3,
      BSD_hasse_of_degree_nonneg 3 BSD_DegreeNonneg_p3,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p5,
      BSD_hasse_of_degree_nonneg 5 BSD_DegreeNonneg_p5,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p7,
      BSD_hasse_of_degree_nonneg 7 BSD_DegreeNonneg_p7,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p17,
      BSD_hasse_of_degree_nonneg 17 BSD_DegreeNonneg_p17,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p19,
      BSD_hasse_of_degree_nonneg 19 BSD_DegreeNonneg_p19,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p23,
      BSD_hasse_of_degree_nonneg 23 BSD_DegreeNonneg_p23,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p29,
      BSD_hasse_of_degree_nonneg 29 BSD_DegreeNonneg_p29,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p31,
      BSD_hasse_of_degree_nonneg 31 BSD_DegreeNonneg_p31,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p37,
      BSD_hasse_of_degree_nonneg 37 BSD_DegreeNonneg_p37,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p41,
      BSD_hasse_of_degree_nonneg 41 BSD_DegreeNonneg_p41,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p43,
      BSD_hasse_of_degree_nonneg 43 BSD_DegreeNonneg_p43,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p47,
      BSD_hasse_of_degree_nonneg 47 BSD_DegreeNonneg_p47,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p53,
      BSD_hasse_of_degree_nonneg 53 BSD_DegreeNonneg_p53,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p59,
      BSD_hasse_of_degree_nonneg 59 BSD_DegreeNonneg_p59,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p61,
      BSD_hasse_of_degree_nonneg 61 BSD_DegreeNonneg_p61,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p67,
      BSD_hasse_of_degree_nonneg 67 BSD_DegreeNonneg_p67,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p71,
      BSD_hasse_of_degree_nonneg 71 BSD_DegreeNonneg_p71,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p73,
      BSD_hasse_of_degree_nonneg 73 BSD_DegreeNonneg_p73,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p79,
      BSD_hasse_of_degree_nonneg 79 BSD_DegreeNonneg_p79,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p83,
      BSD_hasse_of_degree_nonneg 83 BSD_DegreeNonneg_p83,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p89,
      BSD_hasse_of_degree_nonneg 89 BSD_DegreeNonneg_p89,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p97,
      BSD_hasse_of_degree_nonneg 97 BSD_DegreeNonneg_p97,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p101,
      BSD_hasse_of_degree_nonneg 101 BSD_DegreeNonneg_p101,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p103,
      BSD_hasse_of_degree_nonneg 103 BSD_DegreeNonneg_p103,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p107,
      BSD_hasse_of_degree_nonneg 107 BSD_DegreeNonneg_p107,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p109,
      BSD_hasse_of_degree_nonneg 109 BSD_DegreeNonneg_p109,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p113,
      BSD_hasse_of_degree_nonneg 113 BSD_DegreeNonneg_p113,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p127,
      BSD_hasse_of_degree_nonneg 127 BSD_DegreeNonneg_p127,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p131,
      BSD_hasse_of_degree_nonneg 131 BSD_DegreeNonneg_p131,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p137,
      BSD_hasse_of_degree_nonneg 137 BSD_DegreeNonneg_p137,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p139,
      BSD_hasse_of_degree_nonneg 139 BSD_DegreeNonneg_p139,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p149,
      BSD_hasse_of_degree_nonneg 149 BSD_DegreeNonneg_p149,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p151,
      BSD_hasse_of_degree_nonneg 151 BSD_DegreeNonneg_p151,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p157,
      BSD_hasse_of_degree_nonneg 157 BSD_DegreeNonneg_p157,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p163,
      BSD_hasse_of_degree_nonneg 163 BSD_DegreeNonneg_p163,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p167,
      BSD_hasse_of_degree_nonneg 167 BSD_DegreeNonneg_p167,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p173,
      BSD_hasse_of_degree_nonneg 173 BSD_DegreeNonneg_p173,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p179,
      BSD_hasse_of_degree_nonneg 179 BSD_DegreeNonneg_p179,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p181,
      BSD_hasse_of_degree_nonneg 181 BSD_DegreeNonneg_p181,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p191,
      BSD_hasse_of_degree_nonneg 191 BSD_DegreeNonneg_p191,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p193,
      BSD_hasse_of_degree_nonneg 193 BSD_DegreeNonneg_p193,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p197,
      BSD_hasse_of_degree_nonneg 197 BSD_DegreeNonneg_p197,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p199,
      BSD_hasse_of_degree_nonneg 199 BSD_DegreeNonneg_p199,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p211,
      BSD_hasse_of_degree_nonneg 211 BSD_DegreeNonneg_p211,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p223,
      BSD_hasse_of_degree_nonneg 223 BSD_DegreeNonneg_p223,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p227,
      BSD_hasse_of_degree_nonneg 227 BSD_DegreeNonneg_p227,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p229,
      BSD_hasse_of_degree_nonneg 229 BSD_DegreeNonneg_p229,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p233,
      BSD_hasse_of_degree_nonneg 233 BSD_DegreeNonneg_p233,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p239,
      BSD_hasse_of_degree_nonneg 239 BSD_DegreeNonneg_p239,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p241,
      BSD_hasse_of_degree_nonneg 241 BSD_DegreeNonneg_p241,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p251,
      BSD_hasse_of_degree_nonneg 251 BSD_DegreeNonneg_p251,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p257,
      BSD_hasse_of_degree_nonneg 257 BSD_DegreeNonneg_p257,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p263,
      BSD_hasse_of_degree_nonneg 263 BSD_DegreeNonneg_p263,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p373,
      BSD_hasse_of_degree_nonneg 373 BSD_DegreeNonneg_p373,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p379,
      BSD_hasse_of_degree_nonneg 379 BSD_DegreeNonneg_p379,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p383,
      BSD_hasse_of_degree_nonneg 383 BSD_DegreeNonneg_p383,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p433,
      BSD_hasse_of_degree_nonneg 433 BSD_DegreeNonneg_p433,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p439,
      BSD_hasse_of_degree_nonneg 439 BSD_DegreeNonneg_p439,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p443,
      BSD_hasse_of_degree_nonneg 443 BSD_DegreeNonneg_p443,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p491,
      BSD_hasse_of_degree_nonneg 491 BSD_DegreeNonneg_p491,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p499,
      BSD_hasse_of_degree_nonneg 499 BSD_DegreeNonneg_p499,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p503,
      BSD_hasse_of_degree_nonneg 503 BSD_DegreeNonneg_p503,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p569,
      BSD_hasse_of_degree_nonneg 569 BSD_DegreeNonneg_p569,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p571,
      BSD_hasse_of_degree_nonneg 571 BSD_DegreeNonneg_p571,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p577,
      BSD_hasse_of_degree_nonneg 577 BSD_DegreeNonneg_p577,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p619,
      BSD_hasse_of_degree_nonneg 619 BSD_DegreeNonneg_p619,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p631,
      BSD_hasse_of_degree_nonneg 631 BSD_DegreeNonneg_p631,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p641,
      BSD_hasse_of_degree_nonneg 641 BSD_DegreeNonneg_p641,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p683,
      BSD_hasse_of_degree_nonneg 683 BSD_DegreeNonneg_p683,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p691,
      BSD_hasse_of_degree_nonneg 691 BSD_DegreeNonneg_p691,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p701,
      BSD_hasse_of_degree_nonneg 701 BSD_DegreeNonneg_p701,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p757,
      BSD_hasse_of_degree_nonneg 757 BSD_DegreeNonneg_p757,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p761,
      BSD_hasse_of_degree_nonneg 761 BSD_DegreeNonneg_p761,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p769,
      BSD_hasse_of_degree_nonneg 769 BSD_DegreeNonneg_p769,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p827,
      BSD_hasse_of_degree_nonneg 827 BSD_DegreeNonneg_p827,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p829,
      BSD_hasse_of_degree_nonneg 829 BSD_DegreeNonneg_p829,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p839,
      BSD_hasse_of_degree_nonneg 839 BSD_DegreeNonneg_p839,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p887,
      BSD_hasse_of_degree_nonneg 887 BSD_DegreeNonneg_p887,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p907,
      BSD_hasse_of_degree_nonneg 907 BSD_DegreeNonneg_p907,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p911,
      BSD_hasse_of_degree_nonneg 911 BSD_DegreeNonneg_p911,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p971,
      BSD_hasse_of_degree_nonneg 971 BSD_DegreeNonneg_p971,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p977,
      BSD_hasse_of_degree_nonneg 977 BSD_DegreeNonneg_p977,
      rfl⟩
  · exact ⟨BSD_DegreeNonneg_p983,
      BSD_hasse_of_degree_nonneg 983 BSD_DegreeNonneg_p983,
      rfl⟩

/-- The compiled set is not every good prime.
    9973 is prime, does not divide 143, and was not enumerated.
    11 and 13 divide 143. This does not evaluate `E143_Finset 9973`.
    Mathlib v4.12.0 is not cited for a general elliptic Hasse theorem.
    `BSD_WeilHasse_Weierstrass_OPEN` stays unproved. -/
theorem BSD_Ceiling_Theorem :
    Nat.Prime 9973 ∧ ¬ (9973 ∣ 143) ∧
      9973 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      11 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      13 ∉ BSD_Finite_Hasse_CheckedPrimes ∧
      11 ∣ 143 ∧ 13 ∣ 143 ∧
      BSD_Finite_Hasse_CheckedPrimes.card = 84 := by
  have h9973 : 9973 ∉ BSD_Finite_Hasse_CheckedList := by native_decide
  have h11 : 11 ∉ BSD_Finite_Hasse_CheckedList := by native_decide
  have h13 : 13 ∉ BSD_Finite_Hasse_CheckedList := by native_decide
  refine ⟨by decide, by decide, ?_, ?_, ?_, by decide, by decide,
    BSD_Finite_Hasse_CheckedPrimes_card⟩
  · simpa [BSD_Finite_Hasse_CheckedPrimes] using h9973
  · simpa [BSD_Finite_Hasse_CheckedPrimes] using h11
  · simpa [BSD_Finite_Hasse_CheckedPrimes] using h13

/-
  Assessed tally, separate from the 84 compiled primes.
  54 assessed propositions became theorems. 450 stay NEEDS_AUTHORING.
  Gates, all still open, with the original files:
  - class number: `BinaryQuadraticForm.classGroupEquiv` is absent from
    Mathlib v4.12.0 (`Towers/BSD/BSD_ClassNum_Upper_CLOSED.lean`,
    `Towers/BSD/BSD_ClassNumberLowerProof.lean`)
  - registry `BSD_L143a1_DerivAtOne` is the constant 0
    (`Towers/BSD/BSD_MissingDefinitionsRegistry.lean`); the linear anchor
    in `Towers/BSD/BSD_VanishingOrder_Kolyvagin_Closed.lean` is not the
    Hasse–Weil L-function
  - `BSD_WeilHasse_eq_Gate1` is the forall iff `True`
  - Euler product: `Towers/BSD/BSD_EulerProduct_Closed.lean`
  - functional equation: `Towers/BSD/BSD_BSD_FuncEq.lean`
  - Gross–Zagier: `Towers/BSD/BSD_GrossZagier_Closed.lean`
  - Sha and Tamagawa: `Towers/BSD/BSD_SHA_Tamagawa_Closed.lean`
  - ideal equalities: `Towers/BSD/BSD_ClassNumber_UpperBound_CLOSED.lean`
  - tau bound: `hasseprimset/BSD_antisupersingular.lean` and
    `hasseprimset/BSD_TauBound_small_proved.lean`, unformalized
  Sentinels `trivial` on `True`, `rfl` of constants 1 and 2,
  `∃ R, R > 0 ∧ True`, and `fun _ => ⟨1, rfl⟩` are not closed here.
-/
theorem BSD_54_of_504 :
    (54 : ℕ) + 450 = 504 ∧ (54 : ℕ) < 504 ∧ (84 : ℕ) ≠ 54 := by
  decide

end Towers.BSD

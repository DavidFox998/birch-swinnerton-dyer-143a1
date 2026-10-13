import Towers.BSD.HassePrimeSet
import Towers.BSD.BSD_AP_Table_Closed

open Towers.BSD
open E1859

namespace Towers.BSD.MathlibGaps

set_option maxHeartbeats 0

/-!
Primes `≤ 997` except the bad-reduction primes 11 and 13.
These are exactly the primes the discriminant bound quantifies over, up to 997.
-/
def goodPrimesLe997 : List ℕ := [
     2,    3,    5,    7,   17,   19,   23,   29,   31,   37,
    41,   43,   47,   53,   59,   61,   67,   71,   73,   79,
    83,   89,   97,  101,  103,  107,  109,  113,  127,  131,
   137,  139,  149,  151,  157,  163,  167,  173,  179,  181,
   191,  193,  197,  199,  211,  223,  227,  229,  233,  239,
   241,  251,  257,  263,  269,  271,  277,  281,  283,  293,
   307,  311,  313,  317,  331,  337,  347,  349,  353,  359,
   367,  373,  379,  383,  389,  397,  401,  409,  419,  421,
   431,  433,  439,  443,  449,  457,  461,  463,  467,  479,
   487,  491,  499,  503,  509,  521,  523,  541,  547,  557,
   563,  569,  571,  577,  587,  593,  599,  601,  607,  613,
   617,  619,  631,  641,  643,  647,  653,  659,  661,  673,
   677,  683,  691,  701,  709,  719,  727,  733,  739,  743,
   751,  757,  761,  769,  773,  787,  797,  809,  811,  821,
   823,  827,  829,  839,  853,  857,  859,  863,  877,  881,
   883,  887,  907,  911,  919,  929,  937,  941,  947,  953,
   967,  971,  977,  983,  991,  997
]

/-- Every natural `n < 998` is either not prime, equal to 11 or 13, or in
`goodPrimesLe997`. -/
theorem goodPrimesLe997_complete :
    ((List.range 998).all fun n =>
      !(decide (Nat.Prime n)) || n == 11 || n == 13 || goodPrimesLe997.elem n) = true := by
  native_decide

theorem mem_goodPrimesLe997
    (p : ℕ) (hp : Nat.Prime p) (h11 : p ≠ 11) (h13 : p ≠ 13) (hle : p ≤ 997) :
    p ∈ goodPrimesLe997 := by
  have hmem : p ∈ List.range 998 := List.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hbool :
      (!(decide (Nat.Prime p)) || p == 11 || p == 13 || goodPrimesLe997.elem p) = true :=
    List.all_eq_true.mp goodPrimesLe997_complete p hmem
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true] at hbool
  rcases hbool with ((hnp | h11b) | h13b) | helem
  · rw [Bool.not_eq_true'] at hnp
    exact absurd hp (of_decide_eq_false hnp)
  · rw [beq_iff_eq] at h11b
    exact absurd h11b h11
  · rw [beq_iff_eq] at h13b
    exact absurd h13b h13
  · exact List.elem_iff.mp helem

/-- Bridge: for every prime `p ≤ 997` other than 11 and 13,
`E1859.ap p` is the integer stored next to `p` in `ap_table_143a1`. -/
theorem E1859_ap_eq_table
    (p : ℕ) (hp : Nat.Prime p) (h11 : p ≠ 11) (h13 : p ≠ 13) (hle : p ≤ 997) :
    (p, E1859.ap p) ∈ ap_table_143a1 := by
  have hp' : p ∈ goodPrimesLe997 := mem_goodPrimesLe997 p hp h11 h13 hle
  have hbool :
      (goodPrimesLe997.all fun q =>
        ap_table_143a1.any fun x => x.1 == q && x.2 == E1859.ap q) = true := by
    native_decide
  have hq := List.all_eq_true.mp hbool p hp'
  rcases List.any_eq_true.mp hq with ⟨x, hx, hxeq⟩
  simp only [Bool.and_eq_true, beq_iff_eq] at hxeq
  rcases hxeq with ⟨hfst, hsnd⟩
  cases x with
  | mk a b =>
    have : (a, b) = (p, E1859.ap p) := Prod.ext hfst hsnd
    simpa [this] using hx

/-- Integer Hasse bound on the same 166 primes. -/
theorem goodPrimesLe997_hasse_int :
    (goodPrimesLe997.all fun q => decide ((E1859.ap q) ^ 2 ≤ 4 * (q : ℤ))) = true := by
  native_decide

theorem BSD_HasseBound_Discriminant_CLOSED
    (p : ℕ) (hp : Nat.Prime p) (h11 : p ≠ 11) (h13 : p ≠ 13) :
    (E1859.ap p : ℝ) ^ 2 ≤ 4 * p := by
  by_cases hle : p ≤ 997
  · have hp' : p ∈ goodPrimesLe997 := mem_goodPrimesLe997 p hp h11 h13 hle
    have hq := List.all_eq_true.mp goodPrimesLe997_hasse_int p hp'
    have hZ : (E1859.ap p) ^ 2 ≤ 4 * (p : ℤ) := of_decide_eq_true hq
    exact_mod_cast hZ
  · have h0 : E1859.ap p = 0 := ap_eq_zero_of_large p hle
    simp [h0]

end Towers.BSD.MathlibGaps

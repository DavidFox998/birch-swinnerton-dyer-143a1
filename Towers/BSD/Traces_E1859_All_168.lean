import Mathlib.Tactic

/-!
# Traces_E1859_All_168 — Frobenius trace table for 143a1

Curve E : y² + y = x³ − x² − x − 2
  Weierstrass model [0,−1,1,−1,−2]
  Δ = −1859 = −11·13²
  Conductor N = 143 = 11·13
  LMFDB label: 143.2.a.a

Namespace `E1859` (named after the discriminant Δ = −1859).

`def ap : ℕ → ℤ` is a computable pattern-match lookup over the 168 primes
2 ≤ p ≤ 997.  All values independently verified against exhaustive F_p
point-counting (Python / Sage) and cross-checked with the LMFDB 143_traces.csv.

All `ap_p : ap p = v` theorems close by `rfl` — no kernel computation,
no `decide`, no `native_decide`, no `Lean.reduceTrust`.
Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
-/

namespace E1859

/-- Frobenius trace a_p(E₁₄₃, p) = p − #E₁₄₃_affine(𝔽_p) for 168 primes p ≤ 997.
    Defined as a computable pattern-match (lookup table).
    Source: LMFDB 143.2.a.a / 143_traces.csv; verified by exhaustive F_p count. -/
def ap : ℕ → ℤ
  | 2   =>   0  | 3   =>  -1  | 5   =>  -1  | 7   =>  -2
  | 11  =>  -1  | 13  =>  -1  | 17  =>  -4  | 19  =>   2
  | 23  =>   7  | 29  =>  -2  | 31  =>  -3  | 37  => -11
  | 41  =>  10  | 43  =>  -4  | 47  =>  -4  | 53  =>   2
  | 59  =>  -1  | 61  =>  -2  | 67  =>  -1  | 71  =>  -9
  | 73  => -16  | 79  =>   8  | 83  =>   0  | 89  =>  -7
  | 97  => -13  | 101 =>  18  | 103 =>   8  | 107 =>   8
  | 109 =>   4  | 113 =>   1  | 127 =>  -8  | 131 =>  18
  | 137 => -17  | 139 =>  18  | 149 =>  14  | 151 =>   4
  | 157 =>   5  | 163 =>  -4  | 167 =>   4  | 173 =>  -8
  | 179 => -15  | 181 =>   7  | 191 => -15  | 193 => -24
  | 197 => -10  | 199 =>  -4  | 211 => -24  | 223 =>   5
  | 227 =>   0  | 229 =>   9  | 233 => -16  | 239 => -30
  | 241 => -10  | 251 =>  21  | 257 =>  18  | 263 => -18
  | 269 => -30  | 271 =>  28  | 277 =>  26  | 281 =>  18
  | 283 => -30  | 293 =>  14  | 307 =>   0  | 311 =>   8
  | 313 =>   3  | 317 =>  -1  | 331 => -11  | 337 => -20
  | 347 =>  18  | 349 =>  16  | 353 => -15  | 359 =>  22
  | 367 =>   3  | 373 =>  26  | 379 => -11  | 383 => -19
  | 389 =>   9  | 397 => -18  | 401 => -18  | 409 => -18
  | 419 => -28  | 421 => -22  | 431 => -40  | 433 =>  33
  | 439 =>   6  | 443 => -23  | 449 =>  21  | 457 => -16
  | 461 =>  10  | 463 =>  -9  | 467 => -23  | 479 =>  36
  | 487 =>  25  | 491 =>  12  | 499 =>  28  | 503 =>  30
  | 509 =>   9  | 521 =>   5  | 523 => -14  | 541 => -30
  | 547 =>   8  | 557 =>  12  | 563 =>  18  | 569 => -32
  | 571 =>  40  | 577 =>  31  | 587 => -12  | 593 =>  24
  | 599 =>  24  | 601 => -22  | 607 => -22  | 613 =>  -2
  | 617 =>  42  | 619 =>  -7  | 631 => -27  | 641 => -33
  | 643 => -49  | 647 => -15  | 653 => -13  | 659 => -44
  | 661 =>  31  | 673 =>   4  | 677 =>   6  | 683 =>  -4
  | 691 => -45  | 701 => -10  | 709 => -35  | 719 => -41
  | 727 =>  19  | 733 => -46  | 739 =>  -2  | 743 =>  42
  | 751 => -39  | 757 =>  30  | 761 => -34  | 769 =>   0
  | 773 =>  30  | 787 =>  12  | 797 =>  17  | 809 =>  24
  | 811 => -36  | 821 =>   0  | 823 => -29  | 827 =>  50
  | 829 =>  29  | 839 =>  53  | 853 => -50  | 857 => -32
  | 859 =>  13  | 863 =>  48  | 877 =>  38  | 881 =>  33
  | 883 =>  28  | 887 =>  12  | 907 =>  52  | 911 =>  -8
  | 919 =>  40  | 929 => -42  | 937 => -12  | 941 => -36
  | 947 =>  -9  | 953 => -30  | 967 =>  28  | 971 => -49
  | 977 =>  -9  | 983 => -31  | 991 =>  32  | 997 => -18
  | _   =>   0

-- ============================================================
-- All 168 rfl theorems (close by kernel reduction, no decide)
-- ============================================================

theorem ap_2   : ap 2   =   0 := rfl
theorem ap_3   : ap 3   =  -1 := rfl
theorem ap_5   : ap 5   =  -1 := rfl
theorem ap_7   : ap 7   =  -2 := rfl
theorem ap_11  : ap 11  =  -1 := rfl
theorem ap_13  : ap 13  =  -1 := rfl
theorem ap_17  : ap 17  =  -4 := rfl
theorem ap_19  : ap 19  =   2 := rfl
theorem ap_23  : ap 23  =   7 := rfl
theorem ap_29  : ap 29  =  -2 := rfl
theorem ap_31  : ap 31  =  -3 := rfl
theorem ap_37  : ap 37  = -11 := rfl
theorem ap_41  : ap 41  =  10 := rfl
theorem ap_43  : ap 43  =  -4 := rfl
theorem ap_47  : ap 47  =  -4 := rfl
theorem ap_53  : ap 53  =   2 := rfl
theorem ap_59  : ap 59  =  -1 := rfl
theorem ap_61  : ap 61  =  -2 := rfl
theorem ap_67  : ap 67  =  -1 := rfl
theorem ap_71  : ap 71  =  -9 := rfl
theorem ap_73  : ap 73  = -16 := rfl
theorem ap_79  : ap 79  =   8 := rfl
theorem ap_83  : ap 83  =   0 := rfl
theorem ap_89  : ap 89  =  -7 := rfl
theorem ap_97  : ap 97  = -13 := rfl
theorem ap_101 : ap 101 =  18 := rfl
theorem ap_103 : ap 103 =   8 := rfl
theorem ap_107 : ap 107 =   8 := rfl
theorem ap_109 : ap 109 =   4 := rfl
theorem ap_113 : ap 113 =   1 := rfl
theorem ap_127 : ap 127 =  -8 := rfl
theorem ap_131 : ap 131 =  18 := rfl
theorem ap_137 : ap 137 = -17 := rfl
theorem ap_139 : ap 139 =  18 := rfl
theorem ap_149 : ap 149 =  14 := rfl
theorem ap_151 : ap 151 =   4 := rfl
theorem ap_157 : ap 157 =   5 := rfl
theorem ap_163 : ap 163 =  -4 := rfl
theorem ap_167 : ap 167 =   4 := rfl
theorem ap_173 : ap 173 =  -8 := rfl
theorem ap_179 : ap 179 = -15 := rfl
theorem ap_181 : ap 181 =   7 := rfl
theorem ap_191 : ap 191 = -15 := rfl
theorem ap_193 : ap 193 = -24 := rfl
theorem ap_197 : ap 197 = -10 := rfl
theorem ap_199 : ap 199 =  -4 := rfl
theorem ap_211 : ap 211 = -24 := rfl
theorem ap_223 : ap 223 =   5 := rfl
theorem ap_227 : ap 227 =   0 := rfl
theorem ap_229 : ap 229 =   9 := rfl
theorem ap_233 : ap 233 = -16 := rfl
theorem ap_239 : ap 239 = -30 := rfl
theorem ap_241 : ap 241 = -10 := rfl
theorem ap_251 : ap 251 =  21 := rfl
theorem ap_257 : ap 257 =  18 := rfl
theorem ap_263 : ap 263 = -18 := rfl
theorem ap_269 : ap 269 = -30 := rfl
theorem ap_271 : ap 271 =  28 := rfl
theorem ap_277 : ap 277 =  26 := rfl
theorem ap_281 : ap 281 =  18 := rfl
theorem ap_283 : ap 283 = -30 := rfl
theorem ap_293 : ap 293 =  14 := rfl
theorem ap_307 : ap 307 =   0 := rfl
theorem ap_311 : ap 311 =   8 := rfl
theorem ap_313 : ap 313 =   3 := rfl
theorem ap_317 : ap 317 =  -1 := rfl
theorem ap_331 : ap 331 = -11 := rfl
theorem ap_337 : ap 337 = -20 := rfl
theorem ap_347 : ap 347 =  18 := rfl
theorem ap_349 : ap 349 =  16 := rfl
theorem ap_353 : ap 353 = -15 := rfl
theorem ap_359 : ap 359 =  22 := rfl
theorem ap_367 : ap 367 =   3 := rfl
theorem ap_373 : ap 373 =  26 := rfl
theorem ap_379 : ap 379 = -11 := rfl
theorem ap_383 : ap 383 = -19 := rfl
theorem ap_389 : ap 389 =   9 := rfl
theorem ap_397 : ap 397 = -18 := rfl
theorem ap_401 : ap 401 = -18 := rfl
theorem ap_409 : ap 409 = -18 := rfl
theorem ap_419 : ap 419 = -28 := rfl
theorem ap_421 : ap 421 = -22 := rfl
theorem ap_431 : ap 431 = -40 := rfl
theorem ap_433 : ap 433 =  33 := rfl
theorem ap_439 : ap 439 =   6 := rfl
theorem ap_443 : ap 443 = -23 := rfl
theorem ap_449 : ap 449 =  21 := rfl
theorem ap_457 : ap 457 = -16 := rfl
theorem ap_461 : ap 461 =  10 := rfl
theorem ap_463 : ap 463 =  -9 := rfl
theorem ap_467 : ap 467 = -23 := rfl
theorem ap_479 : ap 479 =  36 := rfl
theorem ap_487 : ap 487 =  25 := rfl
theorem ap_491 : ap 491 =  12 := rfl
theorem ap_499 : ap 499 =  28 := rfl
theorem ap_503 : ap 503 =  30 := rfl
theorem ap_509 : ap 509 =   9 := rfl
theorem ap_521 : ap 521 =   5 := rfl
theorem ap_523 : ap 523 = -14 := rfl
theorem ap_541 : ap 541 = -30 := rfl
theorem ap_547 : ap 547 =   8 := rfl
theorem ap_557 : ap 557 =  12 := rfl
theorem ap_563 : ap 563 =  18 := rfl
theorem ap_569 : ap 569 = -32 := rfl
theorem ap_571 : ap 571 =  40 := rfl
theorem ap_577 : ap 577 =  31 := rfl
theorem ap_587 : ap 587 = -12 := rfl
theorem ap_593 : ap 593 =  24 := rfl
theorem ap_599 : ap 599 =  24 := rfl
theorem ap_601 : ap 601 = -22 := rfl
theorem ap_607 : ap 607 = -22 := rfl
theorem ap_613 : ap 613 =  -2 := rfl
theorem ap_617 : ap 617 =  42 := rfl
theorem ap_619 : ap 619 =  -7 := rfl
theorem ap_631 : ap 631 = -27 := rfl
theorem ap_641 : ap 641 = -33 := rfl
theorem ap_643 : ap 643 = -49 := rfl
theorem ap_647 : ap 647 = -15 := rfl
theorem ap_653 : ap 653 = -13 := rfl
theorem ap_659 : ap 659 = -44 := rfl
theorem ap_661 : ap 661 =  31 := rfl
theorem ap_673 : ap 673 =   4 := rfl
theorem ap_677 : ap 677 =   6 := rfl
theorem ap_683 : ap 683 =  -4 := rfl
theorem ap_691 : ap 691 = -45 := rfl
theorem ap_701 : ap 701 = -10 := rfl
theorem ap_709 : ap 709 = -35 := rfl
theorem ap_719 : ap 719 = -41 := rfl
theorem ap_727 : ap 727 =  19 := rfl
theorem ap_733 : ap 733 = -46 := rfl
theorem ap_739 : ap 739 =  -2 := rfl
theorem ap_743 : ap 743 =  42 := rfl
theorem ap_751 : ap 751 = -39 := rfl
theorem ap_757 : ap 757 =  30 := rfl
theorem ap_761 : ap 761 = -34 := rfl
theorem ap_769 : ap 769 =   0 := rfl
theorem ap_773 : ap 773 =  30 := rfl
theorem ap_787 : ap 787 =  12 := rfl
theorem ap_797 : ap 797 =  17 := rfl
theorem ap_809 : ap 809 =  24 := rfl
theorem ap_811 : ap 811 = -36 := rfl
theorem ap_821 : ap 821 =   0 := rfl
theorem ap_823 : ap 823 = -29 := rfl
theorem ap_827 : ap 827 =  50 := rfl
theorem ap_829 : ap 829 =  29 := rfl
theorem ap_839 : ap 839 =  53 := rfl
theorem ap_853 : ap 853 = -50 := rfl
theorem ap_857 : ap 857 = -32 := rfl
theorem ap_859 : ap 859 =  13 := rfl
theorem ap_863 : ap 863 =  48 := rfl
theorem ap_877 : ap 877 =  38 := rfl
theorem ap_881 : ap 881 =  33 := rfl
theorem ap_883 : ap 883 =  28 := rfl
theorem ap_887 : ap 887 =  12 := rfl
theorem ap_907 : ap 907 =  52 := rfl
theorem ap_911 : ap 911 =  -8 := rfl
theorem ap_919 : ap 919 =  40 := rfl
theorem ap_929 : ap 929 = -42 := rfl
theorem ap_937 : ap 937 = -12 := rfl
theorem ap_941 : ap 941 = -36 := rfl
theorem ap_947 : ap 947 =  -9 := rfl
theorem ap_953 : ap 953 = -30 := rfl
theorem ap_967 : ap 967 =  28 := rfl
theorem ap_971 : ap 971 = -49 := rfl
theorem ap_977 : ap 977 =  -9 := rfl
theorem ap_983 : ap 983 = -31 := rfl
theorem ap_991 : ap 991 =  32 := rfl
theorem ap_997 : ap 997 = -18 := rfl

end E1859

/-
================================================================
Towers / BSD / BSD_HasseBridge_CLOSED  (genesis-734)

**Option A + B: Unconditional Hasse bounds for p ∈ {2,3,5,7} via the
§V.5 discriminant route, plus the ap = a_p compatibility bridge.**

### What is proved here (0 sorry, classical trio)

For each prime p ∈ {2, 3, 5, 7} (all good reduction for 143a1):

**Option A — §V.5 unconditional BSD_Hasse_OPEN:**

  Step 1. `BSD_E143_card_pN`   — `(E143_Finset p).card = k`
          Proved by `decide` over `ZMod p × ZMod p` (finite, computable;
          `E143_point_decidable` instance exists in BSD_LFunction.lean).
          Weierstrass model: y*y + y = x*x*x - x*x - x - 2.

  Step 2. `BSD_ap_pN`          — `a_p p = c`  (exact integer value)
          Proved by `unfold a_p; omega` using the card count.

  Step 3. `BSD_DegreeNonneg_pN` — `BSD_FrobeniusDegreeNonneg_OPEN p`
          Proved by `nlinarith` after substituting the exact a_p value.
          Discriminant < 0 for all four primes ⟹ always non-negative:
            p=2: r²+2 ≥ 0            (witness: sq_nonneg r)
            p=3: r²+r+3 = (2r+1)²/4+11/4 ≥ 0  (witness: sq_nonneg (2r+1))
            p=5: r²+r+5 ≥ 0          (same witness)
            p=7: r²+2r+7 = (r+1)²+6 ≥ 0 (witness: sq_nonneg (r+1))

  Step 4. `BSD_Hasse_OPEN_pN`  — `BSD_Hasse_OPEN p`
          Proved unconditionally via `BSD_hasse_of_degree_nonneg`
          (the algebraic bridge from §V.5 skeleton, genesis-733).

**Option B — ap = a_p compatibility bridge:**

  `BSD_ApCompat_pN` — `E1859.ap p = a_p p`
  Proves the trace-table (LMFDB-backed `ap`) equals the geometric count
  (`a_p := p − #E₁₄₃_affine(𝔽_p)`) for each prime.
  Follows immediately from Steps 1+2 + the pattern-match rfl in E1859.

### Key point counts (verified by decide)
  p=2: affine points = {(0,0),(0,1)},  card=2,  a_p=0
  p=3: affine points = 4,              card=4,  a_p=−1
  p=5: affine points = 6,              card=6,  a_p=−1
  p=7: affine points = 9,              card=9,  a_p=−2

### Honest scope
  - BSD_HasseFull_143_OPEN remains OPEN: this file covers only 4 of the
    infinitely many good primes. The high-prime branch still needs
    BSD_FrobeniusDegreeNonneg_OPEN as a general statement
    (EllipticCurve.Frobenius API absent from Mathlib v4.12.0).
  - NOT a brick; NOT registered in BRICKS[]. No Clay claim.
  - Named OPEN surfaces: 7 (unchanged from genesis-733).

Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
================================================================
-/

import Towers.BSD.BSD_Frobenius_Certificate

namespace Towers.BSD

/-! ## Fact p.Prime instances for our four concrete primes -/

private instance instFactPrime2 : Fact (2 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime3 : Fact (3 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime5 : Fact (5 : ℕ).Prime := ⟨by norm_num⟩
private instance instFactPrime7 : Fact (7 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §1. Point counts over 𝔽_p  (by decide) -/

/-- **`BSD_E143_card_p2`** — 143a1 has exactly **2 affine 𝔽₂-points**.
    The two solutions are (0,0) and (0,1): y²+y=0 has y∈{0,1} in 𝔽₂,
    while x=1 gives y²+y=1 which has no solution. Computed by `decide`
    over the full `ZMod 2 × ZMod 2` (4 pairs). -/
theorem BSD_E143_card_p2 : (E143_Finset 2).card = 2 := by decide

/-- **`BSD_E143_card_p3`** — 143a1 has exactly **4 affine 𝔽₃-points**.
    x=0 gives 0 solutions; x=1,2 each give 2 solutions (y=0,2 in 𝔽₃).
    Computed by `decide` over ZMod 3 × ZMod 3 (9 pairs). -/
theorem BSD_E143_card_p3 : (E143_Finset 3).card = 4 := by decide

/-- **`BSD_E143_card_p5`** — 143a1 has exactly **6 affine 𝔽₅-points**.
    Computed by `decide` over ZMod 5 × ZMod 5 (25 pairs). -/
theorem BSD_E143_card_p5 : (E143_Finset 5).card = 6 := by decide

/-- **`BSD_E143_card_p7`** — 143a1 has exactly **9 affine 𝔽₇-points**.
    Computed by `decide` over ZMod 7 × ZMod 7 (49 pairs). -/
theorem BSD_E143_card_p7 : (E143_Finset 7).card = 9 := by decide

/-! ## §2. Exact a_p values -/

/-- **`BSD_ap_p2`** — `a_p 2 = 0`.  Follows from `a_p 2 = 2 − card = 2 − 2 = 0`. -/
theorem BSD_ap_p2 : a_p 2 = (0 : ℤ) := by
  have h := BSD_E143_card_p2
  unfold a_p; omega

/-- **`BSD_ap_p3`** — `a_p 3 = −1`.  Follows from `a_p 3 = 3 − 4 = −1`. -/
theorem BSD_ap_p3 : a_p 3 = (-1 : ℤ) := by
  have h := BSD_E143_card_p3
  unfold a_p; omega

/-- **`BSD_ap_p5`** — `a_p 5 = −1`.  Follows from `a_p 5 = 5 − 6 = −1`. -/
theorem BSD_ap_p5 : a_p 5 = (-1 : ℤ) := by
  have h := BSD_E143_card_p5
  unfold a_p; omega

/-- **`BSD_ap_p7`** — `a_p 7 = −2`.  Follows from `a_p 7 = 7 − 9 = −2`. -/
theorem BSD_ap_p7 : a_p 7 = (-2 : ℤ) := by
  have h := BSD_E143_card_p7
  unfold a_p; omega

/-! ## §3. Degree non-negativity — BSD_FrobeniusDegreeNonneg_OPEN p

For each prime, `BSD_FrobeniusDegreeNonneg_OPEN p = ∀ r:ℝ, r²−(a_p p:ℝ)·r+(p:ℝ) ≥ 0`.
The `key` lemma restates the quadratic (keeping the **same atoms** as the goal —
no `rw` in the goal, so `(a_p p:ℝ)` and the ℕ-cast `↑p` remain) as a completed
square plus a positive remainder; `linarith [sq_nonneg ...]` then closes the goal.
Inside the `key` proof we substitute `hap` and use `push_cast; ring` to normalise. -/

/-- **`BSD_DegreeNonneg_p2`** — `BSD_FrobeniusDegreeNonneg_OPEN 2`.
    Completed square: r²+2 = r²+2 ≥ 0.  Witness: `sq_nonneg r`. -/
theorem BSD_DegreeNonneg_p2 : BSD_FrobeniusDegreeNonneg_OPEN 2 := fun r => by
  have hap : (a_p 2 : ℝ) = 0 := by exact_mod_cast BSD_ap_p2
  have key : r ^ 2 - (a_p 2 : ℝ) * r + ((2 : ℕ) : ℝ) = r ^ 2 + 2 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg r]

/-- **`BSD_DegreeNonneg_p3`** — `BSD_FrobeniusDegreeNonneg_OPEN 3`.
    Completed square: r²+r+3 = (r+½)²+11/4.  Discriminant = −11 < 0. -/
theorem BSD_DegreeNonneg_p3 : BSD_FrobeniusDegreeNonneg_OPEN 3 := fun r => by
  have hap : (a_p 3 : ℝ) = -1 := by exact_mod_cast BSD_ap_p3
  have key : r ^ 2 - (a_p 3 : ℝ) * r + ((3 : ℕ) : ℝ) = (r + 1 / 2) ^ 2 + 11 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1 / 2)]

/-- **`BSD_DegreeNonneg_p5`** — `BSD_FrobeniusDegreeNonneg_OPEN 5`.
    Completed square: r²+r+5 = (r+½)²+19/4.  Discriminant = −19 < 0. -/
theorem BSD_DegreeNonneg_p5 : BSD_FrobeniusDegreeNonneg_OPEN 5 := fun r => by
  have hap : (a_p 5 : ℝ) = -1 := by exact_mod_cast BSD_ap_p5
  have key : r ^ 2 - (a_p 5 : ℝ) * r + ((5 : ℕ) : ℝ) = (r + 1 / 2) ^ 2 + 19 / 4 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1 / 2)]

/-- **`BSD_DegreeNonneg_p7`** — `BSD_FrobeniusDegreeNonneg_OPEN 7`.
    Completed square: r²+2r+7 = (r+1)²+6.  Discriminant = −24 < 0. -/
theorem BSD_DegreeNonneg_p7 : BSD_FrobeniusDegreeNonneg_OPEN 7 := fun r => by
  have hap : (a_p 7 : ℝ) = -2 := by exact_mod_cast BSD_ap_p7
  have key : r ^ 2 - (a_p 7 : ℝ) * r + ((7 : ℕ) : ℝ) = (r + 1) ^ 2 + 6 := by
    rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1)]

/-! ## §4. BSD_Hasse_OPEN — unconditional, via §V.5 bridge

Each `BSD_Hasse_OPEN_pN` is proved by applying `BSD_hasse_of_degree_nonneg`
(genesis-733, §V.5 skeleton) to the degree non-negativity from §3.
This is the first use of the §V.5 algebraic bridge on concrete primes. -/

/-- **`BSD_Hasse_OPEN_p2`** — `BSD_Hasse_OPEN 2`: |a₂(E₁₄₃)| ≤ 2√2.
    UNCONDITIONAL, 0 sorry, classical trio. Route: decide → omega → nlinarith
    → BSD_hasse_of_degree_nonneg. No EllipticCurve.Frobenius API needed. -/
theorem BSD_Hasse_OPEN_p2 : BSD_Hasse_OPEN 2 :=
  BSD_hasse_of_degree_nonneg 2 BSD_DegreeNonneg_p2

/-- **`BSD_Hasse_OPEN_p3`** — `BSD_Hasse_OPEN 3`: |a₃(E₁₄₃)| ≤ 2√3.
    UNCONDITIONAL, 0 sorry, classical trio. -/
theorem BSD_Hasse_OPEN_p3 : BSD_Hasse_OPEN 3 :=
  BSD_hasse_of_degree_nonneg 3 BSD_DegreeNonneg_p3

/-- **`BSD_Hasse_OPEN_p5`** — `BSD_Hasse_OPEN 5`: |a₅(E₁₄₃)| ≤ 2√5.
    UNCONDITIONAL, 0 sorry, classical trio. -/
theorem BSD_Hasse_OPEN_p5 : BSD_Hasse_OPEN 5 :=
  BSD_hasse_of_degree_nonneg 5 BSD_DegreeNonneg_p5

/-- **`BSD_Hasse_OPEN_p7`** — `BSD_Hasse_OPEN 7`: |a₇(E₁₄₃)| ≤ 2√7.
    UNCONDITIONAL, 0 sorry, classical trio. -/
theorem BSD_Hasse_OPEN_p7 : BSD_Hasse_OPEN 7 :=
  BSD_hasse_of_degree_nonneg 7 BSD_DegreeNonneg_p7

/-! ## §5. Compatibility bridge — ap = a_p  (Option B)

The LMFDB trace table `E1859.ap` and the geometric count `a_p` agree
for each of the four primes.  Proved by combining the table's `rfl`
pattern-match value with the geometric value from §2. -/

/-- **`BSD_ApCompat_p2`** — `E1859.ap 2 = a_p 2`.
    `E1859.ap 2 = 0` by the pattern-match table (rfl); `a_p 2 = 0` by §2. -/
theorem BSD_ApCompat_p2 : E1859.ap 2 = a_p 2 :=
  (show E1859.ap 2 = (0 : ℤ) from rfl).trans BSD_ap_p2.symm

/-- **`BSD_ApCompat_p3`** — `E1859.ap 3 = a_p 3`.
    `E1859.ap 3 = −1` by the pattern-match table (rfl); `a_p 3 = −1` by §2. -/
theorem BSD_ApCompat_p3 : E1859.ap 3 = a_p 3 :=
  (show E1859.ap 3 = (-1 : ℤ) from rfl).trans BSD_ap_p3.symm

/-- **`BSD_ApCompat_p5`** — `E1859.ap 5 = a_p 5`.
    `E1859.ap 5 = −1` by the pattern-match table (rfl); `a_p 5 = −1` by §2. -/
theorem BSD_ApCompat_p5 : E1859.ap 5 = a_p 5 :=
  (show E1859.ap 5 = (-1 : ℤ) from rfl).trans BSD_ap_p5.symm

/-- **`BSD_ApCompat_p7`** — `E1859.ap 7 = a_p 7`.
    `E1859.ap 7 = −2` by the pattern-match table (rfl); `a_p 7 = −2` by §2. -/
theorem BSD_ApCompat_p7 : E1859.ap 7 = a_p 7 :=
  (show E1859.ap 7 = (-2 : ℤ) from rfl).trans BSD_ap_p7.symm

end Towers.BSD

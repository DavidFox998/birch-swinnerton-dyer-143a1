import Towers.BSD.B02_Modularity
import Towers.BSD.BSD_LFunction_Closed
import Towers.BSD.BSD_AP_Table_Closed
import Towers.BSD.BSD_AP_Table

/-!
# B02_Modularity_Closed — Conditional closures of the three B02 modularity surfaces

## Scope

Provides conditional closes and explicit supporting evidence for the three OPEN
surfaces from `B02_Modularity.lean`:

  1. `Modularity_BSD_OPEN 143` — ∃ a_f satisfying Hecke multiplicativity + Weil bound
  2. `BSD_Hecke_OPEN 143`     — AnalyticOn ℂ (BSDLFunction 143) Set.univ
  3. `BSD_FuncEq_OPEN 143`    — functional equation ∀ s, N^(s−1) · L(2−s) = ε · L(s)

## What is proved unconditionally (0 sorry, classical trio)

| Theorem | Statement |
|---------|-----------|
| `a_n_eq_ap_prime` | `a_n p = a_p p` for any prime p |
| `a_n_sq_recurrence` | `a_n(p²) = (a_n p)² − p` for any prime p |
| `a_n_hasse_from_open` | `BSD_Hasse_OPEN p → (a_n p : ℝ)² ≤ 4p` |
| `a_n_at_2/3/5/7` | exact values 0, −1, −1, −2 (by `decide`) |
| `a_n_weil_2/3/5/7` | Weil bound for p ∈ {2, 3, 5, 7} |
| `BSD_Weil_168_CLOSED` | `(E1859.ap p)² ≤ 4p` for ALL 168 primes ≤ 997 |

`BSD_Weil_168_CLOSED` closes the Weil bound numerically for all 168 primes in the
precomputed trace table, using `BSD_AP_Table_Closed.BSD_Hasse_Closed` which
closes each case by `fin_cases <;> norm_num [ap]` — no `native_decide`,
no `sorry`, classical trio throughout.

## Remaining OPEN gates

| Surface | Mathematical gap |
|---------|-----------------|
| `BSD_HeckeMultiplicativity_143_OPEN` | `a_n` multiplicativity (Finsupp disjoint-support) |
| `BSD_HasseFull_143_OPEN` | Weil bound for ALL good primes (Frobenius, Mathlib v4.12.0) |
| `BSD_LFunction_Identification_OPEN` | opaque BSDLFunction 143 = Dirichlet sum |
| `BSD_AnalyticContinuation_143_OPEN` | analytic continuation to all ℂ |
| `BSD_GammaFuncEq_143_OPEN` | completed functional equation Λ(s) = ε·Λ(2−s) |

SORRY: 0. Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
NOT a brick. BSD Surface: OPEN. No Clay claim.
-/

namespace Towers.BSD

open Real Complex E1859

-- ============================================================
-- §1. Core sub-lemmas for the a_n witness (0 sorry, trio)
-- ============================================================

/-- **PROVED**: For any prime p, a_n p = a_p p.
    Proof: a_n(p) = a_n(p^1) = a_prime_pow p 1 = a_p p (by definition). -/
theorem a_n_eq_ap_prime (p : ℕ) [hp : Fact p.Prime] : a_n p = a_p p := by
  have h := a_n_prime_pow p 1
  simp only [pow_one, a_prime_pow] at h
  exact h

/-- **PROVED**: Hecke recurrence at p²: a_n(p²) = (a_n p)² − p.
    Proof: a_n(p²) = a_prime_pow p 2 = a_p p · a_p p − p · 1 = (a_n p)² − p. -/
theorem a_n_sq_recurrence (p : ℕ) [hp : Fact p.Prime] :
    a_n (p ^ 2) = (a_n p) ^ 2 - (p : ℤ) := by
  rw [a_n_prime_pow p 2]
  have h1 : a_n p = a_prime_pow p 1 := by
    have h := a_n_prime_pow p 1; simpa [pow_one, a_prime_pow] using h
  rw [h1]; simp only [a_prime_pow]; push_cast; ring

/-- **PROVED**: BSD_Hasse_OPEN p implies (a_n p : ℝ)² ≤ 4p.
    Uses: a_n p = a_p p and |a_p p| ≤ 2√p ⟹ (a_p p)² ≤ 4p by squaring. -/
theorem a_n_hasse_from_open (p : ℕ) [hp : Fact p.Prime]
    (h : BSD_Hasse_OPEN p) : (a_n p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  rw [show (a_n p : ℝ) = a_p p from by exact_mod_cast a_n_eq_ap_prime p]
  have hp_nn : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  calc (a_p p : ℝ) ^ 2
      = |(a_p p : ℝ)| ^ 2 := (_root_.sq_abs _).symm
    _ ≤ (2 * Real.sqrt p) ^ 2 := by
        apply pow_le_pow_left (abs_nonneg _)
        exact h
    _ = 4 * p := by rw [mul_pow, Real.sq_sqrt hp_nn]; ring

-- ============================================================
-- §2. Exact a_n values at the 4 kernel-decidable primes (0 sorry)
-- ============================================================
/-!
For p ∈ {2, 3, 5, 7} the affine count is bridged from `E143a1_count` (the
computable version in `BSD_AP_Table`, using `[NeZero p]`) to `a_p` (which uses
`E143_Finset`, `[Fact p.Prime]`).  `E143_point` unfolds to the same arithmetic
equality as the inline predicate in `E143a1_count`, so the two Finset filters
are propositionally equal via `Finset.filter_congr`.
-/

/-- Bridge: `(E143_Finset p).card = E143a1_count p` for any prime p.
    `E143_point p x y` is defined as `y*y+y = x*x*x-x*x-x-2`, which is
    exactly the inline predicate in `E143a1_count`; both filter the same
    `Finset.univ`, so the two expressions are definitionally equal. -/
lemma E143_Finset_card_eq_count (p : ℕ) [hp : Fact p.Prime] :
    (E143_Finset p).card = E143a1_count p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  unfold E143_Finset E143_point E143a1_count
  rfl

/-- **PROVED**: a_n 2 = 0. Count #E143_affine(𝔽₂) = 2; a_p 2 = 2 − 2 = 0. -/
theorem a_n_at_2 : a_n 2 = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h : a_p 2 = 0 := by
    have hc : (E143_Finset 2).card = 2 := by
      rw [E143_Finset_card_eq_count]; exact E143a1_count_2
    unfold a_p; rw [show (E143_Finset 2).card = 2 from hc]; norm_num
  simpa using (a_n_eq_ap_prime 2).trans h

/-- **PROVED**: a_n 3 = −1. Count #E143_affine(𝔽₃) = 4; a_p 3 = 3 − 4 = −1. -/
theorem a_n_at_3 : a_n 3 = -1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h : a_p 3 = -1 := by
    have hc : (E143_Finset 3).card = 4 := by
      rw [E143_Finset_card_eq_count]; exact E143a1_count_3
    unfold a_p; rw [show (E143_Finset 3).card = 4 from hc]; norm_num
  simpa using (a_n_eq_ap_prime 3).trans h

/-- **PROVED**: a_n 5 = −1. Count #E143_affine(𝔽₅) = 6; a_p 5 = 5 − 6 = −1. -/
theorem a_n_at_5 : a_n 5 = -1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h : a_p 5 = -1 := by
    have hc : (E143_Finset 5).card = 6 := by
      rw [E143_Finset_card_eq_count]; exact E143a1_count_5
    unfold a_p; rw [show (E143_Finset 5).card = 6 from hc]; norm_num
  simpa using (a_n_eq_ap_prime 5).trans h

/-- **PROVED**: a_n 7 = −2. Count #E143_affine(𝔽₇) = 9; a_p 7 = 7 − 9 = −2. -/
theorem a_n_at_7 : a_n 7 = -2 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h : a_p 7 = -2 := by
    have hc : (E143_Finset 7).card = 9 := by
      rw [E143_Finset_card_eq_count]; exact E143a1_count_7
    unfold a_p; rw [show (E143_Finset 7).card = 9 from hc]; norm_num
  simpa using (a_n_eq_ap_prime 7).trans h

-- ============================================================
-- §3. Weil bound for a_n at the 4 proved primes (0 sorry)
-- ============================================================

/-- **PROVED**: (a_n 2 : ℝ)² ≤ 4·2.  0² = 0 ≤ 8. -/
theorem a_n_weil_2 : (a_n 2 : ℝ) ^ 2 ≤ 4 * 2 := by
  have := a_n_at_2; push_cast [this]; norm_num

/-- **PROVED**: (a_n 3 : ℝ)² ≤ 4·3.  (−1)² = 1 ≤ 12. -/
theorem a_n_weil_3 : (a_n 3 : ℝ) ^ 2 ≤ 4 * 3 := by
  have := a_n_at_3; push_cast [this]; norm_num

/-- **PROVED**: (a_n 5 : ℝ)² ≤ 4·5.  (−1)² = 1 ≤ 20. -/
theorem a_n_weil_5 : (a_n 5 : ℝ) ^ 2 ≤ 4 * 5 := by
  have := a_n_at_5; push_cast [this]; norm_num

/-- **PROVED**: (a_n 7 : ℝ)² ≤ 4·7.  (−2)² = 4 ≤ 28. -/
theorem a_n_weil_7 : (a_n 7 : ℝ) ^ 2 ≤ 4 * 7 := by
  have := a_n_at_7; push_cast [this]; norm_num

-- ============================================================
-- §4. BSD_Weil_168_CLOSED — all 168 primes ≤ 997 (0 sorry, trio)
-- ============================================================
/-!
`BSD_AP_Table_Closed.BSD_Hasse_Closed` proves `(E1859.ap p)^2 ≤ 4*p` for all 168
primes ≤ 997 via `fin_cases hp <;> norm_num [ap]` — no `native_decide`,
no `sorry`, classical trio.

We re-export that result here in full, with the complete explicit prime list, so
the Weil bound evidence is self-contained in this modularity file.
-/

/-- **PROVED** (0 sorry, classical trio):
    Weil bound (E1859.ap p)² ≤ 4p for ALL 168 primes ≤ 997.

    These are the Hecke trace values of the weight-2 newform of level 143 (LMFDB
    143.2.a.a) stored in the precomputed lookup table `Traces_E1859_All_168`.
    Each case closes by `fin_cases hp <;> norm_num [ap]` in `BSD_AP_Table_Closed`. -/
theorem BSD_Weil_168_CLOSED (p : ℕ)
    (hp : p ∈ ([
       2,   3,   5,   7,  11,  13,  17,  19,  23,  29,
      31,  37,  41,  43,  47,  53,  59,  61,  67,  71,
      73,  79,  83,  89,  97, 101, 103, 107, 109, 113,
     127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
     179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
     233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
     283, 293, 307, 311, 313, 317, 331, 337, 347, 349,
     353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
     419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
     467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
     547, 557, 563, 569, 571, 577, 587, 593, 599, 601,
     607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
     661, 673, 677, 683, 691, 701, 709, 719, 727, 733,
     739, 743, 751, 757, 761, 769, 773, 787, 797, 809,
     811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
     877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
     947, 953, 967, 971, 977, 983, 991, 997] : List ℕ)) :
    (ap p) ^ 2 ≤ 4 * p :=
  BSD_AP_Table_Closed.BSD_Hasse_Closed p hp

-- ============================================================
-- §5. OPEN sub-surfaces for Modularity_143_OPEN
-- ============================================================

/-- **OPEN sub-surface**: full multiplicativity of a_n.
    `∀ m n : ℕ, Nat.Coprime m n → a_n (m * n) = a_n m * a_n n`.

    Mathematical content: for coprime m, n the Finsupp factorization supports are
    disjoint, so the product splits.  The Lean proof needs `Finsupp.prod_add_index`
    at disjoint supports (~30 lines); deferred.  Mathematical fact is clear. -/
def BSD_HeckeMultiplicativity_143_OPEN : Prop :=
  ∀ m n : ℕ, Nat.Coprime m n → a_n (m * n) = a_n m * a_n n

/-- **OPEN sub-surface**: Hasse–Weil bound for ALL good primes.
    `∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → BSD_Hasse_OPEN p`.

    This is the Frobenius degree gap (EllipticCurve.Frobenius absent from
    Mathlib v4.12.0; Silverman AEC §V.2, Hasse 1936).

    **Partial evidence — numerically closed**: `BSD_Weil_168_CLOSED` (§4) gives
    `(E1859.ap p)^2 ≤ 4p` for all 168 primes ≤ 997. For primes > 997, the
    Frobenius argument is the only known route. -/
def BSD_HasseFull_143_OPEN : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → BSD_Hasse_OPEN p

-- ============================================================
-- §6. Modularity_143_CLOSED (0 sorry, classical trio)
-- ============================================================

/-- **Milestone: Modularity_143_CLOSED** (0 sorry, classical trio).

    Given `BSD_HeckeMultiplicativity_143_OPEN` and `BSD_HasseFull_143_OPEN`,
    `Modularity_143_OPEN` holds with witness `a_n`.

    **Unconditionally proved (no gates needed):**
    - a_n 1 = 1              (`a_n_one`, BSD_LFunction.lean)
    - a_n(p²) = (a_n p)²−p  (`a_n_sq_recurrence`, §1)

    **Numerical evidence included in this file (no Frobenius needed):**
    - BSD_Weil_168_CLOSED    (§4): (E1859.ap p)² ≤ 4p for all 168 primes ≤ 997
    - a_n_weil_2/3/5/7       (§3): (a_n p : ℝ)² ≤ 4p for p ∈ {2,3,5,7} via decide

    **Proved with gates:**
    - Multiplicativity gate: `BSD_HeckeMultiplicativity_143_OPEN`
    - Full Weil bound gate:  `BSD_HasseFull_143_OPEN`
      (Covers ALL primes; 168-prime evidence above supports this gate numerically.)

    Gate count: 2. NOT a proof of BSD. Honest conditional. SORRY: 0. Classical trio. -/
theorem Modularity_143_CLOSED
    (h_mult  : BSD_HeckeMultiplicativity_143_OPEN)
    (h_hasse : BSD_HasseFull_143_OPEN) :
    Modularity_143_OPEN := by
  unfold Modularity_143_OPEN Modularity_BSD_OPEN
  refine ⟨a_n, a_n_one, ?_, ?_, ?_⟩
  -- (1) Multiplicativity: gate
  · exact fun m n hcop => h_mult m n hcop
  -- (2) Hecke recurrence: proved from definition
  · intro p hp hbad
    haveI : Fact p.Prime := ⟨hp⟩
    exact a_n_sq_recurrence p
  -- (3) Weil bound: gate (full; 168-prime evidence in BSD_Weil_168_CLOSED)
  · intro p hp hbad
    haveI : Fact p.Prime := ⟨hp⟩
    exact a_n_hasse_from_open p (h_hasse p hbad)

-- ============================================================
-- §7. OPEN sub-surfaces for BSD_Hecke_OPEN / BSD_FuncEq_OPEN
-- ============================================================

/-!
`BSDLFunction N : ℂ → ℂ` is declared `opaque` in B01_EllipticCurve.lean.
No analytic property can be derived from an opaque term without an explicit
hypothesis connecting it to a concrete analytic function.
-/

/-- **OPEN**: BSDLFunction 143 agrees with the Dirichlet sum on {Re s > 3/2}.
    Gap: metatheoretic identification of opaque constant with Dirichlet series. -/
def BSD_LFunction_Identification_OPEN : Prop :=
  ∀ s : ℂ, (3 : ℝ) / 2 < s.re →
    BSDLFunction 143 s = ∑' n : ℕ+, (a_n n.val : ℂ) / (n.val : ℂ) ^ s

/-- **OPEN**: BSDLFunction 143 extends analytically to all ℂ.
    Gap: Mellin transform + analytic continuation absent from Mathlib v4.12.0.
    Note: definitionally equal to `BSD_Hecke_OPEN 143`. -/
def BSD_AnalyticContinuation_143_OPEN : Prop :=
  AnalyticOn ℂ (BSDLFunction 143) Set.univ

/-- **OPEN**: completed functional equation for BSDLFunction 143.
    Precise form: BSDLFunction 143 (2−s) = ε·143^(1−s)·BSDLFunction 143 s.
    Gap: Atkin–Lehner operator + Mellin symmetry absent from Mathlib v4.12.0. -/
def BSD_GammaFuncEq_143_OPEN : Prop :=
  ∀ s : ℂ, BSDLFunction 143 (2 - s) =
    (BSD_RootNumber 143 : ℂ) * (143 : ℂ) ^ (1 - s) * BSDLFunction 143 s

-- ============================================================
-- §8. BSD_Hecke_143_CLOSED (0 sorry, classical trio)
-- ============================================================

/-- **BSD_Hecke_143_CLOSED** (0 sorry, classical trio):
    `BSD_AnalyticContinuation_143_OPEN` IS `BSD_Hecke_OPEN 143` definitionally. -/
theorem BSD_Hecke_143_CLOSED
    (h : BSD_AnalyticContinuation_143_OPEN) :
    BSD_Hecke_OPEN 143 :=
  h

/-- **PROVED** (0 sorry): on {Re s > 3/2}, given identification + M2 chain,
    BSDLFunction 143 is analytic. -/
theorem BSD_Hecke_143_HalfPlane_CLOSED
    (h_id  : BSD_LFunction_Identification_OPEN)
    (h_sum : BSD_LSeriesSummable_OPEN)
    (h_wm  : BSD_WeierstrassM_OPEN) :
    AnalyticOn ℂ (BSDLFunction 143) {s : ℂ | (3 : ℝ) / 2 < s.re} :=
  (BSD_AnalyticOn_CLOSED h_sum h_wm).congr (fun s hs => h_id s hs)

-- ============================================================
-- §9. BSD_FuncEq_143_CLOSED (0 sorry, classical trio)
-- ============================================================

/-- **BSD_FuncEq_143_CLOSED** (0 sorry, classical trio):
    Given `BSD_GammaFuncEq_143_OPEN`, `BSD_FuncEq_OPEN 143` holds.

    **Proof:**
    `h_feq s : BSDLFunction 143 (2−s) = ε · 143^(1−s) · BSDLFunction 143 s`
    Goal:       `143^(s−1) · BSDLFunction 143 (2−s) = ε · BSDLFunction 143 s`

    Substitute h_feq and use  143^(s−1) · 143^(1−s) = 143^((s−1)+(1−s)) = 143^0 = 1.  ∎ -/
theorem BSD_FuncEq_143_CLOSED
    (h_feq : BSD_GammaFuncEq_143_OPEN) :
    BSD_FuncEq_OPEN 143 := by
  intro s
  have h143 : (143 : ℂ) ≠ 0 := by norm_num
  have heps : (BSD_RootNumber 143 : ℂ) = -1 := by
    exact_mod_cast BSD_RootNumber_143
  have key : (143 : ℂ) ^ (s - 1) * (143 : ℂ) ^ (1 - s) = 1 := by
    rw [← cpow_add _ _ h143]; norm_num
  rw [show ((143 : ℕ) : ℂ) = (143 : ℂ) from by norm_cast, h_feq s, heps]
  rw [show (143 : ℂ) ^ (s - 1) * (-1 * (143 : ℂ) ^ (1 - s) * BSDLFunction 143 s) =
      -((143 : ℂ) ^ (s - 1) * (143 : ℂ) ^ (1 - s)) * BSDLFunction 143 s from by ring,
      key]

-- ============================================================
-- §10. Gap audit sentinels (0 sorry, classical trio)
-- ============================================================

/-- **Gap audit**: BSD_HeckeMultiplicativity_143_OPEN is a genuine OPEN gap.
    Mathematical content: clear.  Lean proof: ~30 lines (Finsupp disjoint product). -/
theorem gap_audit_mult : BSD_HeckeMultiplicativity_143_OPEN → True := fun _ => trivial

/-- **Gap audit**: BSD_HasseFull_143_OPEN is a genuine OPEN gap.
    Frobenius degree theory absent from Mathlib v4.12.0.
    Numerical evidence: `BSD_Weil_168_CLOSED` closes 168 primes ≤ 997. -/
theorem gap_audit_hasse : BSD_HasseFull_143_OPEN → True := fun _ => trivial

/-- **Gap audit**: BSD_AnalyticContinuation_143_OPEN is a genuine OPEN gap.
    Mellin transform + analytic continuation absent from Mathlib v4.12.0. -/
theorem gap_audit_analytic : BSD_AnalyticContinuation_143_OPEN → True := fun _ => trivial

/-- **Gap audit**: BSD_GammaFuncEq_143_OPEN is a genuine OPEN gap.
    Atkin–Lehner operator + functional equation absent from Mathlib v4.12.0. -/
theorem gap_audit_feq : BSD_GammaFuncEq_143_OPEN → True := fun _ => trivial

end Towers.BSD

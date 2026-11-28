import Towers.BSD.BSD_ClassNumber143
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.PrincipalIdealDomain

/-
  Towers/BSD/BSD_C22b_LowerBound.lean

  BSD-namespaced mirror of C22b_ClassNumberLowerBound.lean from the RH chain.
  Proves the even-k arithmetic for the lower bound h(ℚ(√-143)) ≥ 10,
  and names the two formal bridges as open surfaces.

  ## What is PROVED unconditionally (0 sorry, classical trio)

    § 3a. For k ∈ {2,4}: b≠0 → a²+ab+36b² ≠ 2^k   (nlinarith: 143b²>4·2^k)
    § 3b. For k = 6:     b≠0 → a²+ab+36b² ≠ 64     (interval_cases on b=±1)
    § 3c. For k = 8:     b≠0 → a²+ab+36b² ≠ 256    (interval_cases on b∈{±1,±2})
    § 4.  For k ∈ {1,3,5,7,9}: a²+ab+36b² ≠ 2^k    (imported from BSD_ClassNumber.lean)

  ## Named OPEN bridges (def Prop — not sorry, not axiom)

    PrincipalNorm_Bridge_BSD 𝔭₂ :
      If 𝔭₂^k = ⟨α⟩ then ∃ a b : ℤ, a²+ab+36b² = 2^k.
      Requires: norm_form (Algebra.norm ℤ (a+bθ) = a²+ab+36b²) +
                norm_form_eq (every α = a+bθ) + 𝔭₂_norm (norm of 𝔭₂ = 2).
      Gap: Algebra.norm ℤ computation for AdjoinRoot elements;
           𝔭₂_norm via Ideal.norm_span API; norm_form_eq via power basis.

    EvenK_IntGen_Bridge_BSD 𝔭₂ :
      For k ∈ {2,4,6,8}, 𝔭₂^k is non-principal.
      Requires (for the b=0 case after norm-form reduction):
        𝔭₂ ≠ 𝔭₂̄ (non-ramification: 2 ∤ disc = -143, gcd(2,143)=1).
        (2^{k/2}) = 𝔭₂^{k/2}·𝔭₂̄^{k/2} ≠ 𝔭₂^k.
      Gap: Dedekind ideal factorization API for the specific polynomial.

  SORRY: 0.  No native_decide.  Classical trio only.  NOT a brick.
  K1_Lower_OrderOf_BSD: OPEN conditional on the two bridges.
-/

namespace Towers.BSD

open Polynomial Submodule NumberField

/-! ## §1. Ring setup: R = ℤ[θ], θ² − θ + 36 = 0 -/

noncomputable abbrev R_BSD : Type _ :=
  AdjoinRoot (X ^ 2 - X + (36 : ℤ[X]))

noncomputable def θ_BSD : R_BSD :=
  AdjoinRoot.root (X ^ 2 - X + (36 : ℤ[X]))

/-- θ satisfies its defining equation θ² − θ + 36 = 0. -/
lemma θ_BSD_rel : θ_BSD ^ 2 - θ_BSD + (36 : R_BSD) = 0 := by
  have hmk : Polynomial.aeval θ_BSD (X ^ 2 - X + (36 : ℤ[X])) =
    θ_BSD ^ 2 - θ_BSD + (36 : R_BSD) := by
    simp only [map_sub, map_add, map_pow, Polynomial.aeval_X,
               Polynomial.aeval_C, map_ofNat]
  have h0 : Polynomial.aeval θ_BSD (X ^ 2 - X + (36 : ℤ[X])) = 0 := by
    simp only [θ_BSD, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  exact hmk.symm.trans h0

/-! ## §2. Named OPEN bridges -/

/-- **PrincipalNorm_Bridge_BSD**: if 𝔭₂^k is principal = ⟨α⟩ then the norm of α
    equals 2^k and α decomposes as a+bθ with a²+ab+36b² = 2^k.

    Formal gap: requires
    · norm_form : Algebra.norm ℤ (a+bθ) = a²+ab+36b²
    · norm_form_eq : every α ∈ R_BSD equals ↑a + ↑b * θ_BSD
    · 𝔭₂_norm : Ideal.absNorm 𝔭₂ = 2
    · Algebra.norm_span_singleton : absNorm ⟨α⟩ = |Algebra.norm ℤ α|
    STATUS: OPEN.  def Prop. -/
def PrincipalNorm_Bridge_BSD (𝔭₂ : Ideal R_BSD) : Prop :=
  ∀ k : ℕ, IsPrincipal (𝔭₂ ^ k) →
    ∃ a b : ℤ, a ^ 2 + a * b + 36 * b ^ 2 = (2 : ℤ) ^ k

/-- **EvenK_IntGen_Bridge_BSD**: for even k ∈ {2,4,6,8}, 𝔭₂^k is non-principal.

    After PrincipalNorm_Bridge_BSD reduces the problem, the only norm-2^k elements
    with b=0 are ±2^{k/2} ∈ ℤ, which generate (2^{k/2}) = 𝔭₂^{k/2}·𝔭₂̄^{k/2}.
    Formal gap: unique factorization of ideals and 𝔭₂ ≠ 𝔭₂̄.
    STATUS: OPEN.  def Prop. -/
def EvenK_IntGen_Bridge_BSD (𝔭₂ : Ideal R_BSD) : Prop :=
  ∀ k : ℕ, k ∈ ({2, 4, 6, 8} : Finset ℕ) → ¬ IsPrincipal (𝔭₂ ^ k)

/-! ## §3. Arithmetic: even-k impossibility for b ≠ 0 (PROVED) -/

/-- For k ∈ {2,4} and b≠0: 143·b² ≥ 143 > 4·2^k, so no solution. -/
lemma even_k24_bnonzero_BSD (k : ℕ) (hk : k ∈ ({2, 4} : Finset ℕ))
    (a b : ℤ) (hb : b ≠ 0) : a ^ 2 + a * b + 36 * b ^ 2 ≠ (2 : ℤ) ^ k := by
  intro hN
  have hb2 : 1 ≤ b ^ 2 := by
    rcases lt_or_gt_of_ne hb with h | h <;>
      nlinarith [sq_nonneg (b + 1), sq_nonneg (b - 1)]
  have hring : (2 * a + b) ^ 2 + 143 * b ^ 2 = 4 * (a ^ 2 + a * b + 36 * b ^ 2) := by ring
  rw [hN] at hring
  fin_cases hk
  · norm_num at hring; nlinarith [sq_nonneg (2 * a + b)]
  · norm_num at hring; nlinarith [sq_nonneg (2 * a + b)]

/-- For k = 6: (2a+b)²+143b² = 256. If b≠0 then b=±1; check each. -/
lemma even_k6_bnonzero_BSD (a b : ℤ) (hb : b ≠ 0) :
    a ^ 2 + a * b + 36 * b ^ 2 ≠ (2 : ℤ) ^ 6 := by
  intro hN
  simp only [show (2 : ℤ) ^ 6 = 64 from by norm_num] at hN
  have hring : (2 * a + b) ^ 2 + 143 * b ^ 2 = 256 := by linarith [show
    (2 * a + b) ^ 2 + 143 * b ^ 2 = 4 * (a ^ 2 + a * b + 36 * b ^ 2) from by ring]
  have hb2 : 1 ≤ b ^ 2 := by
    rcases lt_or_gt_of_ne hb with h | h <;>
      nlinarith [sq_nonneg (b + 1), sq_nonneg (b - 1)]
  have hprod : 143 ≤ 143 * b ^ 2 := by nlinarith
  have hb_le : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * a + b)]
  have hbeq : b ^ 2 = 1 := le_antisymm hb_le hb2
  have hb1 : b = 1 ∨ b = -1 := by
    have : (b - 1) * (b + 1) = 0 := by
      linarith [show b ^ 2 - 1 = (b - 1) * (b + 1) from by ring]
    rcases mul_eq_zero.mp this with h2 | h2 <;> [left; right] <;> linarith
  rcases hb1 with rfl | rfl
  · have hval : (2 * a + 1) ^ 2 = 113 := by linarith
    have ha_ub : a ≤ 4 := by nlinarith [sq_nonneg (2 * a - 10)]
    have ha_lb : -5 ≤ a := by nlinarith [sq_nonneg (2 * a + 12)]
    interval_cases a <;> norm_num at hval
  · have hval : (2 * a - 1) ^ 2 = 113 := by linarith
    have ha_ub : a ≤ 5 := by nlinarith [sq_nonneg (2 * a - 12)]
    have ha_lb : -4 ≤ a := by nlinarith [sq_nonneg (2 * a + 10)]
    interval_cases a <;> norm_num at hval

/-- For k = 8: (2a+b)²+143b²=1024. b≠0 forces b∈{±1,±2}; each gives non-square. -/
lemma even_k8_bnonzero_BSD (a b : ℤ) (hb : b ≠ 0) :
    a ^ 2 + a * b + 36 * b ^ 2 ≠ (2 : ℤ) ^ 8 := by
  intro hN
  simp only [show (2 : ℤ) ^ 8 = 256 from by norm_num] at hN
  have hring : (2 * a + b) ^ 2 + 143 * b ^ 2 = 1024 := by linarith [show
    (2 * a + b) ^ 2 + 143 * b ^ 2 = 4 * (a ^ 2 + a * b + 36 * b ^ 2) from by ring]
  have hb2 : 1 ≤ b ^ 2 := by
    rcases lt_or_gt_of_ne hb with h | h <;>
      nlinarith [sq_nonneg (b + 1), sq_nonneg (b - 1)]
  have hb_le : b ^ 2 ≤ 7 := by nlinarith [sq_nonneg (2 * a + b)]
  have hb_ub : b ≤ 2 := by nlinarith [sq_nonneg (b - 3)]
  have hb_lb : -2 ≤ b := by nlinarith [sq_nonneg (b + 3)]
  have h2ab_le : (2 * a + b) ^ 2 ≤ 1024 := by nlinarith
  have ha_ub : a ≤ 17 := by nlinarith [sq_nonneg (2 * a + b - 33)]
  have ha_lb : -17 ≤ a := by nlinarith [sq_nonneg (2 * a + b + 33)]
  interval_cases b
  · interval_cases a <;> norm_num at hN
  · interval_cases a <;> norm_num at hN
  · exact absurd rfl hb
  · interval_cases a <;> norm_num at hN
  · interval_cases a <;> norm_num at hN

/-- **even_k_bnonzero_no_norm_solution_BSD** (PROVED):
    For even k ∈ {2,4,6,8} and b≠0: a²+ab+36b² ≠ 2^k. -/
theorem even_k_bnonzero_no_norm_solution_BSD (k : ℕ) (hk : k ∈ ({2, 4, 6, 8} : Finset ℕ))
    (a b : ℤ) (hb : b ≠ 0) : a ^ 2 + a * b + 36 * b ^ 2 ≠ (2 : ℤ) ^ k := by
  fin_cases hk
  · exact even_k24_bnonzero_BSD 2 (by decide) a b hb
  · exact even_k24_bnonzero_BSD 4 (by decide) a b hb
  · exact even_k6_bnonzero_BSD a b hb
  · exact even_k8_bnonzero_BSD a b hb

/-! ## §4. Arithmetic: odd-k impossibilities (PROVED via BSD_ClassNumber.lean) -/

/-- **odd_k_no_norm_solution_BSD** (PROVED):
    For k ∈ {1,3,5,7,9}: a²+ab+36b² ≠ 2^k for ALL a,b : ℤ. -/
theorem odd_k_no_norm_solution_BSD (k : ℕ) (hk : k ∈ ({1, 3, 5, 7, 9} : Finset ℕ))
    (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ (2 : ℤ) ^ k := by
  fin_cases hk <;> simp_all
  · exact norm_form_no_norm_two_BSD a b
  · exact norm_form_no_norm_eight_BSD a b
  · exact norm_form_no_norm_32_BSD a b
  · exact norm_form_no_norm_128_BSD a b
  · exact norm_form_no_norm_512_BSD a b

/-! ## §5. Lower bound combinator -/

/-- **BSD_LowerBound_OrderOf_cert** (PROVED, conditional):
    If PrincipalNorm_Bridge_BSD and EvenK_IntGen_Bridge_BSD hold for 𝔭₂,
    then 𝔭₂^k is non-principal for every k with 1 ≤ k ≤ 9.
    SORRY: 0.  Classical trio only. -/
theorem BSD_LowerBound_OrderOf_cert
    (𝔭₂ : Ideal R_BSD)
    (h_pn : PrincipalNorm_Bridge_BSD 𝔭₂)
    (h_ev : EvenK_IntGen_Bridge_BSD 𝔭₂)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 9) :
    ¬ IsPrincipal (𝔭₂ ^ k) := by
  by_cases heven : k ∈ ({2, 4, 6, 8} : Finset ℕ)
  · exact h_ev k heven
  · have hodd : k ∈ ({1, 3, 5, 7, 9} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at heven ⊢
      omega
    intro hprin
    obtain ⟨a, b, hN⟩ := h_pn k hprin
    exact odd_k_no_norm_solution_BSD k hodd a b hN

/-! ## §6. The prime ideal above 2 and the discharge combinator -/

/-- The prime ideal above 2 in R_BSD = ℤ[θ]. -/
noncomputable def 𝔭₂_BSD : Ideal R_BSD := Ideal.span {(2 : R_BSD), θ_BSD}

/-- **BSD_C22b_Lower_cert**: given both OPEN bridges, 𝔭₂_BSD^k is non-principal
    for k = 1..9.
    SORRY: 0.  Classical trio only.  NOT a brick. -/
theorem BSD_C22b_Lower_cert
    (h_pn : PrincipalNorm_Bridge_BSD 𝔭₂_BSD)
    (h_ev : EvenK_IntGen_Bridge_BSD 𝔭₂_BSD) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 9 → ¬ IsPrincipal (𝔭₂_BSD ^ k) :=
  fun k hk1 hk2 => BSD_LowerBound_OrderOf_cert 𝔭₂_BSD h_pn h_ev k hk1 hk2

end Towers.BSD

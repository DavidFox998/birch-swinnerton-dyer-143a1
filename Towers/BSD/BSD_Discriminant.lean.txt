import Towers.BSD.BSD_NumberField
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Discriminant
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Discriminant

/-
  # BSD_Discriminant — Tier 1 arithmetic for K = ℚ(√-143)

  Concrete number-field arithmetic for K = AdjoinRoot(X²+143 : ℚ[X]).

  ── PROVED (SORRY: 0, axiom footprint: classical trio) ──────────────────────
  • BSD_finrank_proved : BSD_finrank_CLOSED   (= finrank ℚ K = 2)
  • trace_one_BSD       : Algebra.trace ℚ K 1 = 2
  • trace_α_BSD         : Algebra.trace ℚ K α = 0
  • trace_α_sq_BSD      : Algebra.trace ℚ K (α ^ 2) = -286
  • norm_α_BSD          : Algebra.norm ℚ α = 143
  • ω_sq_eq_BSD         : ω ^ 2 - ω + 36 = 0     (ω = (1+α)/2)
  • ω_integral_BSD      : IsIntegral ℤ ω
  • trace_ω_BSD         : Algebra.trace ℚ K ω = 1
  • trace_ω_sq_BSD      : Algebra.trace ℚ K (ω ^ 2) = -71

  ── CLOSED SURFACE (proved in BSD_IntBasis.lean, 0 sorry, classical trio) ───
  • BSD_IntegralSpanning_CLOSED
      Every element of 𝓞 K is a ℤ-linear combination of 1 and ω.
      Content: squarefree-discriminant criterion.  disc(ℤ[1,ω]) = −143 = −11·13
      is squarefree, so [𝓞_K : ℤ[1,ω]]² | −143 forces [𝓞_K : ℤ[1,ω]] = ±1,
      i.e. ℤ[1, ω] = 𝓞_K.  Proved in BSD_IntBasis.lean.

  NOT a brick.  SORRY: 0.  Axiom footprint: classical trio
  {propext, Classical.choice, Quot.sound}.
-/

namespace Towers.BSD

open Polynomial NumberField FiniteDimensional

/-! ### Power basis for K over ℚ -/

noncomputable def pb_BSD : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis (show (X ^ 2 + C (143 : ℚ)) ≠ 0 from by
    intro h
    have := congr_arg (Polynomial.coeff · 2) h
    simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C] at this)

lemma pb_BSD_gen_eq_α : pb_BSD.gen = α := by
  simp [pb_BSD, α, AdjoinRoot.powerBasis]

lemma pb_BSD_monic : (X ^ 2 + C (143 : ℚ)).Monic :=
  monic_X_pow_add (degree_C_le.trans_lt (by decide))

lemma pb_BSD_minpoly : minpoly ℚ pb_BSD.gen = X ^ 2 + C 143 :=
  AdjoinRoot.minpoly_powerBasis_gen_of_monic pb_BSD_monic

/-! ### finrank ℚ K = 2  (proves BSD_finrank_CLOSED) -/

/-- PROVED: finrank ℚ K = 2.  Proof of BSD_finrank_CLOSED.
    Named BSD_finrank_proved to match the consumer import in BSD_IntBasis.lean. -/
theorem BSD_finrank_proved : BSD_finrank_CLOSED := by
  unfold BSD_finrank_CLOSED
  rw [pb_BSD.finrank]
  simp [pb_BSD, Polynomial.natDegree_X_pow_add_C]

/-! ### ℚ-trace computations -/

/-- Algebra.trace ℚ K 1 = 2.
    Proof: 1 = algebraMap ℚ K 1; trace_algebraMap gives finrank ℚ K • 1 = 2. -/
theorem trace_one_BSD : Algebra.trace ℚ K 1 = 2 := by
  rw [show (1 : K) = algebraMap ℚ K 1 from (map_one _).symm,
      Algebra.trace_algebraMap, BSD_finrank_proved]
  norm_num

/-- Algebra.trace ℚ K α = 0.
    Proof: α = pb_BSD.gen; trace_gen_eq_nextCoeff_minpoly gives
    −nextCoeff(X²+143) = −coeff₁ = 0. -/
theorem trace_α_BSD : Algebra.trace ℚ K α = 0 := by
  rw [← pb_BSD_gen_eq_α,
      pb_BSD.trace_gen_eq_nextCoeff_minpoly,
      pb_BSD_minpoly]
  simp [Polynomial.nextCoeff, Polynomial.natDegree_X_pow_add_C,
        Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]

/-- Algebra.trace ℚ K (α ^ 2) = −286.
    Proof: α² = −143; Tr(−143) = −143 · Tr(1) = −286. -/
theorem trace_α_sq_BSD : Algebra.trace ℚ K (α ^ 2) = -286 := by
  rw [α_sq_BSD,
      show -(143 : K) = algebraMap ℚ K (-143) from by norm_cast,
      Algebra.trace_algebraMap, BSD_finrank_proved]
  norm_num

/-! ### Norm computation -/

/-- Algebra.norm ℚ α = 143.
    Proof: norm_gen_eq_coeff_zero_minpoly gives (−1)^2 · coeff₀(X²+143) = 143. -/
theorem norm_α_BSD : Algebra.norm ℚ α = 143 := by
  rw [← pb_BSD_gen_eq_α,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb_BSD,
      pb_BSD_minpoly]
  simp [pb_BSD, AdjoinRoot.powerBasis, Polynomial.natDegree_X_pow_add_C,
        Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]

/-! ### ω = (1 + α) / 2 -/

/-- ω = (1 + α) / 2: the canonical integral generator of 𝓞 K.
    Satisfies ω² − ω + 36 = 0; {1, ω} spans 𝓞 K over ℤ (BSD_IntegralSpanning_CLOSED). -/
noncomputable def ω : K := (1 + α) / 2

/-- ω² − ω + 36 = 0.
    Proof: ω = (1+α)/2, so 4(ω²−ω+36) = (1+α)²−2(1+α)+144 = α²+143 = 0. -/
theorem ω_sq_eq_BSD : ω ^ 2 - ω + 36 = 0 := by
  have hα : α ^ 2 + (143 : K) = 0 := α_eval_zero_BSD
  have key : ω ^ 2 - ω + 36 = (α ^ 2 + 143) / 4 := by
    unfold ω; field_simp; ring
  rw [key, hα, zero_div]

/-- ω is integral over ℤ.
    Witness: monic p = X² − X + 36 with aeval ω p = 0. -/
theorem ω_integral_BSD : IsIntegral ℤ ω := by
  refine ⟨X ^ 2 - X + C (36 : ℤ), ?_, ?_⟩
  · have hrw : X ^ 2 - X + C (36 : ℤ) = X ^ 2 + (-X + C 36) := by ring
    rw [hrw]
    exact monic_X_pow_add (lt_of_le_of_lt (by compute_degree!) (by norm_num))
  · show aeval ω (X ^ 2 - X + C (36 : ℤ)) = 0
    simp only [aeval_add, map_sub, aeval_X_pow, aeval_X, aeval_C]
    have hcast : algebraMap ℤ K (36 : ℤ) = (36 : K) := by norm_cast
    rw [hcast]
    exact ω_sq_eq_BSD

/-! ### Traces of ω and ω² -/

/-- Algebra.trace ℚ K ω = 1.
    Proof: ω = (1/2)·1 + (1/2)·α; by ℚ-linearity, Tr(ω) = (1/2)·2 + (1/2)·0 = 1. -/
theorem trace_ω_BSD : Algebra.trace ℚ K ω = 1 := by
  have hdecomp : ω = (2 : ℚ)⁻¹ • (1 : K) + (2 : ℚ)⁻¹ • α := by
    unfold ω
    simp only [Algebra.smul_def, map_inv₀, map_ofNat]
    field_simp
  rw [hdecomp,
      (Algebra.trace ℚ K).map_add,
      (Algebra.trace ℚ K).map_smul,
      (Algebra.trace ℚ K).map_smul,
      trace_one_BSD, trace_α_BSD]
  norm_num

/-- Algebra.trace ℚ K (ω ^ 2) = −71.
    Proof: ω² = ω − 36 (from ω_sq_eq_BSD);
    Tr(ω²) = Tr(ω) − 36·Tr(1) = 1 − 72 = −71. -/
theorem trace_ω_sq_BSD : Algebra.trace ℚ K (ω ^ 2) = -71 := by
  have h : ω ^ 2 = ω - (36 : K) := by linear_combination ω_sq_eq_BSD
  have h36 : (36 : K) = algebraMap ℚ K 36 := by norm_cast
  rw [h, h36, map_sub, Algebra.trace_algebraMap, BSD_finrank_proved, trace_ω_BSD]
  norm_num

/-!
### BSD_IntegralSpanning_CLOSED — proved in BSD_IntBasis.lean

`∀ x : 𝓞 K, ∃ a b : ℤ, (x : K) = a • (1 : K) + b • ω`

Mathematical content — squarefree discriminant criterion:
disc(ℤ[1, ω]) = det !![2,1;1,-71] = −143 (squarefree).
Any [𝓞_K : ℤ[1,ω]] = d satisfies d² | −143, so d = ±1.
STATUS: CLOSED.  Proved in BSD_IntBasis.lean (0 sorry, classical trio).
-/

end Towers.BSD

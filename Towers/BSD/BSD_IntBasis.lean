import Towers.BSD.BSD_Discriminant
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Discriminant
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree

/-
  # BSD_IntBasis — Integral basis {1, ω} for 𝓞 K, K = ℚ(√-143)

  Proves **BSD_IntegralSpanning_CLOSED** via the squarefree discriminant criterion.

  ── PROVED (SORRY: 0, axiom footprint: classical trio) ──────────────────────
  • BSD_IntegralSpanning_CLOSED
      Every element of 𝓞 K is a ℤ-linear combination of 1 and ω.
      Proof: squarefree discriminant criterion.
        1. Compute disc(ℤ[1,ω]) = det(!![2,1;1,−71]) = −143 via ℤ-traces.
        2. Let b₁ be any ℤ-basis of 𝓞 K and P = b₁.toMatrix([1,ω]).
           Then disc([1,ω]) = P.det² · disc(b₁) = P.det² · disc(𝓞 K).
        3. −143 squarefree ⟹ P.det² | −143 ⟹ IsUnit P.det ⟹ IsUnit P.
        4. Invertible P ⟹ [1, ω] spans 𝓞 K (matrix-inverse argument).
        5. disc([1,ω]) ≠ 0 ⟹ [1, ω] is ℤ-linearly independent.
        6. Basis.mk ⟹ v_basis; read off ℤ-coordinates for every x.

  NOT a brick (BSD surfaces #2, #3 still OPEN).
  Axiom footprint: classical trio only.
-/

namespace Towers.BSD

open Polynomial NumberField FiniteDimensional Matrix Algebra

/-! ### Candidate spanning vectors 1 and ω as elements of 𝓞 K -/

noncomputable def one_OK : 𝓞 K := ⟨1, isIntegral_one⟩
noncomputable def ω_OK  : 𝓞 K := ⟨ω, ω_integral_BSD⟩

lemma one_OK_coe : (one_OK : K) = 1 := rfl
lemma ω_OK_coe   : (ω_OK  : K) = ω := rfl

/-! ### ℤ-trace computations via Algebra.coe_trace_int -/

lemma trace_11_int : Algebra.trace ℤ (𝓞 K) (one_OK * one_OK) = 2 := by
  have h : (Algebra.trace ℤ (𝓞 K) (one_OK * one_OK) : ℚ) = 2 := by
    rw [Algebra.coe_trace_int]
    have heq : ((one_OK * one_OK : 𝓞 K) : K) = 1 := by simp [one_OK]
    rw [heq]; exact_mod_cast trace_one_BSD
  exact_mod_cast h

lemma trace_1ω_int : Algebra.trace ℤ (𝓞 K) (one_OK * ω_OK) = 1 := by
  have h : (Algebra.trace ℤ (𝓞 K) (one_OK * ω_OK) : ℚ) = 1 := by
    rw [Algebra.coe_trace_int]
    have heq : ((one_OK * ω_OK : 𝓞 K) : K) = ω := by simp [one_OK, ω_OK]
    rw [heq]; exact_mod_cast trace_ω_BSD
  exact_mod_cast h

lemma trace_ω1_int : Algebra.trace ℤ (𝓞 K) (ω_OK * one_OK) = 1 := by
  have h : (Algebra.trace ℤ (𝓞 K) (ω_OK * one_OK) : ℚ) = 1 := by
    rw [Algebra.coe_trace_int]
    have heq : ((ω_OK * one_OK : 𝓞 K) : K) = ω := by simp [one_OK, ω_OK]
    rw [heq]; exact_mod_cast trace_ω_BSD
  exact_mod_cast h

lemma trace_ωω_int : Algebra.trace ℤ (𝓞 K) (ω_OK * ω_OK) = -71 := by
  have h : (Algebra.trace ℤ (𝓞 K) (ω_OK * ω_OK) : ℚ) = -71 := by
    rw [Algebra.coe_trace_int]
    have heq : ((ω_OK * ω_OK : 𝓞 K) : K) = ω ^ 2 := by simp [ω_OK, sq]
    rw [heq]; exact_mod_cast trace_ω_sq_BSD
  exact_mod_cast h

/-! ### Candidate pair as a function Fin 2 → 𝓞 K -/

noncomputable def v_BSD : Fin 2 → 𝓞 K := ![one_OK, ω_OK]

lemma v_BSD_zero : v_BSD 0 = one_OK := rfl
lemma v_BSD_one  : v_BSD 1 = ω_OK  := rfl

/-! ### Trace matrix = !![2, 1; 1, -71] -/

lemma traceMatrix_v_BSD :
    Algebra.traceMatrix ℤ v_BSD = !![2, 1; 1, -71] := by
  have h00 : Algebra.traceMatrix ℤ v_BSD 0 0 = 2 := by
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
          v_BSD_zero, trace_11_int]
  have h01 : Algebra.traceMatrix ℤ v_BSD 0 1 = 1 := by
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
          v_BSD_zero, v_BSD_one, trace_1ω_int]
  have h10 : Algebra.traceMatrix ℤ v_BSD 1 0 = 1 := by
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
          v_BSD_zero, v_BSD_one, trace_ω1_int]
  have h11 : Algebra.traceMatrix ℤ v_BSD 1 1 = -71 := by
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
          v_BSD_one, trace_ωω_int]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
              Matrix.head_fin_const]

/-! ### Discriminant of v_BSD = -143 -/

lemma discr_v_BSD : Algebra.discr ℤ v_BSD = -143 := by
  rw [Algebra.discr_def, traceMatrix_v_BSD]
  norm_num [Matrix.det_fin_two]

/-! ### NumberField discriminant -/

private lemma neg143_squarefree : Squarefree (-143 : ℤ) := by
  rw [← Int.squarefree_natAbs, show (-143 : ℤ).natAbs = 143 from rfl,
      Nat.squarefree_iff_prime_squarefree]
  intro p hp hdvd
  have hbnd : p * p ≤ 143 := Nat.le_of_dvd (by norm_num) hdvd
  have hle : p ≤ 11 := by nlinarith [hp.two_le]
  interval_cases p <;>
    first | exact absurd hp (by decide) | norm_num at hdvd

/-- **BSD_K_disc_neg143** (0 sorry, classical trio):
    `NumberField.discr K = -143`.

    Proof: `v_BSD = {1, ω}` has `Algebra.discr ℤ v_BSD = -143` (discr_v_BSD).
    The change-of-basis matrix P from any ℤ-basis b₁ to v_BSD satisfies
    `P.det ^ 2 | -143`; Squarefree(-143) → IsUnit P.det → P.det^2 = 1;
    hence `NumberField.discr K = -143`. -/
theorem BSD_K_disc_neg143 : discr K = -143 := by
  have hrank : finrank ℤ (𝓞 K) = 2 := by
    rw [RingOfIntegers.rank]; exact BSD_finrank_proved
  let b₁ : Basis (Fin 2) ℤ (𝓞 K) := finBasisOfFinrankEq ℤ (𝓞 K) hrank
  let P : Matrix (Fin 2) (Fin 2) ℤ := b₁.toMatrix v_BSD
  have hdisc_formula : Algebra.discr ℤ v_BSD = P.det ^ 2 * Algebra.discr ℤ (↑b₁) := by
    conv_lhs => rw [← Basis.toMatrix_map_vecMul b₁ v_BSD]
    exact Algebra.discr_of_matrix_vecMul (↑b₁) P
  have hdisc_b1 : Algebra.discr ℤ (↑b₁) = discr K :=
    NumberField.discr_eq_discr K b₁
  have hprod : P.det ^ 2 * discr K = -143 := by
    rw [← hdisc_b1, ← hdisc_formula]; exact discr_v_BSD
  have hdvd : P.det ^ 2 ∣ (-143 : ℤ) := ⟨discr K, hprod.symm⟩
  have hunit_det : IsUnit P.det := neg143_squarefree P.det (by rwa [sq] at hdvd)
  have hdet_sq : P.det ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp hunit_det with h | h <;> rw [h] <;> norm_num
  linarith [hdet_sq ▸ hprod]

/-! ### Main theorem: BSD_IntegralSpanning_CLOSED -/

/-- **PROVED** (0 sorry, classical trio):
    Every element of 𝓞 K is a ℤ-linear combination of {1, ω}.

    Proof via squarefree discriminant criterion. -/
theorem BSD_IntegralSpanning_CLOSED :
    ∀ x : 𝓞 K, ∃ a b : ℤ, (x : K) = a • (1 : K) + b • ω := by
  /- Step 1: ℤ-basis b₁ of 𝓞 K -/
  have hrank : finrank ℤ (𝓞 K) = 2 := by
    rw [RingOfIntegers.rank]
    exact BSD_finrank_proved
  let b₁ : Basis (Fin 2) ℤ (𝓞 K) := finBasisOfFinrankEq ℤ (𝓞 K) hrank
  /- Step 2: coordinate matrix P = b₁.toMatrix v_BSD -/
  let P : Matrix (Fin 2) (Fin 2) ℤ := b₁.toMatrix v_BSD
  /- Step 3: b₁ ᵥ* P.map alg = v_BSD -/
  have hv : b₁ ᵥ* (P.map (algebraMap ℤ (𝓞 K))) = v_BSD :=
    Basis.toMatrix_map_vecMul b₁ v_BSD
  /- Step 4: discr ℤ v_BSD = P.det² · discr ℤ b₁ -/
  have hdisc_formula : Algebra.discr ℤ v_BSD = P.det ^ 2 * Algebra.discr ℤ (↑b₁) := by
    conv_lhs => rw [← hv]
    exact Algebra.discr_of_matrix_vecMul (↑b₁) P
  /- Step 5: discr ℤ b₁ = NumberField.discr K
     K is explicit in discr_eq_discr (variable round-parens in Discriminant.lean) -/
  have hdisc_b1 : Algebra.discr ℤ (↑b₁) = NumberField.discr K :=
    NumberField.discr_eq_discr K b₁
  /- Step 6: P.det² | −143 -/
  have hdvd : P.det ^ 2 ∣ (-143 : ℤ) := by
    exact ⟨NumberField.discr K, by
      have h1 := discr_v_BSD
      rw [hdisc_formula, hdisc_b1] at h1
      linarith⟩
  /- Step 7: Squarefree(−143) → IsUnit P.det -/
  have hsq : Squarefree (-143 : ℤ) := by
    rw [← Int.squarefree_natAbs, show (-143 : ℤ).natAbs = 143 from rfl,
        Nat.squarefree_iff_prime_squarefree]
    intro p hp hdvd
    have hbnd : p * p ≤ 143 := Nat.le_of_dvd (by norm_num) hdvd
    have hle : p ≤ 11 := by nlinarith [hp.two_le]
    interval_cases p <;>
      first | exact absurd hp (by decide) | norm_num at hdvd
  have hunit_det : IsUnit P.det := hsq P.det (by rwa [sq] at hdvd)
  /- Step 8: IsUnit P — use dot notation on P since A is explicit in the theorem -/
  have hPunit : IsUnit P := P.isUnit_iff_isUnit_det.mpr hunit_det
  /- Step 9: LinearIndependent ℤ v_BSD (disc ≠ 0) -/
  have hLI : LinearIndependent ℤ v_BSD := by
    by_contra hNLI
    have h0 := Algebra.discr_zero_of_not_linearIndependent (A := ℤ) (B := 𝓞 K) hNLI
    rw [discr_v_BSD] at h0; norm_num at h0
  /- Step 10: v_BSD spans 𝓞 K via matrix-inverse argument -/
  have hspan : ⊤ ≤ Submodule.span ℤ (Set.range v_BSD) := by
    rw [← b₁.span_eq, Submodule.span_le]
    rintro x ⟨j, rfl⟩
    /- Show b₁ j ∈ span v_BSD via: v_BSD ᵥ* Pu⁻¹.map alg = b₁ -/
    let Pu : (Matrix (Fin 2) (Fin 2) ℤ)ˣ := hPunit.unit
    have hPu_val : (Pu : Matrix (Fin 2) (Fin 2) ℤ) = P := hPunit.unit_spec
    have hm1 : (1 : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ (𝓞 K)) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    have hrow : v_BSD ᵥ* (Pu⁻¹.val.map (algebraMap ℤ (𝓞 K))) = (↑b₁ : Fin 2 → 𝓞 K) := by
      have step : ((↑b₁ : Fin 2 → 𝓞 K) ᵥ* (Pu.val.map (algebraMap ℤ (𝓞 K)))) ᵥ*
                  (Pu⁻¹.val.map (algebraMap ℤ (𝓞 K))) = (↑b₁ : Fin 2 → 𝓞 K) := by
        rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, Units.mul_inv, hm1, Matrix.vecMul_one]
      rw [show Pu.val = P from hPu_val, hv] at step
      exact step
    rw [show (↑b₁ : Fin 2 → 𝓞 K) j =
          (v_BSD ᵥ* (Pu⁻¹.val.map (algebraMap ℤ (𝓞 K)))) j from
          (congr_fun hrow j).symm]
    /- Expand vecMul and show each summand is in span v_BSD -/
    simp only [Matrix.vecMul, Matrix.dotProduct, Matrix.map_apply]
    apply Submodule.sum_mem
    intro i _
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  /- Step 11: Basis.mk from LI + spanning -/
  let v_basis : Basis (Fin 2) ℤ (𝓞 K) := Basis.mk hLI hspan
  /- Step 12: For every x, extract ℤ-coordinates -/
  intro x
  refine ⟨v_basis.repr x 0, v_basis.repr x 1, ?_⟩
  /- Identify the basis vectors -/
  have h0 : (v_basis 0 : K) = 1 := by
    rw [show v_basis 0 = v_BSD 0 from Basis.mk_apply hLI hspan 0,
        v_BSD_zero, one_OK_coe]
  have h1 : (v_basis 1 : K) = ω := by
    rw [show v_basis 1 = v_BSD 1 from Basis.mk_apply hLI hspan 1,
        v_BSD_one, ω_OK_coe]
  /- Coerce the sum_repr to K -/
  have hrep_K : (x : K) =
      v_basis.repr x 0 • (v_basis 0 : K) + v_basis.repr x 1 • (v_basis 1 : K) := by
    have h := v_basis.sum_repr x
    -- Expand ∑ i : Fin 2, ... to a two-term sum
    simp only [Fin.sum_univ_two] at h
    -- h : v_basis.repr x 0 • v_basis 0 + v_basis.repr x 1 • v_basis 1 = x  (in 𝓞 K)
    have h2 := congr_arg ((↑) : 𝓞 K → K) h.symm
    -- h2 : (x : K) = ↑(v_basis.repr x 0 • v_basis 0 + v_basis.repr x 1 • v_basis 1)
    simp only [_root_.map_add, _root_.map_smul] at h2
    exact h2
  rw [hrep_K, h0, h1]

/-! ### Public ℤ-basis of 𝓞 K, for absNorm computations -/

lemma _v_BSD_li : LinearIndependent ℤ v_BSD := by
  by_contra hNLI
  have h0 := Algebra.discr_zero_of_not_linearIndependent (A := ℤ) (B := 𝓞 K) hNLI
  rw [discr_v_BSD] at h0; norm_num at h0

lemma _v_BSD_span : ⊤ ≤ Submodule.span ℤ (Set.range v_BSD) := by
  have hrank : finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank]; exact BSD_finrank_proved
  let b₁ : Basis (Fin 2) ℤ (𝓞 K) := finBasisOfFinrankEq ℤ (𝓞 K) hrank
  let P : Matrix (Fin 2) (Fin 2) ℤ := b₁.toMatrix v_BSD
  have hv : b₁ ᵥ* (P.map (algebraMap ℤ (𝓞 K))) = v_BSD :=
    Basis.toMatrix_map_vecMul b₁ v_BSD
  have hdisc_formula : Algebra.discr ℤ v_BSD = P.det ^ 2 * Algebra.discr ℤ (↑b₁) := by
    conv_lhs => rw [← hv]
    exact Algebra.discr_of_matrix_vecMul (↑b₁) P
  have hdisc_b1 : Algebra.discr ℤ (↑b₁) = NumberField.discr K :=
    NumberField.discr_eq_discr K b₁
  have hdvd : P.det ^ 2 ∣ (-143 : ℤ) :=
    ⟨NumberField.discr K, by
      have h1 := discr_v_BSD
      rw [hdisc_formula, hdisc_b1] at h1
      linarith⟩
  have hsq : Squarefree (-143 : ℤ) := by
    rw [← Int.squarefree_natAbs, show (-143 : ℤ).natAbs = 143 from rfl,
        Nat.squarefree_iff_prime_squarefree]
    intro p hp hdvd2
    have hbnd : p * p ≤ 143 := Nat.le_of_dvd (by norm_num) hdvd2
    have hle : p ≤ 11 := by nlinarith [hp.two_le]
    interval_cases p <;> first | exact absurd hp (by decide) | norm_num at hdvd2
  have hunit_det : IsUnit P.det := hsq P.det (by rwa [sq] at hdvd)
  have hPunit : IsUnit P := P.isUnit_iff_isUnit_det.mpr hunit_det
  rw [← b₁.span_eq, Submodule.span_le]
  rintro x ⟨j, rfl⟩
  let Pu : (Matrix (Fin 2) (Fin 2) ℤ)ˣ := hPunit.unit
  have hPu_val : (Pu : Matrix (Fin 2) (Fin 2) ℤ) = P := hPunit.unit_spec
  have hm1 : (1 : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ (𝓞 K)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hrow : v_BSD ᵥ* (Pu⁻¹.val.map (algebraMap ℤ (𝓞 K))) = (↑b₁ : Fin 2 → 𝓞 K) := by
    have step : ((↑b₁ : Fin 2 → 𝓞 K) ᵥ* (Pu.val.map (algebraMap ℤ (𝓞 K)))) ᵥ*
                (Pu⁻¹.val.map (algebraMap ℤ (𝓞 K))) = (↑b₁ : Fin 2 → 𝓞 K) := by
      rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, Units.mul_inv, hm1, Matrix.vecMul_one]
    rw [show Pu.val = P from hPu_val, hv] at step
    exact step
  rw [show (↑b₁ : Fin 2 → 𝓞 K) j =
        (v_BSD ᵥ* (Pu⁻¹.val.map (algebraMap ℤ (𝓞 K)))) j from (congr_fun hrow j).symm]
  simp only [Matrix.vecMul, Matrix.dotProduct, Matrix.map_apply]
  apply Submodule.sum_mem
  intro i _
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- Public ℤ-basis of 𝓞 K: `BSD_intBasis 0 = ⟨1, _⟩` and `BSD_intBasis 1 = ⟨ω, _⟩`. -/
noncomputable def BSD_intBasis : Basis (Fin 2) ℤ (𝓞 K) :=
  Basis.mk _v_BSD_li _v_BSD_span

/-- BSD_intBasis 0 has K-value 1. -/
lemma BSD_intBasis_zero_coe : (BSD_intBasis 0 : K) = 1 := by
  rw [BSD_intBasis, Basis.mk_apply, v_BSD_zero, one_OK_coe]

/-- BSD_intBasis 1 has K-value ω. -/
lemma BSD_intBasis_one_coe : (BSD_intBasis 1 : K) = ω := by
  rw [BSD_intBasis, Basis.mk_apply, v_BSD_one, ω_OK_coe]

end Towers.BSD

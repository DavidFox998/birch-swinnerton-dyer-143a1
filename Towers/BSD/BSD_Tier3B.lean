import Towers.BSD.BSD_NormBridge
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.Norm.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# BSD_Tier3B — Tier 3B: Formal norm certificate for gen(𝔭₂^{10})

Closes `BSD_algNorm_gen_OPEN` by proving `(Algebra.norm ℤ gen_OK : ℤ) = 1024` via:

1. `gen_poly_natDegree` : natDegree (X² + 53X + 1024 : ℚ[X]) = 2
2. `irred_gen_poly_monic` : that polynomial is monic (leadingCoeff = 1)
3. `irred_gen_poly` : irreducible (disc = −1287 < 0 ⟹ no real roots)
4. `gen_OK_minpoly_eq` : minpoly ℚ (gen_OK : K) = X² + 53X + 1024
5. `BSD_algNorm_gen_CLOSED` : norm route via adjoin power basis + coeff₀

## Proved (0 sorry, classical trio only)
-/

namespace Towers.BSD

open NumberField Polynomial IntermediateField FiniteDimensional

/-! ### Step 1: natDegree -/

lemma gen_poly_natDegree : (X ^ 2 + C (53 : ℚ) * X + C 1024).natDegree = 2 := by
  have h_C : (X ^ 2 + C (53 : ℚ) * X + C (1024 : ℚ)).natDegree =
             (X ^ 2 + C (53 : ℚ) * X).natDegree := natDegree_add_C
  have h_CX : natDegree (C (53 : ℚ) * X) = 1 := natDegree_C_mul_X _ (by norm_num)
  have h_Xsq : natDegree (X ^ 2 : ℚ[X]) = 2 := natDegree_X_pow 2
  have hlt : natDegree (C (53 : ℚ) * X) < natDegree (X ^ 2 : ℚ[X]) := by
    rw [h_CX, h_Xsq]; norm_num
  rw [h_C, natDegree_add_eq_left_of_natDegree_lt hlt, h_Xsq]

/-! ### Step 2: Monic -/

lemma irred_gen_poly_monic : (X ^ 2 + C (53 : ℚ) * X + C 1024).Monic := by
  rw [Monic, leadingCoeff, gen_poly_natDegree]
  norm_num [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]

/-! ### Step 3: Irreducible -/

lemma irred_gen_poly : Irreducible (X ^ 2 + C (53 : ℚ) * X + C 1024) := by
  have hne1 : X ^ 2 + C (53 : ℚ) * X + C 1024 ≠ 1 := by
    intro h
    have := gen_poly_natDegree
    rw [h, natDegree_one] at this
    exact absurd this (by norm_num)
  rw [irred_gen_poly_monic.irreducible_iff_lt_natDegree_lt hne1]
  intro q hqm hqdeg hqdvd
  have hq1 : q.natDegree = 1 := by
    simp only [gen_poly_natDegree, show (2 : ℕ) / 2 = 1 from rfl,
               Finset.mem_Ioc] at hqdeg; omega
  have hqdeg1 : q.degree = 1 := by
    rw [degree_eq_natDegree hqm.ne_zero, hq1]; norm_cast
  obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one hqdeg1
  have hroot : IsRoot (X ^ 2 + C (53 : ℚ) * X + C 1024) r :=
    dvd_iff_isRoot.mp (dvd_trans (dvd_iff_isRoot.mpr hr) hqdvd)
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hroot
  nlinarith [sq_nonneg (2 * r + 53), hroot]

/-! ### Step 4: Minimal polynomial -/

/-- The key cast: gen_sq_BSD (in 𝓞 K) implies the same equation in K. -/
lemma gen_OK_sq_K : (gen_OK : K) ^ 2 + 53 * (gen_OK : K) + 1024 = 0 := by
  have h := congr_arg (algebraMap (𝓞 K) K) gen_sq_BSD
  simp only [map_add, map_pow, map_mul, map_ofNat, map_zero] at h
  exact h

lemma gen_OK_minpoly_eq :
    X ^ 2 + C (53 : ℚ) * X + C 1024 = minpoly ℚ (gen_OK : K) := by
  apply minpoly.eq_of_irreducible_of_monic irred_gen_poly _ irred_gen_poly_monic
  have heq : Polynomial.aeval (gen_OK : K) (X ^ 2 + C (53 : ℚ) * X + C 1024) =
             (gen_OK : K) ^ 2 + 53 * (gen_OK : K) + 1024 := by
    simp only [map_add, map_pow, map_mul, aeval_X, aeval_C, map_ofNat]
  rw [heq]
  exact gen_OK_sq_K

/-! ### Tier 3B main theorem -/

/-- **BSD_Tier3B_algNorm_cert**: `(Algebra.norm ℤ gen_OK : ℤ) = 1024`.
Proves the ℤ-norm of gen_OK = −28 + 3ω equals 1024 = 2^{10},
via Algebra.norm_eq_norm_adjoin + minpoly route.
(The canonical surface proof is BSD_algNorm_gen_proof in BSD_AlgNorm.lean.) -/
theorem BSD_Tier3B_algNorm_cert : (Algebra.norm ℤ gen_OK : ℤ) = 1024 := by
  have hx_int : IsIntegral ℚ (gen_OK : K) := gen_OK.2.tower_top
  suffices h : Algebra.norm ℚ (gen_OK : K) = 1024 by
    have hcast := Algebra.coe_norm_int (K := K) gen_OK
    rw [h] at hcast; exact_mod_cast hcast
  rw [Algebra.norm_eq_norm_adjoin ℚ (gen_OK : K)]
  have hfr_adj : finrank ℚ ℚ⟮(gen_OK : K)⟯ = 2 := by
    rw [adjoin.finrank hx_int, ← gen_OK_minpoly_eq]
    exact gen_poly_natDegree
  have hfK : finrank ℚ K = 2 := by
    have hne : (X ^ 2 + C (143 : ℚ)) ≠ 0 :=
      (monic_X_pow_add (degree_C_le.trans_lt (by norm_cast))).ne_zero
    rw [(AdjoinRoot.powerBasis hne).finrank]
    show (X ^ 2 + C (143 : ℚ)).natDegree = 2
    simp [natDegree_X_pow_add_C]
  have hfr1 : finrank ℚ⟮(gen_OK : K)⟯ K = 1 := by
    have h_mul := finrank_mul_finrank (F := ℚ) (K := ℚ⟮(gen_OK : K)⟯) (A := K)
    rw [hfr_adj, hfK] at h_mul; omega
  rw [hfr1, pow_one, ← adjoin.powerBasis_gen hx_int,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
  have hdim : (adjoin.powerBasis hx_int).dim = 2 := by
    simp only [adjoin.powerBasis_dim, ← gen_OK_minpoly_eq]
    exact gen_poly_natDegree
  have hmpoly : minpoly ℚ (adjoin.powerBasis hx_int).gen =
      X ^ 2 + C (53 : ℚ) * X + C 1024 := by
    rw [adjoin.powerBasis_gen, minpoly_gen, ← gen_OK_minpoly_eq]
  rw [hdim, hmpoly]
  norm_num [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]

end Towers.BSD

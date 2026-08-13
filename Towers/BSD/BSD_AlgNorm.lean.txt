import Towers.BSD.BSD_Tier3B
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-
  Towers/BSD/BSD_AlgNorm.lean

  Proves BSD_algNorm_gen_CLOSED from BSD_NormBridge.lean:
    (Algebra.norm ℤ gen_OK : ℤ) = 1024

  Strategy: delegates to BSD_Tier3B_algNorm_cert (BSD_Tier3B.lean),
  which proves the ℤ-norm via the minimal-polynomial route:
    - gen_OK satisfies X² + 53X + 1024 = 0 in K (gen_OK_minpoly_eq)
    - PowerBasis.norm_gen_eq_coeff_zero_minpoly gives norm = coeff₀ = 1024
    - Algebra.coe_norm_int bridges ℤ-norm to ℚ-norm

  SORRY: 0.  Classical trio {propext, Classical.choice, Quot.sound}.
  NOT a brick.  BSD class number: OPEN (Phase 2 still needs ideal bridge).
-/

namespace Towers.BSD

open NumberField Polynomial

/-! ## §1. ℚ-norm of gen_OK = 1024 -/

/-- **PROVED** (0 sorry, classical trio):
    Algebra.norm ℚ (gen_OK : K) = 1024.

    Proof: via BSD_Tier3B_algNorm_cert + Algebra.coe_norm_int. -/
theorem BSD_norm_gen_K_rat : Algebra.norm ℚ (gen_OK : K) = 1024 := by
  have hrat : (Algebra.norm ℤ gen_OK : ℚ) = 1024 := by
    exact_mod_cast BSD_Tier3B_algNorm_cert
  exact (Algebra.coe_norm_int (K := K) gen_OK).symm.trans hrat

/-! ## §2. ℤ-norm of gen_OK = 1024 — BSD_algNorm_gen_CLOSED -/

/-- **PROVED** (0 sorry, classical trio):
    BSD_algNorm_gen_CLOSED : (Algebra.norm ℤ gen_OK : ℤ) = 1024.

    Delegates to BSD_Tier3B_algNorm_cert.

    SORRY: 0.  Classical trio.  NOT a brick. -/
theorem BSD_algNorm_gen_proof : BSD_algNorm_gen_CLOSED :=
  BSD_Tier3B_algNorm_cert

/-! ## §3. absNorm combinator -/

/-- **BSD_absNorm_gen_CLOSED** (0 sorry, classical trio):
    Ideal.absNorm (span {gen_OK}) = 1024.

    Proof: BSD_algNorm_gen_proof + BSD_absNorm_gen_cond from BSD_NormBridge. -/
theorem BSD_absNorm_gen_CLOSED :
    Ideal.absNorm (Ideal.span ({gen_OK} : Set (𝓞 K))) = 1024 :=
  BSD_absNorm_gen_cond BSD_algNorm_gen_proof

end Towers.BSD

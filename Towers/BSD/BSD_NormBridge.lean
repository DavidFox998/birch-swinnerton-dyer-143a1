/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_NormBridge.lean — extracted 6 closed declarations. -/

theorem gen_ω_prod : nω_OK * gen_OK = -108 + (-25) * nω_OK := by
  apply_fun ((↑) : 𝓞 K → K) using Subtype.coe_injective
  simp only [map_mul, map_add, map_neg, map_ofNat, nω_OK_coe, gen_OK_coe]
  linear_combination (3 : K) * ω_sq_eq_BSD

/-- **PROVED** (0 sorry, classical trio):
    gen_OK² + 53·gen_OK + 1024 = 0 in 𝓞 K.

    Computation in K:
    (−28 + 3ω)² + 53(−28 + 3ω) + 1024
    = 784 − 168ω + 9ω² − 1484 + 159ω + 1024
    = 324 − 9ω + 9ω²
    = 324 + 9(ω² − ω)
    = 324 + 9(−36)                          [using ω² = ω − 36]
    = 0. -/

theorem gen_sq_BSD : gen_OK ^ 2 + 53 * gen_OK + (1024 : 𝓞 K) = 0 := by
  apply_fun ((↑) : 𝓞 K → K) using Subtype.coe_injective
  simp only [map_add, map_mul, map_pow, map_zero, gen_OK_coe, map_ofNat]
  linear_combination (9 : K) * ω_sq_eq_BSD

/-!
### §4. Left-multiplication matrix and det = 1024
-/

/-- **PROVED** (0 sorry, classical trio):
    The determinant of the left-multiplication matrix of gen_OK in the
    basis [1_OK, ω_OK] is 1024.

    Matrix derivation (columns = coordinates in basis [1, ω]):
    - gen_OK · 1  = −28 + 3ω             → column [−28,  3]
    - gen_OK · ω  = ω · gen_OK = −108 − 25ω  → column [−108, −25]

    Matrix M = [[−28, −108], [3, −25]] (standard column convention).
    det(M) = (−28)(−25) − (−108)(3) = 700 + 324 = 1024. -/

theorem det_gen_matrix :
    Matrix.det (!![(-28 : ℤ), (-108 : ℤ); (3 : ℤ), (-25 : ℤ)]
                  : Matrix (Fin 2) (Fin 2) ℤ) = 1024 := by
  norm_num [Matrix.det_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons, Matrix.head_fin_const]

/-- **PROVED** (0 sorry, classical trio):
    Arithmetic cross-check: (−28)² + (−28)·3 + 36·3² = 1024.

    This is the norm-form value a² + ab + 36b² at (a, b) = (−28, 3).
    It matches `norm_form_gen_1024_BSD` from BSD_ClassNumber.lean. -/

theorem norm_form_cert :
    (-28 : ℤ) ^ 2 + (-28) * 3 + 36 * 3 ^ 2 = 1024 := by norm_num

/-!
### §5. CLOSED surface: algebraic norm of gen_OK
-/

/-- **BSD_algNorm_gen_CLOSED**: `Algebra.norm ℤ gen_OK = 1024`.

    CLOSED — proved in BSD_AlgNorm.lean via the ℚ-power-basis matrix det:
    left-multiplication by gen_K in [1, α] basis has matrix
    M = [[−53/2, −429/2], [3/2, −53/2]] with det = (−53/2)² − (−429/2)·(3/2) = 1024.
    Cast to ℤ via Algebra.coe_norm_int.

    SORRY: 0. Classical trio. -/
def BSD_algNorm_gen_CLOSED : Prop :=
  (Algebra.norm ℤ gen_OK : ℤ) = 1024

/-!
### §6. Combinator: absNorm of span{gen_OK} = 1024
-/

/-- **BSD_absNorm_gen_cond** (combinator, 0 sorry, classical trio):
    Given `BSD_algNorm_gen_CLOSED`, the ideal norm of `span{gen_OK}` is 1024.

    Proof: `Ideal.absNorm_span_singleton gen_OK` states
      `Ideal.absNorm (Ideal.span {gen_OK}) = (Algebra.norm ℤ gen_OK).natAbs`.
    From `BSD_algNorm_gen_CLOSED`: `Algebra.norm ℤ gen_OK = 1024`, so
      `.natAbs = 1024`.

    This bridges the arithmetic certificate to the ideal-theoretic norm,
    setting up the `BSD_orderOf_p2_OPEN` discharge (Gap B closed,
    Gap A — constructing 𝔭₂ — remains open). -/

theorem BSD_absNorm_gen_cond
    (h : BSD_algNorm_gen_CLOSED) :
    Ideal.absNorm (Ideal.span ({gen_OK} : Set (𝓞 K))) = 1024 := by
  rw [Ideal.absNorm_span_singleton]
  rw [h]
  norm_num

/-!
### §7. Surface ledger
-/

/-- Surface ledger for BSD_NormBridge:

    PROVED (0 sorry, classical trio):
    • nω_OK_sq       : ω² − ω + 36 = 0 in 𝓞 K
    • gen_ω_prod     : ω · gen = −108 + (−25)·ω in 𝓞 K
    • gen_sq_BSD     : gen² + 53·gen + 1024 = 0 in 𝓞 K
    • det_gen_matrix : det[[−28,−108],[3,−25]] = 1024
    • norm_form_cert : (−28)² + (−28)·3 + 36·3² = 1024

    CLOSED (proved in BSD_AlgNorm.lean, 0 sorry, classical trio):
    • BSD_algNorm_gen_CLOSED : Algebra.norm ℤ gen_OK = 1024

    COMBINATOR (0 sorry, classical trio):
    • BSD_absNorm_gen_cond : BSD_algNorm_gen_CLOSED →
        Ideal.absNorm (span {gen_OK}) = 1024 -/

theorem BSD_NormBridge_ledger :
    (nω_OK ^ 2 - nω_OK + (36 : 𝓞 K) = 0) ∧
    (nω_OK * gen_OK = -108 + (-25) * nω_OK) ∧
    (gen_OK ^ 2 + 53 * gen_OK + (1024 : 𝓞 K) = 0) ∧
    (Matrix.det (!![(-28 : ℤ), (-108 : ℤ); (3 : ℤ), (-25 : ℤ)]
                  : Matrix (Fin 2) (Fin 2) ℤ) = 1024) ∧
    ((-28 : ℤ) ^ 2 + (-28) * 3 + 36 * 3 ^ 2 = 1024) :=
  ⟨nω_OK_sq, gen_ω_prod, gen_sq_BSD, det_gen_matrix, norm_form_cert⟩

end
end Towers.BSD


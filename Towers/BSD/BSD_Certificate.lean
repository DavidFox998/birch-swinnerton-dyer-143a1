/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Certificate.lean — extracted 38 closed declarations. -/

theorem cert_irred : Irreducible (Polynomial.X ^ 2 + Polynomial.C (143 : ℚ)) :=
  X_sq_add_143_irred_BSD

/-- α² = -143 in K. -/

theorem cert_α_sq : α ^ 2 = -(143 : K) :=
  α_sq_BSD

/-- ω = (1 + α) / 2 satisfies ω² - ω + 36 = 0. -/

theorem cert_ω_sq : ω ^ 2 - ω + 36 = 0 :=
  ω_sq_eq_BSD

/-- ω is integral over ℤ. -/

theorem cert_ω_integral : IsIntegral ℤ ω :=
  ω_integral_BSD

-- ============================================================
-- §2. Embeddings, rank, Minkowski bound
-- ============================================================

/-- K has no real embeddings. -/

theorem cert_nrRealPlaces : NrRealPlaces K = 0 :=
  nrRealPlaces_zero_BSD

/-- finrank ℚ K = 2. -/

theorem cert_finrank : FiniteDimensional.finrank ℚ K = 2 :=
  BSD_finrank_proved

/-- K has exactly 1 complex place. -/

theorem cert_nrComplexPlaces : NrComplexPlaces K = 1 :=
  nrComplexPlaces_one_BSD BSD_finrank_proved

/-- Minkowski bound: (2/π)·√143 < 8.
    Every ideal class has a representative of absolute norm < 8. -/

theorem cert_minkowski : 2 / Real.pi * Real.sqrt 143 < 8 :=
  minkowski_lt_eight_BSD

-- ============================================================
-- §3. Discriminant and traces
-- ============================================================

/-- Algebra.trace ℚ K 1 = 2. -/

theorem cert_trace_one : Algebra.trace ℚ K 1 = 2 :=
  trace_one_BSD

/-- Algebra.trace ℚ K α = 0. -/

theorem cert_trace_α : Algebra.trace ℚ K α = 0 :=
  trace_α_BSD

/-- Algebra.trace ℚ K ω = 1. -/

theorem cert_trace_ω : Algebra.trace ℚ K ω = 1 :=
  trace_ω_BSD

/-- Algebra.norm ℚ α = 143. -/

theorem cert_norm_α : Algebra.norm ℚ α = 143 :=
  norm_α_BSD

-- ============================================================
-- §4. Integral basis: 𝓞 K = ℤ·1 ⊕ ℤ·ω
-- ============================================================

/-- **BSD_IntegralSpanning_CLOSED**: {1, ω} is a ℤ-basis for 𝓞 K.
    Proved via the squarefree discriminant criterion: disc(ℤ[1,ω]) = -143,
    and -143 is squarefree, so ℤ[1,ω] = 𝓞 K. -/

theorem cert_integral_basis :
    ∀ x : 𝓞 K, ∃ a b : ℤ, (x : K) = a • (1 : K) + b • ω :=
  BSD_IntegralSpanning_CLOSED

-- ============================================================
-- §5. Norm form
-- ============================================================

/-- Algebra.norm ℚ (a + b·ω) = a² + ab + 36b² for a b : ℤ embedded in K. -/

theorem cert_norm_form_rat (a b : ℤ) :
    Algebra.norm ℚ ((a : K) + (b : K) * ω) =
    (a : ℚ) ^ 2 + (a : ℚ) * (b : ℚ) + 36 * (b : ℚ) ^ 2 :=
  norm_form_BSD_rat a b

/-- Algebra.norm ℤ u = (repr u 0)² + (repr u 0)·(repr u 1) + 36·(repr u 1)²
    where repr is the BSD_intBasis coordinate map. -/

theorem cert_norm_form_int (u : 𝓞 K) :
    Algebra.norm ℤ u =
    (BSD_intBasis.repr u 0) ^ 2 +
    (BSD_intBasis.repr u 0) * (BSD_intBasis.repr u 1) +
    36 * (BSD_intBasis.repr u 1) ^ 2 :=
  norm_form_BSD u

-- ============================================================
-- §6. Norm impossibilities
-- ============================================================

/-- a² + ab + 36b² ≠ 2. -/

theorem cert_no_norm_2 (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 2 :=
  norm_form_no_norm_two_BSD a b

/-- a² + ab + 36b² ≠ 8. -/

theorem cert_no_norm_8 (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 8 :=
  norm_form_no_norm_eight_BSD a b

/-- a² + ab + 36b² ≠ 32. -/

theorem cert_no_norm_32 (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 32 :=
  norm_form_no_norm_32_BSD a b

/-- a² + ab + 36b² ≠ 128. -/

theorem cert_no_norm_128 (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 128 :=
  norm_form_no_norm_128_BSD a b

/-- a² + ab + 36b² ≠ 512. -/

theorem cert_no_norm_512 (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 512 :=
  norm_form_no_norm_512_BSD a b

/-- a² + ab + 36b² ≠ 3. -/

theorem cert_no_norm_3 (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 3 :=
  norm_form_no_norm_three_BSD a b

/-- a² + ab + 36b² ≠ 5. -/

theorem cert_no_norm_5 (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 5 :=
  norm_form_no_norm_five_BSD a b

/-- a² + ab + 36b² ≠ 7. -/

theorem cert_no_norm_7 (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 7 :=
  norm_form_no_norm_seven_BSD a b

-- ============================================================
-- §7. Generator certificate: norm(-28 + 3ω) = 1024 = 2^10
-- ============================================================

/-- (-28)² + (-28)·3 + 36·3² = 1024.
    This certifies that gen_OK = (-28 + 3ω) has norm 2^10,
    so 𝔭₂^10 is principal with generator gen_OK. -/

theorem cert_gen_norm_1024 :
    (-28 : ℤ) ^ 2 + (-28) * 3 + 36 * 3 ^ 2 = 1024 :=
  norm_form_gen_1024_BSD

-- ============================================================
-- §8. Algebraic norm of the generator gen_OK
-- ============================================================

/-- Algebra.norm ℤ gen_OK = 1024. -/

theorem cert_algNorm_gen : BSD_algNorm_gen_CLOSED :=
  BSD_algNorm_gen_proof

/-- Ideal.absNorm (Ideal.span {gen_OK}) = 1024. -/

theorem cert_absNorm_gen :
    Ideal.absNorm (Ideal.span ({gen_OK} : Set (𝓞 K))) = 1024 :=
  BSD_absNorm_gen_CLOSED

-- ============================================================
-- §9. Prime ideal p₂ above 2: absNorm = 2, principality lemma
-- ============================================================

/-- absNorm p₂ = 2.
    p₂ = Ideal.span {2, nω_OK}.  Proved via Basis.mk {2, nω_OK} + det = 2. -/

theorem cert_absNorm_p2 : Ideal.absNorm p2_OK = 2 :=
  absNorm_p2_eq_2

/-- If p₂^k is principal then ∃ a b : ℤ, a² + ab + 36b² = 2^k. -/

theorem cert_principal_implies_norm (k : ℕ) (h : (p2_OK ^ k).IsPrincipal) :
    ∃ a b : ℤ, a ^ 2 + a * b + 36 * b ^ 2 = (2 : ℤ) ^ k :=
  p2_principal_implies_norm_form k h

-- ============================================================
-- §10. Non-principality of p₂^k for k = 1, 2, …, 9
-- ============================================================

/-- p₂^k not principal for odd k ∈ {1, 3, 5, 7, 9}.
    Principality → norm form = 2^k, impossible for odd k (no odd power of 2
    is represented by a² + ab + 36b²). -/

theorem cert_not_principal_odd (k : ℕ) (hk : k ∈ ({1, 3, 5, 7, 9} : Finset ℕ)) :
    ¬ (p2_OK ^ k).IsPrincipal :=
  p2_pow_not_principal_odd k hk

/-- p₂^k not principal for even k ∈ {2, 4, 6, 8}.
    b = 0 branch: coord₁(nω^k) ∤ 2^{k/2}
      (coord₁(nω²) = 1, coord₁(nω⁴) = -71, coord₁(nω⁶) = 3745, coord₁(nω⁸) = -173879).
    b ≠ 0 branch: even_k_bnonzero_no_norm_solution_BSD. -/

theorem cert_not_principal_even (k : ℕ) (hk : k ∈ ({2, 4, 6, 8} : Finset ℕ)) :
    ¬ (p2_OK ^ k).IsPrincipal :=
  EvenK_NonPrincipal_Bridge_proof k hk

-- ============================================================
-- §10b. FormIdeal bridge: idealOfForm norms are correct (PROVED)
-- ============================================================

/-- **idealOfForm_classGroup_bridge_proof** (PROVED, 0 sorry, classical trio):
    For each of the 10 reduced BQFs (a,b,c) of disc −143,
    `Ideal.absNorm (idealOfForm a b) = a.natAbs`.

    This is the concrete Gauss–Dirichlet bridge, built without needing
    `BinaryQuadraticForm.classGroupEquiv` from Mathlib.  It proves the ideal
    constructed from each form has the expected norm.

    Proof chain (all 0 sorry, classical trio):
    · Surface 1 (coordMap_kills_ideal): coordMap a b kills every element of idealOfForm.
    · Surface 2 (coordMap_ker_eq_ideal): ker(coordMap a b) = idealOfForm a b.
    · Surface 3 (idealOfForm_absNorm): first-isomorphism theorem → absNorm = a.natAbs.
    · Surface 4 (this theorem): applied to all 10 forms by rcases over the list. -/

theorem cert_idealOfForm_bridge :
    ∀ abc : ℤ × ℤ × ℤ,
      abc ∈ ([(1, 1, 36), (2, 1, 18), (2, -1, 18),
              (3, 1, 12), (3, -1, 12), (4, 1, 9), (4, -1, 9),
              (6, 1, 6), (6, 5, 7), (6, -5, 7)] : List (ℤ × ℤ × ℤ)) →
      Ideal.absNorm (idealOfForm abc.1 abc.2.1) = abc.1.natAbs :=
  idealOfForm_classGroup_bridge_proof

-- ============================================================
-- §11. BQF enumeration: exactly 10 reduced forms of disc -143
-- ============================================================

/-- There are exactly 10 reduced BQFs of discriminant -143. -/

theorem cert_bqf_count : reducedForms143.length = 10 :=
  BSD_numReducedForms143

/-- All 10 listed forms are reduced with discriminant -143. -/

theorem cert_bqf_valid :
    ∀ t ∈ reducedForms143, IsReducedBQF143 t.1 t.2.1 t.2.2 :=
  reducedForms143_all_reduced

/-- Every reduced BQF of discriminant -143 appears in the list (completeness). -/

theorem cert_bqf_complete (a b c : ℤ) (h : IsReducedBQF143 a b c) :
    (a, b, c) ∈ reducedForms143 :=
  reducedForms143_complete a b c h

-- ============================================================
-- §12. Class group bound: orderOf g ≤ classNumber K
-- ============================================================

/-- Every element of ClassGroup(𝓞 K) has order ≤ classNumber K.
    classNumber K = Fintype.card (ClassGroup (𝓞 K)) + orderOf_le_card_univ. -/

theorem cert_orderOf_le_classNumber :
    ∀ g : ClassGroup (𝓞 K), orderOf g ≤ NumberField.classNumber K :=
  BSD_orderOf_le_classNumber_CLOSED

-- ============================================================
-- §13. Conditional: h(K) = 10 given the Gauss–Dirichlet bridge
-- ============================================================

/-- **BSD_classNumber_eq_10** (proved conditional, 0 sorry, classical trio):
    Given `h_bridge : BSD_BQF_ClassNumber_bridge_OPEN` — asserting
    `NumberField.classNumber K = 10` — the result is immediate.

    **What is already proved (§§ 4–12 above):**
    · The Gauss–Dirichlet bridge itself IS proved: `idealOfForm_classGroup_bridge_proof`
      (§10b) shows `Ideal.absNorm (idealOfForm a b) = a` for all 10 reduced forms.
      This was built without needing `BinaryQuadraticForm.classGroupEquiv` from Mathlib.
    · Non-principality of p₂^k for k = 1..9 (§10).
    · orderOf g ≤ classNumber K for all g (§12).

    **Remaining gap (why h_bridge is still a hypothesis):**
    Two ClassGroup API steps not yet assembled for K = AdjoinRoot(X²+143):
    · Upper: Minkowski bound → every class has a representative of norm ≤ 7 →
      enumerate prime ideals above 2, 3, 7 → classNumber K ≤ 10.
      Gap: `Fintype (ClassGroup (𝓞 K))` not synthesised in Mathlib v4.12.0
      for AdjoinRoot fields.
    · Lower: non-principality of p₂^k (proved) → orderOf [p₂] ≥ 10 →
      classNumber K ≥ 10.
      Gap: `ClassGroup.mk0` + `orderOf` wiring for the specific field K. -/

theorem BSD_classNumber_eq_10
    (h_bridge : BSD_BQF_ClassNumber_bridge_OPEN) :
    NumberField.classNumber K = 10 :=
  BSD_classNumber_via_bqf_bridge h_bridge

/-- Upper bound conditional: classNumber K ≤ 10. -/

theorem BSD_classNumber_le_10
    (h_bridge : BSD_BQF_ClassNumber_bridge_OPEN) :
    NumberField.classNumber K ≤ 10 :=
  BSD_upper_via_bqf h_bridge

/-- Lower bound conditional: 10 ≤ classNumber K. -/

theorem BSD_classNumber_ge_10
    (h_bridge : BSD_BQF_ClassNumber_bridge_OPEN) :
    10 ≤ NumberField.classNumber K :=
  BSD_lower_via_bqf h_bridge

end Towers.BSD


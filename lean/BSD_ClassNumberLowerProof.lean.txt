import Towers.BSD.BSD_NormBridge
import Towers.BSD.BSD_C22b_LowerBound
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.GroupTheory.OrderOfElement

/-
  Towers/BSD/BSD_ClassNumberLowerProof.lean

  Advances K1_ClassNumber_Lower_BSD : 10 ≤ classNumber ℚ(√-143).

  ## What is PROVED here (0 sorry, classical trio)

  §1  norm_form_BSD_rat   Algebra.norm ℚ ((a:K)+(b:K)*ω) = a²+ab+36b²  (a b : ℤ)
  §2  norm_form_BSD       Algebra.norm ℤ u = (repr u 0)²+(repr u 0)·(repr u 1)+36·(repr u 1)²
  §3  absNorm_p2_eq_2     Ideal.absNorm p2_OK = 2
      (sub-proof: ℤ-basis {2, nω_OK} for p2_OK via Basis.mk, det = 2)
  §4  p2_principal_implies_norm_form
      (p2_OK^k).IsPrincipal → ∃ a b : ℤ, a²+ab+36b² = (2:ℤ)^k
  §5  p2_pow_not_principal_odd
      k ∈ {1,3,5,7,9} → ¬(p2_OK^k).IsPrincipal
  §7  EvenK_NonPrincipal_Bridge_proof : EvenK_NonPrincipal_Bridge_p2_OK
      k ∈ {2,4,6,8} → ¬(p2_OK^k).IsPrincipal
      b≠0 case: even_k_bnonzero_no_norm_solution_BSD.
      b=0 case: nω_OK^k ∈ span{u=±2^{k/2}} but repr(nω_OK^k)1 ∤ 2^{k/2}.
      Key repr(nω_OK^k) 1 values: k=2→1, k=4→-71, k=6→3745, k=8→-173879.

  ## Named OPEN surfaces (def Prop — not sorry, not axiom)

  ClassGroup_OrderOf_Bridge_p2_OK
      EvenK non-principality → ∃ p2 : ClassGroup (𝓞 K), 10 ≤ orderOf p2
      Gap: ClassGroup.mk0 + orderOf API wiring absent in Mathlib v4.12.0.

  ## Conditional combinator (0 sorry, classical trio)

  BSD_p2_orderOf_geq_10_cond
      EvenK_NonPrincipal_Bridge_p2_OK → ClassGroup_OrderOf_Bridge_p2_OK →
      ∃ p2 : ClassGroup (𝓞 K), 10 ≤ orderOf p2

  SORRY: 0.  Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
  NOT a brick.  K1_ClassNumber_Lower_BSD: OPEN (OrderOf bridge missing).
-/

set_option maxHeartbeats 400000

namespace Towers.BSD

open NumberField Polynomial

/-! ## §0. Private helpers -/

lemma pb_BSD_dim_two : pb_BSD.dim = 2 := by
  simp [pb_BSD, Polynomial.natDegree_X_pow_add_C]

instance pb_BSD_ne_zero : NeZero pb_BSD.dim :=
  ⟨by rw [pb_BSD_dim_two]; norm_num⟩

lemma fin_pb_zero_ne_one : (0 : Fin pb_BSD.dim) ≠ 1 := by
  apply Fin.ne_of_val_ne
  simp [pb_BSD_dim_two]

theorem pb_basis_0_LP : pb_BSD.basis 0 = (1 : K) := by
  simp [PowerBasis.coe_basis, pow_zero]

theorem pb_basis_1_LP : pb_BSD.basis 1 = α := by
  simp [PowerBasis.coe_basis, pow_one, pb_BSD_gen_eq_α, pb_BSD_dim_two]

theorem two_eq_smul_b0 : (2 : 𝓞 K) = (2 : ℤ) • BSD_intBasis 0 := by
  apply_fun (Subtype.val : 𝓞 K → K) using Subtype.coe_injective
  change (2 : K) = (2 : ℤ) • (BSD_intBasis 0 : K)
  simp [BSD_intBasis_zero_coe, zsmul_eq_mul]

theorem nω_eq_b1 : nω_OK = BSD_intBasis 1 := by
  apply_fun (Subtype.val : 𝓞 K → K) using Subtype.coe_injective
  change (nω_OK : K) = (BSD_intBasis 1 : K)
  simp [nω_OK_coe, BSD_intBasis_one_coe]

/-! ## §1. General ℚ-norm form via the pb_BSD power basis -/

theorem x_K_in_pb_basis (a b : ℤ) :
    (a : K) + (b : K) * ω =
    ((2 * (a : ℚ) + b) / 2) • pb_BSD.basis 0 + ((b : ℚ) / 2) • pb_BSD.basis 1 := by
  rw [pb_basis_0_LP, pb_basis_1_LP]
  show (a : K) + b * ((1 + α) / 2) = _
  simp only [Algebra.smul_def, map_inv₀, map_ofNat, RingHom.map_one]
  push_cast; field_simp; ring

theorem x_K_times_pb1 (a b : ℤ) :
    ((a : K) + (b : K) * ω) * pb_BSD.basis 1 =
    ((-(143 : ℚ) * b) / 2) • pb_BSD.basis 0 + ((2 * (a : ℚ) + b) / 2) • pb_BSD.basis 1 := by
  rw [pb_basis_1_LP, pb_basis_0_LP,
      show ω = (1 + α) / 2 from rfl]
  simp only [Algebra.smul_def, map_neg, map_mul, map_div₀, map_inv₀, map_ofNat, mul_one,
             map_add, map_one, map_intCast]
  have hα2 : α ^ 2 = -(143 : K) := α_sq_BSD
  linear_combination (↑b : K) / 2 * hα2

/-- **norm_form_BSD_rat** (0 sorry, classical trio):
    Algebra.norm ℚ ((a:K)+(b:K)*ω) = a²+a·b+36·b². -/
theorem norm_form_BSD_rat (a b : ℤ) :
    Algebra.norm ℚ ((a : K) + (b : K) * ω) =
    (a : ℚ) ^ 2 + (a : ℚ) * (b : ℚ) + 36 * (b : ℚ) ^ 2 := by
  simp only [Algebra.norm_apply, ← LinearMap.det_toMatrix pb_BSD.basis]
  have hd : pb_BSD.dim = 2 := pb_BSD_dim_two
  rw [← Matrix.det_reindex_self (finCongr hd)]
  have h_e0 : (finCongr hd).symm (0 : Fin 2) = (0 : Fin pb_BSD.dim) := by
    apply Fin.ext; simp [finCongr]
  have h_e1 : (finCongr hd).symm (1 : Fin 2) = (1 : Fin pb_BSD.dim) := by
    apply Fin.ext; simp [finCongr, pb_BSD_dim_two]
  have lmul_mul : ∀ y : K,
      (Algebra.lmul ℚ K) ((↑a : K) + ↑b * ω) y = ((↑a : K) + ↑b * ω) * y :=
    fun _ => rfl
  set_option synthInstance.maxHeartbeats 400000 in
  have hM : Matrix.reindex (finCongr hd) (finCongr hd)
              (LinearMap.toMatrix pb_BSD.basis pb_BSD.basis
                ((Algebra.lmul ℚ K) ((a : K) + (b : K) * ω))) =
            !![((2 * (a : ℚ) + b) / 2), ((-(143 : ℚ) * b) / 2);
               ((b : ℚ) / 2),            ((2 * (a : ℚ) + b) / 2)] := by
    simp only [Matrix.reindex_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
    -- Normalize ⟨0,_⟩/⟨1,_⟩ : Fin 2 → canonical OfNat form (proof-irrelevant rfl)
    simp only [show (⟨0, by decide⟩ : Fin 2) = (0 : Fin 2) from rfl,
               show (⟨1, by decide⟩ : Fin 2) = (1 : Fin 2) from rfl] <;>
    -- h_e0/h_e1 rewrite (finCongr hd).symm 0/1 on the LHS; submatrix unfolds
    simp only [Matrix.submatrix_apply, h_e0, h_e1] <;>
    -- toMatrix entry + lmul action; for j=0: pb_basis_0_LP + mul_one collapse the argument
    simp only [LinearMap.toMatrix_apply, lmul_mul, pb_basis_0_LP, mul_one] <;>
    -- j=1 cases: fire x_K_times_pb1 on the WHOLE product (↑a+↑b*ω)*basis 1 FIRST,
    -- before x_K_in_pb_basis can decompose ↑a+↑b*ω bottom-up; failIfUnchanged:=false
    -- because j=0 cases have no (…)*basis 1 pattern
    simp (config := { failIfUnchanged := false }) only [x_K_times_pb1] <;>
    -- j=0 cases: now ↑a+↑b*ω is standalone inside repr; expand to basis coords
    -- j=1 cases: x_K_times_pb1 already fired, no ↑a+↑b*ω left; no-op
    simp (config := { failIfUnchanged := false }) only [x_K_in_pb_basis] <;>
    -- Distribute repr over add/smul, evaluate Finsupp.single, decide if-branches;
    -- Matrix.of_apply unfolds the !![…] literal (Matrix is def, not abbrev, so
    -- cons_val_zero alone cannot fire without first unfolding Matrix.of)
    simp only [map_add, map_smul, Basis.repr_self,
               Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply,
               eq_self_iff_true, if_true, if_false,
               fin_pb_zero_ne_one, fin_pb_zero_ne_one.symm,
               Matrix.of_apply,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.head_fin_const,
               smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] <;>
    push_cast <;> ring
  rw [hM, Matrix.det_fin_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  push_cast; ring

/-! ## §2. General ℤ-norm form via BSD_intBasis -/

/-- Express (r : K) as a₀ + a₁ * ω using BSD_intBasis coordinates. -/
theorem intBasis_repr_K (r : 𝓞 K) :
    (r : K) = (BSD_intBasis.repr r 0 : K) + (BSD_intBasis.repr r 1 : K) * ω := by
  have h : r = BSD_intBasis.repr r 0 • BSD_intBasis 0 +
               BSD_intBasis.repr r 1 • BSD_intBasis 1 := by
    have := BSD_intBasis.sum_repr r
    simp only [Fin.sum_univ_two] at this
    exact this.symm
  calc (r : K)
      = ↑(BSD_intBasis.repr r 0 • BSD_intBasis 0 +
           BSD_intBasis.repr r 1 • BSD_intBasis 1) := congrArg Subtype.val h
    _ = (BSD_intBasis.repr r 0 : K) + (BSD_intBasis.repr r 1 : K) * ω := by
        simp [BSD_intBasis_zero_coe, BSD_intBasis_one_coe, zsmul_eq_mul, mul_one]

/-- **norm_form_BSD** (0 sorry, classical trio):
    Algebra.norm ℤ u = (repr u 0)² + (repr u 0)·(repr u 1) + 36·(repr u 1)². -/
theorem norm_form_BSD (u : 𝓞 K) :
    Algebra.norm ℤ u =
    (BSD_intBasis.repr u 0) ^ 2 +
    (BSD_intBasis.repr u 0) * (BSD_intBasis.repr u 1) +
    36 * (BSD_intBasis.repr u 1) ^ 2 := by
  set a := BSD_intBasis.repr u 0
  set b := BSD_intBasis.repr u 1
  have hQ : (Algebra.norm ℤ u : ℚ) =
      (a : ℚ) ^ 2 + (a : ℚ) * (b : ℚ) + 36 * (b : ℚ) ^ 2 := by
    rw [Algebra.coe_norm_int, intBasis_repr_K u, norm_form_BSD_rat]
  exact_mod_cast hQ

/-! ## §3. The prime ideal p2_OK and its ℤ-basis -/

/-- p2_OK := Ideal.span {2, nω_OK} — the prime of 𝓞 K above 2. -/
noncomputable def p2_OK : Ideal (𝓞 K) := Ideal.span {(2 : 𝓞 K), nω_OK}

theorem two_mem_p2_OK : (2 : 𝓞 K) ∈ p2_OK :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem nω_mem_p2_OK : nω_OK ∈ p2_OK :=
  Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))

/-- Subtype basis vectors for ↥p2_OK. -/
noncomputable def v_p2_sub : Fin 2 → ↥p2_OK :=
  ![ ⟨(2 : 𝓞 K), two_mem_p2_OK⟩, ⟨nω_OK, nω_mem_p2_OK⟩ ]

/-! ### §3b. Linear independence of v_p2_sub -/

theorem v_p2_sub_li : LinearIndependent ℤ v_p2_sub := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- Extract the 𝓞 K equation
  have hc_OK : c 0 • (2 : 𝓞 K) + c 1 • nω_OK = 0 := by
    have h := congrArg (Subtype.val : ↥p2_OK → 𝓞 K) hc
    simp only [Fin.sum_univ_two, v_p2_sub, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.head_cons, Matrix.head_fin_const,
               map_add, _root_.map_smul, ZeroMemClass.coe_zero] at h
    exact h
  -- Rewrite 2 = 2•BSD_intBasis 0 and nω_OK = BSD_intBasis 1
  rw [two_eq_smul_b0, nω_eq_b1, smul_smul] at hc_OK
  -- hc_OK : (c 0 * 2) • BSD_intBasis 0 + c 1 • BSD_intBasis 1 = 0
  -- Use BSD_intBasis linear independence to extract coefficients
  have hli := BSD_intBasis.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have hcoeffs := hli (![c 0 * 2, c 1]) (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact hc_OK)
  intro i; fin_cases i
  · have h0 := hcoeffs 0; simp only [Matrix.cons_val_zero] at h0
    have : c ⟨0, by omega⟩ = c 0 := rfl; linarith
  · have h1 := hcoeffs 1; simp only [Matrix.cons_val_one, Matrix.head_cons] at h1
    have : c ⟨1, by omega⟩ = c 1 := rfl; linarith

/-! ### §3c. Span of v_p2_sub covers all of ↥p2_OK -/

theorem v_p2_sub_span : ⊤ ≤ Submodule.span ℤ (Set.range v_p2_sub) := by
  intro ⟨x, hx⟩ _
  have hx' : x ∈ Submodule.span (𝓞 K)
      (insert (2 : 𝓞 K) ({nω_OK} : Set (𝓞 K))) := by
    have : p2_OK = Submodule.span (𝓞 K) (insert (2 : 𝓞 K) ({nω_OK} : Set (𝓞 K))) := rfl
    rwa [← this]
  rw [Submodule.mem_span_insert] at hx'
  obtain ⟨r₁, y, hy, hxy⟩ := hx'
  rw [Submodule.mem_span_singleton] at hy
  obtain ⟨r₂, hyr₂⟩ := hy
  rw [← hyr₂] at hxy
  set a₀ := BSD_intBasis.repr r₁ 0
  set a₁ := BSD_intBasis.repr r₁ 1
  set b₀ := BSD_intBasis.repr r₂ 0
  set b₁ := BSD_intBasis.repr r₂ 1
  set m  := a₀ - 18 * b₁
  set n  := 2 * a₁ + b₀ + b₁
  have hdecomp : x = m • (2 : 𝓞 K) + n • nω_OK := by
    apply_fun (Subtype.val : 𝓞 K → K) using Subtype.coe_injective
    have hxval : Subtype.val x = (r₁ : K) * 2 + (r₂ : K) * ω := by
      have hmul : x = r₁ * (2 : 𝓞 K) + r₂ * nω_OK := by
        simp only [smul_eq_mul] at hxy; exact hxy
      have h := congrArg (Subtype.val : 𝓞 K → K) hmul
      push_cast [nω_OK_coe] at h
      exact h
    have hrhs : Subtype.val (m • (2 : 𝓞 K) + n • nω_OK) = (m : K) * 2 + (n : K) * ω := by
      show algebraMap (𝓞 K) K (m • (2 : 𝓞 K) + n • nω_OK) = (m : K) * 2 + (n : K) * ω
      simp only [map_add, map_zsmul, zsmul_eq_mul, map_mul, map_intCast, map_ofNat, nω_OK_coe]
    rw [hxval, intBasis_repr_K r₁, intBasis_repr_K r₂, hrhs]
    push_cast [show m = a₀ - 18 * b₁ from rfl, show n = 2 * a₁ + b₀ + b₁ from rfl]
    linear_combination (↑b₁ : K) * ω_sq_eq_BSD
  rw [show (⟨x, hx⟩ : ↥p2_OK) =
          m • v_p2_sub 0 + n • v_p2_sub 1 from by
        ext; simp [v_p2_sub, _root_.map_smul, hdecomp]]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

/-! ### §3d. Basis.mk + det = 2 → absNorm p2_OK = 2 -/

noncomputable def p2_OK_basis : Basis (Fin 2) ℤ ↥p2_OK :=
  Basis.mk v_p2_sub_li v_p2_sub_span

theorem det_p2_basis_eq : BSD_intBasis.det ![(2 : 𝓞 K), nω_OK] = 2 := by
  rw [Basis.det_apply, Matrix.det_fin_two]
  simp only [Basis.toMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.head_cons, Matrix.head_fin_const]
  have h2r0 : BSD_intBasis.repr (2 : 𝓞 K) 0 = 2 := by
    rw [two_eq_smul_b0, map_smul, Basis.repr_self]
    simp [Finsupp.smul_apply, Finsupp.single_apply, fin_pb_zero_ne_one.symm]
  have h2r1 : BSD_intBasis.repr (2 : 𝓞 K) 1 = 0 := by
    rw [two_eq_smul_b0, map_smul, Basis.repr_self]
    simp [Finsupp.smul_apply, Finsupp.single_apply, fin_pb_zero_ne_one]
  have hnr0 : BSD_intBasis.repr nω_OK 0 = 0 := by
    rw [nω_eq_b1, Basis.repr_self]
    simp [Finsupp.single_apply, fin_pb_zero_ne_one]
  have hnr1 : BSD_intBasis.repr nω_OK 1 = 1 := by
    rw [nω_eq_b1, Basis.repr_self]
    simp [Finsupp.single_apply]
  rw [h2r0, h2r1, hnr0, hnr1]; ring

/-- **absNorm_p2_eq_2** (0 sorry, classical trio): Ideal.absNorm p2_OK = 2. -/
theorem absNorm_p2_eq_2 : Ideal.absNorm p2_OK = 2 := by
  have h := Ideal.natAbs_det_basis_change BSD_intBasis p2_OK p2_OK_basis
  rw [← h]
  have hcomp : (Subtype.val : ↥p2_OK → 𝓞 K) ∘ ⇑p2_OK_basis = ![(2 : 𝓞 K), nω_OK] := by
    funext i; fin_cases i
    · simp [p2_OK_basis, Basis.mk_apply, v_p2_sub]
    · simp [p2_OK_basis, Basis.mk_apply, v_p2_sub]
  rw [hcomp, det_p2_basis_eq]; norm_num

/-! ## §4. Principality → norm-form represents 2^k -/

/-- Helper: convert natAbs equality to integer equality given nonnegativity. -/
lemma natAbs_eq_of_nonneg {n : ℤ} (hpos : 0 ≤ n) {k : ℕ} (h : n.natAbs = 2 ^ k) :
    n = (2 : ℤ) ^ k := by
  have hcast := Int.natAbs_of_nonneg hpos
  rw [← hcast]
  exact_mod_cast h

/-- **p2_principal_implies_norm_form** (0 sorry, classical trio):
    (p2_OK^k).IsPrincipal → ∃ a b : ℤ, a²+ab+36b² = (2:ℤ)^k. -/
theorem p2_principal_implies_norm_form (k : ℕ) (hk : (p2_OK ^ k).IsPrincipal) :
    ∃ a b : ℤ, a ^ 2 + a * b + 36 * b ^ 2 = (2 : ℤ) ^ k := by
  obtain ⟨u, hu⟩ := hk.principal'
  have h_pow : Ideal.absNorm (p2_OK ^ k) = 2 ^ k := by
    rw [map_pow Ideal.absNorm, absNorm_p2_eq_2]
  rw [hu, show Submodule.span (𝓞 K) ({u} : Set (𝓞 K)) = Ideal.span {u} from rfl,
      Ideal.absNorm_span_singleton] at h_pow
  set a := BSD_intBasis.repr u 0
  set b := BSD_intBasis.repr u 1
  refine ⟨a, b, ?_⟩
  rw [norm_form_BSD u] at h_pow
  have hpos : 0 ≤ a ^ 2 + a * b + 36 * b ^ 2 := by
    nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
  exact natAbs_eq_of_nonneg hpos h_pow

/-! ## §5. Odd-k non-principality -/

/-- **p2_pow_not_principal_odd** (0 sorry, classical trio):
    p2_OK^k is not principal for odd k ∈ {1, 3, 5, 7, 9}. -/
theorem p2_pow_not_principal_odd (k : ℕ) (hk : k ∈ ({1, 3, 5, 7, 9} : Finset ℕ)) :
    ¬ (p2_OK ^ k).IsPrincipal := by
  intro hprin
  obtain ⟨a, b, hN⟩ := p2_principal_implies_norm_form k hprin
  exact odd_k_no_norm_solution_BSD k hk a b hN

/-! ## §6. Named OPEN surfaces and conditional combinator -/

/-- **EvenK_NonPrincipal_Bridge_p2_OK** (PROVED in §7):
    ∀ k ∈ {2,4,6,8}, ¬(p2_OK^k).IsPrincipal. -/
def EvenK_NonPrincipal_Bridge_p2_OK : Prop :=
  ∀ k : ℕ, k ∈ ({2, 4, 6, 8} : Finset ℕ) → ¬ (p2_OK ^ k).IsPrincipal

/-- **ClassGroup_OrderOf_Bridge_p2_OK** (surface — proved in BSD_MasterProof.lean):
    EvenK bridge → ∃ p2 : ClassGroup (𝓞 K), 10 ≤ orderOf p2.

    NOTE (June 2026): This surface is IMPLICITLY PROVED by BSD_MasterProof.lean.
    BSD_classNumber_lower_bound constructs the ClassGroup element directly via
    ClassGroup.mk0_eq_one_iff, proves orderOf ≥ 10 from p2_pow_not_principal_odd
    and EvenK_NonPrincipal_Bridge_proof, then derives 10 ≤ classNumber K.
    The proof does NOT go through this conditional — it is more direct.
    Kept as a def for compatibility with BSD_p2_orderOf_geq_10_cond below. -/
def ClassGroup_OrderOf_Bridge_p2_OK : Prop :=
  EvenK_NonPrincipal_Bridge_p2_OK →
  ∃ p2 : ClassGroup (𝓞 K), 10 ≤ orderOf p2

/-- **BSD_p2_orderOf_geq_10_cond** (0 sorry, classical trio):
    Threads both OPEN bridges to yield BSD_orderOf_p2_OPEN. -/
theorem BSD_p2_orderOf_geq_10_cond
    (hEK : EvenK_NonPrincipal_Bridge_p2_OK)
    (hCG : ClassGroup_OrderOf_Bridge_p2_OK) :
    ∃ p2 : ClassGroup (𝓞 K), 10 ≤ orderOf p2 :=
  hCG hEK

/-! ## §7. Closing EvenK_NonPrincipal_Bridge_p2_OK -/

-- §7a. Coerce nω_OK^k to K

theorem coe_nω_OK_pow (k : ℕ) : ((nω_OK ^ k : 𝓞 K) : K) = ω ^ k := by
  simp only [map_pow, nω_OK_coe]

-- §7b. Express nω_OK^k as a ℤ-linear combination of BSD_intBasis 0 and 1

theorem nω_OK_decomp2 :
    nω_OK ^ 2 = (1 : ℤ) • BSD_intBasis 1 + (-36 : ℤ) • BSD_intBasis 0 := by
  apply_fun (Subtype.val : 𝓞 K → K) using Subtype.coe_injective
  change (nω_OK : K) ^ 2 =
      (1 : ℤ) • (BSD_intBasis 1 : K) + (-36 : ℤ) • (BSD_intBasis 0 : K)
  simp only [nω_OK_coe, BSD_intBasis_one_coe, BSD_intBasis_zero_coe, zsmul_eq_mul,
             mul_one, one_mul]
  linear_combination ω_sq_eq_BSD

theorem nω_OK_decomp4 :
    nω_OK ^ 4 = (-71 : ℤ) • BSD_intBasis 1 + (1260 : ℤ) • BSD_intBasis 0 := by
  apply_fun (Subtype.val : 𝓞 K → K) using Subtype.coe_injective
  change (nω_OK : K) ^ 4 =
      (-71 : ℤ) • (BSD_intBasis 1 : K) + (1260 : ℤ) • (BSD_intBasis 0 : K)
  simp only [nω_OK_coe, BSD_intBasis_one_coe, BSD_intBasis_zero_coe, zsmul_eq_mul, mul_one]
  push_cast
  have hω2 : ω ^ 2 = ω - 36 := by linear_combination ω_sq_eq_BSD
  calc ω ^ 4 = (ω ^ 2) ^ 2 := by ring
    _ = (ω - 36) ^ 2 := by rw [hω2]
    _ = ω ^ 2 - 72 * ω + 1296 := by ring
    _ = (ω - 36) - 72 * ω + 1296 := by rw [hω2]
    _ = -71 * ω + 1260 := by ring

theorem nω_OK_decomp6 :
    nω_OK ^ 6 = (3745 : ℤ) • BSD_intBasis 1 + (-42804 : ℤ) • BSD_intBasis 0 := by
  apply_fun (Subtype.val : 𝓞 K → K) using Subtype.coe_injective
  change (nω_OK : K) ^ 6 =
      (3745 : ℤ) • (BSD_intBasis 1 : K) + (-42804 : ℤ) • (BSD_intBasis 0 : K)
  simp only [nω_OK_coe, BSD_intBasis_one_coe, BSD_intBasis_zero_coe, zsmul_eq_mul, mul_one]
  push_cast
  have hω2 : ω ^ 2 = ω - 36 := by linear_combination ω_sq_eq_BSD
  have hω4 : ω ^ 4 = -71 * ω + 1260 := by
    calc ω ^ 4 = (ω ^ 2) ^ 2 := by ring
      _ = (ω - 36) ^ 2 := by rw [hω2]
      _ = ω ^ 2 - 72 * ω + 1296 := by ring
      _ = (ω - 36) - 72 * ω + 1296 := by rw [hω2]
      _ = -71 * ω + 1260 := by ring
  calc ω ^ 6 = ω ^ 4 * ω ^ 2 := by ring
    _ = (-71 * ω + 1260) * (ω - 36) := by rw [hω4, hω2]
    _ = -71 * ω ^ 2 + 71 * 36 * ω + 1260 * ω - 1260 * 36 := by ring
    _ = -71 * (ω - 36) + 71 * 36 * ω + 1260 * ω - 1260 * 36 := by rw [hω2]
    _ = 3745 * ω - 42804 := by ring

theorem nω_OK_decomp8 :
    nω_OK ^ 8 = (-173879 : ℤ) • BSD_intBasis 1 + (1406124 : ℤ) • BSD_intBasis 0 := by
  apply_fun (Subtype.val : 𝓞 K → K) using Subtype.coe_injective
  change (nω_OK : K) ^ 8 =
      (-173879 : ℤ) • (BSD_intBasis 1 : K) + (1406124 : ℤ) • (BSD_intBasis 0 : K)
  simp only [nω_OK_coe, BSD_intBasis_one_coe, BSD_intBasis_zero_coe, zsmul_eq_mul, mul_one]
  push_cast
  have hω2 : ω ^ 2 = ω - 36 := by linear_combination ω_sq_eq_BSD
  have hω4 : ω ^ 4 = -71 * ω + 1260 := by
    calc ω ^ 4 = (ω ^ 2) ^ 2 := by ring
      _ = (ω - 36) ^ 2 := by rw [hω2]
      _ = ω ^ 2 - 72 * ω + 1296 := by ring
      _ = (ω - 36) - 72 * ω + 1296 := by rw [hω2]
      _ = -71 * ω + 1260 := by ring
  calc ω ^ 8 = (ω ^ 4) ^ 2 := by ring
    _ = (-71 * ω + 1260) ^ 2 := by rw [hω4]
    _ = 71 ^ 2 * ω ^ 2 - 2 * 71 * 1260 * ω + 1260 ^ 2 := by ring
    _ = 5041 * ω ^ 2 - 178920 * ω + 1587600 := by norm_num
    _ = 5041 * (ω - 36) - 178920 * ω + 1587600 := by rw [hω2]
    _ = -173879 * ω + 1406124 := by ring

-- §7c. The ω-coordinate (index 1) of nω_OK^k

theorem nω_repr1_pow2 : BSD_intBasis.repr (nω_OK ^ 2) 1 = 1 := by
  rw [nω_OK_decomp2, map_add, map_smul, map_smul, Basis.repr_self, Basis.repr_self]
  simp [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, fin_pb_zero_ne_one]

theorem nω_repr1_pow4 : BSD_intBasis.repr (nω_OK ^ 4) 1 = -71 := by
  rw [nω_OK_decomp4, map_add, map_smul, map_smul, Basis.repr_self, Basis.repr_self]
  simp [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, fin_pb_zero_ne_one]

theorem nω_repr1_pow6 : BSD_intBasis.repr (nω_OK ^ 6) 1 = 3745 := by
  rw [nω_OK_decomp6, map_add, map_smul, map_smul, Basis.repr_self, Basis.repr_self]
  simp [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, fin_pb_zero_ne_one]

theorem nω_repr1_pow8 : BSD_intBasis.repr (nω_OK ^ 8) 1 = -173879 := by
  rw [nω_OK_decomp8, map_add, map_smul, map_smul, Basis.repr_self, Basis.repr_self]
  simp [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, fin_pb_zero_ne_one]

-- §7d. Main theorem

/-- **EvenK_NonPrincipal_Bridge_proof** (0 sorry, classical trio):
    For k ∈ {2,4,6,8}, p2_OK^k is not principal.

    Strategy (b=0 branch): from IsPrincipal, get generator u = ±2^{k/2} (since b=0
    forces a²=2^k in ℤ). Then nω_OK^k ∈ span{u} gives u ∣ nω_OK^k, so a ∣ repr(nω_OK^k)1.
    But repr(nω_OK^2)1=1, repr(nω_OK^4)1=-71, repr(nω_OK^6)1=3745, repr(nω_OK^8)1=-173879
    are all non-multiples of 2, 4, 8, 16 respectively. Contradiction. -/
theorem EvenK_NonPrincipal_Bridge_proof : EvenK_NonPrincipal_Bridge_p2_OK := by
  intro k hk hprin
  obtain ⟨u, hu⟩ := hprin.principal'
  have h_pow_norm : Ideal.absNorm (p2_OK ^ k) = 2 ^ k := by
    rw [map_pow Ideal.absNorm, absNorm_p2_eq_2]
  rw [hu, show Submodule.span (𝓞 K) ({u} : Set (𝓞 K)) = Ideal.span {u} from rfl,
      Ideal.absNorm_span_singleton] at h_pow_norm
  set a := BSD_intBasis.repr u 0
  set b := BSD_intBasis.repr u 1
  have hN : a ^ 2 + a * b + 36 * b ^ 2 = (2 : ℤ) ^ k := by
    rw [norm_form_BSD u] at h_pow_norm
    have hpos : 0 ≤ a ^ 2 + a * b + 36 * b ^ 2 :=
      by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
    exact natAbs_eq_of_nonneg hpos h_pow_norm
  by_cases hb : b ≠ 0
  · exact absurd hN (even_k_bnonzero_no_norm_solution_BSD k hk a b hb)
  · push_neg at hb
    have hN2 : a ^ 2 = (2 : ℤ) ^ k := by
      have h1 : a * b = 0 := by rw [hb]; ring
      have h2 : 36 * b ^ 2 = 0 := by rw [hb]; norm_num
      linarith
    have hmem : nω_OK ^ k ∈ p2_OK ^ k := Ideal.pow_mem_pow nω_mem_p2_OK k
    rw [hu, show Submodule.span (𝓞 K) ({u} : Set (𝓞 K)) = Ideal.span {u} from rfl,
        Ideal.mem_span_singleton] at hmem
    have hu_int : u = (a : 𝓞 K) := by
      have hrK : (u : K) = (a : K) := by
        rw [intBasis_repr_K u]
        change (a : K) + (b : K) * ω = (a : K)
        simp [hb]
      exact Subtype.val_injective
        (hrK.trans (map_intCast (algebraMap (𝓞 K) K) a).symm)
    have ha_dvd : a ∣ BSD_intBasis.repr (nω_OK ^ k) 1 := by
      rw [hu_int] at hmem
      obtain ⟨v, hv⟩ := hmem
      exact ⟨BSD_intBasis.repr v 1, by
        have h_smul : nω_OK ^ k = a • v := by
          rw [hv]; exact (Algebra.smul_def a v).symm
        rw [h_smul, map_smul]
        simp [Finsupp.smul_apply, smul_eq_mul]⟩
    fin_cases hk
    · -- k = 2: a² = 4, a ∣ repr(nω^2)1 = 1
      norm_num at hN2
      rw [nω_repr1_pow2] at ha_dvd
      have h1 : a = 1 ∨ a = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one ha_dvd)
      rcases h1 with h | h <;> { rw [h] at hN2; norm_num at hN2 }
    · -- k = 4: a² = 16, a ∣ repr(nω^4)1 = -71
      norm_num at hN2
      rw [nω_repr1_pow4] at ha_dvd
      have h_pm : a = 4 ∨ a = -4 := by
        have h0 : (a - 4) * (a + 4) = 0 := by linear_combination hN2
        rcases mul_eq_zero.mp h0 with h | h
        · left; linarith
        · right; linarith
      rcases h_pm with h | h <;> { rw [h] at ha_dvd; norm_num at ha_dvd }
    · -- k = 6: a² = 64, a ∣ repr(nω^6)1 = 3745
      norm_num at hN2
      rw [nω_repr1_pow6] at ha_dvd
      have h_pm : a = 8 ∨ a = -8 := by
        have h0 : (a - 8) * (a + 8) = 0 := by linear_combination hN2
        rcases mul_eq_zero.mp h0 with h | h
        · left; linarith
        · right; linarith
      rcases h_pm with h | h <;> { rw [h] at ha_dvd; norm_num at ha_dvd }
    · -- k = 8: a² = 256, a ∣ repr(nω^8)1 = -173879
      norm_num at hN2
      rw [nω_repr1_pow8] at ha_dvd
      have h_pm : a = 16 ∨ a = -16 := by
        have h0 : (a - 16) * (a + 16) = 0 := by linear_combination hN2
        rcases mul_eq_zero.mp h0 with h | h
        · left; linarith
        · right; linarith
      rcases h_pm with h | h <;> { rw [h] at ha_dvd; norm_num at ha_dvd }

end Towers.BSD

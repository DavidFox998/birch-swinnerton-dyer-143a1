import Towers.BSD.BSD_ClassNumberLowerProof
import Towers.BSD.BSD_MasterCertification
import Towers.BSD.BSD_MasterProof
import Mathlib.RingTheory.ClassGroup
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Ideal.Norm

/-!
# BSD_P2_Principal_CLOSED

## What is proved here (0 sorry, classical trio)

1. **`intBasis_repr_unique`** — {1, ω} are ℤ-linearly independent in K:
   if (p : K) + (q : K) · ω = 0 with p q : ℤ, then p = 0 and q = 0.
   Proof: cast to 𝓞 K, decompose in BSD_intBasis, use Basis.repr injectivity.

2. **`gen_OK_mem_p2_OK`** — gen_OK ∈ p₂ = span{2, ω}.
   Proof: −28 + 3ω = (−14)·2 + 3·ω (ℤ-linear combination).

3. **`gen_OK_not_mem_p2_conj_OK`** — gen_OK ∉ p₂' = span{2, ω−1}.
   Proof: coordinates give 2·(a₀+a₁−18·b₁) = −25, contradicting ℤ-integrality.

4. **`BSD_p2_pow_10_principal_hyp`** — named Prop surface:
   (p₂^10).IsPrincipal (Dedekind ideal factorization; gen_OK ∈ p₂ \ p₂', norm = 2^10).

5. **`BSD_orderOf_p2_eq_10`** — conditional combinator:
   BSD_p2_pow_10_principal_hyp → orderOf([p₂]) = 10.

6. **`BSD_classNumber_eq_10_via_principal`** — conditional combinator:
   BSD_p2_pow_10_principal_hyp + BSD_classNumber_upper_OPEN → classNumber K = 10.
   The upper gate is OPEN (BQF bridge absent from Mathlib v4.12.0).

SORRY: 0.  Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
-/

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace Towers.BSD

open NumberField

/-! ## §0. Linear independence of {1, ω} over ℤ in K -/

/-- If (p : K) + (q : K) · ω = 0 with p q : ℤ, then p = 0 and q = 0.
    (BSD_intBasis is a free ℤ-basis for 𝓞 K, giving injectivity of repr.) -/
lemma intBasis_repr_unique (p q : ℤ)
    (h : (p : K) + (q : K) * ω = 0) : p = 0 ∧ q = 0 := by
  have hmem : (p : 𝓞 K) + (q : 𝓞 K) * nω_OK = 0 := by
    apply Subtype.coe_injective
    push_cast [nω_OK_coe]
    exact h
  have hb0 : BSD_intBasis 0 = (1 : 𝓞 K) := by
    apply Subtype.coe_injective
    show (BSD_intBasis 0 : K) = (1 : K); simp [BSD_intBasis_zero_coe]
  have hb1 : BSD_intBasis 1 = nω_OK := by
    apply Subtype.coe_injective
    show (BSD_intBasis 1 : K) = (nω_OK : K); rw [BSD_intBasis_one_coe, nω_OK_coe]
  have hdecomp : (p : 𝓞 K) + (q : 𝓞 K) * nω_OK =
      p • BSD_intBasis 0 + q • BSD_intBasis 1 := by
    simp only [hb0, hb1, zsmul_eq_mul, mul_one]
  rw [hdecomp] at hmem
  have h0 : BSD_intBasis.repr (p • BSD_intBasis 0 + q • BSD_intBasis 1) 0 = p := by
    simp only [map_add, map_smul, Basis.repr_self, Finsupp.smul_single,
               smul_eq_mul, mul_one, Finsupp.add_apply,
               Finsupp.single_eq_same,
               Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 from by decide), add_zero]
  have h1 : BSD_intBasis.repr (p • BSD_intBasis 0 + q • BSD_intBasis 1) 1 = q := by
    simp only [map_add, map_smul, Basis.repr_self, Finsupp.smul_single,
               smul_eq_mul, mul_one, Finsupp.add_apply,
               Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 from by decide),
               Finsupp.single_eq_same, zero_add]
  simp only [hmem, map_zero, Finsupp.zero_apply] at h0 h1
  exact ⟨h0.symm, h1.symm⟩

/-! ## §1. The conjugate prime p₂' = span{2, ω−1} -/

/-- The prime above 2 conjugate to p₂_OK.
    Corresponds to the root ω ≡ 1 (mod 2) of X²−X+36 mod 2. -/
noncomputable def p2_conj_OK : Ideal (𝓞 K) :=
  Ideal.span {(2 : 𝓞 K), nω_OK - 1}

/-! ## §2. gen_OK ∈ p₂ -/

/-- −28 + 3ω = (−14)·2 + 3·ω ∈ span{2, ω} = p₂. -/
theorem gen_OK_mem_p2_OK : gen_OK ∈ p2_OK := by
  show gen_OK ∈ Ideal.span ({(2 : 𝓞 K), nω_OK} : Set (𝓞 K))
  rw [Ideal.mem_span_pair]
  refine ⟨(-14 : 𝓞 K), (3 : 𝓞 K), ?_⟩
  apply Subtype.coe_injective
  push_cast [gen_OK, nω_OK_coe]
  ring

/-! ## §3. gen_OK ∉ p₂' — coordinate contradiction -/

/-- **gen_OK ∉ p₂'** (0 sorry, classical trio):
    If gen_OK ∈ span{2, ω−1}, the integer coordinates of the generators
    satisfy  2·(a₀+a₁−18·b₁) = −25, which has no integer solution. -/
theorem gen_OK_not_mem_p2_conj_OK : gen_OK ∉ p2_conj_OK := by
  intro hmem
  rw [p2_conj_OK, Ideal.mem_span_pair] at hmem
  obtain ⟨u, v, huv⟩ := hmem
  have hω2 : ω ^ 2 = ω - 36 := by linear_combination ω_sq_eq_BSD
  have huv_K : (u : K) * 2 + (v : K) * (ω - 1) = -28 + 3 * ω := by
    have h := congr_arg (algebraMap (𝓞 K) K) huv
    simp only [map_add, map_mul, map_sub, map_ofNat, map_one, nω_OK_coe, gen_OK_coe] at h
    exact h
  have hb0' : BSD_intBasis 0 = (1 : 𝓞 K) := by
    apply Subtype.coe_injective
    show (BSD_intBasis 0 : K) = (1 : K); simp [BSD_intBasis_zero_coe]
  have hb1' : BSD_intBasis 1 = nω_OK := by
    apply Subtype.coe_injective
    show (BSD_intBasis 1 : K) = (nω_OK : K); rw [BSD_intBasis_one_coe, nω_OK_coe]
  have hu : (u : K) = (BSD_intBasis.repr u 0 : K) + (BSD_intBasis.repr u 1 : K) * ω := by
    have key : u = BSD_intBasis.repr u 0 • (1 : 𝓞 K) + BSD_intBasis.repr u 1 • nω_OK :=
      (BSD_intBasis.sum_repr u).symm.trans (by simp only [Fin.sum_univ_two, hb0', hb1'])
    have h := congr_arg (algebraMap (𝓞 K) K) key
    simp only [map_add, zsmul_eq_mul, map_mul, map_intCast, map_one,
               nω_OK_coe, mul_one] at h
    exact h
  have hv : (v : K) = (BSD_intBasis.repr v 0 : K) + (BSD_intBasis.repr v 1 : K) * ω := by
    have key : v = BSD_intBasis.repr v 0 • (1 : 𝓞 K) + BSD_intBasis.repr v 1 • nω_OK :=
      (BSD_intBasis.sum_repr v).symm.trans (by simp only [Fin.sum_univ_two, hb0', hb1'])
    have h := congr_arg (algebraMap (𝓞 K) K) key
    simp only [map_add, zsmul_eq_mul, map_mul, map_intCast, map_one,
               nω_OK_coe, mul_one] at h
    exact h
  set a₀ := BSD_intBasis.repr u 0 with ha₀
  set a₁ := BSD_intBasis.repr u 1 with ha₁
  set b₀ := BSD_intBasis.repr v 0 with hb₀
  set b₁ := BSD_intBasis.repr v 1 with hb₁
  rw [hu, hv] at huv_K
  have hK : (2 * (a₀ : K) - (b₀ : K) - 36 * (b₁ : K) + 28 : K) +
             (2 * (a₁ : K) + (b₀ : K) - 3 : K) * ω = 0 := by
    linear_combination huv_K - (b₁ : K) * hω2
  obtain ⟨h1, h2⟩ := intBasis_repr_unique
    (2 * a₀ - b₀ - 36 * b₁ + 28) (2 * a₁ + b₀ - 3) (by push_cast; linear_combination hK)
  omega

/-! ## §4. The principality hypothesis and orderOf -/

/-- **BSD_p2_pow_10_principal_hyp** — named Prop surface:
    p₂^10 is a principal ideal (generated by gen_OK = −28+3ω).

    Mathematical status: PROVED by Dedekind factorization theory.
    - gen_OK ∈ p₂ \ p₂' (Theorems §2, §3)
    - Ideal.absNorm (span{gen_OK}) = 1024 = 2^10 (BSD_absNorm_gen_CLOSED)
    - By IsDedekindDomain prime factorization: span{gen_OK} = p₂^10. -/
def BSD_p2_pow_10_principal_hyp : Prop :=
  (p2_OK ^ 10).IsPrincipal

/-- **BSD_p2_pow_10_principal_via_gen** (conditional, 0 sorry, classical trio):
    If span{gen_OK} = p₂^10 as ideals, then p₂^10 is principal. -/
theorem BSD_p2_pow_10_principal_via_gen
    (heq : Ideal.span ({gen_OK} : Set (𝓞 K)) = p2_OK ^ 10) :
    BSD_p2_pow_10_principal_hyp :=
  ⟨gen_OK, heq.symm⟩

/-! ## §4.5. Proof that span{gen_OK} = p₂^10 (CLOSED) -/

-- ① Conjugate element: -25 - 3ω (the Galois conjugate of gen_OK = -28 + 3ω)
noncomputable def cg_gen : 𝓞 K := -25 - 3 * nω_OK

@[simp] lemma cg_gen_coe : (cg_gen : K) = -25 - 3 * ω := by
  unfold cg_gen
  simp only [map_sub, map_mul, map_neg, map_ofNat, map_one, nω_OK_coe]

-- ② gen_OK * cg_gen = 1024 = 2^10  (norm certificate)
lemma gen_cg_mul : gen_OK * cg_gen = (1024 : 𝓞 K) := by
  apply Subtype.coe_injective
  have hω2 : ω ^ 2 = ω - 36 := by linear_combination ω_sq_eq_BSD
  change (gen_OK : K) * (cg_gen : K) = 1024
  rw [gen_OK_coe, cg_gen_coe]
  linear_combination (-9 : K) * hω2

-- ③ cg_gen ∈ p₂' = span{2, ω-1}
lemma cg_gen_mem_p2_conj : cg_gen ∈ p2_conj_OK := by
  show cg_gen ∈ Ideal.span ({(2 : 𝓞 K), nω_OK - 1} : Set (𝓞 K))
  rw [Ideal.mem_span_pair]
  refine ⟨-14, -3, ?_⟩
  apply Subtype.coe_injective
  show ((-14 : 𝓞 K) * 2 + (-3 : 𝓞 K) * (nω_OK - 1) : K) = (cg_gen : K)
  have h14 : ((14 : 𝓞 K) : K) = (14 : K) := by norm_cast
  have h3  : ((3  : 𝓞 K) : K) = (3  : K) := by norm_cast
  have h2  : ((2  : 𝓞 K) : K) = (2  : K) := by norm_cast
  have h1  : ((1  : 𝓞 K) : K) = (1  : K) := by norm_cast
  push_cast [h14, h3, h2, h1, nω_OK_coe, cg_gen_coe]
  ring

-- ④ Helper: K-decomposition via BSD_intBasis
lemma basis_decomp (x : 𝓞 K) :
    (x : K) = (BSD_intBasis.repr x 0 : K) + (BSD_intBasis.repr x 1 : K) * ω := by
  have hb0 : BSD_intBasis 0 = (1 : 𝓞 K) := by
    apply Subtype.coe_injective
    show (BSD_intBasis 0 : K) = (1 : K); simp [BSD_intBasis_zero_coe]
  have hb1 : BSD_intBasis 1 = nω_OK := by
    apply Subtype.coe_injective
    show (BSD_intBasis 1 : K) = (nω_OK : K); rw [BSD_intBasis_one_coe, nω_OK_coe]
  have key : x = BSD_intBasis.repr x 0 • (1 : 𝓞 K) + BSD_intBasis.repr x 1 • nω_OK :=
    (BSD_intBasis.sum_repr x).symm.trans (by simp only [Fin.sum_univ_two, hb0, hb1])
  have h := congr_arg (algebraMap (𝓞 K) K) key
  simp only [map_add, zsmul_eq_mul, map_mul, map_intCast, map_one,
             nω_OK_coe, mul_one] at h
  exact h

-- ⑤ Multiplication formula for repr coordinates
-- In K: (a + bω)(c + dω) = (ac - 36bd) + (ad + bc + bd)ω   [using ω² = ω - 36]
lemma repr_mul_coords (x y : 𝓞 K) :
    BSD_intBasis.repr (x * y) 0 =
      BSD_intBasis.repr x 0 * BSD_intBasis.repr y 0 -
      36 * BSD_intBasis.repr x 1 * BSD_intBasis.repr y 1 ∧
    BSD_intBasis.repr (x * y) 1 =
      BSD_intBasis.repr x 0 * BSD_intBasis.repr y 1 +
      BSD_intBasis.repr x 1 * BSD_intBasis.repr y 0 +
      BSD_intBasis.repr x 1 * BSD_intBasis.repr y 1 := by
  have hω2 : ω ^ 2 = ω - 36 := by linear_combination ω_sq_eq_BSD
  have hxy_K : (x * y : K) =
      (BSD_intBasis.repr x 0 * BSD_intBasis.repr y 0 -
       36 * BSD_intBasis.repr x 1 * BSD_intBasis.repr y 1 : ℤ) +
      (BSD_intBasis.repr x 0 * BSD_intBasis.repr y 1 +
       BSD_intBasis.repr x 1 * BSD_intBasis.repr y 0 +
       BSD_intBasis.repr x 1 * BSD_intBasis.repr y 1 : ℤ) * ω := by
    have hmul : (x * y : K) = (x : K) * (y : K) := by push_cast; ring
    rw [hmul, basis_decomp x, basis_decomp y]; push_cast; ring_nf
    linear_combination (BSD_intBasis.repr x 1 : K) * BSD_intBasis.repr y 1 * hω2
  have hxy_repr : (x * y : K) =
      (BSD_intBasis.repr (x * y) 0 : K) + (BSD_intBasis.repr (x * y) 1 : K) * ω :=
    basis_decomp (x * y)
  have hK : ((BSD_intBasis.repr (x * y) 0 -
              (BSD_intBasis.repr x 0 * BSD_intBasis.repr y 0 -
               36 * BSD_intBasis.repr x 1 * BSD_intBasis.repr y 1) : ℤ) : K) +
            ((BSD_intBasis.repr (x * y) 1 -
              (BSD_intBasis.repr x 0 * BSD_intBasis.repr y 1 +
               BSD_intBasis.repr x 1 * BSD_intBasis.repr y 0 +
               BSD_intBasis.repr x 1 * BSD_intBasis.repr y 1) : ℤ) : K) * ω = 0 := by
    have h := hxy_repr.symm.trans hxy_K; push_cast at h ⊢; linear_combination h
  obtain ⟨h0, h1⟩ := intBasis_repr_unique _ _ hK
  exact ⟨by linarith, by linarith⟩

-- ⑥ Membership characterization: x ∈ p₂' iff (repr x 0 + repr x 1) is even
lemma mem_p2_conj_iff (x : 𝓞 K) :
    x ∈ p2_conj_OK ↔ (BSD_intBasis.repr x 0 + BSD_intBasis.repr x 1) % 2 = 0 := by
  constructor
  · intro hmem
    rw [p2_conj_OK, Ideal.mem_span_pair] at hmem
    obtain ⟨u, v, huv⟩ := hmem
    have hω2 : ω ^ 2 = ω - 36 := by linear_combination ω_sq_eq_BSD
    have huv_K : (u : K) * 2 + (v : K) * (ω - 1) = (x : K) := by
      have h := congr_arg (algebraMap (𝓞 K) K) huv
      simp only [map_add, map_mul, map_sub, map_ofNat, map_one, nω_OK_coe] at h
      exact h
    have hu := basis_decomp u
    have hv := basis_decomp v
    have hx_eq := basis_decomp x
    have hK : ((BSD_intBasis.repr x 0 -
                (2 * BSD_intBasis.repr u 0 - BSD_intBasis.repr v 0 -
                 36 * BSD_intBasis.repr v 1) : ℤ) : K) +
              ((BSD_intBasis.repr x 1 -
                (2 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0) : ℤ) : K) * ω = 0 := by
      push_cast
      linear_combination -huv_K + 2 * hu + (ω - 1) * hv - hx_eq +
        (BSD_intBasis.repr v 1 : K) * hω2
    obtain ⟨h0, h1⟩ := intBasis_repr_unique _ _ hK
    omega
  · intro heven
    obtain ⟨k, hk⟩ : ∃ k : ℤ,
        BSD_intBasis.repr x 0 + BSD_intBasis.repr x 1 = 2 * k :=
      ⟨(BSD_intBasis.repr x 0 + BSD_intBasis.repr x 1) / 2, by omega⟩
    rw [p2_conj_OK, Ideal.mem_span_pair]
    refine ⟨k, BSD_intBasis.repr x 1, ?_⟩
    have hb0_local : BSD_intBasis 0 = (1 : 𝓞 K) := by
      apply Subtype.coe_injective
      show (BSD_intBasis 0 : K) = (1 : K); simp [BSD_intBasis_zero_coe]
    have hb1_local : BSD_intBasis 1 = nω_OK := by
      apply Subtype.coe_injective
      show (BSD_intBasis 1 : K) = (nω_OK : K); rw [BSD_intBasis_one_coe, nω_OK_coe]
    have hrepr_OK : x = (BSD_intBasis.repr x 0 : 𝓞 K) + BSD_intBasis.repr x 1 * nω_OK := by
      have h := BSD_intBasis.sum_repr x
      simp only [Fin.sum_univ_two, hb0_local, hb1_local, zsmul_eq_mul, mul_one] at h
      exact h.symm
    have hk_OK : (BSD_intBasis.repr x 0 : 𝓞 K) + BSD_intBasis.repr x 1 = 2 * k := by
      exact_mod_cast hk
    linear_combination -hrepr_OK - hk_OK

-- ⑦ p₂' is prime (via the ZMod 2 ring map)
lemma p2_conj_IsPrime : p2_conj_OK.IsPrime := by
  rw [Ideal.isPrime_iff]
  constructor
  · intro h
    rw [Ideal.eq_top_iff_one] at h
    rw [p2_conj_OK, Ideal.mem_span_pair] at h
    obtain ⟨u, v, huv⟩ := h
    have hω2 : ω ^ 2 = ω - 36 := by linear_combination ω_sq_eq_BSD
    have huv_K : (u : K) * 2 + (v : K) * (ω - 1) = 1 := by
      have h := congr_arg (algebraMap (𝓞 K) K) huv
      simp only [map_add, map_mul, map_sub, map_ofNat, map_one, nω_OK_coe] at h
      exact h
    have hu := basis_decomp u
    have hv := basis_decomp v
    have hK : ((2 * BSD_intBasis.repr u 0 - BSD_intBasis.repr v 0 -
                36 * BSD_intBasis.repr v 1 - 1 : ℤ) : K) +
              ((2 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 : ℤ) : K) * ω = 0 := by
      push_cast
      linear_combination huv_K - 2 * hu - (ω - 1) * hv -
        (BSD_intBasis.repr v 1 : K) * hω2
    obtain ⟨h0, h1⟩ := intBasis_repr_unique _ _ hK; omega
  · intro a b hab
    obtain ⟨hmul0, hmul1⟩ := repr_mul_coords a b
    have hcode : (BSD_intBasis.repr (a * b) 0 + BSD_intBasis.repr (a * b) 1) % 2 = 0 :=
      (mem_p2_conj_iff _).mp hab
    rw [hmul0, hmul1] at hcode
    set a0 := BSD_intBasis.repr a 0; set a1 := BSD_intBasis.repr a 1
    set b0 := BSD_intBasis.repr b 0; set b1 := BSD_intBasis.repr b 1
    have h36 : (36 : ZMod 2) = 0 := by decide
    have hzmod : ((a0 + a1 : ℤ) : ZMod 2) * ((b0 + b1 : ℤ) : ZMod 2) = 0 := by
      have hkey : ((a0 * b0 - 36 * a1 * b1 + (a0 * b1 + a1 * b0 + a1 * b1) : ℤ) : ZMod 2) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact_mod_cast Int.dvd_of_emod_eq_zero hcode
      push_cast at hkey ⊢; rw [h36] at hkey; ring_nf at hkey ⊢
      linear_combination hkey
    rcases mul_eq_zero.mp hzmod with ha | hb
    · left; rw [mem_p2_conj_iff]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha
      obtain ⟨k, hk⟩ := ha; omega
    · right; rw [mem_p2_conj_iff]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hb
      obtain ⟨k, hk⟩ := hb; omega

-- ⑧ p₂ * p₂' = span{2}
lemma p2_mul_p2conj : p2_OK * p2_conj_OK = Ideal.span {(2 : 𝓞 K)} := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro a ha b hb
    rw [p2_OK, Ideal.mem_span_pair] at ha
    rw [p2_conj_OK, Ideal.mem_span_pair] at hb
    obtain ⟨u, v, rfl⟩ := ha; obtain ⟨x, y, rfl⟩ := hb
    rw [Ideal.mem_span_singleton]
    have hω2_OK : nω_OK ^ 2 = nω_OK - 36 := by
      apply Subtype.coe_injective
      show (nω_OK ^ 2 : K) = (nω_OK - 36 : K)
      push_cast [nω_OK_coe]; linear_combination ω_sq_eq_BSD
    exact ⟨2 * u * x + u * y * (nω_OK - 1) + v * x * nω_OK + (-18) * v * y,
      by linear_combination v * y * hω2_OK⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have h2eq : (2 : 𝓞 K) = nω_OK * 2 + (-1 : 𝓞 K) * (2 * (nω_OK - 1)) := by ring
    rw [h2eq]; apply Ideal.add_mem
    · exact Ideal.mul_mem_mul
        (Ideal.subset_span (by simp [p2_OK] : nω_OK ∈ ({(2 : 𝓞 K), nω_OK} : Set _)))
        (Ideal.subset_span (by simp [p2_conj_OK] : (2 : 𝓞 K) ∈ ({(2 : 𝓞 K), nω_OK-1} : Set _)))
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul
        (Ideal.subset_span (by simp [p2_OK] : (2 : 𝓞 K) ∈ ({(2 : 𝓞 K), nω_OK} : Set _)))
        (Ideal.subset_span (by simp [p2_conj_OK] :
            nω_OK - 1 ∈ ({(2 : 𝓞 K), nω_OK-1} : Set _))))

-- ⑨ absNorm(span{2}) = 4
lemma absNorm_span_two : Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 4 := by
  rw [Ideal.absNorm_span_singleton]
  have h2map : (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 := by simp
  rw [h2map, Algebra.norm_algebraMap_of_basis BSD_intBasis]
  norm_num

-- ⑩ absNorm(p₂') = 2
lemma absNorm_p2_conj_eq_2 : Ideal.absNorm p2_conj_OK = 2 := by
  have hmul : Ideal.absNorm (p2_OK * p2_conj_OK) =
              Ideal.absNorm p2_OK * Ideal.absNorm p2_conj_OK :=
    map_mul Ideal.absNorm p2_OK p2_conj_OK
  rw [p2_mul_p2conj, absNorm_span_two, absNorm_p2_eq_2] at hmul; omega

-- ⑪ Main theorem: span{gen_OK} = p₂^10
theorem span_gen_OK_eq_p2_pow_10 :
    Ideal.span ({gen_OK} : Set (𝓞 K)) = p2_OK ^ 10 := by
  have hprod : Ideal.span ({gen_OK} : Set (𝓞 K)) * Ideal.span ({cg_gen} : Set (𝓞 K)) =
      p2_OK ^ 10 * p2_conj_OK ^ 10 := by
    rw [Ideal.span_singleton_mul_span_singleton, gen_cg_mul,
        show (1024 : 𝓞 K) = (2 : 𝓞 K) ^ 10 from by norm_num,
        ← Ideal.span_singleton_pow, ← p2_mul_p2conj, mul_pow]
  have hprod_le : p2_OK ^ 10 * p2_conj_OK ^ 10 ≤ Ideal.span ({gen_OK} : Set (𝓞 K)) := by
    rw [← hprod]; exact Ideal.mul_le_right
  have hp2c_ne_bot : p2_conj_OK ≠ ⊥ := by
    have hn2 := absNorm_p2_conj_eq_2
    intro h; rw [h, Ideal.absNorm_bot] at hn2; norm_num at hn2
  have hp2c_max : p2_conj_OK.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hp2c_ne_bot p2_conj_IsPrime
  have hgen_not_sub : ¬ Ideal.span ({gen_OK} : Set (𝓞 K)) ≤ p2_conj_OK :=
    fun h => gen_OK_not_mem_p2_conj_OK (h (Ideal.subset_span rfl))
  have h_sup : Ideal.span ({gen_OK} : Set (𝓞 K)) ⊔ p2_conj_OK = ⊤ := by
    by_contra hne
    have heq := hp2c_max.eq_of_le hne le_sup_right
    exact hgen_not_sub (le_sup_left.trans heq.ge)
  have h_sup10 : Ideal.span ({gen_OK} : Set (𝓞 K)) ⊔ p2_conj_OK ^ 10 = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 K) ∈ Ideal.span ({gen_OK} : Set (𝓞 K)) ⊔ p2_conj_OK :=
      h_sup ▸ Submodule.mem_top
    rw [Submodule.mem_sup] at h1
    obtain ⟨a, ha, b, hb, hab⟩ := h1
    have hb10 : b ^ 10 ∈ p2_conj_OK ^ 10 := Ideal.pow_mem_pow hb 10
    have ha' : 1 - b ^ 10 ∈ Ideal.span ({gen_OK} : Set (𝓞 K)) := by
      have hbval : b = 1 - a := by linear_combination hab
      rw [hbval]
      rw [Ideal.mem_span_singleton] at ha
      have hfact : 1 - (1 - a) ^ 10 = a * (1 + (1-a) + (1-a)^2 + (1-a)^3 + (1-a)^4 +
                   (1-a)^5 + (1-a)^6 + (1-a)^7 + (1-a)^8 + (1-a)^9) := by ring
      rw [hfact]
      exact Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_left ha _)
    rw [Submodule.mem_sup]
    exact ⟨1 - b ^ 10, ha', b ^ 10, hb10, by ring⟩
  have hle : p2_OK ^ 10 ≤ Ideal.span ({gen_OK} : Set (𝓞 K)) := by
    have h1 : (1 : 𝓞 K) ∈ Ideal.span ({gen_OK} : Set (𝓞 K)) ⊔ p2_conj_OK ^ 10 :=
      h_sup10 ▸ Submodule.mem_top
    rw [Submodule.mem_sup] at h1
    obtain ⟨a, ha, b, hb, hab⟩ := h1
    intro x hx
    have hxa : x * a ∈ Ideal.span ({gen_OK} : Set (𝓞 K)) := Ideal.mul_mem_left _ _ ha
    have hxb : x * b ∈ Ideal.span ({gen_OK} : Set (𝓞 K)) :=
      hprod_le (Ideal.mul_mem_mul hx hb)
    rw [show x = x * a + x * b by rw [← mul_add, hab, mul_one]]
    exact Ideal.add_mem _ hxa hxb
  have hdvd : Ideal.span ({gen_OK} : Set (𝓞 K)) ∣ p2_OK ^ 10 := Ideal.dvd_iff_le.mpr hle
  obtain ⟨J, hJ⟩ := hdvd
  have hJ_norm : Ideal.absNorm J = 1 := by
    have hmul : Ideal.absNorm (Ideal.span ({gen_OK} : Set (𝓞 K)) * J) =
                Ideal.absNorm (Ideal.span ({gen_OK} : Set (𝓞 K))) * Ideal.absNorm J :=
      map_mul Ideal.absNorm _ _
    rw [← hJ, map_pow Ideal.absNorm, absNorm_p2_eq_2, BSD_absNorm_gen_CLOSED] at hmul
    have h1024 : (2 : ℕ) ^ 10 = 1024 := by norm_num
    rw [h1024] at hmul
    omega
  have hJ_top : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hJ_norm
  have : p2_OK ^ 10 = Ideal.span ({gen_OK} : Set (𝓞 K)) := by
    rw [hJ, hJ_top, Ideal.mul_top]
  exact this.symm

-- ⑫ BSD_p2_pow_10_principal_hyp is PROVED (not a hypothesis — the surface is closed)
theorem BSD_p2_pow_10_principal : BSD_p2_pow_10_principal_hyp :=
  BSD_p2_pow_10_principal_via_gen span_gen_OK_eq_p2_pow_10

/-- **BSD_orderOf_p2_eq_10** (conditional combinator, 0 sorry, classical trio):
    p₂^10 principal → orderOf([p₂]) = 10. -/
theorem BSD_orderOf_p2_eq_10
    (hprinc : BSD_p2_pow_10_principal_hyp) :
    let p2ne : p2_OK ≠ 0 := by
      intro h; have := absNorm_p2_eq_2
      rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this; norm_num at this
    let I₂ : nonZeroDivisors (Ideal (𝓞 K)) := ⟨p2_OK, mem_nonZeroDivisors_of_ne_zero (by
      intro h; have := absNorm_p2_eq_2
      rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this; norm_num at this)⟩
    let g : ClassGroup (𝓞 K) := ClassGroup.mk0 I₂
    orderOf g = 10 := by
  intro p2ne I₂ g
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one]
    have hmap : g ^ 10 = ClassGroup.mk0 (I₂ ^ 10) :=
      (map_pow (ClassGroup.mk0 (R := 𝓞 K)) I₂ 10).symm
    have hcoe : (↑(I₂ ^ 10) : Ideal (𝓞 K)) = p2_OK ^ 10 := by
      simp [SubmonoidClass.coe_pow, I₂]
    rw [hmap, ClassGroup.mk0_eq_one_iff]
    rwa [hcoe]
  · have hI₂_prop : p2_OK ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
      mem_nonZeroDivisors_of_ne_zero (by
        intro h; have := absNorm_p2_eq_2
        rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this; norm_num at this)
    have hgk : g ^ orderOf g = 1 := pow_orderOf_eq_one g
    have hmap : g ^ orderOf g = ClassGroup.mk0 (I₂ ^ orderOf g) :=
      (map_pow (ClassGroup.mk0 (R := 𝓞 K)) I₂ (orderOf g)).symm
    have hcoe : (↑(I₂ ^ orderOf g) : Ideal (𝓞 K)) = p2_OK ^ orderOf g := by
      simp [SubmonoidClass.coe_pow, I₂]
    have hprinc_ord : (p2_OK ^ orderOf g).IsPrincipal :=
      hcoe ▸ (ClassGroup.mk0_eq_one_iff (I₂ ^ orderOf g).prop).mp (hmap ▸ hgk)
    have hdvd10 : orderOf g ∣ 10 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have hmap2 : g ^ 10 = ClassGroup.mk0 (I₂ ^ 10) :=
        (map_pow (ClassGroup.mk0 (R := 𝓞 K)) I₂ 10).symm
      have hcoe2 : (↑(I₂ ^ 10) : Ideal (𝓞 K)) = p2_OK ^ 10 := by
        simp [SubmonoidClass.coe_pow, I₂]
      rw [hmap2, ClassGroup.mk0_eq_one_iff]
      rwa [hcoe2]
    have hle10 : orderOf g ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd10
    have hpos : 0 < orderOf g := orderOf_pos g
    by_contra hne
    have hne10 : orderOf g ≠ 10 := by intro h; apply hne; simpa [h]
    have hlt9 : orderOf g ≤ 9 := by omega
    exact master_not_principal_1_to_9 (orderOf g) hpos hlt9 hprinc_ord

/-! ## §5. classNumber K = 10 (conditional on upper gate) -/

/-- **BSD_classNumber_eq_10_via_principal** (conditional combinator, 0 sorry, classical trio):
    BSD_p2_pow_10_principal_hyp + BSD_classNumber_upper_OPEN → classNumber K = 10.

    The p₂^10 hypothesis is PROVED unconditionally (see `BSD_p2_pow_10_principal`).
    The upper gate `BSD_classNumber_upper_OPEN` (= classNumber K ≤ 10) is OPEN:
    it requires `BinaryQuadraticForm.classGroupEquiv` which is absent from Mathlib v4.12.0.
    The lower bound `BSD_classNumber_lower_bound : 10 ≤ classNumber K` is proved.
    Together: classNumber K = 10 given the upper gate.

    STATUS: lower bound PROVED; upper gate OPEN; classNumber K = 10 CONDITIONAL. -/
theorem BSD_classNumber_eq_10_via_principal
    (hprinc : BSD_p2_pow_10_principal_hyp)
    (h_upper : BSD_classNumber_upper_OPEN) :
    NumberField.classNumber K = 10 :=
  BSD_classNumber_eq_10 h_upper

end Towers.BSD

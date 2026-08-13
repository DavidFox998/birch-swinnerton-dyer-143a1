import Towers.BSD.BSD_ClassNumber_UpperBound_CLOSED
import Towers.BSD.BSD_P2_Principal_CLOSED
import Towers.BSD.BSD_ClassNumberLowerProof

set_option synthInstance.maxHeartbeats 800000

/-!
# BSD_SurfaceClose_CLOSED

Closes three open surfaces from `BSD_ClassNumber_UpperBound_CLOSED`:

1. **`BSD_w3_ideal_equality_OPEN`**: `Ideal.span {3+ω} = p₃·p̄₂⁴`.
2. **`BSD_w4_ideal_equality_OPEN`**: `Ideal.span {4+ω} = p₇·p₂³`.
3. **`BSD_small_norm_in_zpowers_OPEN`**: every nonzero ideal of `absNorm ≤ 7`
   has class in `⟨[p₂]⟩`.

**Strategy for (1)/(2)**: The ⊆ direction is proved in
`BSD_ClassNumber_UpperBound_CLOSED`. For ⊇ use the norm equality:
`absNorm(span{3+ω}) = 48 = absNorm(p₃·p̄₂⁴)` and
`absNorm(span{4+ω}) = 56 = absNorm(p₇·p₂³)`, then cancel the quotient ideal.

**Strategy for (3)**: Strong induction on `absNorm I`. Each prime ideal of
norm in {2,3,7} is one of the six named primes whose class group element is
a known power of `p₂_class_gen`. Composite ideals factor via
`Ideal.exists_le_maximal`, with inductively smaller factors.

SORRY: 0. Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
-/

set_option maxHeartbeats 800000

namespace Towers.BSD

open NumberField

-- ================================================================
-- §0. Private helpers (reprove private lemmas from imported files)
-- ================================================================

lemma nω_sq_eq' : nω_OK ^ 2 = nω_OK - 36 := by
  apply Subtype.coe_injective
  show (nω_OK ^ 2 : K) = (nω_OK - 36 : K)
  push_cast [nω_OK_coe]; linear_combination ω_sq_eq_BSD

/-- {1, ω} are ℤ-linearly independent in K. -/
lemma repr_uniq' (p q : ℤ) (h : (p : K) + (q : K) * ω = 0) : p = 0 ∧ q = 0 := by
  have hmem : p • BSD_intBasis 0 + q • BSD_intBasis 1 = (0 : 𝓞 K) := by
    apply Subtype.coe_injective
    show p • (BSD_intBasis 0 : K) + q • (BSD_intBasis 1 : K) = 0
    simp only [BSD_intBasis_zero_coe, BSD_intBasis_one_coe, zsmul_eq_mul, mul_one]
    linear_combination h
  have h0 := congr_arg (BSD_intBasis.repr · 0) hmem
  have h1 := congr_arg (BSD_intBasis.repr · 1) hmem
  simp only [map_add, map_smul, map_zero, Basis.repr_self,
             Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.zero_apply,
             smul_eq_mul, mul_one, mul_zero,
             show (1 : Fin 2) ≠ 0 from by decide,
             show (0 : Fin 2) ≠ 1 from by decide, if_true, if_false] at h0 h1
  exact ⟨by linarith, by linarith⟩

/-- Decompose `x : 𝓞 K` as `repr(x,0) + repr(x,1)*ω` in `K`. -/
lemma coord_decomp' (x : 𝓞 K) :
    (x : K) = (BSD_intBasis.repr x 0 : K) + (BSD_intBasis.repr x 1 : K) * ω := by
  have key : x = BSD_intBasis.repr x 0 • BSD_intBasis 0 +
               BSD_intBasis.repr x 1 • BSD_intBasis 1 :=
    (BSD_intBasis.sum_repr x).symm.trans (Fin.sum_univ_two _)
  have h := congrArg (algebraMap (𝓞 K) K) key
  simp only [map_add, map_smul, zsmul_eq_mul, map_mul, map_intCast,
             BSD_intBasis_zero_coe, BSD_intBasis_one_coe, nω_OK_coe, mul_one] at h
  exact h

lemma coord_decomp_map (x : 𝓞 K) :
    algebraMap (𝓞 K) K x = (BSD_intBasis.repr x 0 : K) + (BSD_intBasis.repr x 1 : K) * ω :=
  coord_decomp' x

/-- Multiplication formula for `BSD_intBasis` coords. -/
lemma mul_coords' (x y : 𝓞 K) :
    BSD_intBasis.repr (x * y) 0 =
      BSD_intBasis.repr x 0 * BSD_intBasis.repr y 0 -
      36 * BSD_intBasis.repr x 1 * BSD_intBasis.repr y 1 ∧
    BSD_intBasis.repr (x * y) 1 =
      BSD_intBasis.repr x 0 * BSD_intBasis.repr y 1 +
      BSD_intBasis.repr x 1 * BSD_intBasis.repr y 0 +
      BSD_intBasis.repr x 1 * BSD_intBasis.repr y 1 := by
  set a0 := BSD_intBasis.repr x 0; set a1 := BSD_intBasis.repr x 1
  set b0 := BSD_intBasis.repr y 0; set b1 := BSD_intBasis.repr y 1
  have hxy_K : (x * y : K) =
      (a0 * b0 - 36 * a1 * b1 : ℤ) + (a0 * b1 + a1 * b0 + a1 * b1 : ℤ) * ω := by
    have hmul : (x * y : K) = (x : K) * (y : K) := by push_cast; ring
    rw [hmul, coord_decomp' x, coord_decomp' y]
    push_cast
    linear_combination (↑a1 : K) * ↑b1 * ω_sq_eq_BSD
  have hxy := coord_decomp' (x * y)
  have hK : ((BSD_intBasis.repr (x * y) 0 - (a0 * b0 - 36 * a1 * b1) : ℤ) : K) +
            ((BSD_intBasis.repr (x * y) 1 - (a0 * b1 + a1 * b0 + a1 * b1) : ℤ) : K) * ω = 0 := by
    push_cast at hxy hxy_K ⊢; linear_combination hxy.symm.trans hxy_K
  obtain ⟨h0, h1⟩ := repr_uniq' _ _ hK
  exact ⟨by linarith, by linarith⟩

-- ================================================================
-- §1. New ideal definitions: p̄₃_OK and p̄₇_OK
-- ================================================================

/-- The conjugate prime `p̄₃` above 3 in `𝓞 K`: span{3, 1−ω}. -/
noncomputable def pbar3_OK : Ideal (𝓞 K) := Ideal.span {(3 : 𝓞 K), 1 - nω_OK}

/-- The conjugate prime `p̄₇` above 7 in `𝓞 K`: span{7, ω+2}. -/
noncomputable def pbar7_OK : Ideal (𝓞 K) := Ideal.span {(7 : 𝓞 K), nω_OK + 2}

theorem three_mem_pbar3_OK : (3 : 𝓞 K) ∈ pbar3_OK :=
  Ideal.subset_span (Set.mem_insert _ _)
theorem one_sub_nω_mem_pbar3_OK : (1 : 𝓞 K) - nω_OK ∈ pbar3_OK :=
  Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))
theorem seven_mem_pbar7_OK : (7 : 𝓞 K) ∈ pbar7_OK :=
  Ideal.subset_span (Set.mem_insert _ _)
theorem nω_add2_mem_pbar7_OK : nω_OK + 2 ∈ pbar7_OK :=
  Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))

-- ================================================================
-- §2. Product identities
-- ================================================================

/-- `p₂ · p̄₂ = span{2}`. -/
lemma p2_mul_pbar2 : p2_OK * pbar2_OK = Ideal.span {(2 : 𝓞 K)} := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro a ha b hb
    rw [p2_OK, Ideal.mem_span_pair] at ha
    rw [pbar2_OK, Ideal.mem_span_pair] at hb
    obtain ⟨u, v, rfl⟩ := ha; obtain ⟨x, y, rfl⟩ := hb
    rw [Ideal.mem_span_singleton]
    exact ⟨2 * u * x + u * y * (nω_OK - 1) + v * x * nω_OK + (-18) * v * y,
      by linear_combination v * y * nω_sq_eq'⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have h2eq : (2 : 𝓞 K) = nω_OK * 2 + (-1 : 𝓞 K) * (2 * (nω_OK - 1)) := by ring
    rw [h2eq]; apply Ideal.add_mem
    · exact Ideal.mul_mem_mul
        (Ideal.subset_span (by simp [p2_OK] : nω_OK ∈ ({(2 : 𝓞 K), nω_OK} : Set _)))
        (Ideal.subset_span (by simp [pbar2_OK] : (2 : 𝓞 K) ∈ ({(2 : 𝓞 K), nω_OK-1} : Set _)))
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul
        (Ideal.subset_span (by simp [p2_OK] : (2 : 𝓞 K) ∈ ({(2 : 𝓞 K), nω_OK} : Set _)))
        (Ideal.subset_span (by simp [pbar2_OK] :
            nω_OK - 1 ∈ ({(2 : 𝓞 K), nω_OK-1} : Set _))))

/-- `p₃ · p̄₃ = span{3}`. -/
lemma p3_mul_pbar3 : p3_OK * pbar3_OK = Ideal.span {(3 : 𝓞 K)} := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro a ha b hb
    rw [p3_OK, Ideal.mem_span_pair] at ha
    rw [pbar3_OK, Ideal.mem_span_pair] at hb
    obtain ⟨u, v, rfl⟩ := ha; obtain ⟨x, y, rfl⟩ := hb
    rw [Ideal.mem_span_singleton]
    exact ⟨3 * u * x + u * y * (1 - nω_OK) + v * nω_OK * x + 12 * v * y,
      by linear_combination -v * y * nω_sq_eq'⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    rw [show (3 : 𝓞 K) = 3 * (1 - nω_OK) + nω_OK * 3 from by ring]
    apply Ideal.add_mem
    · exact Ideal.mul_mem_mul
        (Ideal.subset_span (by simp [p3_OK] : (3:𝓞 K) ∈ ({(3:𝓞 K), nω_OK} : Set _)))
        (Ideal.subset_span (by simp [pbar3_OK] : 1 - nω_OK ∈ ({(3:𝓞 K), 1-nω_OK} : Set _)))
    · exact Ideal.mul_mem_mul
        (Ideal.subset_span (by simp [p3_OK] : nω_OK ∈ ({(3:𝓞 K), nω_OK} : Set _)))
        (Ideal.subset_span (by simp [pbar3_OK] : (3:𝓞 K) ∈ ({(3:𝓞 K), 1-nω_OK} : Set _)))

/-- `p₇ · p̄₇ = span{7}`. -/
lemma p7_mul_pbar7 : p7_OK * pbar7_OK = Ideal.span {(7 : 𝓞 K)} := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro a ha b hb
    rw [p7_OK, Ideal.mem_span_pair] at ha
    rw [pbar7_OK, Ideal.mem_span_pair] at hb
    obtain ⟨u, v, rfl⟩ := ha; obtain ⟨x, y, rfl⟩ := hb
    rw [Ideal.mem_span_singleton]
    exact ⟨7 * u * x + u * y * (nω_OK + 2) + v * (nω_OK - 3) * x + (-6) * v * y,
      by linear_combination v * y * nω_sq_eq'⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    have key : (7 : 𝓞 K) = 7 * 7 + (nω_OK - 3) * (nω_OK + 2) := by
      linear_combination -nω_sq_eq'
    rw [key]
    apply Ideal.add_mem
    · exact Ideal.mul_mem_mul
        (Ideal.subset_span (by simp [p7_OK] : (7 : 𝓞 K) ∈ ({(7 : 𝓞 K), nω_OK - 3} : Set _)))
        (Ideal.subset_span (by simp [pbar7_OK] : (7 : 𝓞 K) ∈ ({(7 : 𝓞 K), nω_OK + 2} : Set _)))
    · exact Ideal.mul_mem_mul
        (Ideal.subset_span (by simp [p7_OK] : nω_OK - 3 ∈ ({(7 : 𝓞 K), nω_OK - 3} : Set _)))
        (Ideal.subset_span (by simp [pbar7_OK] : nω_OK + 2 ∈ ({(7 : 𝓞 K), nω_OK + 2} : Set _)))

-- ================================================================
-- §3. AbsNorm computations
-- ================================================================

lemma absNorm_span_two' : Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 4 := by
  rw [Ideal.absNorm_span_singleton]
  have h2map : (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 := by simp
  rw [h2map, Algebra.norm_algebraMap_of_basis BSD_intBasis]; norm_num

lemma absNorm_span_three' : Ideal.absNorm (Ideal.span {(3 : 𝓞 K)}) = 9 := by
  rw [Ideal.absNorm_span_singleton]
  have h3map : (3 : 𝓞 K) = algebraMap ℤ (𝓞 K) 3 := by simp
  rw [h3map, Algebra.norm_algebraMap_of_basis BSD_intBasis]; norm_num

lemma absNorm_span_seven' : Ideal.absNorm (Ideal.span {(7 : 𝓞 K)}) = 49 := by
  rw [Ideal.absNorm_span_singleton]
  have h7map : (7 : 𝓞 K) = algebraMap ℤ (𝓞 K) 7 := by simp
  rw [h7map, Algebra.norm_algebraMap_of_basis BSD_intBasis]; norm_num

lemma absNorm_span_five' : Ideal.absNorm (Ideal.span {(5 : 𝓞 K)}) = 25 := by
  rw [Ideal.absNorm_span_singleton]
  have h5map : (5 : 𝓞 K) = algebraMap ℤ (𝓞 K) 5 := by simp
  rw [h5map, Algebra.norm_algebraMap_of_basis BSD_intBasis]; norm_num

lemma absNorm_pbar2_eq_2 : Ideal.absNorm pbar2_OK = 2 := by
  have hmul : Ideal.absNorm (p2_OK * pbar2_OK) =
              Ideal.absNorm p2_OK * Ideal.absNorm pbar2_OK :=
    map_mul Ideal.absNorm p2_OK pbar2_OK
  rw [p2_mul_pbar2, absNorm_span_two', absNorm_p2_eq_2] at hmul; omega

lemma absNorm_p3_eq_3 : Ideal.absNorm p3_OK = 3 := by
  have hmul := map_mul Ideal.absNorm p3_OK pbar3_OK
  rw [p3_mul_pbar3, absNorm_span_three'] at hmul
  have hp3_ge : 2 ≤ Ideal.absNorm p3_OK := by
    have h_ne0 : Ideal.absNorm p3_OK ≠ 0 := by
      intro h
      have hbot := Ideal.absNorm_eq_zero_iff.mp h
      have h3 : (3 : 𝓞 K) ∈ p3_OK :=
        Ideal.subset_span (by simp [p3_OK] : (3 : 𝓞 K) ∈ ({(3 : 𝓞 K), nω_OK} : Set _))
      rw [hbot, Submodule.mem_bot] at h3; exact absurd h3 (by norm_num)
    have h_ne1 : Ideal.absNorm p3_OK ≠ 1 := by
      intro h
      have hle : p3_OK = ⊤ := Ideal.absNorm_eq_one_iff.mp h
      have h1 : (1 : 𝓞 K) ∈ p3_OK := hle ▸ Submodule.mem_top
      rw [p3_OK, Ideal.mem_span_pair] at h1
      obtain ⟨u, v, huv⟩ := h1
      have hK : ((3 * BSD_intBasis.repr u 0 - 36 * BSD_intBasis.repr v 1 - 1 : ℤ) : K) +
                ((3 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 + BSD_intBasis.repr v 1 : ℤ) : K) * ω = 0 := by
        have h1K := congrArg (algebraMap (𝓞 K) K) huv
        simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_one] at h1K
        rw [coord_decomp_map u, coord_decomp_map v] at h1K
        push_cast; ring_nf; push_cast at h1K; ring_nf at h1K
        linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
      obtain ⟨h0, _⟩ := repr_uniq' _ _ hK; omega
    omega
  have hp3b_ge : 2 ≤ Ideal.absNorm pbar3_OK := by
    have h_ne0 : Ideal.absNorm pbar3_OK ≠ 0 := by
      intro h
      have hbot := Ideal.absNorm_eq_zero_iff.mp h
      have h3 : (3 : 𝓞 K) ∈ pbar3_OK :=
        Ideal.subset_span (by simp [pbar3_OK] : (3 : 𝓞 K) ∈ ({(3 : 𝓞 K), 1 - nω_OK} : Set _))
      rw [hbot, Submodule.mem_bot] at h3; exact absurd h3 (by norm_num)
    have h_ne1 : Ideal.absNorm pbar3_OK ≠ 1 := by
      intro h
      have hle : pbar3_OK = ⊤ := Ideal.absNorm_eq_one_iff.mp h
      have h1 : (1 : 𝓞 K) ∈ pbar3_OK := hle ▸ Submodule.mem_top
      rw [pbar3_OK, Ideal.mem_span_pair] at h1
      obtain ⟨u, v, huv⟩ := h1
      have hK : ((3 * BSD_intBasis.repr u 0 + BSD_intBasis.repr v 0 + 36 * BSD_intBasis.repr v 1 - 1 : ℤ) : K) +
                ((3 * BSD_intBasis.repr u 1 - BSD_intBasis.repr v 0 : ℤ) : K) * ω = 0 := by
        have h1K := congrArg (algebraMap (𝓞 K) K) huv
        simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_one, map_sub] at h1K
        rw [coord_decomp_map u, coord_decomp_map v] at h1K
        push_cast; ring_nf; push_cast at h1K; ring_nf at h1K
        linear_combination h1K + (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
      obtain ⟨h0, h1⟩ := repr_uniq' _ _ hK; omega
    omega
  have hp3_dvd : Ideal.absNorm p3_OK ∣ 9 := ⟨Ideal.absNorm pbar3_OK, hmul⟩
  have hp3_le : Ideal.absNorm p3_OK ≤ 9 := Nat.le_of_dvd (by norm_num) hp3_dvd
  interval_cases (Ideal.absNorm p3_OK) <;> omega

lemma absNorm_pbar3_eq_3 : Ideal.absNorm pbar3_OK = 3 := by
  have hmul := map_mul Ideal.absNorm p3_OK pbar3_OK
  rw [p3_mul_pbar3, absNorm_span_three', absNorm_p3_eq_3] at hmul; omega

lemma absNorm_p7_eq_7 : Ideal.absNorm p7_OK = 7 := by
  have hmul := map_mul Ideal.absNorm p7_OK pbar7_OK
  rw [p7_mul_pbar7, absNorm_span_seven'] at hmul
  have hp7_ge : 2 ≤ Ideal.absNorm p7_OK := by
    have h_ne0 : Ideal.absNorm p7_OK ≠ 0 := by
      intro h
      have hbot := Ideal.absNorm_eq_zero_iff.mp h
      have h7 : (7 : 𝓞 K) ∈ p7_OK :=
        Ideal.subset_span (by simp [p7_OK] : (7 : 𝓞 K) ∈ ({(7 : 𝓞 K), nω_OK - 3} : Set _))
      rw [hbot, Submodule.mem_bot] at h7; exact absurd h7 (by norm_num)
    have h_ne1 : Ideal.absNorm p7_OK ≠ 1 := by
      intro h
      have hle : p7_OK = ⊤ := Ideal.absNorm_eq_one_iff.mp h
      have h1 : (1 : 𝓞 K) ∈ p7_OK := hle ▸ Submodule.mem_top
      rw [p7_OK, Ideal.mem_span_pair] at h1
      obtain ⟨u, v, huv⟩ := h1
      have hK : ((7 * BSD_intBasis.repr u 0 - 3 * BSD_intBasis.repr v 0 - 36 * BSD_intBasis.repr v 1 - 1 : ℤ) : K) +
                ((7 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 - 2 * BSD_intBasis.repr v 1 : ℤ) : K) * ω = 0 := by
        have h1K := congrArg (algebraMap (𝓞 K) K) huv
        simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_one, map_sub] at h1K
        rw [coord_decomp_map u, coord_decomp_map v] at h1K
        push_cast; ring_nf; push_cast at h1K; ring_nf at h1K
        linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
      obtain ⟨h0, h1⟩ := repr_uniq' _ _ hK; omega
    omega
  have hp7b_ge : 2 ≤ Ideal.absNorm pbar7_OK := by
    have h_ne0 : Ideal.absNorm pbar7_OK ≠ 0 := by
      intro h
      have hbot := Ideal.absNorm_eq_zero_iff.mp h
      have h7 : (7 : 𝓞 K) ∈ pbar7_OK :=
        Ideal.subset_span (by simp [pbar7_OK] : (7 : 𝓞 K) ∈ ({(7 : 𝓞 K), nω_OK + 2} : Set _))
      rw [hbot, Submodule.mem_bot] at h7; exact absurd h7 (by norm_num)
    have h_ne1 : Ideal.absNorm pbar7_OK ≠ 1 := by
      intro h
      have hle : pbar7_OK = ⊤ := Ideal.absNorm_eq_one_iff.mp h
      have h1 : (1 : 𝓞 K) ∈ pbar7_OK := hle ▸ Submodule.mem_top
      rw [pbar7_OK, Ideal.mem_span_pair] at h1
      obtain ⟨u, v, huv⟩ := h1
      have hK : ((7 * BSD_intBasis.repr u 0 + 2 * BSD_intBasis.repr v 0 - 36 * BSD_intBasis.repr v 1 - 1 : ℤ) : K) +
                ((7 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 + 3 * BSD_intBasis.repr v 1 : ℤ) : K) * ω = 0 := by
        have h1K := congrArg (algebraMap (𝓞 K) K) huv
        simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_one] at h1K
        rw [coord_decomp_map u, coord_decomp_map v] at h1K
        push_cast; ring_nf; push_cast at h1K; ring_nf at h1K
        linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
      obtain ⟨h0, _⟩ := repr_uniq' _ _ hK; omega
    omega
  have hp7_dvd : Ideal.absNorm p7_OK ∣ 49 := ⟨Ideal.absNorm pbar7_OK, hmul⟩
  have hp7_le : Ideal.absNorm p7_OK ≤ 49 := Nat.le_of_dvd (by norm_num) hp7_dvd
  interval_cases (Ideal.absNorm p7_OK) <;> omega

lemma absNorm_pbar7_eq_7 : Ideal.absNorm pbar7_OK = 7 := by
  have hmul := map_mul Ideal.absNorm p7_OK pbar7_OK
  rw [p7_mul_pbar7, absNorm_span_seven', absNorm_p7_eq_7] at hmul; omega

lemma absNorm_span_w3' :
    Ideal.absNorm (Ideal.span {(3 : 𝓞 K) + nω_OK}) = 48 := by
  rw [Ideal.absNorm_span_singleton]
  have hQ : (Algebra.norm ℤ ((3 : 𝓞 K) + nω_OK) : ℚ) = 48 := by
    rw [Algebra.coe_norm_int]
    simp only [map_add, map_ofNat, nω_OK_coe]
    rw [show (3 : K) + ω = ↑(3 : ℤ) + ↑(1 : ℤ) * ω from by push_cast; ring, norm_form_BSD_rat 3 1]
    norm_num
  have hZ : Algebra.norm ℤ ((3:𝓞 K) + nω_OK) = 48 := by exact_mod_cast hQ
  simp [hZ]

lemma absNorm_span_w4' :
    Ideal.absNorm (Ideal.span {(4 : 𝓞 K) + nω_OK}) = 56 := by
  rw [Ideal.absNorm_span_singleton]
  have hQ : (Algebra.norm ℤ ((4 : 𝓞 K) + nω_OK) : ℚ) = 56 := by
    rw [Algebra.coe_norm_int]
    simp only [map_add, map_ofNat, nω_OK_coe]
    rw [show (4 : K) + ω = ↑(4 : ℤ) + ↑(1 : ℤ) * ω from by push_cast; ring, norm_form_BSD_rat 4 1]
    norm_num
  have hZ : Algebra.norm ℤ ((4:𝓞 K) + nω_OK) = 56 := by exact_mod_cast hQ
  simp [hZ]

-- ================================================================
-- §4. BSD_w3 and BSD_w4 closures (norm argument)
-- ================================================================

/-- **BSD_w3_ideal_equality_CLOSED** (0 sorry, classical trio):
    `span{3+ω} = p₃ · p̄₂⁴`. The ⊆ direction comes from
    `w3_span_le_p3_mul_pbar2pow4`; ⊇ follows from norm equality 48 = 48. -/
theorem BSD_w3_ideal_equality_CLOSED : BSD_w3_ideal_equality_OPEN := by
  apply le_antisymm w3_span_le_p3_mul_pbar2pow4
  -- ⊇: use norm argument: absNorm(J) | I and equal norms → J/I = ⊤
  rw [← Ideal.dvd_iff_le]
  have hw3_le : p3_OK * pbar2_OK ^ 4 ∣ Ideal.span {(3 : 𝓞 K) + nω_OK} :=
    Ideal.dvd_iff_le.mpr w3_span_le_p3_mul_pbar2pow4
  obtain ⟨L, hL⟩ := hw3_le
  have hL_norm : Ideal.absNorm L = 1 := by
    have h_eq : Ideal.absNorm (Ideal.span {(3:𝓞 K) + nω_OK}) =
                Ideal.absNorm p3_OK * Ideal.absNorm pbar2_OK ^ 4 * Ideal.absNorm L := by
      have := congr_arg Ideal.absNorm hL; rw [map_mul, map_mul, map_pow] at this; exact this
    rw [absNorm_span_w3', absNorm_p3_eq_3, absNorm_pbar2_eq_2] at h_eq
    omega
  have hL_top : L = ⊤ := Ideal.absNorm_eq_one_iff.mp hL_norm
  rw [hL_top, Ideal.mul_top] at hL
  exact ⟨1, by rw [mul_one]; exact hL.symm⟩

/-- **BSD_w4_ideal_equality_CLOSED** (0 sorry, classical trio):
    `span{4+ω} = p₇ · p₂³`. The ⊆ direction comes from
    `w4_span_le_p7_mul_p2pow3`; ⊇ follows from norm equality 56 = 56. -/
theorem BSD_w4_ideal_equality_CLOSED : BSD_w4_ideal_equality_OPEN := by
  apply le_antisymm w4_span_le_p7_mul_p2pow3
  rw [← Ideal.dvd_iff_le]
  have hw4_le : p7_OK * p2_OK ^ 3 ∣ Ideal.span {(4 : 𝓞 K) + nω_OK} :=
    Ideal.dvd_iff_le.mpr w4_span_le_p7_mul_p2pow3
  obtain ⟨L, hL⟩ := hw4_le
  have hL_norm : Ideal.absNorm L = 1 := by
    have h_eq : Ideal.absNorm (Ideal.span {(4:𝓞 K) + nω_OK}) =
                Ideal.absNorm p7_OK * Ideal.absNorm p2_OK ^ 3 * Ideal.absNorm L := by
      have := congr_arg Ideal.absNorm hL; rw [map_mul, map_mul, map_pow] at this; exact this
    rw [absNorm_span_w4', absNorm_p7_eq_7, absNorm_p2_eq_2] at h_eq
    omega
  have hL_top : L = ⊤ := Ideal.absNorm_eq_one_iff.mp hL_norm
  rw [hL_top, Ideal.mul_top] at hL
  exact ⟨1, by rw [mul_one]; exact hL.symm⟩

-- ================================================================
-- §5. IsPrime for new primes and span{5}
-- ================================================================

lemma pbar2_IsPrime : pbar2_OK.IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · rw [Ideal.eq_top_iff_one, pbar2_OK, Ideal.mem_span_pair] at h
    obtain ⟨u, v, huv⟩ := h
    have hK : ((2 * BSD_intBasis.repr u 0 - BSD_intBasis.repr v 0 -
                36 * BSD_intBasis.repr v 1 - 1 : ℤ) : K) +
              ((2 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 : ℤ) : K) * ω = 0 := by
      have h1K := congrArg (algebraMap (𝓞 K) K) huv
      simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_one, map_sub] at h1K
      rw [coord_decomp_map u, coord_decomp_map v] at h1K
      push_cast at h1K ⊢
      linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
    obtain ⟨h0, h1⟩ := repr_uniq' _ _ hK
    omega
  · rw [pbar2_OK, Ideal.mem_span_pair] at hab ⊢
    have ⟨hmul0, hmul1⟩ := mul_coords' a b
    obtain ⟨u, v, huv⟩ := hab
    have hK : ((2 * BSD_intBasis.repr u 0 - BSD_intBasis.repr v 0 -
                36 * BSD_intBasis.repr v 1 - BSD_intBasis.repr (a * b) 0 : ℤ) : K) +
              ((2 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 -
                BSD_intBasis.repr (a * b) 1 : ℤ) : K) * ω = 0 := by
      have h1K := congrArg (algebraMap (𝓞 K) K) huv
      simp only [map_add] at h1K
      rw [coord_decomp_map (a * b)] at h1K
      simp only [map_mul, map_ofNat, nω_OK_coe, map_sub] at h1K
      rw [coord_decomp_map u, coord_decomp_map v] at h1K
      push_cast at h1K ⊢
      linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
    obtain ⟨eq0, eq1⟩ := repr_uniq' _ _ hK
    have hsum_dvd : (2 : ℤ) ∣ BSD_intBasis.repr (a * b) 0 + BSD_intBasis.repr (a * b) 1 :=
      ⟨BSD_intBasis.repr u 0 + BSD_intBasis.repr u 1 - 18 * BSD_intBasis.repr v 1, by linarith⟩
    have hzmod : ((BSD_intBasis.repr (a * b) 0 + BSD_intBasis.repr (a * b) 1 : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hsum_dvd
    rw [hmul0, hmul1] at hzmod
    push_cast at hzmod
    have h36 : (36 : ZMod 2) = 0 := by decide
    simp only [h36, zero_mul, mul_zero, sub_zero] at hzmod
    have hprod : ((BSD_intBasis.repr a 0 + BSD_intBasis.repr a 1 : ℤ) : ZMod 2) *
                 ((BSD_intBasis.repr b 0 + BSD_intBasis.repr b 1 : ℤ) : ZMod 2) = 0 := by
      push_cast at hzmod ⊢; ring_nf at hzmod ⊢; exact hzmod
    rcases mul_eq_zero.mp hprod with ha | hb
    · left
      have hdvd : (2 : ℤ) ∣ BSD_intBasis.repr a 0 + BSD_intBasis.repr a 1 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp ha
      obtain ⟨k, hk⟩ := hdvd
      have hk_eq : BSD_intBasis.repr a 0 = 2 * k - BSD_intBasis.repr a 1 := by linarith
      refine ⟨k • BSD_intBasis 0, BSD_intBasis.repr a 1 • BSD_intBasis 0, ?_⟩
      apply Subtype.coe_injective
      show k • (BSD_intBasis 0 : K) * 2 +
          BSD_intBasis.repr a 1 • (BSD_intBasis 0 : K) * ((nω_OK : K) - 1) = (a : K)
      simp only [BSD_intBasis_zero_coe, nω_OK_coe, zsmul_eq_mul, mul_one, one_mul]
      rw [coord_decomp' a, hk_eq]; push_cast; ring
    · right
      have hdvd : (2 : ℤ) ∣ BSD_intBasis.repr b 0 + BSD_intBasis.repr b 1 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hb
      obtain ⟨k, hk⟩ := hdvd
      have hk_eq : BSD_intBasis.repr b 0 = 2 * k - BSD_intBasis.repr b 1 := by linarith
      rw [Ideal.mem_span_pair]
      refine ⟨k • BSD_intBasis 0, BSD_intBasis.repr b 1 • BSD_intBasis 0, ?_⟩
      apply Subtype.coe_injective
      show k • (BSD_intBasis 0 : K) * 2 +
          BSD_intBasis.repr b 1 • (BSD_intBasis 0 : K) * ((nω_OK : K) - 1) = (b : K)
      simp only [BSD_intBasis_zero_coe, nω_OK_coe, zsmul_eq_mul, mul_one, one_mul]
      rw [coord_decomp' b, hk_eq]; push_cast; ring

theorem p2_IsPrime : p2_OK.IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · rw [Ideal.eq_top_iff_one, p2_OK, Ideal.mem_span_pair] at h
    obtain ⟨u, v, huv⟩ := h
    have hK : ((2 * BSD_intBasis.repr u 0 - 36 * BSD_intBasis.repr v 1 - 1 : ℤ) : K) +
              ((2 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 + BSD_intBasis.repr v 1 : ℤ) : K) * ω = 0 := by
      have h1K := congrArg (algebraMap (𝓞 K) K) huv
      simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_one] at h1K
      rw [coord_decomp_map u, coord_decomp_map v] at h1K
      push_cast at h1K ⊢
      linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
    obtain ⟨h0, _⟩ := repr_uniq' _ _ hK
    have : (2 : ℤ) ∣ 1 := ⟨BSD_intBasis.repr u 0 - 18 * BSD_intBasis.repr v 1, by linarith⟩
    omega
  · rw [p2_OK, Ideal.mem_span_pair] at hab ⊢
    have ⟨hmul0, _⟩ := mul_coords' a b
    obtain ⟨u, v, huv⟩ := hab
    have eq0 : BSD_intBasis.repr (a * b) 0 = 2 * BSD_intBasis.repr u 0 - 36 * BSD_intBasis.repr v 1 := by
      have hK : ((2 * BSD_intBasis.repr u 0 - 36 * BSD_intBasis.repr v 1 -
                  BSD_intBasis.repr (a * b) 0 : ℤ) : K) +
                ((2 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 + BSD_intBasis.repr v 1 -
                  BSD_intBasis.repr (a * b) 1 : ℤ) : K) * ω = 0 := by
        have h1K := congrArg (algebraMap (𝓞 K) K) huv
        simp only [map_add] at h1K
        rw [coord_decomp_map (a * b)] at h1K
        simp only [map_mul, map_ofNat, nω_OK_coe] at h1K
        rw [coord_decomp_map u, coord_decomp_map v] at h1K
        push_cast at h1K ⊢
        linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
      linarith [(repr_uniq' _ _ hK).1]
    have hdvd2 : (2 : ℤ) ∣ BSD_intBasis.repr (a * b) 0 :=
      ⟨BSD_intBasis.repr u 0 - 18 * BSD_intBasis.repr v 1, by linarith⟩
    have hzmod_ab : ((BSD_intBasis.repr (a * b) 0 : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hdvd2
    rw [hmul0] at hzmod_ab; push_cast at hzmod_ab
    have h36 : (36 : ZMod 2) = 0 := by decide
    simp only [h36, zero_mul, mul_zero, sub_zero] at hzmod_ab
    rcases mul_eq_zero.mp hzmod_ab with ha0 | hb0
    · left
      have h2a0 : (2 : ℤ) ∣ BSD_intBasis.repr a 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp ha0
      obtain ⟨k, hk⟩ := h2a0
      refine ⟨k • BSD_intBasis 0, BSD_intBasis.repr a 1 • BSD_intBasis 0, ?_⟩
      apply Subtype.coe_injective
      show k • (BSD_intBasis 0 : K) * 2 +
          BSD_intBasis.repr a 1 • (BSD_intBasis 0 : K) * (nω_OK : K) = (a : K)
      simp only [BSD_intBasis_zero_coe, nω_OK_coe, zsmul_eq_mul, mul_one, one_mul]
      rw [coord_decomp' a, hk]; push_cast; ring
    · right
      have h2b0 : (2 : ℤ) ∣ BSD_intBasis.repr b 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hb0
      obtain ⟨k, hk⟩ := h2b0
      rw [Ideal.mem_span_pair]
      refine ⟨k • BSD_intBasis 0, BSD_intBasis.repr b 1 • BSD_intBasis 0, ?_⟩
      apply Subtype.coe_injective
      show k • (BSD_intBasis 0 : K) * 2 +
          BSD_intBasis.repr b 1 • (BSD_intBasis 0 : K) * (nω_OK : K) = (b : K)
      simp only [BSD_intBasis_zero_coe, nω_OK_coe, zsmul_eq_mul, mul_one, one_mul]
      rw [coord_decomp' b, hk]; push_cast; ring


lemma p3_IsPrime : p3_OK.IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · rw [Ideal.eq_top_iff_one, p3_OK, Ideal.mem_span_pair] at h
    obtain ⟨u, v, huv⟩ := h
    have hK : ((3 * BSD_intBasis.repr u 0 - 36 * BSD_intBasis.repr v 1 - 1 : ℤ) : K) +
              ((3 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 + BSD_intBasis.repr v 1 : ℤ) : K) * ω = 0 := by
      have h1K := congrArg (algebraMap (𝓞 K) K) huv
      simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_one] at h1K
      rw [coord_decomp_map u, coord_decomp_map v] at h1K
      push_cast at h1K ⊢
      linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
    obtain ⟨h0, _⟩ := repr_uniq' _ _ hK; omega
  · rw [p3_OK, Ideal.mem_span_pair] at hab ⊢
    have ⟨hmul0, _⟩ := mul_coords' a b
    obtain ⟨u, v, huv⟩ := hab
    have eq0 : BSD_intBasis.repr (a * b) 0 = 3 * BSD_intBasis.repr u 0 - 36 * BSD_intBasis.repr v 1 := by
      have hK : ((3 * BSD_intBasis.repr u 0 - 36 * BSD_intBasis.repr v 1 -
                  BSD_intBasis.repr (a * b) 0 : ℤ) : K) +
                ((3 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 + BSD_intBasis.repr v 1 -
                  BSD_intBasis.repr (a * b) 1 : ℤ) : K) * ω = 0 := by
        have h1K := congrArg (algebraMap (𝓞 K) K) huv
        simp only [map_add] at h1K
        rw [coord_decomp_map (a * b)] at h1K
        simp only [map_mul, map_ofNat, nω_OK_coe] at h1K
        rw [coord_decomp_map u, coord_decomp_map v] at h1K
        push_cast at h1K ⊢
        linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
      linarith [(repr_uniq' _ _ hK).1]
    have hzmod : ((BSD_intBasis.repr a 0 : ℤ) : ZMod 3) *
                 ((BSD_intBasis.repr b 0 : ℤ) : ZMod 3) = 0 := by
      have hdvd : (3 : ℤ) ∣ BSD_intBasis.repr (a * b) 0 :=
        ⟨BSD_intBasis.repr u 0 - 12 * BSD_intBasis.repr v 1, by linarith⟩
      have h36 : (36 : ZMod 3) = 0 := by decide
      have hab0 : ((BSD_intBasis.repr (a * b) 0 : ℤ) : ZMod 3) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hdvd
      rw [hmul0] at hab0; push_cast at hab0
      simp only [h36, zero_mul, mul_zero, sub_zero] at hab0; exact hab0
    rcases mul_eq_zero.mp hzmod with ha | hb
    · left
      have h3a0 : (3 : ℤ) ∣ BSD_intBasis.repr a 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ha
      obtain ⟨k, hk⟩ := h3a0
      refine ⟨k • BSD_intBasis 0, BSD_intBasis.repr a 1 • BSD_intBasis 0, ?_⟩
      apply Subtype.coe_injective
      show k • (BSD_intBasis 0 : K) * 3 +
          BSD_intBasis.repr a 1 • (BSD_intBasis 0 : K) * (nω_OK : K) = (a : K)
      simp only [BSD_intBasis_zero_coe, nω_OK_coe, zsmul_eq_mul, mul_one, one_mul]
      rw [coord_decomp' a, hk]; push_cast; ring
    · right
      have h3b0 : (3 : ℤ) ∣ BSD_intBasis.repr b 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hb
      obtain ⟨k, hk⟩ := h3b0
      rw [Ideal.mem_span_pair]
      refine ⟨k • BSD_intBasis 0, BSD_intBasis.repr b 1 • BSD_intBasis 0, ?_⟩
      apply Subtype.coe_injective
      show k • (BSD_intBasis 0 : K) * 3 +
          BSD_intBasis.repr b 1 • (BSD_intBasis 0 : K) * (nω_OK : K) = (b : K)
      simp only [BSD_intBasis_zero_coe, nω_OK_coe, zsmul_eq_mul, mul_one, one_mul]
      rw [coord_decomp' b, hk]; push_cast; ring

lemma p7_IsPrime : p7_OK.IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · rw [Ideal.eq_top_iff_one, p7_OK, Ideal.mem_span_pair] at h
    obtain ⟨u, v, huv⟩ := h
    have hK : ((7 * BSD_intBasis.repr u 0 - 3 * BSD_intBasis.repr v 0 -
                36 * BSD_intBasis.repr v 1 - 1 : ℤ) : K) +
              ((7 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 -
                2 * BSD_intBasis.repr v 1 : ℤ) : K) * ω = 0 := by
      have h1K := congrArg (algebraMap (𝓞 K) K) huv
      simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_one, map_sub] at h1K
      rw [coord_decomp_map u, coord_decomp_map v] at h1K
      push_cast at h1K ⊢
      linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
    obtain ⟨h0, h1⟩ := repr_uniq' _ _ hK
    omega
  · rw [p7_OK, Ideal.mem_span_pair] at hab ⊢
    obtain ⟨u, v, huv⟩ := hab
    have hmul0 := (mul_coords' a b).1; have hmul1 := (mul_coords' a b).2
    have eq0 : BSD_intBasis.repr (a * b) 0 =
        7 * BSD_intBasis.repr u 0 - 3 * BSD_intBasis.repr v 0 - 36 * BSD_intBasis.repr v 1 := by
      have hK : ((7 * BSD_intBasis.repr u 0 - 3 * BSD_intBasis.repr v 0 - 36 * BSD_intBasis.repr v 1 -
                  BSD_intBasis.repr (a * b) 0 : ℤ) : K) +
                ((7 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 - 2 * BSD_intBasis.repr v 1 -
                  BSD_intBasis.repr (a * b) 1 : ℤ) : K) * ω = 0 := by
        have h1K := congrArg (algebraMap (𝓞 K) K) huv
        simp only [map_add] at h1K
        rw [coord_decomp_map (a * b)] at h1K
        simp only [map_mul, map_ofNat, nω_OK_coe, map_sub] at h1K
        rw [coord_decomp_map u, coord_decomp_map v] at h1K
        push_cast at h1K ⊢
        linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
      linarith [(repr_uniq' _ _ hK).1]
    have eq1 : BSD_intBasis.repr (a * b) 1 =
        7 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 - 2 * BSD_intBasis.repr v 1 := by
      have hK : ((7 * BSD_intBasis.repr u 0 - 3 * BSD_intBasis.repr v 0 - 36 * BSD_intBasis.repr v 1 -
                  BSD_intBasis.repr (a * b) 0 : ℤ) : K) +
                ((7 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 - 2 * BSD_intBasis.repr v 1 -
                  BSD_intBasis.repr (a * b) 1 : ℤ) : K) * ω = 0 := by
        have h1K := congrArg (algebraMap (𝓞 K) K) huv
        simp only [map_add] at h1K
        rw [coord_decomp_map (a * b)] at h1K
        simp only [map_mul, map_ofNat, nω_OK_coe, map_sub] at h1K
        rw [coord_decomp_map u, coord_decomp_map v] at h1K
        push_cast at h1K ⊢
        linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
      linarith [(repr_uniq' _ _ hK).2]
    have hzmod : ((BSD_intBasis.repr a 0 : ℤ) : ZMod 7) + 3 *
                 ((BSD_intBasis.repr a 1 : ℤ) : ZMod 7) = 0 ∨
                 ((BSD_intBasis.repr b 0 : ℤ) : ZMod 7) + 3 *
                 ((BSD_intBasis.repr b 1 : ℤ) : ZMod 7) = 0 := by
      have key : (((BSD_intBasis.repr a 0 : ℤ) : ZMod 7) + 3 * ((BSD_intBasis.repr a 1 : ℤ) : ZMod 7)) *
                 (((BSD_intBasis.repr b 0 : ℤ) : ZMod 7) + 3 * ((BSD_intBasis.repr b 1 : ℤ) : ZMod 7)) = 0 := by
        have hdvd : (7 : ℤ) ∣ BSD_intBasis.repr a 0 * BSD_intBasis.repr b 0 +
                    3 * BSD_intBasis.repr a 0 * BSD_intBasis.repr b 1 +
                    3 * BSD_intBasis.repr a 1 * BSD_intBasis.repr b 0 +
                    3 * BSD_intBasis.repr a 1 * BSD_intBasis.repr b 1 -
                    36 * BSD_intBasis.repr a 1 * BSD_intBasis.repr b 1 := by
          rw [show BSD_intBasis.repr a 0 * BSD_intBasis.repr b 0 +
                  3 * BSD_intBasis.repr a 0 * BSD_intBasis.repr b 1 +
                  3 * BSD_intBasis.repr a 1 * BSD_intBasis.repr b 0 +
                  3 * BSD_intBasis.repr a 1 * BSD_intBasis.repr b 1 -
                  36 * BSD_intBasis.repr a 1 * BSD_intBasis.repr b 1 =
                  BSD_intBasis.repr (a*b) 0 + 3 * BSD_intBasis.repr (a*b) 1 from
                  by rw [hmul0, hmul1]; ring]
          exact ⟨BSD_intBasis.repr u 0 + 3 * BSD_intBasis.repr u 1 - 6 * BSD_intBasis.repr v 1,
                 by linarith⟩
        have hdvd_mod := (ZMod.intCast_zmod_eq_zero_iff_dvd
          (BSD_intBasis.repr a 0 * BSD_intBasis.repr b 0 + 3 * BSD_intBasis.repr a 0 * BSD_intBasis.repr b 1 +
           3 * BSD_intBasis.repr a 1 * BSD_intBasis.repr b 0 + 3 * BSD_intBasis.repr a 1 * BSD_intBasis.repr b 1 -
           36 * BSD_intBasis.repr a 1 * BSD_intBasis.repr b 1) 7).mpr hdvd
        have h36 : (36 : ZMod 7) = 1 := by decide
        have h7z : (7 : ZMod 7) = 0 := by decide
        push_cast at hdvd_mod ⊢
        simp only [h36] at hdvd_mod
        linear_combination hdvd_mod +
          ↑(BSD_intBasis.repr a 1) * ↑(BSD_intBasis.repr b 1) * h7z
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      exact mul_eq_zero.mp key
    rcases hzmod with ha | hb
    · left
      have h7 : (7 : ℤ) ∣ BSD_intBasis.repr a 0 + 3 * BSD_intBasis.repr a 1 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp (by push_cast at ha ⊢; exact ha)
      obtain ⟨k, hk⟩ := h7
      have hk_eq : BSD_intBasis.repr a 0 = 7 * k - 3 * BSD_intBasis.repr a 1 := by linarith
      refine ⟨k • BSD_intBasis 0, BSD_intBasis.repr a 1 • BSD_intBasis 0, ?_⟩
      apply Subtype.coe_injective
      show k • (BSD_intBasis 0 : K) * 7 +
          BSD_intBasis.repr a 1 • (BSD_intBasis 0 : K) * ((nω_OK : K) - 3) = (a : K)
      simp only [BSD_intBasis_zero_coe, nω_OK_coe, zsmul_eq_mul, mul_one, one_mul]
      rw [coord_decomp' a, hk_eq]; push_cast; ring
    · right
      have h7 : (7 : ℤ) ∣ BSD_intBasis.repr b 0 + 3 * BSD_intBasis.repr b 1 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp (by push_cast at hb ⊢; exact hb)
      obtain ⟨k, hk⟩ := h7
      have hk_eq : BSD_intBasis.repr b 0 = 7 * k - 3 * BSD_intBasis.repr b 1 := by linarith
      rw [Ideal.mem_span_pair]
      refine ⟨k • BSD_intBasis 0, BSD_intBasis.repr b 1 • BSD_intBasis 0, ?_⟩
      apply Subtype.coe_injective
      show k • (BSD_intBasis 0 : K) * 7 +
          BSD_intBasis.repr b 1 • (BSD_intBasis 0 : K) * ((nω_OK : K) - 3) = (b : K)
      simp only [BSD_intBasis_zero_coe, nω_OK_coe, zsmul_eq_mul, mul_one, one_mul]
      rw [coord_decomp' b, hk_eq]; push_cast; ring

-- ================================================================
-- §6. Nonzero-divisor wrappers for named ideals
-- ================================================================

noncomputable def p2_nzd_local : p2_OK ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
  mem_nonZeroDivisors_of_ne_zero (by
    intro h; have := absNorm_p2_eq_2; rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this; norm_num at this)

noncomputable def pbar2_nzd : pbar2_OK ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
  mem_nonZeroDivisors_of_ne_zero (by
    intro h; have := absNorm_pbar2_eq_2; rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this; norm_num at this)

noncomputable def p3_nzd : p3_OK ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
  mem_nonZeroDivisors_of_ne_zero (by
    intro h; have := absNorm_p3_eq_3; rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this; norm_num at this)

noncomputable def pbar3_nzd : pbar3_OK ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
  mem_nonZeroDivisors_of_ne_zero (by
    intro h; have := absNorm_pbar3_eq_3; rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this; norm_num at this)

noncomputable def p7_nzd : p7_OK ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
  mem_nonZeroDivisors_of_ne_zero (by
    intro h; have := absNorm_p7_eq_7; rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this; norm_num at this)

noncomputable def pbar7_nzd : pbar7_OK ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
  mem_nonZeroDivisors_of_ne_zero (by
    intro h; have := absNorm_pbar7_eq_7; rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this; norm_num at this)

-- ================================================================
-- §7. Class group elements and zpowers membership
-- ================================================================

noncomputable def pbar2_class : ClassGroup (𝓞 K) := ClassGroup.mk0 ⟨pbar2_OK, pbar2_nzd⟩
noncomputable def p3_class    : ClassGroup (𝓞 K) := ClassGroup.mk0 ⟨p3_OK,    p3_nzd⟩
noncomputable def pbar3_class : ClassGroup (𝓞 K) := ClassGroup.mk0 ⟨pbar3_OK, pbar3_nzd⟩
noncomputable def p7_class    : ClassGroup (𝓞 K) := ClassGroup.mk0 ⟨p7_OK,    p7_nzd⟩
noncomputable def pbar7_class : ClassGroup (𝓞 K) := ClassGroup.mk0 ⟨pbar7_OK, pbar7_nzd⟩

/-- `[p̄₂] = [p₂]⁻¹`. From `p₂ · p̄₂ = span{2}` (principal → class = 1). -/
lemma pbar2_class_eq_inv : pbar2_class = p2_class_gen⁻¹ := by
  have h_prod : p2_class_gen * pbar2_class = 1 := by
    have hprinc : p2_OK * pbar2_OK = Ideal.span {(2 : 𝓞 K)} := p2_mul_pbar2
    have h2_nzd : Ideal.span {(2 : 𝓞 K)} ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
      mem_nonZeroDivisors_of_ne_zero (by simp [Ideal.absNorm_span_singleton])
    have hmk := (ClassGroup.mk0 : nonZeroDivisors (Ideal (𝓞 K)) →* ClassGroup (𝓞 K)).map_mul
      ⟨p2_OK, p2_nzd_local⟩ ⟨pbar2_OK, pbar2_nzd⟩
    simp only [p2_class_gen, pbar2_class] at hmk ⊢
    rw [← hmk]
    have heq : (⟨p2_OK, p2_nzd_local⟩ * ⟨pbar2_OK, pbar2_nzd⟩ : nonZeroDivisors (Ideal (𝓞 K))) =
               ⟨Ideal.span {(2 : 𝓞 K)}, h2_nzd⟩ := Subtype.ext hprinc
    rw [heq]
    exact (ClassGroup.mk0_eq_one_iff h2_nzd).mpr ⟨⟨2, rfl⟩⟩
  exact eq_inv_of_mul_eq_one_right h_prod

/-- `[p₃] = [p₂]⁴`. From BSD_w3: `span{3+ω} = p₃·p̄₂⁴`. -/
lemma p3_class_eq_pow4 : p3_class = p2_class_gen ^ 4 := by
  have hw3_nzd : Ideal.span {(3:𝓞 K) + nω_OK} ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
    mem_nonZeroDivisors_of_ne_zero (by
      intro h; have := absNorm_span_w3'
      rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this; norm_num at this)
  have h1 : ClassGroup.mk0 ⟨Ideal.span {(3:𝓞 K) + nω_OK}, hw3_nzd⟩ = 1 :=
    (ClassGroup.mk0_eq_one_iff hw3_nzd).mpr ⟨⟨3 + nω_OK, rfl⟩⟩
  have hpbar2_pow4_nzd : pbar2_OK ^ 4 ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
    mem_nonZeroDivisors_of_ne_zero (by
      intro h
      have := map_pow Ideal.absNorm pbar2_OK 4
      rw [h] at this
      simp only [show (0 : Ideal (𝓞 K)) = ⊥ from rfl, Ideal.absNorm_bot] at this
      simp [absNorm_pbar2_eq_2] at this)
  have h2 : p3_class * pbar2_class ^ 4 = 1 := by
    simp only [p3_class, pbar2_class]
    rw [← map_pow (ClassGroup.mk0), ← map_mul (ClassGroup.mk0)]
    have heq : (⟨p3_OK, p3_nzd⟩ * ⟨pbar2_OK, pbar2_nzd⟩ ^ 4 : nonZeroDivisors (Ideal (𝓞 K))) =
               ⟨Ideal.span {(3:𝓞 K) + nω_OK}, hw3_nzd⟩ :=
      Subtype.ext (by simp [mul_pow]; exact BSD_w3_ideal_equality_CLOSED.symm)
    rw [heq]; exact h1
  rw [pbar2_class_eq_inv] at h2
  have hstep : p3_class = (p2_class_gen⁻¹ ^ 4)⁻¹ := eq_inv_of_mul_eq_one_left h2
  simp [inv_pow, inv_inv] at hstep; exact hstep

/-- `[p̄₃] = [p₂]⁶`. From `p₃ · p̄₃ = span{3}` and `[p₃] = [p₂]⁴`. -/
lemma pbar3_class_eq_pow6 : pbar3_class = p2_class_gen ^ 6 := by
  have h_prod3 : p3_class * pbar3_class = 1 := by
    have h3_nzd : Ideal.span {(3:𝓞 K)} ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
      mem_nonZeroDivisors_of_ne_zero (by simp [absNorm_span_three'])
    have h1 : ClassGroup.mk0 ⟨Ideal.span {(3:𝓞 K)}, h3_nzd⟩ = 1 :=
      (ClassGroup.mk0_eq_one_iff h3_nzd).mpr ⟨⟨3, rfl⟩⟩
    simp only [p3_class, pbar3_class]
    rw [← map_mul (ClassGroup.mk0)]
    have heq : (⟨p3_OK, p3_nzd⟩ * ⟨pbar3_OK, pbar3_nzd⟩ : nonZeroDivisors (Ideal (𝓞 K))) =
               ⟨Ideal.span {(3:𝓞 K)}, h3_nzd⟩ :=
      Subtype.ext p3_mul_pbar3
    rw [heq]; exact h1
  rw [p3_class_eq_pow4] at h_prod3
  have hstep3 : pbar3_class = (p2_class_gen ^ 4)⁻¹ := eq_inv_of_mul_eq_one_right h_prod3
  rw [hstep3]
  have hord : orderOf p2_class_gen = 10 := BSD_orderOf_p2_eq_10 BSD_p2_pow_10_principal
  have h10 : p2_class_gen ^ 10 = 1 := hord ▸ pow_orderOf_eq_one p2_class_gen
  have h46 : p2_class_gen ^ 4 * p2_class_gen ^ 6 = 1 := by
    rw [← pow_add, show 4 + 6 = 10 from by norm_num]; exact h10
  exact (eq_inv_of_mul_eq_one_right h46).symm

/-- `[p₇] = [p₂]⁷`. From BSD_w4: `span{4+ω} = p₇·p₂³`. -/
lemma p7_class_eq_pow7 : p7_class = p2_class_gen ^ 7 := by
  have hw4_nzd : Ideal.span {(4:𝓞 K) + nω_OK} ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
    mem_nonZeroDivisors_of_ne_zero (by
      intro h; have := absNorm_span_w4'
      rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this; norm_num at this)
  have h1 : ClassGroup.mk0 ⟨Ideal.span {(4:𝓞 K) + nω_OK}, hw4_nzd⟩ = 1 :=
    (ClassGroup.mk0_eq_one_iff hw4_nzd).mpr ⟨⟨4 + nω_OK, rfl⟩⟩
  have hp2_pow3_nzd : p2_OK ^ 3 ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
    mem_nonZeroDivisors_of_ne_zero (by
      intro h
      have := map_pow Ideal.absNorm p2_OK 3
      rw [h] at this
      simp only [show (0 : Ideal (𝓞 K)) = ⊥ from rfl, Ideal.absNorm_bot] at this
      simp [absNorm_p2_eq_2] at this)
  have h2 : p7_class * p2_class_gen ^ 3 = 1 := by
    simp only [p7_class, p2_class_gen]
    rw [← map_pow (ClassGroup.mk0), ← map_mul (ClassGroup.mk0)]
    have heq : (⟨p7_OK, p7_nzd⟩ * ⟨p2_OK, p2_nzd⟩ ^ 3 : nonZeroDivisors (Ideal (𝓞 K))) =
               ⟨Ideal.span {(4:𝓞 K) + nω_OK}, hw4_nzd⟩ :=
      Subtype.ext (by simp [mul_pow]; exact BSD_w4_ideal_equality_CLOSED.symm)
    rw [heq]; exact h1
  have hstep7 : p7_class = (p2_class_gen ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h2
  rw [hstep7]
  have hord : orderOf p2_class_gen = 10 := BSD_orderOf_p2_eq_10 BSD_p2_pow_10_principal
  have h10 : p2_class_gen ^ 10 = 1 := hord ▸ pow_orderOf_eq_one p2_class_gen
  have h37 : p2_class_gen ^ 3 * p2_class_gen ^ 7 = 1 := by
    rw [← pow_add, show 3 + 7 = 10 from by norm_num]; exact h10
  exact (eq_inv_of_mul_eq_one_right h37).symm

/-- `[p̄₇] = [p₂]³`. From `p₇ · p̄₇ = span{7}` and `[p₇] = [p₂]⁷`. -/
lemma pbar7_class_eq_pow3 : pbar7_class = p2_class_gen ^ 3 := by
  have h_prod7 : p7_class * pbar7_class = 1 := by
    have h7_nzd : Ideal.span {(7:𝓞 K)} ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
      mem_nonZeroDivisors_of_ne_zero (by simp [absNorm_span_seven'])
    have h1 : ClassGroup.mk0 ⟨Ideal.span {(7:𝓞 K)}, h7_nzd⟩ = 1 :=
      (ClassGroup.mk0_eq_one_iff h7_nzd).mpr ⟨⟨7, rfl⟩⟩
    simp only [p7_class, pbar7_class]
    rw [← map_mul (ClassGroup.mk0)]
    have heq : (⟨p7_OK, p7_nzd⟩ * ⟨pbar7_OK, pbar7_nzd⟩ : nonZeroDivisors (Ideal (𝓞 K))) =
               ⟨Ideal.span {(7:𝓞 K)}, h7_nzd⟩ :=
      Subtype.ext p7_mul_pbar7
    rw [heq]; exact h1
  rw [p7_class_eq_pow7] at h_prod7
  have hstep73 : pbar7_class = (p2_class_gen ^ 7)⁻¹ := eq_inv_of_mul_eq_one_right h_prod7
  rw [hstep73]
  have hord : orderOf p2_class_gen = 10 := BSD_orderOf_p2_eq_10 BSD_p2_pow_10_principal
  have h10 : p2_class_gen ^ 10 = 1 := hord ▸ pow_orderOf_eq_one p2_class_gen
  have h73 : p2_class_gen ^ 7 * p2_class_gen ^ 3 = 1 := by
    rw [← pow_add, show 7 + 3 = 10 from by norm_num]; exact h10
  exact (eq_inv_of_mul_eq_one_right h73).symm

-- ================================================================
-- §8. BSD_small_norm closure
-- ================================================================

/-- Helper: for any prime ideal P of norm 2, P = p₂ or P = p̄₂. -/
lemma prime_norm2_eq (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hn : Ideal.absNorm P = 2) :
    P = p2_OK ∨ P = pbar2_OK := by
  -- 2 ∈ P: additive group of 𝓞 K/P has order 2, so 2·1 = 0
  have h2 : (2 : 𝓞 K) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hcard : Nat.card (𝓞 K ⧸ P) = 2 := by rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
    have hord : addOrderOf (1 : 𝓞 K ⧸ P) ∣ 2 := by
      have h := addOrderOf_dvd_natCard (1 : 𝓞 K ⧸ P)
      rwa [hcard] at h
    rw [addOrderOf_dvd_iff_nsmul_eq_zero] at hord
    change (2 : 𝓞 K ⧸ P) = 0
    rw [show (2 : 𝓞 K ⧸ P) = (2 : ℕ) • (1 : 𝓞 K ⧸ P) from by norm_num]
    exact hord
  have hP_dvd : P ∣ p2_OK * pbar2_OK := by
    rw [p2_mul_pbar2]
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr h2)
  have hP_ne_bot : P ≠ ⊥ := by intro h; rw [h, Ideal.absNorm_bot] at hn; norm_num at hn
  have hP_prime_el : Prime P := (Ideal.prime_iff_isPrime hP_ne_bot).mpr hP
  rcases hP_prime_el.dvd_or_dvd hP_dvd with h | h
  · left
    have hp2_le : p2_OK ≤ P := Ideal.dvd_iff_le.mp h
    have hp2_max := Ring.DimensionLEOne.maximalOfPrime (by
      intro heq; have h_abs := absNorm_p2_eq_2; rw [heq, Ideal.absNorm_bot] at h_abs; norm_num at h_abs) p2_IsPrime
    have hP_ne_top : P ≠ ⊤ := by
      intro heq; rw [Ideal.absNorm_eq_one_iff.mpr heq] at hn; norm_num at hn
    exact (hp2_max.eq_of_le hP_ne_top hp2_le).symm
  · right
    have hpb2_le : pbar2_OK ≤ P := Ideal.dvd_iff_le.mp h
    have hpb2_max := Ring.DimensionLEOne.maximalOfPrime (by
      intro heq; have h_abs := absNorm_pbar2_eq_2; rw [heq, Ideal.absNorm_bot] at h_abs; norm_num at h_abs) pbar2_IsPrime
    have hP_ne_top : P ≠ ⊤ := by
      intro heq; rw [Ideal.absNorm_eq_one_iff.mpr heq] at hn; norm_num at hn
    exact (hpb2_max.eq_of_le hP_ne_top hpb2_le).symm

/-- Helper: for any prime ideal P of norm 3, P = p₃ or P = p̄₃. -/
lemma prime_norm3_eq (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hn : Ideal.absNorm P = 3) :
    P = p3_OK ∨ P = pbar3_OK := by
  have h3 : (3 : 𝓞 K) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hcard : Nat.card (𝓞 K ⧸ P) = 3 := by rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
    have hord : addOrderOf (1 : 𝓞 K ⧸ P) ∣ 3 := hcard ▸ addOrderOf_dvd_natCard _
    rw [addOrderOf_dvd_iff_nsmul_eq_zero] at hord
    change (3 : 𝓞 K ⧸ P) = 0
    rw [show (3 : 𝓞 K ⧸ P) = (3 : ℕ) • (1 : 𝓞 K ⧸ P) from by norm_num]
    exact hord
  have hP_dvd : P ∣ p3_OK * pbar3_OK := by
    rw [p3_mul_pbar3]
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr h3)
  have hP_ne_top : P ≠ ⊤ := by
    intro heq; rw [Ideal.absNorm_eq_one_iff.mpr heq] at hn; norm_num at hn
  have hP_ne_bot : P ≠ ⊥ := by intro h; rw [h, Ideal.absNorm_bot] at hn; norm_num at hn
  have hP_prime_el : Prime P := (Ideal.prime_iff_isPrime hP_ne_bot).mpr hP
  rcases hP_prime_el.dvd_or_dvd hP_dvd with h | h
  · left
    have hp3_max := Ring.DimensionLEOne.maximalOfPrime (by
      intro heq; have h_abs := absNorm_p3_eq_3; rw [heq, Ideal.absNorm_bot] at h_abs; norm_num at h_abs) p3_IsPrime
    exact (hp3_max.eq_of_le hP_ne_top (Ideal.dvd_iff_le.mp h)).symm
  · right
    have hpb3_IsPrime : pbar3_OK.IsPrime := by
      rw [Ideal.isPrime_iff]
      refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
      · rw [Ideal.eq_top_iff_one, pbar3_OK, Ideal.mem_span_pair] at h
        obtain ⟨u, v, huv⟩ := h
        have hK : ((3 * BSD_intBasis.repr u 0 + BSD_intBasis.repr v 0 + 36 * BSD_intBasis.repr v 1 - 1 : ℤ) : K) +
                  ((3 * BSD_intBasis.repr u 1 - BSD_intBasis.repr v 0 : ℤ) : K) * ω = 0 := by
          have h1K := congrArg (algebraMap (𝓞 K) K) huv
          simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_one, map_sub] at h1K
          rw [coord_decomp_map u, coord_decomp_map v] at h1K
          push_cast; ring_nf; push_cast at h1K; ring_nf at h1K
          linear_combination h1K + (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
        obtain ⟨h0, h1⟩ := repr_uniq' _ _ hK; omega
      · simp only [pbar3_OK, Ideal.mem_span_pair] at hab ⊢
        obtain ⟨u, v, huv⟩ := hab
        have hmul0 := (mul_coords' a b).1; have hmul1 := (mul_coords' a b).2
        have eq_sum : BSD_intBasis.repr (a*b) 0 + BSD_intBasis.repr (a*b) 1 =
            3 * BSD_intBasis.repr u 0 + 3 * BSD_intBasis.repr u 1 + 36 * BSD_intBasis.repr v 1 := by
          have hK : ((3 * BSD_intBasis.repr u 0 + BSD_intBasis.repr v 0 + 36 * BSD_intBasis.repr v 1 -
                      BSD_intBasis.repr (a*b) 0 : ℤ) : K) +
                    ((3 * BSD_intBasis.repr u 1 - BSD_intBasis.repr v 0 -
                      BSD_intBasis.repr (a*b) 1 : ℤ) : K) * ω = 0 := by
            have h1K := congrArg (algebraMap (𝓞 K) K) huv
            simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_sub] at h1K
            conv at h1K => rhs; rw [← map_mul]
            rw [coord_decomp_map (a*b), coord_decomp_map u, coord_decomp_map v] at h1K
            push_cast; ring_nf; push_cast at h1K; ring_nf at h1K
            linear_combination h1K + (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
          have e0 := (repr_uniq' _ _ hK).1; have e1 := (repr_uniq' _ _ hK).2; linarith
        have hzmod : ((BSD_intBasis.repr a 0 + BSD_intBasis.repr a 1 : ℤ) : ZMod 3) *
                     ((BSD_intBasis.repr b 0 + BSD_intBasis.repr b 1 : ℤ) : ZMod 3) = 0 := by
          have hdvd : (3 : ℤ) ∣ (BSD_intBasis.repr a 0 + BSD_intBasis.repr a 1) *
                                 (BSD_intBasis.repr b 0 + BSD_intBasis.repr b 1) :=
            ⟨BSD_intBasis.repr u 0 + BSD_intBasis.repr u 1 + 12 * BSD_intBasis.repr v 1 +
             12 * BSD_intBasis.repr a 1 * BSD_intBasis.repr b 1,
             by nlinarith [hmul0, hmul1, eq_sum]⟩
          have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hdvd
          push_cast at h ⊢; exact h
        rcases mul_eq_zero.mp hzmod with ha | hb
        · left
          have h3 : (3:ℤ) ∣ BSD_intBasis.repr a 0 + BSD_intBasis.repr a 1 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast at ha ⊢; exact ha)
          obtain ⟨k, hk⟩ := h3
          exact ⟨k • BSD_intBasis 0, (-BSD_intBasis.repr a 1) • BSD_intBasis 0, by
            have heq : (algebraMap (𝓞 K) K)
                (k • BSD_intBasis 0 * 3 + (-BSD_intBasis.repr a 1) • BSD_intBasis 0 * (1 - nω_OK)) =
                (algebraMap (𝓞 K) K) a := by
              simp only [map_add, map_mul, map_ofNat, zsmul_eq_mul, map_neg, map_sub, map_intCast,
                         BSD_intBasis_zero_coe, BSD_intBasis_one_coe, nω_OK_coe, coord_decomp' a,
                         mul_one, one_mul]
              push_cast
              have hk' : (3 : K) * k = BSD_intBasis.repr a 0 + BSD_intBasis.repr a 1 := by
                exact_mod_cast hk.symm
              linear_combination hk'
            exact Subtype.coe_injective heq⟩
        · right
          have h3 : (3:ℤ) ∣ BSD_intBasis.repr b 0 + BSD_intBasis.repr b 1 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast at hb ⊢; exact hb)
          obtain ⟨k, hk⟩ := h3
          exact ⟨k • BSD_intBasis 0, (-BSD_intBasis.repr b 1) • BSD_intBasis 0, by
            have heq : (algebraMap (𝓞 K) K)
                (k • BSD_intBasis 0 * 3 + (-BSD_intBasis.repr b 1) • BSD_intBasis 0 * (1 - nω_OK)) =
                (algebraMap (𝓞 K) K) b := by
              simp only [map_add, map_mul, map_ofNat, zsmul_eq_mul, map_neg, map_sub, map_intCast,
                         BSD_intBasis_zero_coe, BSD_intBasis_one_coe, nω_OK_coe, coord_decomp' b,
                         mul_one, one_mul]
              push_cast
              have hk' : (3 : K) * k = BSD_intBasis.repr b 0 + BSD_intBasis.repr b 1 := by
                exact_mod_cast hk.symm
              linear_combination hk'
            exact Subtype.coe_injective heq⟩
    have hpb3_max := Ring.DimensionLEOne.maximalOfPrime (by
      intro heq; have h_abs := absNorm_pbar3_eq_3; rw [heq, Ideal.absNorm_bot] at h_abs; norm_num at h_abs) hpb3_IsPrime
    exact (hpb3_max.eq_of_le hP_ne_top (Ideal.dvd_iff_le.mp h)).symm

/-- pbar3_OK is a prime ideal (extracted for reuse). -/
lemma pbar3_OK_isPrime : pbar3_OK.IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · rw [Ideal.eq_top_iff_one, pbar3_OK, Ideal.mem_span_pair] at h
    obtain ⟨u, v, huv⟩ := h
    have hK : ((3 * BSD_intBasis.repr u 0 + BSD_intBasis.repr v 0 + 36 * BSD_intBasis.repr v 1 - 1 : ℤ) : K) +
              ((3 * BSD_intBasis.repr u 1 - BSD_intBasis.repr v 0 : ℤ) : K) * ω = 0 := by
      have h1K := congrArg (algebraMap (𝓞 K) K) huv
      simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_one, map_sub] at h1K
      rw [coord_decomp_map u, coord_decomp_map v] at h1K
      push_cast; ring_nf; push_cast at h1K; ring_nf at h1K
      linear_combination h1K + (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
    obtain ⟨h0, h1⟩ := repr_uniq' _ _ hK; omega
  · simp only [pbar3_OK, Ideal.mem_span_pair] at hab ⊢
    obtain ⟨u, v, huv⟩ := hab
    have hmul0 := (mul_coords' a b).1; have hmul1 := (mul_coords' a b).2
    have eq_sum : BSD_intBasis.repr (a*b) 0 + BSD_intBasis.repr (a*b) 1 =
        3 * BSD_intBasis.repr u 0 + 3 * BSD_intBasis.repr u 1 + 36 * BSD_intBasis.repr v 1 := by
      have hK : ((3 * BSD_intBasis.repr u 0 + BSD_intBasis.repr v 0 + 36 * BSD_intBasis.repr v 1 -
                  BSD_intBasis.repr (a*b) 0 : ℤ) : K) +
                ((3 * BSD_intBasis.repr u 1 - BSD_intBasis.repr v 0 -
                  BSD_intBasis.repr (a*b) 1 : ℤ) : K) * ω = 0 := by
        have h1K := congrArg (algebraMap (𝓞 K) K) huv
        simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_sub] at h1K
        conv at h1K => rhs; rw [← map_mul]
        rw [coord_decomp_map (a*b), coord_decomp_map u, coord_decomp_map v] at h1K
        push_cast; ring_nf; push_cast at h1K; ring_nf at h1K
        linear_combination h1K + (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
      have e0 := (repr_uniq' _ _ hK).1; have e1 := (repr_uniq' _ _ hK).2; linarith
    have hzmod : ((BSD_intBasis.repr a 0 + BSD_intBasis.repr a 1 : ℤ) : ZMod 3) *
                 ((BSD_intBasis.repr b 0 + BSD_intBasis.repr b 1 : ℤ) : ZMod 3) = 0 := by
      have hdvd : (3 : ℤ) ∣ (BSD_intBasis.repr a 0 + BSD_intBasis.repr a 1) *
                             (BSD_intBasis.repr b 0 + BSD_intBasis.repr b 1) :=
        ⟨BSD_intBasis.repr u 0 + BSD_intBasis.repr u 1 + 12 * BSD_intBasis.repr v 1 +
         12 * BSD_intBasis.repr a 1 * BSD_intBasis.repr b 1,
         by nlinarith [hmul0, hmul1, eq_sum]⟩
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hdvd
      push_cast at h ⊢; exact h
    rcases mul_eq_zero.mp hzmod with ha | hb
    · left
      have h3 : (3:ℤ) ∣ BSD_intBasis.repr a 0 + BSD_intBasis.repr a 1 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast at ha ⊢; exact ha)
      obtain ⟨k, hk⟩ := h3
      exact ⟨k • BSD_intBasis 0, (-BSD_intBasis.repr a 1) • BSD_intBasis 0, by
        have heq : (algebraMap (𝓞 K) K)
            (k • BSD_intBasis 0 * 3 + (-BSD_intBasis.repr a 1) • BSD_intBasis 0 * (1 - nω_OK)) =
            (algebraMap (𝓞 K) K) a := by
          simp only [map_add, map_mul, map_ofNat, zsmul_eq_mul, map_neg, map_sub, map_intCast,
                     BSD_intBasis_zero_coe, BSD_intBasis_one_coe, nω_OK_coe, coord_decomp' a,
                     mul_one, one_mul]
          push_cast
          have hk' : (3 : K) * k = BSD_intBasis.repr a 0 + BSD_intBasis.repr a 1 := by
            exact_mod_cast hk.symm
          linear_combination hk'
        exact Subtype.coe_injective heq⟩
    · right
      have h3 : (3:ℤ) ∣ BSD_intBasis.repr b 0 + BSD_intBasis.repr b 1 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by push_cast at hb ⊢; exact hb)
      obtain ⟨k, hk⟩ := h3
      exact ⟨k • BSD_intBasis 0, (-BSD_intBasis.repr b 1) • BSD_intBasis 0, by
        have heq : (algebraMap (𝓞 K) K)
            (k • BSD_intBasis 0 * 3 + (-BSD_intBasis.repr b 1) • BSD_intBasis 0 * (1 - nω_OK)) =
            (algebraMap (𝓞 K) K) b := by
          simp only [map_add, map_mul, map_ofNat, zsmul_eq_mul, map_neg, map_sub, map_intCast,
                     BSD_intBasis_zero_coe, BSD_intBasis_one_coe, nω_OK_coe, coord_decomp' b,
                     mul_one, one_mul]
          push_cast
          have hk' : (3 : K) * k = BSD_intBasis.repr b 0 + BSD_intBasis.repr b 1 := by
            exact_mod_cast hk.symm
          linear_combination hk'
        exact Subtype.coe_injective heq⟩

/-- Helper: for any prime ideal P of norm 7, P = p₇ or P = p̄₇. -/
lemma prime_norm7_eq (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hn : Ideal.absNorm P = 7) :
    P = p7_OK ∨ P = pbar7_OK := by
  have h7 : (7 : 𝓞 K) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hcard : Nat.card (𝓞 K ⧸ P) = 7 := by rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
    have hord : addOrderOf (1 : 𝓞 K ⧸ P) ∣ 7 := hcard ▸ addOrderOf_dvd_natCard _
    rw [addOrderOf_dvd_iff_nsmul_eq_zero] at hord
    change (7 : 𝓞 K ⧸ P) = 0
    rw [show (7 : 𝓞 K ⧸ P) = (7 : ℕ) • (1 : 𝓞 K ⧸ P) from by norm_num]
    exact hord
  have hP_dvd : P ∣ p7_OK * pbar7_OK := by
    rw [p7_mul_pbar7]
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr h7)
  have hP_ne_top : P ≠ ⊤ := by
    intro heq; rw [Ideal.absNorm_eq_one_iff.mpr heq] at hn; norm_num at hn
  have hpb7_IsPrime : pbar7_OK.IsPrime := by
    rw [Ideal.isPrime_iff]
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · rw [Ideal.eq_top_iff_one, pbar7_OK, Ideal.mem_span_pair] at h
      obtain ⟨u, v, huv⟩ := h
      have hK : ((1 - 7 * BSD_intBasis.repr u 0 - 2 * BSD_intBasis.repr v 0 + 36 * BSD_intBasis.repr v 1 : ℤ) : K) +
                ((-7 * BSD_intBasis.repr u 1 - BSD_intBasis.repr v 0 - 3 * BSD_intBasis.repr v 1 : ℤ) : K) * ω = 0 := by
        have h1K := congrArg (algebraMap (𝓞 K) K) huv
        simp only [map_add, map_mul, map_ofNat, nω_OK_coe, map_one] at h1K
        rw [coord_decomp_map u, coord_decomp_map v] at h1K
        push_cast; ring_nf; push_cast at h1K; ring_nf at h1K
        linear_combination -h1K + (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
      obtain ⟨h0, h1⟩ := repr_uniq' _ _ hK
      have : (7 : ℤ) ∣ 1 :=
        ⟨BSD_intBasis.repr u 0 - 2 * BSD_intBasis.repr u 1 - 6 * BSD_intBasis.repr v 1, by linarith⟩
      omega
    · simp only [pbar7_OK, Ideal.mem_span_pair] at hab ⊢
      obtain ⟨u, v, huv⟩ := hab
      have hmul0 := (mul_coords' a b).1; have hmul1 := (mul_coords' a b).2
      have hzmod : ((BSD_intBasis.repr a 0 : ℤ) : ZMod 7) + 5 *
                   ((BSD_intBasis.repr a 1 : ℤ) : ZMod 7) = 0 ∨
                   ((BSD_intBasis.repr b 0 : ℤ) : ZMod 7) + 5 *
                   ((BSD_intBasis.repr b 1 : ℤ) : ZMod 7) = 0 := by
        have hK : ((7 * BSD_intBasis.repr u 0 + 2 * BSD_intBasis.repr v 0 - 36 * BSD_intBasis.repr v 1 -
                    BSD_intBasis.repr (a*b) 0 : ℤ) : K) +
                  ((7 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 + 3 * BSD_intBasis.repr v 1 -
                    BSD_intBasis.repr (a*b) 1 : ℤ) : K) * ω = 0 := by
          have h1K := congrArg (algebraMap (𝓞 K) K) huv
          simp only [map_add, map_mul, map_ofNat, nω_OK_coe] at h1K
          conv at h1K => rhs; rw [← map_mul]
          rw [coord_decomp_map (a*b), coord_decomp_map u, coord_decomp_map v] at h1K
          push_cast; ring_nf; push_cast at h1K; ring_nf at h1K
          linear_combination h1K - (BSD_intBasis.repr v 1 : K) * ω_sq_eq_BSD
        have eq0 : BSD_intBasis.repr (a*b) 0 =
            7 * BSD_intBasis.repr u 0 + 2 * BSD_intBasis.repr v 0 - 36 * BSD_intBasis.repr v 1 := by
          have := (repr_uniq' _ _ hK).1; linarith
        have eq1 : BSD_intBasis.repr (a*b) 1 =
            7 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 + 3 * BSD_intBasis.repr v 1 := by
          have := (repr_uniq' _ _ hK).2; linarith
        have hdvd : (7 : ℤ) ∣ (BSD_intBasis.repr a 0 + 5 * BSD_intBasis.repr a 1) *
                               (BSD_intBasis.repr b 0 + 5 * BSD_intBasis.repr b 1) :=
          ⟨BSD_intBasis.repr u 0 + 5 * BSD_intBasis.repr u 1 + BSD_intBasis.repr v 0 -
           3 * BSD_intBasis.repr v 1 + 8 * BSD_intBasis.repr a 1 * BSD_intBasis.repr b 1,
           by nlinarith [hmul0, hmul1, eq0, eq1]⟩
        have key : (((BSD_intBasis.repr a 0 : ℤ) : ZMod 7) + 5 * ((BSD_intBasis.repr a 1 : ℤ) : ZMod 7)) *
                   (((BSD_intBasis.repr b 0 : ℤ) : ZMod 7) + 5 * ((BSD_intBasis.repr b 1 : ℤ) : ZMod 7)) = 0 := by
          have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hdvd
          push_cast at h; exact h
        haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
        exact mul_eq_zero.mp key
      rcases hzmod with ha | hb
      · left
        have h7 : (7 : ℤ) ∣ BSD_intBasis.repr a 0 + 5 * BSD_intBasis.repr a 1 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp (by push_cast at ha ⊢; exact ha)
        obtain ⟨k, hk⟩ := h7
        exact ⟨(k - BSD_intBasis.repr a 1) • BSD_intBasis 0, BSD_intBasis.repr a 1 • BSD_intBasis 0, by
          have heq : (algebraMap (𝓞 K) K)
              ((k - BSD_intBasis.repr a 1) • BSD_intBasis 0 * 7 +
               BSD_intBasis.repr a 1 • BSD_intBasis 0 * (nω_OK + 2)) =
              (algebraMap (𝓞 K) K) a := by
            simp only [map_add, map_mul, map_ofNat, zsmul_eq_mul, map_neg, map_sub, map_intCast,
                       BSD_intBasis_zero_coe, BSD_intBasis_one_coe, nω_OK_coe, coord_decomp' a,
                       mul_one, one_mul]
            push_cast
            have hk' : (BSD_intBasis.repr a 0 : K) + 5 * (BSD_intBasis.repr a 1 : K) = 7 * (k : K) := by
              exact_mod_cast hk
            linear_combination -hk'
          exact Subtype.coe_injective heq⟩
      · right
        have h7 : (7 : ℤ) ∣ BSD_intBasis.repr b 0 + 5 * BSD_intBasis.repr b 1 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp (by push_cast at hb ⊢; exact hb)
        obtain ⟨k, hk⟩ := h7
        exact ⟨(k - BSD_intBasis.repr b 1) • BSD_intBasis 0, BSD_intBasis.repr b 1 • BSD_intBasis 0, by
          have heq : (algebraMap (𝓞 K) K)
              ((k - BSD_intBasis.repr b 1) • BSD_intBasis 0 * 7 +
               BSD_intBasis.repr b 1 • BSD_intBasis 0 * (nω_OK + 2)) =
              (algebraMap (𝓞 K) K) b := by
            simp only [map_add, map_mul, map_ofNat, zsmul_eq_mul, map_neg, map_sub, map_intCast,
                       BSD_intBasis_zero_coe, BSD_intBasis_one_coe, nω_OK_coe, coord_decomp' b,
                       mul_one, one_mul]
            push_cast
            have hk' : (BSD_intBasis.repr b 0 : K) + 5 * (BSD_intBasis.repr b 1 : K) = 7 * (k : K) := by
              exact_mod_cast hk
            linear_combination -hk'
          exact Subtype.coe_injective heq⟩
  have hP_ne_bot : P ≠ ⊥ := by intro h; rw [h, Ideal.absNorm_bot] at hn; norm_num at hn
  have hP_prime_el : Prime P := (Ideal.prime_iff_isPrime hP_ne_bot).mpr hP
  rcases hP_prime_el.dvd_or_dvd hP_dvd with h | h
  · left
    have hp7_max := Ring.DimensionLEOne.maximalOfPrime (by
      intro heq; have h_abs := absNorm_p7_eq_7; rw [heq, Ideal.absNorm_bot] at h_abs; norm_num at h_abs) p7_IsPrime
    exact (hp7_max.eq_of_le hP_ne_top (Ideal.dvd_iff_le.mp h)).symm
  · right
    have hpb7_max := Ring.DimensionLEOne.maximalOfPrime (by
      intro heq; have h_abs := absNorm_pbar7_eq_7; rw [heq, Ideal.absNorm_bot] at h_abs; norm_num at h_abs) hpb7_IsPrime
    exact (hpb7_max.eq_of_le hP_ne_top (Ideal.dvd_iff_le.mp h)).symm

/-- The class of a prime ideal of norm in {2,3,7} is in ⟨p₂_class_gen⟩. -/
lemma prime_class_in_zpowers (P : Ideal (𝓞 K))
    (hP_prime : P.IsPrime)
    (hP_ne_bot : P ≠ ⊥)
    (hP_norm_le7 : Ideal.absNorm P ≤ 7)
    (hP_norm_ge2 : 2 ≤ Ideal.absNorm P)
    (hP_nzd : P ∈ nonZeroDivisors (Ideal (𝓞 K))) :
    ClassGroup.mk0 ⟨P, hP_nzd⟩ ∈ Subgroup.zpowers p2_class_gen := by
  -- absNorm P is a prime (since P is a prime ideal in a number field of degree 2)
  -- and it lies in {2, 3, 5, 7} ∩ {2,...,7} = {2,3,5,7}
  -- absNorm = 5 is impossible (5 is inert, prime above 5 has norm 25)
  -- So absNorm P ∈ {2, 3, 7}; classify
  have hP_absNorm_bound : Ideal.absNorm P ≤ 7 := hP_norm_le7
  interval_cases h : Ideal.absNorm P
  all_goals (first | omega | skip)
  · -- absNorm P = 2
    rcases prime_norm2_eq P hP_prime h with rfl | rfl
    · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp [p2_class_gen]⟩
    · rw [show ClassGroup.mk0 ⟨pbar2_OK, hP_nzd⟩ = pbar2_class from rfl,
          pbar2_class_eq_inv]
      exact Subgroup.mem_zpowers_iff.mpr ⟨-1, by simp [zpow_neg_one]⟩
  · -- absNorm P = 3
    rcases prime_norm3_eq P hP_prime h with rfl | rfl
    · rw [show ClassGroup.mk0 ⟨p3_OK, hP_nzd⟩ = p3_class from rfl, p3_class_eq_pow4]
      exact Subgroup.mem_zpowers_iff.mpr ⟨4, by norm_cast⟩
    · rw [show ClassGroup.mk0 ⟨pbar3_OK, hP_nzd⟩ = pbar3_class from rfl, pbar3_class_eq_pow6]
      exact Subgroup.mem_zpowers_iff.mpr ⟨6, by norm_cast⟩
  · -- absNorm P = 4: impossible (no prime of norm 4; 2 splits giving norm 2 primes)
    have h4_imp : False := by
      -- Any prime of norm 4 would contain 2, divide p2*pbar2, and by maximality = p2 or pbar2,
      -- but those have norm 2, contradiction
      have h4 : (4 : 𝓞 K) ∈ P := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        have hcard : Nat.card (𝓞 K ⧸ P) = 4 := by rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
        have hord4 : (4 : ℕ) • (1 : 𝓞 K ⧸ P) = 0 :=
          addOrderOf_dvd_iff_nsmul_eq_zero.mp (hcard ▸ addOrderOf_dvd_natCard _)
        change (4 : 𝓞 K ⧸ P) = 0
        rw [show (4 : 𝓞 K ⧸ P) = (4 : ℕ) • (1 : 𝓞 K ⧸ P) from by norm_num]; exact hord4
      have hP_dvd_sq : P ∣ p2_OK ^ 2 * pbar2_OK ^ 2 := by
        have hsq : p2_OK ^ 2 * pbar2_OK ^ 2 = Ideal.span {(4 : 𝓞 K)} := by
          rw [show (4 : 𝓞 K) = (2 : 𝓞 K) ^ 2 from by norm_num,
              ← Ideal.span_singleton_pow, ← p2_mul_pbar2, mul_pow]
        rw [hsq]; exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr h4)
      have hP_prime_el : Prime P := (Ideal.prime_iff_isPrime hP_ne_bot).mpr hP_prime
      rcases hP_prime_el.dvd_or_dvd hP_dvd_sq with h2sq | hpb2sq
      · have : P ∣ p2_OK := hP_prime_el.dvd_of_dvd_pow h2sq
        have hp2_max := Ring.DimensionLEOne.maximalOfPrime (by
          intro heq; have h_abs := absNorm_p2_eq_2; rw [heq, Ideal.absNorm_bot] at h_abs; norm_num at h_abs) p2_IsPrime
        have hP_ne_top : P ≠ ⊤ := by
          intro heq; rw [Ideal.absNorm_eq_one_iff.mpr heq] at h; norm_num at h
        have hP_eq_p2 := (hp2_max.eq_of_le hP_ne_top (Ideal.dvd_iff_le.mp this)).symm
        rw [hP_eq_p2, absNorm_p2_eq_2] at h; norm_num at h
      · have : P ∣ pbar2_OK := hP_prime_el.dvd_of_dvd_pow hpb2sq
        have hpb2_max := Ring.DimensionLEOne.maximalOfPrime (by
          intro heq; have h_abs := absNorm_pbar2_eq_2; rw [heq, Ideal.absNorm_bot] at h_abs; norm_num at h_abs) pbar2_IsPrime
        have hP_ne_top : P ≠ ⊤ := by
          intro heq; rw [Ideal.absNorm_eq_one_iff.mpr heq] at h; norm_num at h
        have hP_eq_pb2 := (hpb2_max.eq_of_le hP_ne_top (Ideal.dvd_iff_le.mp this)).symm
        rw [hP_eq_pb2, absNorm_pbar2_eq_2] at h; norm_num at h
    exact h4_imp.elim
  · -- absNorm P = 5: impossible (5 is inert, prime above 5 has norm 25)
    have h5_imp : False := by
      have h5 : (5 : 𝓞 K) ∈ P := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        have hcard : Nat.card (𝓞 K ⧸ P) = 5 := by rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
        have hord : (5 : ℕ) • (1 : 𝓞 K ⧸ P) = 0 :=
          addOrderOf_dvd_iff_nsmul_eq_zero.mp (hcard ▸ addOrderOf_dvd_natCard _)
        change (5 : 𝓞 K ⧸ P) = 0
        rw [show (5 : 𝓞 K ⧸ P) = (5 : ℕ) • (1 : 𝓞 K ⧸ P) from by norm_num]; exact hord
      have hP_dvd5 : P ∣ Ideal.span {(5 : 𝓞 K)} :=
        Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr h5)
      -- span{5} has norm 25; P has norm 5; P | span{5} and P.IsPrime
      -- In a Dedekind domain, P | span{5} means span{5} = P * J
      obtain ⟨J, hJ⟩ := hP_dvd5
      have hJ_norm : Ideal.absNorm J = 5 := by
        have := congr_arg Ideal.absNorm hJ
        rw [map_mul, h, absNorm_span_five'] at this; omega
      -- But span{5} is irreducible (5 is inert): absNorm span{5} = 25 = 5^2
      -- and its only factorization must have J prime of norm 5
      -- which means J = span{5}/P... this creates an infinite descent
      -- More directly: absNorm(J) = 5, so J has a prime factor M of norm ≤ 5
      -- and absNorm(J) * absNorm(P) = 25 = absNorm(span{5})
      -- P | span{5} and span{5} is an Ideal; from span{5} IsPrime:
      -- span{5} = algebraMap 5, which in ℤ[√-143] factors as... 5 inert means span{5}.IsPrime
      -- Let's show span{5} is prime and derive contradiction
      have h5_prime : (Ideal.span {(5 : 𝓞 K)}).IsPrime := by
        rw [Ideal.isPrime_iff]
        refine ⟨fun h5top => ?_, fun {a} {b} hab => ?_⟩
        · have h1 := Ideal.absNorm_eq_one_iff.mpr h5top
          linarith [absNorm_span_five']
        · simp only [Ideal.mem_span_singleton] at hab ⊢
          have ⟨hmul0, hmul1⟩ := mul_coords' a b
          have hdvd5 : (5 : ℤ) ∣ BSD_intBasis.repr (a*b) 0 := by
            obtain ⟨u, hu⟩ := hab
            have hK : ((5 * BSD_intBasis.repr u 0 - BSD_intBasis.repr (a*b) 0 : ℤ) : K) +
                      ((5 * BSD_intBasis.repr u 1 - BSD_intBasis.repr (a*b) 1 : ℤ) : K) * ω = 0 := by
              have h1K := congrArg (algebraMap (𝓞 K) K) hu
              simp only [map_mul, map_ofNat] at h1K
              conv at h1K => lhs; rw [← map_mul]
              rw [coord_decomp_map (a*b), coord_decomp_map u] at h1K
              push_cast; push_cast at h1K; linear_combination -h1K
            exact ⟨BSD_intBasis.repr u 0, by linarith [(repr_uniq' _ _ hK).1]⟩
          have hdvd5' : (5 : ℤ) ∣ BSD_intBasis.repr (a*b) 1 := by
            obtain ⟨u, hu⟩ := hab
            have hK : ((5 * BSD_intBasis.repr u 0 - BSD_intBasis.repr (a*b) 0 : ℤ) : K) +
                      ((5 * BSD_intBasis.repr u 1 - BSD_intBasis.repr (a*b) 1 : ℤ) : K) * ω = 0 := by
              have h1K := congrArg (algebraMap (𝓞 K) K) hu
              simp only [map_mul, map_ofNat] at h1K
              conv at h1K => lhs; rw [← map_mul]
              rw [coord_decomp_map (a*b), coord_decomp_map u] at h1K
              push_cast; push_cast at h1K; linear_combination -h1K
            exact ⟨BSD_intBasis.repr u 1, by linarith [(repr_uniq' _ _ hK).2]⟩
          have hzmod : ((BSD_intBasis.repr a 0 : ℤ) : ZMod 5) *
                       ((BSD_intBasis.repr b 0 : ℤ) : ZMod 5) -
                       ((BSD_intBasis.repr a 1 : ℤ) : ZMod 5) *
                       ((BSD_intBasis.repr b 1 : ℤ) : ZMod 5) = 0 ∧
                       ((BSD_intBasis.repr a 0 : ℤ) : ZMod 5) *
                       ((BSD_intBasis.repr b 1 : ℤ) : ZMod 5) +
                       ((BSD_intBasis.repr a 1 : ℤ) : ZMod 5) *
                       ((BSD_intBasis.repr b 0 : ℤ) : ZMod 5) +
                       ((BSD_intBasis.repr a 1 : ℤ) : ZMod 5) *
                       ((BSD_intBasis.repr b 1 : ℤ) : ZMod 5) = 0 := by
            constructor
            · have h36 : (36 : ZMod 5) = 1 := by decide
              have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (BSD_intBasis.repr (a*b) 0) 5).mpr hdvd5
              rw [hmul0] at h0; push_cast [h36] at h0 ⊢
              linear_combination h0
            · have := (ZMod.intCast_zmod_eq_zero_iff_dvd (BSD_intBasis.repr (a*b) 1) 5).mpr hdvd5'
              rw [hmul1] at this; push_cast at this ⊢; exact this
          -- decide: over ZMod 5, the above system implies a=0 or b=0
          have h5_domain : ∀ a0 a1 b0 b1 : ZMod 5,
              a0 * b0 - a1 * b1 = 0 →
              a0 * b1 + a1 * b0 + a1 * b1 = 0 →
              (a0 = 0 ∧ a1 = 0) ∨ (b0 = 0 ∧ b1 = 0) := by decide
          have := h5_domain (BSD_intBasis.repr a 0 : ZMod 5) (BSD_intBasis.repr a 1 : ZMod 5)
                             (BSD_intBasis.repr b 0 : ZMod 5) (BSD_intBasis.repr b 1 : ZMod 5)
            hzmod.1 hzmod.2
          rcases this with ⟨ha0, ha1⟩ | ⟨hb0, hb1⟩
          · left
            have h5a0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp ha0
            have h5a1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp ha1
            obtain ⟨c, hc⟩ := h5a0; obtain ⟨d, hd⟩ := h5a1
            exact ⟨c • BSD_intBasis 0 + d • BSD_intBasis 1, by
              have heq : (algebraMap (𝓞 K) K) a =
                         (algebraMap (𝓞 K) K) (5 * (c • BSD_intBasis 0 + d • BSD_intBasis 1)) := by
                simp only [map_mul, map_ofNat, map_add, zsmul_eq_mul, map_intCast,
                           BSD_intBasis_zero_coe, BSD_intBasis_one_coe, mul_one, one_mul,
                           coord_decomp' a]
                push_cast
                have hc' : (BSD_intBasis.repr a 0 : K) = 5 * c := by exact_mod_cast hc
                have hd' : (BSD_intBasis.repr a 1 : K) = 5 * d := by exact_mod_cast hd
                rw [hc', hd']; ring
              exact Subtype.coe_injective heq⟩
          · right
            have h5b0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp hb0
            have h5b1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp hb1
            obtain ⟨c, hc⟩ := h5b0; obtain ⟨d, hd⟩ := h5b1
            exact ⟨c • BSD_intBasis 0 + d • BSD_intBasis 1, by
              have heq : (algebraMap (𝓞 K) K) b =
                         (algebraMap (𝓞 K) K) (5 * (c • BSD_intBasis 0 + d • BSD_intBasis 1)) := by
                simp only [map_mul, map_ofNat, map_add, zsmul_eq_mul, map_intCast,
                           BSD_intBasis_zero_coe, BSD_intBasis_one_coe, mul_one, one_mul,
                           coord_decomp' b]
                push_cast
                have hc' : (BSD_intBasis.repr b 0 : K) = 5 * c := by exact_mod_cast hc
                have hd' : (BSD_intBasis.repr b 1 : K) = 5 * d := by exact_mod_cast hd
                rw [hc', hd']; ring
              exact Subtype.coe_injective heq⟩
      -- P divides span{5} which is prime; by primality of span{5}: P = span{5}
      have hP_ne_top : P ≠ ⊤ := by intro heq; rw [Ideal.absNorm_eq_one_iff.mpr heq] at h; norm_num at h
      have h5_ne_bot : Ideal.span {(5:𝓞 K)} ≠ ⊥ := by simp [absNorm_span_five']
      have h5_ne_top : Ideal.span {(5:𝓞 K)} ≠ ⊤ := by
        intro heq; have := absNorm_span_five'; rw [heq, Ideal.absNorm_top] at this; norm_num at this
      have h5_max := Ring.DimensionLEOne.maximalOfPrime h5_ne_bot h5_prime
      -- P ≤ span{5} (from P | span{5})
      have hP_le_5 : Ideal.span {(5:𝓞 K)} ≤ P := Ideal.dvd_iff_le.mp ⟨J, hJ⟩
      have hP_eq_5 := (h5_max.eq_of_le hP_ne_top hP_le_5).symm
      rw [hP_eq_5, absNorm_span_five'] at h; norm_num at h
    exact h5_imp.elim
  · -- absNorm P = 6: impossible (not a prime power; 6 = 2*3)
    -- A prime ideal in a number field of degree 2 has norm p^f, f ∈ {1,2}
    -- So norm ∈ {p, p^2} for rational prime p. 6 = 2*3 is not a prime power.
    -- Derive contradiction: P | span{2} or P | span{3}
    have h2or3 : (2 : 𝓞 K) ∈ P ∨ (3 : 𝓞 K) ∈ P := by
      by_contra hboth
      push_neg at hboth
      obtain ⟨h2, h3⟩ := hboth
      -- P + span{2} = ⊤ (since 2 ∉ P and P is maximal)
      have hP_ne_top : P ≠ ⊤ := by intro heq; rw [Ideal.absNorm_eq_one_iff.mpr heq] at h; norm_num at h
      have hP_max := Ring.DimensionLEOne.maximalOfPrime hP_ne_bot hP_prime
      have h2_notmem : ¬ (Ideal.span {(2:𝓞 K)} ≤ P) := by
        rwa [Ideal.span_singleton_le_iff_mem]
      have h3_notmem : ¬ (Ideal.span {(3:𝓞 K)} ≤ P) := by
        rwa [Ideal.span_singleton_le_iff_mem]
      -- Since P is maximal and span{2} ⊄ P: P + span{2} = ⊤
      -- Then P ∩ span{6} = P*(P + span{2})*... complex; use norm argument instead
      -- absNorm P = 6 = 2*3; |𝓞 K/P| = 6; but P.IsPrime means 𝓞 K/P is a domain
      -- A finite domain has prime power order; 6 is not a prime power. Contradiction.
      -- In Lean: use that a finite integral domain has characteristic that is prime
      -- and characteristic^degree = |domain|, so |domain| is a prime power
      -- For a field of order 6: impossible by Wedderburn since 6 is not a prime power
      have hcard : Nat.card (𝓞 K ⧸ P) = 6 := by rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
      -- 2*3 = 0 in 𝓞 K/P (since |𝓞 K/P| = 6 and 6*1 = 0)
      have h6z : (6 : ℕ) • (1 : 𝓞 K ⧸ P) = 0 :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mp (hcard ▸ addOrderOf_dvd_natCard _)
      -- 6·1 = 0 in an integral domain 𝓞 K/P
      -- So (2·1)*(3·1) = 6·1 = 0, and by ID: 2·1=0 or 3·1=0
      have h2or3_quot : (2 : 𝓞 K ⧸ P) = 0 ∨ (3 : 𝓞 K ⧸ P) = 0 := by
        have hprod : (2 : 𝓞 K ⧸ P) * (3 : 𝓞 K ⧸ P) = 0 := by
          rw [show (2 : 𝓞 K ⧸ P) * 3 = (6 : 𝓞 K ⧸ P) from by norm_num]
          rw [show (6 : 𝓞 K ⧸ P) = (6 : ℕ) • (1 : 𝓞 K ⧸ P) from by norm_num]
          exact h6z
        haveI : P.IsPrime := hP_prime
        exact mul_eq_zero.mp hprod
      rcases h2or3_quot with h2q | h3q
      · exact h2 ((Ideal.Quotient.eq_zero_iff_mem).mp h2q)
      · exact h3 ((Ideal.Quotient.eq_zero_iff_mem).mp h3q)
    have hP_prime_el : Prime P := (Ideal.prime_iff_isPrime hP_ne_bot).mpr hP_prime
    rcases h2or3 with h2 | h3
    · -- P contains 2, so P | span{2} = p2 * pbar2
      have hP_dvd2 : P ∣ p2_OK * pbar2_OK := by
        rw [p2_mul_pbar2]; exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr h2)
      rcases hP_prime_el.dvd_or_dvd hP_dvd2 with hdvd2 | hdvd2
      · have hP_le := Ideal.dvd_iff_le.mp hdvd2
        have hP_ne_top2 : P ≠ ⊤ := by intro heq; rw [Ideal.absNorm_eq_one_iff.mpr heq] at h; norm_num at h
        have hp2_max := Ring.DimensionLEOne.maximalOfPrime (by intro heq; have h_abs := absNorm_p2_eq_2; rw [heq, Ideal.absNorm_bot] at h_abs; norm_num at h_abs) p2_IsPrime
        have heq2 := (hp2_max.eq_of_le hP_ne_top2 hP_le).symm
        rw [heq2, absNorm_p2_eq_2] at h; norm_num at h
      · have hP_le := Ideal.dvd_iff_le.mp hdvd2
        have hP_ne_top2 : P ≠ ⊤ := by intro heq; rw [Ideal.absNorm_eq_one_iff.mpr heq] at h; norm_num at h
        have hpb2_max := Ring.DimensionLEOne.maximalOfPrime (by intro heq; have h_abs := absNorm_pbar2_eq_2; rw [heq, Ideal.absNorm_bot] at h_abs; norm_num at h_abs) pbar2_IsPrime
        have heq2 := (hpb2_max.eq_of_le hP_ne_top2 hP_le).symm
        rw [heq2, absNorm_pbar2_eq_2] at h; norm_num at h
    · -- P contains 3, so P | span{3} = p3 * pbar3
      have hP_dvd3 : P ∣ p3_OK * pbar3_OK := by
        rw [p3_mul_pbar3]; exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr h3)
      rcases hP_prime_el.dvd_or_dvd hP_dvd3 with hdvd3 | hdvd3
      · have hP_le := Ideal.dvd_iff_le.mp hdvd3
        have hP_ne_top3 : P ≠ ⊤ := by intro heq; rw [Ideal.absNorm_eq_one_iff.mpr heq] at h; norm_num at h
        have hp3_max := Ring.DimensionLEOne.maximalOfPrime (by intro heq; have h_abs := absNorm_p3_eq_3; rw [heq, Ideal.absNorm_bot] at h_abs; norm_num at h_abs) p3_IsPrime
        have heq3 := (hp3_max.eq_of_le hP_ne_top3 hP_le).symm
        rw [heq3, absNorm_p3_eq_3] at h; norm_num at h
      · have hP_le := Ideal.dvd_iff_le.mp hdvd3
        have hP_ne_top3 : P ≠ ⊤ := by intro heq; rw [Ideal.absNorm_eq_one_iff.mpr heq] at h; norm_num at h
        have hpb3_ne_bot : pbar3_OK ≠ ⊥ := by intro heq; have h_abs := absNorm_pbar3_eq_3; rw [heq, Ideal.absNorm_bot] at h_abs; norm_num at h_abs
        have hpb3_max := Ring.DimensionLEOne.maximalOfPrime hpb3_ne_bot pbar3_OK_isPrime
        have heq3 := (hpb3_max.eq_of_le hP_ne_top3 hP_le).symm
        rw [heq3, absNorm_pbar3_eq_3] at h; norm_num at h
  · -- absNorm P = 7
    rcases prime_norm7_eq P hP_prime h with rfl | rfl
    · rw [show ClassGroup.mk0 ⟨p7_OK, hP_nzd⟩ = p7_class from rfl, p7_class_eq_pow7]
      exact Subgroup.mem_zpowers_iff.mpr ⟨7, by norm_cast⟩
    · rw [show ClassGroup.mk0 ⟨pbar7_OK, hP_nzd⟩ = pbar7_class from rfl, pbar7_class_eq_pow3]
      exact Subgroup.mem_zpowers_iff.mpr ⟨3, by norm_cast⟩

/-- **BSD_small_norm_in_zpowers_CLOSED** (0 sorry, classical trio):
    Every nonzero ideal `I` of `absNorm I ≤ 7` has `[I] ∈ ⟨[p₂]⟩`. -/
theorem BSD_small_norm_in_zpowers_CLOSED : BSD_small_norm_in_zpowers_OPEN := by
  intro I hn7
  -- Strong induction on n = absNorm I
  set n := Ideal.absNorm (I : Ideal (𝓞 K)) with hn_def
  -- Build the general statement via Nat.strongRecOn
  suffices key : ∀ m : ℕ, m ≤ 7 → ∀ J : nonZeroDivisors (Ideal (𝓞 K)),
      Ideal.absNorm (J : Ideal (𝓞 K)) = m →
      ClassGroup.mk0 J ∈ Subgroup.zpowers p2_class_gen from
    key n hn7 I rfl
  intro m hm7
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro J hJm
    have hJ_absNorm_pos : 0 < Ideal.absNorm (J : Ideal (𝓞 K)) :=
      Nat.pos_of_ne_zero (fun h => nonZeroDivisors.coe_ne_zero J (Ideal.absNorm_eq_zero_iff.mp h))
    rcases Nat.eq_or_lt_of_le hJ_absNorm_pos with h1 | h1
    · -- absNorm J = 1 → J = ⊤ → class = 1
      have hJ_top : (J : Ideal (𝓞 K)) = ⊤ := Ideal.absNorm_eq_one_iff.mp (by omega)
      have hmk1 : ClassGroup.mk0 J = 1 :=
        (ClassGroup.mk0_eq_one_iff J.property).mpr
          ⟨⟨1, hJ_top.trans Ideal.span_singleton_one.symm⟩⟩
      rw [hmk1]; exact Subgroup.one_mem _
    · -- absNorm J ≥ 2: get a maximal ideal M with M ≤ J
      have hJ_ne_top : (J : Ideal (𝓞 K)) ≠ ⊤ := by
        intro h
        have h_abs : Ideal.absNorm (↑J : Ideal (𝓞 K)) = 1 := Ideal.absNorm_eq_one_iff.mpr h
        linarith [h_abs, h1]
      obtain ⟨M, hM_max, hM_le⟩ := Ideal.exists_le_maximal (J : Ideal (𝓞 K)) hJ_ne_top
      have hM_prime := hM_max.isPrime
      -- M ∣ J
      have hM_dvd : M ∣ (J : Ideal (𝓞 K)) := Ideal.dvd_iff_le.mpr hM_le
      obtain ⟨L, hL⟩ := hM_dvd
      -- absNorm M * absNorm L = m
      have hM_ne_bot : M ≠ ⊥ := by
        intro heq
        rw [heq] at hM_le
        have hJbot : (↑J : Ideal (𝓞 K)) = ⊥ := le_bot_iff.mp hM_le
        exact nonZeroDivisors.coe_ne_zero J hJbot
      have hM_ne_top : M ≠ ⊤ := hM_max.ne_top
      have hM_norm_ge2 : 2 ≤ Ideal.absNorm M := by
        have h0 : Ideal.absNorm M ≠ 0 := by
          intro h; exact hM_ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
        have h1' : Ideal.absNorm M ≠ 1 := fun h => hM_ne_top (Ideal.absNorm_eq_one_iff.mp h)
        omega
      have hML_eq : Ideal.absNorm M * Ideal.absNorm L = m := by
        have := congr_arg Ideal.absNorm hL
        rw [map_mul, hJm] at this; exact this.symm
      have hL_norm_lt : Ideal.absNorm L < m := by
        rcases Nat.eq_zero_or_pos (Ideal.absNorm L) with hL0 | hLpos
        · simp only [hL0, Nat.mul_zero] at hML_eq; linarith [hJm ▸ h1]
        · have h2L : 2 * Ideal.absNorm L ≤ Ideal.absNorm M * Ideal.absNorm L :=
            Nat.mul_le_mul_right (Ideal.absNorm L) hM_norm_ge2
          linarith [hML_eq, hLpos]
      have hL_norm_le7 : Ideal.absNorm L ≤ 7 := le_trans (Nat.le_of_lt hL_norm_lt) (by omega)
      -- L is a nonzero divisor
      have hL_ne_bot : L ≠ ⊥ := by
        intro heq
        simp only [heq, Ideal.mul_bot] at hL
        exact nonZeroDivisors.coe_ne_zero J hL
      have hL_nzd : L ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
        mem_nonZeroDivisors_of_ne_zero hL_ne_bot
      -- M is a nonzero divisor
      have hM_nzd : M ∈ nonZeroDivisors (Ideal (𝓞 K)) :=
        mem_nonZeroDivisors_of_ne_zero hM_ne_bot
      -- absNorm M ≤ 7 (since absNorm M ≤ m ≤ 7)
      have hM_norm_le7 : Ideal.absNorm M ≤ 7 := by
        have hL_pos : 1 ≤ Ideal.absNorm L :=
          Nat.one_le_iff_ne_zero.mpr (by intro h; exact hL_ne_bot (Ideal.absNorm_eq_zero_iff.mp (by omega)))
        nlinarith [hML_eq, hm7]
      -- Class group: [J] = [M] * [L]
      have hJML : ClassGroup.mk0 J =
                  ClassGroup.mk0 ⟨M, hM_nzd⟩ * ClassGroup.mk0 ⟨L, hL_nzd⟩ := by
        rw [← (ClassGroup.mk0 : nonZeroDivisors (Ideal (𝓞 K)) →* ClassGroup (𝓞 K)).map_mul]
        congr 1
        exact Subtype.ext hL
      rw [hJML]
      -- [M] ∈ zpowers (from prime classification)
      have hM_in : ClassGroup.mk0 ⟨M, hM_nzd⟩ ∈ Subgroup.zpowers p2_class_gen :=
        prime_class_in_zpowers M hM_prime hM_ne_bot hM_norm_le7 hM_norm_ge2 hM_nzd
      -- [L] ∈ zpowers (by induction hypothesis)
      have hL_norm_pos : 0 < Ideal.absNorm L :=
        Nat.pos_of_ne_zero (fun h => hL_ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
      have hL_in : ClassGroup.mk0 ⟨L, hL_nzd⟩ ∈ Subgroup.zpowers p2_class_gen := by
        rcases Nat.eq_or_lt_of_le hL_norm_pos with hL1 | hL1
        · have hL_top : L = ⊤ := Ideal.absNorm_eq_one_iff.mp (by omega)
          rw [show ClassGroup.mk0 ⟨L, hL_nzd⟩ = 1 from
            (ClassGroup.mk0_eq_one_iff hL_nzd).mpr ⟨⟨1, hL_top.trans Ideal.span_singleton_one.symm⟩⟩]
          exact Subgroup.one_mem _
        · exact ih (Ideal.absNorm L) hL_norm_lt hL_norm_le7 ⟨L, hL_nzd⟩ rfl
      -- Product of zpowers elements is in zpowers
      exact Subgroup.mul_mem _ hM_in hL_in

end Towers.BSD

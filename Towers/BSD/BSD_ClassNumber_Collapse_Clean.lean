/-
  The 14 → 10 collapse for the class group of K = ℚ(√-143).

  `ω = (1 + √-143) / 2` satisfies `ω² = ω - 36`, and `𝓞 K = ℤ[ω]`.
  The ideal `p2_OK = (2, ω)` has order at least 10 in the class group.
  The element `-28 + 3ω` has norm `1024` and lies in `p2_OK ^ 10`, whose
  absolute norm is also `1024`, so `p2_OK ^ 10 = (-28 + 3ω)` and the
  order is exactly 10.

  Above 2, 3 and 7 the rational prime splits as a pair of conjugate prime
  ideals. There is no ideal of norm 5. Every prime ideal factor of an
  integral ideal of absolute norm at most 7 is one of those six primes,
  and each of those six classes is a power of `[p2_OK]`. Every class
  therefore has a representative in the cyclic subgroup of order 10, so
  `classNumber K = 10`.

  The fourteen Hermite forms of index at most 7 are identified with
  `⊤`, the six split primes, `(2)`, `p2²`, `p2b²`, and the four products
  of a prime above 2 with a prime above 3. Their classes are the ten
  powers of `[p2_OK]`.

  This does not rewrite the 26 assessed Group B definitions.
  The assessed tally stays 54 of 504. No sorry.
-/

import Towers.BSD.BSD_ClassNumber_Clean
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

set_option maxHeartbeats 2000000

namespace Towers.BSD

open NumberField UniqueFactorizationMonoid
open scoped nonZeroDivisors

/-! ### Coordinates on ℤ[ω] -/

noncomputable def zLin (x y : ℤ) : 𝓞 K := (x : 𝓞 K) + (y : 𝓞 K) * nω_OK

theorem zLin_coe (x y : ℤ) : (zLin x y : K) = (x : K) + (y : K) * ω := by
  simp [zLin, map_add, map_mul, map_intCast, nω_OK_coe]

theorem nω_sq : nω_OK ^ 2 = nω_OK - 36 := by
  apply RingOfIntegers.ext
  simp only [map_pow, map_sub, map_ofNat, nω_OK_coe]
  linear_combination ω_sq_eq_BSD

theorem zLin_int (a : ℤ) : zLin a 0 = (a : 𝓞 K) := by
  simp [zLin]

theorem zLin_zero_one : zLin 0 1 = nω_OK := by
  simp [zLin]

theorem zLin_mul (x1 y1 x2 y2 : ℤ) :
    zLin x1 y1 * zLin x2 y2 =
      zLin (x1 * x2 - 36 * y1 * y2) (x1 * y2 + y1 * x2 + y1 * y2) := by
  apply RingOfIntegers.ext
  simp only [map_mul, zLin_coe]
  have hω : ω ^ 2 = ω - 36 := by linear_combination ω_sq_eq_BSD
  push_cast
  linear_combination (y1 * y2 : K) * hω

theorem zLin_mul_nat (n x y : ℤ) : (n : 𝓞 K) * zLin x y = zLin (n * x) (n * y) := by
  apply RingOfIntegers.ext
  simp only [map_mul, map_intCast, zLin_coe]
  push_cast
  ring

theorem zLin_zsmul (c x y : ℤ) : c • zLin x y = zLin (c * x) (c * y) := by
  rw [zsmul_eq_mul, zLin_mul_nat]

theorem zLin_add (x1 y1 x2 y2 : ℤ) :
    zLin x1 y1 + zLin x2 y2 = zLin (x1 + x2) (y1 + y2) := by
  apply RingOfIntegers.ext
  simp only [map_add, zLin_coe]
  push_cast
  ring

theorem zLin_combo4 (c0 c1 c2 c3 x0 y0 x1 y1 x2 y2 x3 y3 : ℤ) :
    c0 • zLin x0 y0 + c1 • zLin x1 y1 + c2 • zLin x2 y2 + c3 • zLin x3 y3 =
      zLin (c0 * x0 + c1 * x1 + c2 * x2 + c3 * x3)
        (c0 * y0 + c1 * y1 + c2 * y2 + c3 * y3) := by
  rw [zLin_zsmul, zLin_zsmul, zLin_zsmul, zLin_zsmul, zLin_add, zLin_add, zLin_add]

theorem basis_zero_eq_one : BSD_intBasis 0 = (1 : 𝓞 K) := by
  apply RingOfIntegers.ext
  simp [BSD_intBasis_zero_coe]

theorem zLin_eq_basis (x y : ℤ) :
    zLin x y = x • BSD_intBasis 0 + y • BSD_intBasis 1 := by
  rw [basis_zero_eq_one, nω_eq_b1.symm, zLin]
  simp [zsmul_eq_mul]

theorem zLin_repr (x y : ℤ) :
    BSD_intBasis.repr (zLin x y) = Finsupp.single 0 x + Finsupp.single 1 y := by
  rw [zLin_eq_basis, map_add, map_smul, map_smul, Basis.repr_self, Basis.repr_self]
  simp [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem zLin_repr0 (x y : ℤ) : BSD_intBasis.repr (zLin x y) 0 = x := by
  rw [zLin_repr]
  simp [Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]

theorem zLin_repr1 (x y : ℤ) : BSD_intBasis.repr (zLin x y) 1 = y := by
  rw [zLin_repr]
  simp [Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)]

theorem zLin_of_repr (r : 𝓞 K) :
    r = zLin (BSD_intBasis.repr r 0) (BSD_intBasis.repr r 1) := by
  apply RingOfIntegers.ext
  rw [intBasis_repr_K, zLin_coe]

theorem norm_zLin (x y : ℤ) :
    Algebra.norm ℤ (zLin x y) = x ^ 2 + x * y + 36 * y ^ 2 := by
  have hQ : (Algebra.norm ℤ (zLin x y) : ℚ) =
      (x : ℚ) ^ 2 + (x : ℚ) * (y : ℚ) + 36 * (y : ℚ) ^ 2 := by
    rw [Algebra.coe_norm_int, zLin_coe, norm_form_BSD_rat]
  exact_mod_cast hQ

theorem absNorm_span_zLin (x y : ℤ) :
    Ideal.absNorm (Ideal.span {zLin x y}) = (x ^ 2 + x * y + 36 * y ^ 2).natAbs := by
  rw [Ideal.absNorm_span_singleton, norm_zLin]

theorem zLin_mem_span_nat {n x y : ℤ} (h : zLin x y ∈ Ideal.span {(n : 𝓞 K)}) :
    n ∣ x ∧ n ∣ y := by
  rw [Ideal.mem_span_singleton'] at h
  obtain ⟨r, hr⟩ := h
  rw [zLin_of_repr r, mul_comm, zLin_mul_nat] at hr
  constructor
  · refine ⟨BSD_intBasis.repr r 0, ?_⟩
    have h0 := congrArg (fun z => BSD_intBasis.repr z 0) hr
    have hx : n * BSD_intBasis.repr r 0 = x := by simpa [zLin_repr0] using h0
    exact hx.symm
  · refine ⟨BSD_intBasis.repr r 1, ?_⟩
    have h1 := congrArg (fun z => BSD_intBasis.repr z 1) hr
    have hy : n * BSD_intBasis.repr r 1 = y := by simpa [zLin_repr1] using h1
    exact hy.symm

/-! ### Ideals with Hermite basis `(a, b + ω)` -/

noncomputable def pairSpan (a b : ℤ) : Ideal (𝓞 K) :=
  Ideal.span {((a : ℤ) : 𝓞 K), zLin b 1}

theorem pairSpan_p2 : pairSpan 2 0 = p2_OK := by
  simp [pairSpan, p2_OK, zLin_int, zLin_zero_one]

theorem zLin_mem_pairSpan {a b x y : ℤ} (h : a ∣ x - b * y) : zLin x y ∈ pairSpan a b := by
  obtain ⟨q, hq⟩ := h
  rw [pairSpan, Ideal.mem_span_pair]
  refine ⟨(q : 𝓞 K), (y : 𝓞 K), ?_⟩
  apply RingOfIntegers.ext
  simp only [map_add, map_mul, map_intCast, zLin_coe]
  have hx : (x : ℤ) = a * q + b * y := by linear_combination hq
  calc (q : K) * (a : K) + (y : K) * ((b : K) + (1 : K) * ω)
      = (q : K) * (a : K) + (y : K) * ((b : K) + ω) := by ring
    _ = (x : K) + (y : K) * ω := by rw [hx]; push_cast; ring

theorem combo4_mem (c0 c1 c2 c3 : ℤ) (g0 g1 g2 g3 : 𝓞 K) :
    c0 • g0 + c1 • g1 + c2 • g2 + c3 • g3 ∈
      Ideal.span ({g0, g1, g2, g3} : Set (𝓞 K)) := by
  have h0 : g0 ∈ Ideal.span ({g0, g1, g2, g3} : Set (𝓞 K)) :=
    Ideal.subset_span (Set.mem_insert _ _)
  have h1 : g1 ∈ Ideal.span ({g0, g1, g2, g3} : Set (𝓞 K)) :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have h2 : g2 ∈ Ideal.span ({g0, g1, g2, g3} : Set (𝓞 K)) :=
    Ideal.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have h3 : g3 ∈ Ideal.span ({g0, g1, g2, g3} : Set (𝓞 K)) :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_) ?_
  · rw [zsmul_eq_mul]; exact Ideal.mul_mem_left _ _ h0
  · rw [zsmul_eq_mul]; exact Ideal.mul_mem_left _ _ h1
  · rw [zsmul_eq_mul]; exact Ideal.mul_mem_left _ _ h2
  · rw [zsmul_eq_mul]; exact Ideal.mul_mem_left _ _ h3

theorem pair_prod_span (a b c d : ℤ) :
    pairSpan a b * pairSpan c d =
      Ideal.span
        {zLin (a * c) 0, zLin (a * d) a, zLin (b * c) c,
          zLin (b * d - 36) (b + d + 1)} := by
  rw [pairSpan, pairSpan, Ideal.span_pair_mul_span_pair]
  have e0 : (a : 𝓞 K) * (c : 𝓞 K) = zLin (a * c) 0 := by
    rw [← zLin_int, ← zLin_int, zLin_mul]
    simp
  have e1 : (a : 𝓞 K) * zLin d 1 = zLin (a * d) a := by
    rw [← zLin_int, zLin_mul]
    simp
  have e2 : zLin b 1 * (c : 𝓞 K) = zLin (b * c) c := by
    rw [mul_comm, ← zLin_int, zLin_mul]
    simp [mul_comm]
  have e3 : zLin b 1 * zLin d 1 = zLin (b * d - 36) (b + d + 1) := by
    rw [zLin_mul]
    simp
  rw [e0, e1, e2, e3]

theorem zLin_combo_mem_prod {a b c d x y u0 u1 u2 u3 : ℤ}
    (huX : u0 * (a * c) + u1 * (a * d) + u2 * (b * c) + u3 * (b * d - 36) = x)
    (huY : u0 * 0 + u1 * a + u2 * c + u3 * (b + d + 1) = y) :
    zLin x y ∈ pairSpan a b * pairSpan c d := by
  rw [pair_prod_span]
  have hcomb :
      zLin x y =
        u0 • zLin (a * c) 0 + u1 • zLin (a * d) a + u2 • zLin (b * c) c +
          u3 • zLin (b * d - 36) (b + d + 1) := by
    rw [zLin_combo4, huX, huY]
  rw [hcomb]
  exact combo4_mem _ _ _ _ _ _ _ _

theorem pairSpan_mul_eq (a b c d a' b' u0 u1 u2 u3 v0 v1 v2 v3 : ℤ)
    (h0 : a' ∣ a * c - b' * 0) (h1 : a' ∣ a * d - b' * a)
    (h2 : a' ∣ b * c - b' * c) (h3 : a' ∣ b * d - 36 - b' * (b + d + 1))
    (huX : u0 * (a * c) + u1 * (a * d) + u2 * (b * c) + u3 * (b * d - 36) = a')
    (huY : u0 * 0 + u1 * a + u2 * c + u3 * (b + d + 1) = 0)
    (hvX : v0 * (a * c) + v1 * (a * d) + v2 * (b * c) + v3 * (b * d - 36) = b')
    (hvY : v0 * 0 + v1 * a + v2 * c + v3 * (b + d + 1) = 1) :
    pairSpan a b * pairSpan c d = pairSpan a' b' := by
  apply le_antisymm
  · rw [pair_prod_span]
    refine Ideal.span_le.2 ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact zLin_mem_pairSpan h0
    · exact zLin_mem_pairSpan h1
    · exact zLin_mem_pairSpan h2
    · exact zLin_mem_pairSpan h3
  · rw [pairSpan]
    refine Ideal.span_le.2 ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [← zLin_int]
      exact zLin_combo_mem_prod huX huY
    · exact zLin_combo_mem_prod hvX hvY

theorem zLin_eq_nat_mul {n x y q r : ℤ} (hx : x = n * q) (hy : y = n * r) :
    zLin x y = zLin q r * (n : 𝓞 K) := by
  rw [mul_comm, zLin_mul_nat, hx, hy]

theorem pairSpan_mul_eq_span_nat (a b c d n u0 u1 u2 u3 : ℤ)
    (huX : u0 * (a * c) + u1 * (a * d) + u2 * (b * c) + u3 * (b * d - 36) = n)
    (huY : u0 * 0 + u1 * a + u2 * c + u3 * (b + d + 1) = 0)
    (d0x : n ∣ a * c) (d0y : n ∣ (0 : ℤ)) (d1x : n ∣ a * d) (d1y : n ∣ a)
    (d2x : n ∣ b * c) (d2y : n ∣ c) (d3x : n ∣ b * d - 36) (d3y : n ∣ b + d + 1) :
    pairSpan a b * pairSpan c d = Ideal.span {(n : 𝓞 K)} := by
  apply le_antisymm
  · rw [pair_prod_span]
    refine Ideal.span_le.2 ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have mem_of {x y : ℤ} (hx : n ∣ x) (hy : n ∣ y) (hzl : z = zLin x y) :
        z ∈ Ideal.span {(n : 𝓞 K)} := by
      obtain ⟨qx, hqx⟩ := hx
      obtain ⟨qy, hqy⟩ := hy
      rw [hzl, zLin_eq_nat_mul hqx hqy, Ideal.mem_span_singleton']
      exact ⟨zLin qx qy, rfl⟩
    rcases hz with rfl | rfl | rfl | rfl
    · exact mem_of d0x d0y rfl
    · exact mem_of d1x d1y rfl
    · exact mem_of d2x d2y rfl
    · exact mem_of d3x d3y rfl
  · rw [Ideal.span_le, Set.singleton_subset_iff, ← zLin_int]
    exact zLin_combo_mem_prod huX huY

theorem eq_span_of_mem {I : Ideal (𝓞 K)} {α : 𝓞 K} (hmem : α ∈ I)
    (hN : Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm I) (hI : Ideal.absNorm I ≠ 0) :
    I = Ideal.span {α} := by
  have hle : Ideal.span {α} ≤ I := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmem
  obtain ⟨Kideal, hK⟩ := Ideal.dvd_iff_le.mpr hle
  have hmul : Ideal.absNorm I * Ideal.absNorm Kideal = Ideal.absNorm I := by
    rw [← map_mul Ideal.absNorm, ← hK, hN]
  have hK1 : Ideal.absNorm Kideal = 1 := by
    have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero hI
    have : Ideal.absNorm I * Ideal.absNorm Kideal = Ideal.absNorm I * 1 := by
      rw [mul_one, hmul]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  rw [Ideal.absNorm_eq_one_iff.mp hK1, Ideal.mul_top] at hK
  exact hK.symm

theorem mul_eq_span_of_combo (a b c d x y u0 u1 u2 u3 : ℤ)
    (huX : u0 * (a * c) + u1 * (a * d) + u2 * (b * c) + u3 * (b * d - 36) = x)
    (huY : u0 * 0 + u1 * a + u2 * c + u3 * (b + d + 1) = y)
    (hN : Ideal.absNorm (pairSpan a b) * Ideal.absNorm (pairSpan c d) =
      (x ^ 2 + x * y + 36 * y ^ 2).natAbs)
    (hne : x ^ 2 + x * y + 36 * y ^ 2 ≠ 0) :
    pairSpan a b * pairSpan c d = Ideal.span {zLin x y} := by
  have hmem : zLin x y ∈ pairSpan a b * pairSpan c d := zLin_combo_mem_prod huX huY
  have hnorm : Ideal.absNorm (Ideal.span {zLin x y}) =
      Ideal.absNorm (pairSpan a b * pairSpan c d) := by
    rw [map_mul Ideal.absNorm, absNorm_span_zLin, hN]
  have hpos : Ideal.absNorm (pairSpan a b * pairSpan c d) ≠ 0 := by
    rw [← hnorm, absNorm_span_zLin, Int.natAbs_ne_zero]
    exact hne
  exact eq_span_of_mem hmem hnorm hpos

/-! ### Powers of `p2_OK` -/

theorem p2_pow_hnf_2 : p2_OK ^ 2 = pairSpan 4 0 := by
  have hmul : pairSpan 2 0 * pairSpan 2 0 = pairSpan 4 0 :=
    pairSpan_mul_eq 2 0 2 0 4 0 1 (-12) 12 0 (-9) (-11) 12 (-1)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [pow_two, pairSpan_p2] using hmul

theorem p2_pow_hnf_3 : p2_OK ^ 3 = pairSpan 8 4 := by
  have hmul : pairSpan 4 0 * pairSpan 2 0 = pairSpan 8 4 :=
    pairSpan_mul_eq 4 0 2 0 8 4 (-8) (-5) 11 (-2) (-4) (-5) 11 (-1)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [← p2_pow_hnf_2, pairSpan_p2, ← pow_succ] using hmul

theorem p2_pow_hnf_4 : p2_OK ^ 4 = pairSpan 16 12 := by
  have hmul : pairSpan 8 4 * pairSpan 2 0 = pairSpan 16 12 :=
    pairSpan_mul_eq 8 4 2 0 16 12 (-12) 4 (-1) (-6) (-12) (-1) 12 (-3)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [← p2_pow_hnf_3, pairSpan_p2, ← pow_succ] using hmul

theorem p2_pow_hnf_5 : p2_OK ^ 5 = pairSpan 32 12 := by
  have hmul : pairSpan 16 12 * pairSpan 2 0 = pairSpan 32 12 :=
    pairSpan_mul_eq 16 12 2 0 32 12 (-11) 2 10 (-4) (-12) 1 12 (-3)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [← p2_pow_hnf_4, pairSpan_p2, ← pow_succ] using hmul

theorem p2_pow_hnf_6 : p2_OK ^ 6 = pairSpan 64 12 := by
  have hmul : pairSpan 32 12 * pairSpan 2 0 = pairSpan 64 12 :=
    pairSpan_mul_eq 32 12 2 0 64 12 (-5) 1 10 (-4) (-9) 3 11 (-9)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [← p2_pow_hnf_5, pairSpan_p2, ← pow_succ] using hmul

theorem p2_pow_hnf_7 : p2_OK ^ 7 = pairSpan 128 76 := by
  have hmul : pairSpan 64 12 * pairSpan 2 0 = pairSpan 128 76 :=
    pairSpan_mul_eq 64 12 2 0 128 76 (-2) 1 7 (-6) (-4) 2 8 (-11)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [← p2_pow_hnf_6, pairSpan_p2, ← pow_succ] using hmul

theorem p2_pow_hnf_8 : p2_OK ^ 8 = pairSpan 256 76 := by
  have hmul : pairSpan 128 76 * pairSpan 2 0 = pairSpan 256 76 :=
    pairSpan_mul_eq 128 76 2 0 256 76 (-5) (-5) 12 8 (-1) 3 1 (-5)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [← p2_pow_hnf_7, pairSpan_p2, ← pow_succ] using hmul

theorem p2_pow_hnf_9 : p2_OK ^ 9 = pairSpan 512 332 := by
  have hmul : pairSpan 256 76 * pairSpan 2 0 = pairSpan 512 332 :=
    pairSpan_mul_eq 256 76 2 0 512 332 0 3 1 (-10) 4 1 (-12) (-3)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [← p2_pow_hnf_8, pairSpan_p2, ← pow_succ] using hmul

theorem p2_pow_hnf_10 : p2_OK ^ 10 = pairSpan 1024 332 := by
  have hmul : pairSpan 512 332 * pairSpan 2 0 = pairSpan 1024 332 :=
    pairSpan_mul_eq 512 332 2 0 1024 332 1 0 0 0 8 2 (-12) (-3)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [← p2_pow_hnf_9, pairSpan_p2, ← pow_succ] using hmul

theorem gen10_mem : zLin (-28) 3 ∈ p2_OK ^ 10 := by
  rw [p2_pow_hnf_10]
  exact zLin_mem_pairSpan (by decide : (1024 : ℤ) ∣ -28 - 332 * 3)

theorem p2_pow_ten_span : p2_OK ^ 10 = Ideal.span {zLin (-28) 3} := by
  have hmem := gen10_mem
  have hN : Ideal.absNorm (Ideal.span {zLin (-28) 3}) = Ideal.absNorm (p2_OK ^ 10) := by
    rw [absNorm_span_zLin, map_pow Ideal.absNorm, absNorm_p2_eq_2]
    decide
  have hpos : Ideal.absNorm (p2_OK ^ 10) ≠ 0 := by
    rw [map_pow Ideal.absNorm, absNorm_p2_eq_2]
    decide
  exact eq_span_of_mem hmem hN hpos

/-! ### The class of `p2_OK` has order 10 -/

noncomputable def nzIdeal (I : Ideal (𝓞 K)) (hI : I ≠ 0) : (Ideal (𝓞 K))⁰ :=
  ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩

noncomputable def p2_class : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 (nzIdeal p2_OK p2_ne_bot)

theorem p2_class_pow_ten : p2_class ^ 10 = 1 := by
  have hprin : (p2_OK ^ 10).IsPrincipal := by
    rw [Submodule.isPrincipal_iff]
    exact ⟨zLin (-28) 3, p2_pow_ten_span⟩
  have hsub : (nzIdeal p2_OK p2_ne_bot) ^ 10 =
      nzIdeal (p2_OK ^ 10) (pow_ne_zero 10 p2_ne_bot) := by
    apply Subtype.ext
    simp [nzIdeal, SubmonoidClass.coe_pow]
  rw [p2_class, ← map_pow, hsub, ClassGroup.mk0_eq_one_iff]
  simpa [nzIdeal] using hprin

theorem orderOf_p2_class : orderOf p2_class = 10 := by
  refine (orderOf_eq_iff (by decide : 0 < 10)).2 ⟨p2_class_pow_ten, ?_⟩
  intro m hm hmpos hg
  have hmap : p2_class ^ m = ClassGroup.mk0 ((nzIdeal p2_OK p2_ne_bot) ^ m) :=
    (map_pow (ClassGroup.mk0 (R := 𝓞 K)) _ m).symm
  have hcoe : (↑((nzIdeal p2_OK p2_ne_bot) ^ m) : Ideal (𝓞 K)) = p2_OK ^ m := by
    simp [nzIdeal, SubmonoidClass.coe_pow]
  have hprinc : (↑((nzIdeal p2_OK p2_ne_bot) ^ m) : Ideal (𝓞 K)).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff _).mp (hmap ▸ hg)
  exact master_not_principal_1_to_9 m (by omega) (by omega) (hcoe ▸ hprinc)

theorem p2_class_pow (n : ℕ) :
    ClassGroup.mk0 (nzIdeal (p2_OK ^ n) (pow_ne_zero n p2_ne_bot)) = p2_class ^ n := by
  have hsub : (nzIdeal p2_OK p2_ne_bot) ^ n =
      nzIdeal (p2_OK ^ n) (pow_ne_zero n p2_ne_bot) := by
    apply Subtype.ext
    simp [nzIdeal, SubmonoidClass.coe_pow]
  calc ClassGroup.mk0 (nzIdeal (p2_OK ^ n) (pow_ne_zero n p2_ne_bot))
      = ClassGroup.mk0 ((nzIdeal p2_OK p2_ne_bot) ^ n) := by
        apply congrArg ClassGroup.mk0
        exact hsub.symm
    _ = p2_class ^ n := by rw [map_pow]; rfl

theorem p2_class_pow_mod (n : ℕ) : p2_class ^ n = p2_class ^ (n % 10) := by
  conv_lhs => rw [← Nat.div_add_mod n 10]
  rw [pow_add, pow_mul, p2_class_pow_ten, one_pow, one_mul]

theorem mk_mul {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0) :
    ClassGroup.mk0 (nzIdeal I hI) * ClassGroup.mk0 (nzIdeal J hJ) =
      ClassGroup.mk0 (nzIdeal (I * J) (mul_ne_zero hI hJ)) := by
  have hsub : nzIdeal I hI * nzIdeal J hJ = nzIdeal (I * J) (mul_ne_zero hI hJ) := by
    apply Subtype.ext
    simp [nzIdeal, Submonoid.coe_mul]
  rw [← map_mul (ClassGroup.mk0 (R := 𝓞 K)), hsub]

/-! ### The split primes above 2, 3 and 7 -/

noncomputable def p2b_OK : Ideal (𝓞 K) := pairSpan 2 1
noncomputable def p3_OK : Ideal (𝓞 K) := pairSpan 3 0
noncomputable def p3b_OK : Ideal (𝓞 K) := pairSpan 3 2
noncomputable def p7_OK : Ideal (𝓞 K) := pairSpan 7 2
noncomputable def p7b_OK : Ideal (𝓞 K) := pairSpan 7 4

theorem two_split : p2_OK * p2b_OK = Ideal.span {(2 : 𝓞 K)} := by
  have hmul :=
    pairSpan_mul_eq_span_nat 2 0 2 1 2 (-15) (-5) 7 (-2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [pairSpan_p2, p2b_OK] using hmul

theorem three_split : p3_OK * p3b_OK = Ideal.span {(3 : 𝓞 K)} := by
  exact pairSpan_mul_eq_span_nat 3 0 3 2 3 (-15) (-7) 12 (-5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem seven_split : p7_OK * p7b_OK = Ideal.span {(7 : 𝓞 K)} := by
  exact pairSpan_mul_eq_span_nat 7 2 7 4 7 (-15) 8 7 (-15)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem p2b_ne_top : p2b_OK ≠ ⊤ := by
  intro h
  have hsplit := two_split
  rw [h, Ideal.mul_top] at hsplit
  have hω : zLin 0 1 ∈ Ideal.span {(2 : 𝓞 K)} := by
    rw [← hsplit, zLin_zero_one]
    exact nω_mem_p2_OK
  have hd := (zLin_mem_span_nat hω).2
  norm_num at hd

theorem p3_ne_top : p3_OK ≠ ⊤ := by
  intro h
  have hsplit := three_split
  rw [h, Ideal.top_mul] at hsplit
  have hgen : zLin 2 1 ∈ Ideal.span {(3 : 𝓞 K)} := by
    rw [← hsplit]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hd := (zLin_mem_span_nat hgen).2
  norm_num at hd

theorem p3b_ne_top : p3b_OK ≠ ⊤ := by
  intro h
  have hsplit := three_split
  rw [h, Ideal.mul_top] at hsplit
  have hgen : zLin 0 1 ∈ Ideal.span {(3 : 𝓞 K)} := by
    rw [← hsplit]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hd := (zLin_mem_span_nat hgen).2
  norm_num at hd

theorem p7_ne_top : p7_OK ≠ ⊤ := by
  intro h
  have hsplit := seven_split
  rw [h, Ideal.top_mul] at hsplit
  have hgen : zLin 4 1 ∈ Ideal.span {(7 : 𝓞 K)} := by
    rw [← hsplit]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hd := (zLin_mem_span_nat hgen).2
  norm_num at hd

theorem p7b_ne_top : p7b_OK ≠ ⊤ := by
  intro h
  have hsplit := seven_split
  rw [h, Ideal.mul_top] at hsplit
  have hgen : zLin 2 1 ∈ Ideal.span {(7 : 𝓞 K)} := by
    rw [← hsplit]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hd := (zLin_mem_span_nat hgen).2
  norm_num at hd

private lemma mul_eq_nine {x y : ℕ} (h : x * y = 9) (hx : x ≠ 1) (hy : y ≠ 1) :
    x = 3 ∧ y = 3 := by
  have hxle : x ≤ 9 := Nat.le_of_dvd (by decide) ⟨y, h.symm⟩
  interval_cases x <;> omega

private lemma mul_eq_fortynine {x y : ℕ} (h : x * y = 49) (hx : x ≠ 1) (hy : y ≠ 1) :
    x = 7 ∧ y = 7 := by
  have hxle : x ≤ 49 := Nat.le_of_dvd (by decide) ⟨y, h.symm⟩
  interval_cases x <;> omega

private theorem absNorm_span_int (n : ℤ) :
    Ideal.absNorm (Ideal.span {((n : ℤ) : 𝓞 K)}) = (n ^ 2).natAbs := by
  rw [← zLin_int, absNorm_span_zLin]
  simp

theorem absNorm_p2b : Ideal.absNorm p2b_OK = 2 := by
  have hmul : Ideal.absNorm p2_OK * Ideal.absNorm p2b_OK = 4 := by
    rw [← map_mul Ideal.absNorm, two_split,
      show (2 : 𝓞 K) = ((2 : ℤ) : 𝓞 K) by norm_cast, absNorm_span_int 2]
    decide
  rw [absNorm_p2_eq_2] at hmul
  omega

theorem absNorm_p3 : Ideal.absNorm p3_OK = 3 := by
  have hmul : Ideal.absNorm p3_OK * Ideal.absNorm p3b_OK = 9 := by
    rw [← map_mul Ideal.absNorm, three_split,
      show (3 : 𝓞 K) = ((3 : ℤ) : 𝓞 K) by norm_cast, absNorm_span_int 3]
    decide
  have hx : Ideal.absNorm p3_OK ≠ 1 := by
    intro h; exact p3_ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hy : Ideal.absNorm p3b_OK ≠ 1 := by
    intro h; exact p3b_ne_top (Ideal.absNorm_eq_one_iff.mp h)
  exact (mul_eq_nine hmul hx hy).1

theorem absNorm_p3b : Ideal.absNorm p3b_OK = 3 := by
  have hmul : Ideal.absNorm p3_OK * Ideal.absNorm p3b_OK = 9 := by
    rw [← map_mul Ideal.absNorm, three_split,
      show (3 : 𝓞 K) = ((3 : ℤ) : 𝓞 K) by norm_cast, absNorm_span_int 3]
    decide
  have hx : Ideal.absNorm p3_OK ≠ 1 := by
    intro h; exact p3_ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hy : Ideal.absNorm p3b_OK ≠ 1 := by
    intro h; exact p3b_ne_top (Ideal.absNorm_eq_one_iff.mp h)
  exact (mul_eq_nine hmul hx hy).2

theorem absNorm_p7 : Ideal.absNorm p7_OK = 7 := by
  have hmul : Ideal.absNorm p7_OK * Ideal.absNorm p7b_OK = 49 := by
    rw [← map_mul Ideal.absNorm, seven_split,
      show (7 : 𝓞 K) = ((7 : ℤ) : 𝓞 K) by norm_cast, absNorm_span_int 7]
    decide
  have hx : Ideal.absNorm p7_OK ≠ 1 := by
    intro h; exact p7_ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hy : Ideal.absNorm p7b_OK ≠ 1 := by
    intro h; exact p7b_ne_top (Ideal.absNorm_eq_one_iff.mp h)
  exact (mul_eq_fortynine hmul hx hy).1

theorem absNorm_p7b : Ideal.absNorm p7b_OK = 7 := by
  have hmul : Ideal.absNorm p7_OK * Ideal.absNorm p7b_OK = 49 := by
    rw [← map_mul Ideal.absNorm, seven_split,
      show (7 : 𝓞 K) = ((7 : ℤ) : 𝓞 K) by norm_cast, absNorm_span_int 7]
    decide
  have hx : Ideal.absNorm p7_OK ≠ 1 := by
    intro h; exact p7_ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hy : Ideal.absNorm p7b_OK ≠ 1 := by
    intro h; exact p7b_ne_top (Ideal.absNorm_eq_one_iff.mp h)
  exact (mul_eq_fortynine hmul hx hy).2

theorem p2_isPrime : p2_OK.IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm (by rw [absNorm_p2_eq_2]; exact Nat.prime_two)

theorem p2b_isPrime : p2b_OK.IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm (by rw [absNorm_p2b]; exact Nat.prime_two)

theorem p3_isPrime : p3_OK.IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm (by rw [absNorm_p3]; exact (by decide : Nat.Prime 3))

theorem p3b_isPrime : p3b_OK.IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm (by rw [absNorm_p3b]; exact (by decide : Nat.Prime 3))

theorem p7_isPrime : p7_OK.IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm (by rw [absNorm_p7]; exact (by decide : Nat.Prime 7))

theorem p7b_isPrime : p7b_OK.IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm (by rw [absNorm_p7b]; exact (by decide : Nat.Prime 7))

theorem p2_prime : Prime (p2_OK : Ideal (𝓞 K)) := Ideal.prime_of_isPrime p2_ne_bot p2_isPrime

theorem p2b_ne_zero : p2b_OK ≠ 0 := by
  intro h
  have := absNorm_p2b
  rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this
  norm_num at this

theorem p3_ne_zero : p3_OK ≠ 0 := by
  intro h
  have := absNorm_p3
  rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this
  norm_num at this

theorem p3b_ne_zero : p3b_OK ≠ 0 := by
  intro h
  have := absNorm_p3b
  rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this
  norm_num at this

theorem p7_ne_zero : p7_OK ≠ 0 := by
  intro h
  have := absNorm_p7
  rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this
  norm_num at this

theorem p7b_ne_zero : p7b_OK ≠ 0 := by
  intro h
  have := absNorm_p7b
  rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at this
  norm_num at this

theorem p2b_prime : Prime (p2b_OK : Ideal (𝓞 K)) := Ideal.prime_of_isPrime p2b_ne_zero p2b_isPrime
theorem p3_prime : Prime (p3_OK : Ideal (𝓞 K)) := Ideal.prime_of_isPrime p3_ne_zero p3_isPrime
theorem p3b_prime : Prime (p3b_OK : Ideal (𝓞 K)) := Ideal.prime_of_isPrime p3b_ne_zero p3b_isPrime
theorem p7_prime : Prime (p7_OK : Ideal (𝓞 K)) := Ideal.prime_of_isPrime p7_ne_zero p7_isPrime
theorem p7b_prime : Prime (p7b_OK : Ideal (𝓞 K)) := Ideal.prime_of_isPrime p7b_ne_zero p7b_isPrime

theorem eq_of_prime_dvd {P Q : Ideal (𝓞 K)} (hP : Prime P) (hQ : Prime Q) (h : P ∣ Q) : P = Q :=
  associated_iff_eq.mp (hP.irreducible.associated_of_dvd hQ.irreducible h)

/-! ### Principality relations that place the split primes in `⟨[p2]⟩` -/

theorem p3_mul_p2_pow_six : p3_OK * p2_OK ^ 6 = Ideal.span {zLin (-12) (-1)} := by
  rw [show p3_OK = pairSpan 3 0 from rfl, p2_pow_hnf_6]
  exact mul_eq_span_of_combo 3 0 64 12 (-12) (-1) (-10) 23 5 (-30)
    (by decide) (by decide)
    (by rw [show pairSpan 3 0 = p3_OK from rfl, p2_pow_hnf_6.symm, absNorm_p3,
        map_pow Ideal.absNorm, absNorm_p2_eq_2]; decide)
    (by decide)

theorem p3b_mul_p2_pow_four : p3b_OK * p2_OK ^ 4 = Ideal.span {zLin 4 (-1)} := by
  rw [show p3b_OK = pairSpan 3 2 from rfl, p2_pow_hnf_4]
  exact mul_eq_span_of_combo 3 2 16 12 4 (-1) (-29) 6 26 (-29)
    (by decide) (by decide)
    (by rw [show pairSpan 3 2 = p3b_OK from rfl, p2_pow_hnf_4.symm, absNorm_p3b,
        map_pow Ideal.absNorm, absNorm_p2_eq_2]; decide)
    (by decide)

theorem p7_mul_p2_pow_seven : p7_OK * p2_OK ^ 7 = Ideal.span {zLin 4 (-5)} := by
  rw [show p7_OK = pairSpan 7 2 from rfl, p2_pow_hnf_7]
  exact mul_eq_span_of_combo 7 2 128 76 4 (-5) (-17) 27 17 (-30)
    (by decide) (by decide)
    (by rw [show pairSpan 7 2 = p7_OK from rfl, p2_pow_hnf_7.symm, absNorm_p7,
        map_pow Ideal.absNorm, absNorm_p2_eq_2]; decide)
    (by decide)

theorem p7b_mul_p2_pow_three : p7b_OK * p2_OK ^ 3 = Ideal.span {zLin (-4) (-1)} := by
  rw [show p7b_OK = pairSpan 7 4 from rfl, p2_pow_hnf_3]
  exact mul_eq_span_of_combo 7 4 8 4 (-4) (-1) (-30) 11 24 (-30)
    (by decide) (by decide)
    (by rw [show pairSpan 7 4 = p7b_OK from rfl, p2_pow_hnf_3.symm, absNorm_p7b,
        map_pow Ideal.absNorm, absNorm_p2_eq_2]; decide)
    (by decide)

theorem zLin_ne_zero_of_norm {x y : ℤ} (h : x ^ 2 + x * y + 36 * y ^ 2 ≠ 0) : zLin x y ≠ 0 := by
  intro hz
  have hn := norm_zLin x y
  rw [hz, Algebra.norm_zero] at hn
  exact h hn.symm

private theorem inv_pow_p2 (k m : ℕ) (h : k + m = 10) : (p2_class ^ k)⁻¹ = p2_class ^ m := by
  have hmul : p2_class ^ m * p2_class ^ k = 1 := by
    rw [mul_comm, ← pow_add, h, p2_class_pow_ten]
  exact inv_eq_of_mul_eq_one_left hmul

theorem class_p2b (h : p2b_OK ≠ 0) : ClassGroup.mk0 (nzIdeal p2b_OK h) = p2_class ^ 9 := by
  have htwo : (2 : 𝓞 K) ≠ 0 := by exact_mod_cast (by decide : (2 : ℤ) ≠ 0)
  have hinv : ClassGroup.mk0 (nzIdeal p2b_OK h) =
      (ClassGroup.mk0 (nzIdeal p2_OK p2_ne_bot))⁻¹ := by
    rw [ClassGroup.mk0_eq_mk0_inv_iff]
    refine ⟨(2 : 𝓞 K), htwo, ?_⟩
    simpa [nzIdeal, Submonoid.coe_mul, mul_comm] using two_split
  rw [hinv]
  change (p2_class)⁻¹ = p2_class ^ 9
  have hpow : (p2_class ^ 1)⁻¹ = p2_class ^ 9 := inv_pow_p2 1 9 (by decide)
  rw [pow_one] at hpow
  exact hpow

theorem class_p3 (h : p3_OK ≠ 0) : ClassGroup.mk0 (nzIdeal p3_OK h) = p2_class ^ 4 := by
  have hα : zLin (-12) (-1) ≠ 0 := zLin_ne_zero_of_norm (by decide)
  have hinv : ClassGroup.mk0 (nzIdeal p3_OK h) =
      (ClassGroup.mk0 (nzIdeal (p2_OK ^ 6) (pow_ne_zero 6 p2_ne_bot)))⁻¹ := by
    rw [ClassGroup.mk0_eq_mk0_inv_iff]
    refine ⟨zLin (-12) (-1), hα, ?_⟩
    simpa [nzIdeal, Submonoid.coe_mul] using p3_mul_p2_pow_six
  rw [hinv, p2_class_pow, inv_pow_p2 6 4 (by decide)]

theorem class_p3b (h : p3b_OK ≠ 0) : ClassGroup.mk0 (nzIdeal p3b_OK h) = p2_class ^ 6 := by
  have hthree : (3 : 𝓞 K) ≠ 0 := by exact_mod_cast (by decide : (3 : ℤ) ≠ 0)
  have hinv : ClassGroup.mk0 (nzIdeal p3b_OK h) =
      (ClassGroup.mk0 (nzIdeal p3_OK p3_ne_zero))⁻¹ := by
    rw [ClassGroup.mk0_eq_mk0_inv_iff]
    refine ⟨(3 : 𝓞 K), hthree, ?_⟩
    simpa [nzIdeal, Submonoid.coe_mul, mul_comm] using three_split
  rw [hinv, class_p3, inv_pow_p2 4 6 (by decide)]

theorem class_p7 (h : p7_OK ≠ 0) : ClassGroup.mk0 (nzIdeal p7_OK h) = p2_class ^ 3 := by
  have hα : zLin 4 (-5) ≠ 0 := zLin_ne_zero_of_norm (by decide)
  have hinv : ClassGroup.mk0 (nzIdeal p7_OK h) =
      (ClassGroup.mk0 (nzIdeal (p2_OK ^ 7) (pow_ne_zero 7 p2_ne_bot)))⁻¹ := by
    rw [ClassGroup.mk0_eq_mk0_inv_iff]
    refine ⟨zLin 4 (-5), hα, ?_⟩
    simpa [nzIdeal, Submonoid.coe_mul] using p7_mul_p2_pow_seven
  rw [hinv, p2_class_pow, inv_pow_p2 7 3 (by decide)]

theorem class_p7b (h : p7b_OK ≠ 0) : ClassGroup.mk0 (nzIdeal p7b_OK h) = p2_class ^ 7 := by
  have hseven : (7 : 𝓞 K) ≠ 0 := by exact_mod_cast (by decide : (7 : ℤ) ≠ 0)
  have hinv : ClassGroup.mk0 (nzIdeal p7b_OK h) =
      (ClassGroup.mk0 (nzIdeal p7_OK p7_ne_zero))⁻¹ := by
    rw [ClassGroup.mk0_eq_mk0_inv_iff]
    refine ⟨(7 : 𝓞 K), hseven, ?_⟩
    simpa [nzIdeal, Submonoid.coe_mul, mul_comm] using seven_split
  rw [hinv, class_p7, inv_pow_p2 3 7 (by decide)]

/-! ### No ideal of norm 5, and the prime factors of a small ideal -/

theorem absNorm_ne_zero_of_ne_zero (I : Ideal (𝓞 K)) (hI : I ≠ 0) : Ideal.absNorm I ≠ 0 := by
  rw [Ideal.zero_eq_bot] at hI
  haveI := Ideal.fintypeQuotientOfFreeOfNeBot I hI
  exact (Ideal.absNorm_ne_zero_iff I).2 (Finite.of_fintype _)

set_option synthInstance.maxHeartbeats 400000 in
theorem no_absNorm_five (I : Ideal (𝓞 K)) : Ideal.absNorm I ≠ 5 := by
  intro h
  have hcardNat : Nat.card (𝓞 K ⧸ I) = 5 := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, h]
  have hpos : 0 < Nat.card (𝓞 K ⧸ I) := by rw [hcardNat]; decide
  obtain ⟨_, _⟩ := Nat.card_pos_iff.mp hpos
  let _ft : Fintype (𝓞 K ⧸ I) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ I) = 5 := by rw [Fintype.card_eq_nat_card, hcardNat]
  let e : (𝓞 K ⧸ I) ≃+* ZMod 5 := (ZMod.ringEquivOfPrime _ (by decide) hcard).symm
  have hz : nω_OK ^ 2 - nω_OK + 36 = 0 := by rw [nω_sq]; ring
  set q : 𝓞 K ⧸ I := Ideal.Quotient.mk I nω_OK
  have hq : q ^ 2 - q + 36 = 0 := by
    change Ideal.Quotient.mk I nω_OK ^ 2 - Ideal.Quotient.mk I nω_OK + 36 = 0
    rw [← map_ofNat (Ideal.Quotient.mk I) 36]
    rw [← map_pow, ← map_sub, ← map_add, hz, map_zero]
  have hq' : (e q) ^ 2 - e q + 36 = 0 := by
    have hmap := congrArg (RingEquiv.toRingHom e) hq
    simp only [map_add, map_sub, map_pow, map_ofNat, map_zero] at hmap
    exact hmap
  have hno : ∀ a : ZMod 5, a ^ 2 - a + 36 ≠ 0 := by decide
  exact hno (e q) hq'

theorem span_four : Ideal.span {(4 : 𝓞 K)} = p2_OK ^ 2 * p2b_OK ^ 2 := by
  rw [show (4 : 𝓞 K) = ((2 : ℤ) : 𝓞 K) * ((2 : ℤ) : 𝓞 K) by norm_num,
    ← Ideal.span_singleton_mul_span_singleton,
    show ((2 : ℤ) : 𝓞 K) = (2 : 𝓞 K) by norm_cast, two_split.symm, ← pow_two, mul_pow]

theorem span_six : Ideal.span {(6 : 𝓞 K)} = p2_OK * p2b_OK * p3_OK * p3b_OK := by
  rw [show (6 : 𝓞 K) = ((2 : ℤ) : 𝓞 K) * ((3 : ℤ) : 𝓞 K) by norm_num,
    ← Ideal.span_singleton_mul_span_singleton,
    show ((2 : ℤ) : 𝓞 K) = (2 : 𝓞 K) by norm_cast,
    show ((3 : ℤ) : 𝓞 K) = (3 : 𝓞 K) by norm_cast,
    two_split.symm, three_split.symm]
  ac_rfl

theorem span_seven : Ideal.span {(7 : 𝓞 K)} = p7_OK * p7b_OK := seven_split.symm

theorem factor_is_split (I : Ideal (𝓞 K)) (hI : I ≠ 0) (hN : Ideal.absNorm I ≤ 7)
    {P : Ideal (𝓞 K)} (hP : P ∈ normalizedFactors I) :
    P = p2_OK ∨ P = p2b_OK ∨ P = p3_OK ∨ P = p3b_OK ∨ P = p7_OK ∨ P = p7b_OK := by
  have hPrime : Prime P := prime_of_normalized_factor P hP
  have hdivI : P ∣ I := dvd_of_mem_normalizedFactors hP
  have hNdvd : Ideal.absNorm P ∣ Ideal.absNorm I := map_dvd Ideal.absNorm hdivI
  have hIpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (absNorm_ne_zero_of_ne_zero I hI)
  have hle : Ideal.absNorm P ≤ 7 := Nat.le_trans (Nat.le_of_dvd hIpos hNdvd) hN
  have hP0 : P ≠ 0 := hPrime.ne_zero
  have hne1 : Ideal.absNorm P ≠ 1 := by
    intro h1
    exact hPrime.not_unit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h1))
  have hne0 : Ideal.absNorm P ≠ 0 := absNorm_ne_zero_of_ne_zero P hP0
  have hge : 2 ≤ Ideal.absNorm P := by omega
  set n := Ideal.absNorm P with hn
  interval_cases n
  · -- norm 2
    have hdiv : P ∣ Ideal.span {(2 : 𝓞 K)} := by
      apply Ideal.dvd_span_singleton.mpr
      have hmem := Ideal.absNorm_mem P
      rw [← hn] at hmem
      exact hmem
    rw [two_split.symm] at hdiv
    rcases hPrime.dvd_or_dvd hdiv with h | h
    · exact Or.inl (eq_of_prime_dvd hPrime p2_prime h)
    · exact Or.inr (Or.inl (eq_of_prime_dvd hPrime p2b_prime h))
  · -- norm 3
    have hdiv : P ∣ Ideal.span {(3 : 𝓞 K)} := by
      apply Ideal.dvd_span_singleton.mpr
      have hmem := Ideal.absNorm_mem P
      rw [← hn] at hmem
      exact hmem
    rw [three_split.symm] at hdiv
    rcases hPrime.dvd_or_dvd hdiv with h | h
    · exact Or.inr (Or.inr (Or.inl (eq_of_prime_dvd hPrime p3_prime h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_of_prime_dvd hPrime p3b_prime h))))
  · -- norm 4 cannot occur
    have hdiv : P ∣ Ideal.span {(4 : 𝓞 K)} := by
      apply Ideal.dvd_span_singleton.mpr
      have hmem := Ideal.absNorm_mem P
      rw [← hn] at hmem
      exact hmem
    rw [span_four] at hdiv
    have hPQ : P ∣ p2_OK ∨ P ∣ p2b_OK := by
      have hsq : p2_OK ^ 2 * p2b_OK ^ 2 = (p2_OK * p2_OK) * (p2b_OK * p2b_OK) := by
        rw [pow_two, pow_two]
      rcases hdiv with ⟨C, hC⟩
      have hdiv' : P ∣ (p2_OK * p2_OK) * (p2b_OK * p2b_OK) := ⟨C, by rw [← hsq]; exact hC⟩
      rcases hPrime.dvd_or_dvd hdiv' with h | h
      · rcases hPrime.dvd_or_dvd h with h | h <;> exact Or.inl h
      · rcases hPrime.dvd_or_dvd h with h | h <;> exact Or.inr h
    rcases hPQ with h | h
    · have heq := eq_of_prime_dvd hPrime p2_prime h
      rw [heq, absNorm_p2_eq_2] at hn
      norm_num at hn
    · have heq := eq_of_prime_dvd hPrime p2b_prime h
      rw [heq, absNorm_p2b] at hn
      norm_num at hn
  · exact absurd hn.symm (no_absNorm_five P)
  · -- norm 6 cannot occur
    have hdiv : P ∣ Ideal.span {(6 : 𝓞 K)} := by
      apply Ideal.dvd_span_singleton.mpr
      have hmem := Ideal.absNorm_mem P
      rw [← hn] at hmem
      exact hmem
    rw [span_six] at hdiv
    have hPQ : P = p2_OK ∨ P = p2b_OK ∨ P = p3_OK ∨ P = p3b_OK := by
      rcases hPrime.dvd_or_dvd hdiv with h | h
      · rcases hPrime.dvd_or_dvd h with h | h
        · rcases hPrime.dvd_or_dvd h with h | h
          · exact Or.inl (eq_of_prime_dvd hPrime p2_prime h)
          · exact Or.inr (Or.inl (eq_of_prime_dvd hPrime p2b_prime h))
        · exact Or.inr (Or.inr (Or.inl (eq_of_prime_dvd hPrime p3_prime h)))
      · exact Or.inr (Or.inr (Or.inr (eq_of_prime_dvd hPrime p3b_prime h)))
    rcases hPQ with h | h | h | h
    · rw [h, absNorm_p2_eq_2] at hn; norm_num at hn
    · rw [h, absNorm_p2b] at hn; norm_num at hn
    · rw [h, absNorm_p3] at hn; norm_num at hn
    · rw [h, absNorm_p3b] at hn; norm_num at hn
  · -- norm 7
    have hdiv : P ∣ Ideal.span {(7 : 𝓞 K)} := by
      apply Ideal.dvd_span_singleton.mpr
      have hmem := Ideal.absNorm_mem P
      rw [← hn] at hmem
      exact hmem
    rw [span_seven] at hdiv
    rcases hPrime.dvd_or_dvd hdiv with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_of_prime_dvd hPrime p7_prime h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_of_prime_dvd hPrime p7b_prime h)))))

theorem prime_class_pow (P : Ideal (𝓞 K))
    (h : P = p2_OK ∨ P = p2b_OK ∨ P = p3_OK ∨ P = p3b_OK ∨ P = p7_OK ∨ P = p7b_OK) :
    ∃ e : ℕ, ∀ hP : P ≠ 0, ClassGroup.mk0 (nzIdeal P hP) = p2_class ^ e := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, fun hP => by
      have : nzIdeal p2_OK hP = nzIdeal p2_OK p2_ne_bot := Subtype.ext rfl
      simp [this, p2_class, pow_one]⟩
  · exact ⟨9, fun hP => class_p2b hP⟩
  · exact ⟨4, fun hP => class_p3 hP⟩
  · exact ⟨6, fun hP => class_p3b hP⟩
  · exact ⟨3, fun hP => class_p7 hP⟩
  · exact ⟨7, fun hP => class_p7b hP⟩

theorem class_of_factor_multiset (s : Multiset (Ideal (𝓞 K)))
    (hp : ∀ P ∈ s, P = p2_OK ∨ P = p2b_OK ∨ P = p3_OK ∨ P = p3b_OK ∨ P = p7_OK ∨ P = p7b_OK) :
    ∃ k : ℕ, ∀ hs : s.prod ≠ 0,
      ClassGroup.mk0 (nzIdeal s.prod hs) = p2_class ^ k := by
  induction s using Multiset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    intro hs
    rw [pow_zero, ClassGroup.mk0_eq_one_iff, Submodule.isPrincipal_iff]
    refine ⟨(1 : 𝓞 K), ?_⟩
    simp [nzIdeal, Ideal.one_eq_top, Ideal.span_singleton_one]
  | cons P s ih =>
    have hpP := hp P (Multiset.mem_cons_self _ _)
    have hps : ∀ Q ∈ s,
        Q = p2_OK ∨ Q = p2b_OK ∨ Q = p3_OK ∨ Q = p3b_OK ∨ Q = p7_OK ∨ Q = p7b_OK :=
      fun Q hQ => hp Q (Multiset.mem_cons_of_mem hQ)
    obtain ⟨k, hk⟩ := ih hps
    obtain ⟨e, he⟩ := prime_class_pow P hpP
    refine ⟨e + k, ?_⟩
    intro hs
    have hP0 : P ≠ 0 := by
      intro h0
      rcases hpP with rfl | rfl | rfl | rfl | rfl | rfl
      · exact p2_ne_bot h0
      · exact p2b_ne_zero h0
      · exact p3_ne_zero h0
      · exact p3b_ne_zero h0
      · exact p7_ne_zero h0
      · exact p7b_ne_zero h0
    have hs0 : s.prod ≠ 0 := by
      intro h0
      have : (P ::ₘ s).prod = 0 := by rw [Multiset.prod_cons, h0, mul_zero]
      exact hs this
    have hprod : (P ::ₘ s).prod = P * s.prod := Multiset.prod_cons _ _
    calc ClassGroup.mk0 (nzIdeal (P ::ₘ s).prod hs)
        = ClassGroup.mk0 (nzIdeal (P * s.prod) (mul_ne_zero hP0 hs0)) := by
            apply congrArg ClassGroup.mk0
            exact Subtype.ext hprod
      _ = ClassGroup.mk0 (nzIdeal P hP0) * ClassGroup.mk0 (nzIdeal s.prod hs0) := by
            rw [mk_mul]
      _ = p2_class ^ e * p2_class ^ k := by rw [he hP0, hk hs0]
      _ = p2_class ^ (e + k) := by rw [pow_add]

theorem BSD_small_norm_class_is_p2_power (I : (Ideal (𝓞 K))⁰)
    (hN : Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 7) :
    ∃ k : ℕ, k < 10 ∧ ClassGroup.mk0 I = p2_class ^ k := by
  have hI0 : (I : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  let s := normalizedFactors (I : Ideal (𝓞 K))
  have hprod : s.prod = (I : Ideal (𝓞 K)) :=
    prod_normalizedFactors_eq_self (by simpa [Ideal.zero_eq_bot] using hI0)
  have hp : ∀ P ∈ s, P = p2_OK ∨ P = p2b_OK ∨ P = p3_OK ∨ P = p3b_OK ∨ P = p7_OK ∨ P = p7b_OK :=
    fun P hP => factor_is_split (I : Ideal (𝓞 K)) hI0 hN hP
  obtain ⟨k, hk⟩ := class_of_factor_multiset s hp
  have hs0 : s.prod ≠ 0 := by simpa [hprod] using hI0
  have hclass : ClassGroup.mk0 I = p2_class ^ k := by
    have hsub : (I : (Ideal (𝓞 K))⁰) = nzIdeal s.prod hs0 := Subtype.ext hprod.symm
    rw [hsub]
    exact hk hs0
  refine ⟨k % 10, Nat.mod_lt _ (by decide), ?_⟩
  rw [hclass, p2_class_pow_mod]

/-- Every ideal class is a power of `[p2_OK]`, and that element has order 10. -/
theorem BSD_class_pow_surjective :
    Function.Surjective (fun k : Fin 10 => p2_class ^ (k : ℕ)) := by
  intro C
  obtain ⟨I, hI, hN⟩ := BSD_every_class_has_norm_le_seven C
  obtain ⟨k, hk, hkC⟩ := BSD_small_norm_class_is_p2_power I hN
  exact ⟨⟨k, hk⟩, by simpa [hI] using hkC.symm⟩

/-- `classNumber K = 10`. The lower bound supplies `10 ≤ classNumber K`, and
    the powers of `[p2_OK]` hit every class. -/
theorem BSD_classNumber_eq_ten_collapse : NumberField.classNumber K = 10 :=
  BSD_classNumber_eq_ten (fun k : Fin 10 => p2_class ^ (k : ℕ)) BSD_class_pow_surjective
    (by simp [Fintype.card_fin])

/-! ### The fourteen Hermite lattices -/

theorem lattice_p2b_sq : p2b_OK ^ 2 = pairSpan 4 3 := by
  have hmul : pairSpan 2 1 * pairSpan 2 1 = pairSpan 4 3 :=
    pairSpan_mul_eq 2 1 2 1 4 3 1 (-12) 12 0 (-9) (-10) 12 (-1)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [pow_two, p2b_OK] using hmul

theorem lattice_p2_p3 : p2_OK * p3_OK = pairSpan 6 0 := by
  have hmul :=
    pairSpan_mul_eq 2 0 3 0 6 0 (-11) (-11) 8 (-2) (-12) (-12) 9 (-2)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [pairSpan_p2, p3_OK] using hmul

theorem lattice_p2_p3b : p2_OK * p3b_OK = pairSpan 6 2 := by
  have hmul :=
    pairSpan_mul_eq 2 0 3 2 6 2 (-11) (-9) 9 (-3) (-11) (-10) 10 (-3)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  simpa [pairSpan_p2, p3b_OK] using hmul

theorem lattice_p2b_p3 : p2b_OK * p3_OK = pairSpan 6 3 := by
  exact pairSpan_mul_eq 2 1 3 0 6 3 (-12) (-1) 2 (-2) (-12) 1 1 (-2)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem lattice_p2b_p3b : p2b_OK * p3b_OK = pairSpan 6 5 := by
  exact pairSpan_mul_eq 2 1 3 2 6 5 (-12) 1 2 (-2) (-12) 0 3 (-2)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem class_mul_pow {I J : Ideal (𝓞 K)} {k m : ℕ} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hk : ClassGroup.mk0 (nzIdeal I hI) = p2_class ^ k)
    (hm : ClassGroup.mk0 (nzIdeal J hJ) = p2_class ^ m) :
    ClassGroup.mk0 (nzIdeal (I * J) (mul_ne_zero hI hJ)) = p2_class ^ ((k + m) % 10) := by
  rw [← mk_mul, hk, hm, ← pow_add, p2_class_pow_mod]

theorem top_ideal_ne_zero : (⊤ : Ideal (𝓞 K)) ≠ 0 := by
  intro h
  rw [Ideal.zero_eq_bot] at h
  exact bot_ne_top h.symm

theorem two_OK_ne_zero : (2 : 𝓞 K) ≠ 0 := by
  exact_mod_cast (by decide : (2 : ℤ) ≠ 0)

theorem span_two_ne_zero : Ideal.span {(2 : 𝓞 K)} ≠ 0 := by
  intro h
  rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h
  exact two_OK_ne_zero h

/-- The fourteen lattices of index at most 7, written as the unit ideal,
    the six split primes, the principal ideal `(2)`, and the products
    `p2²`, `p2b²`, `p2 p3`, `p2 p3b`, `p2b p3`, `p2b p3b`.
    Each class equals `p2_class ^ e` for an exponent read off the
    multiplication table, so these fourteen ideals determine ten classes. -/
theorem BSD_fourteen_lattices_ten_classes :
    ClassGroup.mk0 (nzIdeal (⊤ : Ideal (𝓞 K)) top_ideal_ne_zero) = p2_class ^ 0 ∧
      ClassGroup.mk0 (nzIdeal p2_OK p2_ne_bot) = p2_class ^ 1 ∧
      ClassGroup.mk0 (nzIdeal p2b_OK p2b_ne_zero) = p2_class ^ 9 ∧
      ClassGroup.mk0 (nzIdeal p3_OK p3_ne_zero) = p2_class ^ 4 ∧
      ClassGroup.mk0 (nzIdeal p3b_OK p3b_ne_zero) = p2_class ^ 6 ∧
      ClassGroup.mk0 (nzIdeal (p2_OK ^ 2) (pow_ne_zero 2 p2_ne_bot)) = p2_class ^ 2 ∧
      ClassGroup.mk0 (nzIdeal (Ideal.span {(2 : 𝓞 K)}) span_two_ne_zero) = p2_class ^ 0 ∧
      ClassGroup.mk0 (nzIdeal (p2b_OK ^ 2) (pow_ne_zero 2 p2b_ne_zero)) = p2_class ^ 8 ∧
      ClassGroup.mk0 (nzIdeal (p2_OK * p3_OK) (mul_ne_zero p2_ne_bot p3_ne_zero)) =
          p2_class ^ 5 ∧
      ClassGroup.mk0 (nzIdeal (p2_OK * p3b_OK) (mul_ne_zero p2_ne_bot p3b_ne_zero)) =
          p2_class ^ 7 ∧
      ClassGroup.mk0 (nzIdeal (p2b_OK * p3_OK) (mul_ne_zero p2b_ne_zero p3_ne_zero)) =
          p2_class ^ 3 ∧
      ClassGroup.mk0 (nzIdeal (p2b_OK * p3b_OK) (mul_ne_zero p2b_ne_zero p3b_ne_zero)) =
          p2_class ^ 5 ∧
      ClassGroup.mk0 (nzIdeal p7_OK p7_ne_zero) = p2_class ^ 3 ∧
      ClassGroup.mk0 (nzIdeal p7b_OK p7b_ne_zero) = p2_class ^ 7 := by
  refine ⟨?_, ?_, class_p2b _, class_p3 _, class_p3b _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, class_p7 _,
    class_p7b _⟩
  · rw [pow_zero, ClassGroup.mk0_eq_one_iff, Submodule.isPrincipal_iff]
    exact ⟨(1 : 𝓞 K), by simp [nzIdeal, Ideal.span_singleton_one]⟩
  · simp [p2_class, pow_one, nzIdeal]
  · exact p2_class_pow 2
  · rw [pow_zero, ClassGroup.mk0_eq_one_iff, Submodule.isPrincipal_iff]
    exact ⟨(2 : 𝓞 K), by simp [nzIdeal]⟩
  · have h := class_mul_pow p2b_ne_zero p2b_ne_zero (class_p2b p2b_ne_zero) (class_p2b p2b_ne_zero)
    have hsub : nzIdeal (p2b_OK ^ 2) (pow_ne_zero 2 p2b_ne_zero) =
        nzIdeal (p2b_OK * p2b_OK) (mul_ne_zero p2b_ne_zero p2b_ne_zero) :=
      Subtype.ext (pow_two p2b_OK)
    rw [hsub, h]
  · have hp2 : ClassGroup.mk0 (nzIdeal p2_OK p2_ne_bot) = p2_class ^ 1 := by
      simp [p2_class, pow_one]
    have h := class_mul_pow p2_ne_bot p3_ne_zero hp2 (class_p3 p3_ne_zero)
    rw [h]
  · have hp2 : ClassGroup.mk0 (nzIdeal p2_OK p2_ne_bot) = p2_class ^ 1 := by
      simp [p2_class, pow_one]
    have h := class_mul_pow p2_ne_bot p3b_ne_zero hp2 (class_p3b p3b_ne_zero)
    rw [h]
  · have h := class_mul_pow p2b_ne_zero p3_ne_zero (class_p2b _) (class_p3 _)
    rw [h]
  · have h := class_mul_pow p2b_ne_zero p3b_ne_zero (class_p2b _) (class_p3b _)
    rw [h]

/-- Order 10, the norm-7 classes inside that cyclic subgroup, and
    `classNumber K = 10`. The 26 assessed definitions stay untouched,
    so this is not a change of the 54/504 tally. -/
theorem BSD_classNumber_collapse_record :
    orderOf p2_class = 10 ∧
      NumberField.classNumber K = 10 ∧
      (∀ I : (Ideal (𝓞 K))⁰, Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 7 →
        ∃ k : ℕ, k < 10 ∧ ClassGroup.mk0 I = p2_class ^ k) ∧
      (84 : ℕ) ≠ 54 :=
  ⟨orderOf_p2_class, BSD_classNumber_eq_ten_collapse, BSD_small_norm_class_is_p2_power,
    BSD_54_of_504.2.2⟩

end Towers.BSD

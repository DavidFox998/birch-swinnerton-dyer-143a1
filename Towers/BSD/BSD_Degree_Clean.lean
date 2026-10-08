/-
  Group A. The function-field degree of the coordinate `p`-power map.

  Let `k = 𝔽_p` and let `k(E) = k(x, y)` with `y² + y = x³ − x² − x − 2`.
  The subfield `k(x^p, y^p)` is the pullback of `(x, y) ↦ (x^p, y^p)`.
  `degree_frobenius p` is `[k(E) : k(x^p, y^p)]`. `BSD_Frobenius_degree_eq_p`
  proves that this degree equals `p`, for every prime `p`.

  `[k(x, y) : k(x)] = 2` and `[k(x) : k(x^p)] = p`, so `[k(x, y) : k(x^p)] = 2p`.
  `[k(x^p, y^p) : k(x^p)] = 2`, and the tower law gives the quotient `p`.
  `X` is not a `p`-th power in `k(X)`, by degrees, so `T^p - X` is irreducible.
  `T² + T - (X³ - X² - X - 2)` has no root in `k(X)`: a root would be a polynomial
  whose square has degree `3`.

  Mathlib v4.12.0 has no degree of a general elliptic endomorphism. This file does
  not prove `deg(n - m φ) = n² - a_p n m + m² p` and does not prove `a_p² ≤ 4p`
  for every prime outside `1859`. The 328 assessed definitions were not rewritten.
  The tally stays 54 of 504. No new point count. No prime at or above 1000. No sorry.
-/

import Towers.BSD.BSD_Finite_Hasse_54_Theorem
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.Adjoin
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.CharP.ExpChar
import Mathlib.Algebra.Polynomial.Expand

noncomputable section

open Polynomial IntermediateField AdjoinRoot FiniteDimensional

namespace Towers.BSD

/-- `X³ - X² - X - 2`. -/
def gPoly (R : Type*) [CommRing R] : R[X] :=
  X ^ 3 - (X ^ 2 + X + C 2)

lemma natDegree_gPoly {R : Type*} [CommRing R] [Nontrivial R] : (gPoly R).natDegree = 3 := by
  have hle : (X ^ 2 + X + C (2 : R)).natDegree ≤ 2 := by
    calc
      _ ≤ max (X ^ 2 + X : R[X]).natDegree (C (2 : R)).natDegree := natDegree_add_le _ _
      _ ≤ 2 := by
        refine max_le ?_ (by simp)
        calc
          (X ^ 2 + X : R[X]).natDegree ≤
              max (X ^ 2 : R[X]).natDegree (X : R[X]).natDegree := natDegree_add_le _ _
          _ = 2 := by simp
  have hlt : (X ^ 2 + X + C (2 : R)).natDegree < (X ^ 3 : R[X]).natDegree := by
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt hle (by norm_num)
  rw [gPoly, natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_X_pow]

lemma gPoly_ne_zero {R : Type*} [CommRing R] [Nontrivial R] : gPoly R ≠ 0 := by
  intro h
  have := congrArg natDegree h
  rw [natDegree_gPoly, natDegree_zero] at this
  simp at this

lemma intDegree_pow {K : Type*} [Field K] {x : RatFunc K} (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).intDegree = (n : ℤ) * x.intDegree := by
  induction n with
  | zero => simp [RatFunc.intDegree_one]
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero n hx) hx, ih, Nat.cast_succ, add_mul,
      one_mul, add_comm]

/-- The indeterminate is not a `p`-th power in `k(X)` when `1 < p`. -/
lemma X_not_pow {K : Type*} [Field K] {n : ℕ} (hn : 1 < n) (r : RatFunc K) :
    r ^ n ≠ RatFunc.X := by
  intro h
  have hr : r ≠ 0 := by
    intro hr0
    rw [hr0, zero_pow (by omega : n ≠ 0)] at h
    exact RatFunc.X_ne_zero h.symm
  have hdeg : (n : ℤ) * r.intDegree = 1 := by
    have := congrArg RatFunc.intDegree h
    rwa [intDegree_pow hr n, RatFunc.intDegree_X] at this
  have hmul : n * r.intDegree.natAbs = 1 := Int.natAbs_mul_natAbs_eq hdeg
  exact ne_of_gt hn (Nat.eq_one_of_mul_eq_one_right (m := n) (n := r.intDegree.natAbs) hmul)

abbrev Rx (p : ℕ) [Fact p.Prime] := RatFunc (ZMod p)

/-- The rational function `X³ - X² - X - 2`. -/
def gCoord (p : ℕ) [Fact p.Prime] : Rx p :=
  algebraMap ((ZMod p)[X]) (Rx p) (gPoly (ZMod p))

/-- `T² + T - (X³ - X² - X - 2)` over `k(X)`. -/
def quad (p : ℕ) [Fact p.Prime] : (Rx p)[X] :=
  X ^ 2 + X - C (gCoord p)

lemma quad_natDegree (p : ℕ) [Fact p.Prime] : (quad p).natDegree = 2 := by
  rw [quad, add_sub_assoc, natDegree_add_eq_left_of_natDegree_lt
    (by rw [natDegree_X_pow, natDegree_X_sub_C]; omega), natDegree_X_pow]

lemma quad_monic (p : ℕ) [Fact p.Prime] : (quad p).Monic := by
  rw [quad, add_sub_assoc]
  exact (monic_X_pow 2).add_of_left (by
    rw [degree_X_pow, degree_X_sub_C]
    exact WithBot.coe_lt_coe.mpr one_lt_two)

lemma quad_ne_one (p : ℕ) [Fact p.Prime] : quad p ≠ 1 := by
  intro h
  have := congrArg natDegree h
  rw [quad_natDegree, natDegree_one] at this
  simp at this

/-- No rational function satisfies `r² + r = X³ - X² - X - 2`. -/
lemma rat_not_weier (p : ℕ) [Fact p.Prime] (r : Rx p) : r ^ 2 + r ≠ gCoord p := by
  intro h
  set n := r.num
  set d := r.denom
  have hd : d ≠ 0 := r.denom_ne_zero
  have hrepr : algebraMap _ _ n / algebraMap _ _ d = r := RatFunc.num_div_denom r
  set N : Rx p := algebraMap ((ZMod p)[X]) (Rx p) n
  set D : Rx p := algebraMap ((ZMod p)[X]) (Rx p) d
  have hD : D ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have hmul : N ^ 2 + N * D = gCoord p * D ^ 2 := by
    have hdiv : (N / D) ^ 2 + N / D = gCoord p := by rwa [← hrepr] at h
    have hscale : ((N / D) ^ 2 + N / D) * D ^ 2 = gCoord p * D ^ 2 :=
      congr_arg (· * D ^ 2) hdiv
    rw [add_mul] at hscale
    have hleft : (N / D) ^ 2 * D ^ 2 + (N / D) * D ^ 2 = N ^ 2 + N * D := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hD)]
      rw [show (N / D) * D ^ 2 = N * D by rw [pow_two, ← mul_assoc, div_mul_cancel₀ _ hD]]
    rw [hleft] at hscale
    exact hscale
  have hpoly : n ^ 2 + n * d = gPoly (ZMod p) * d ^ 2 := by
    apply RatFunc.algebraMap_injective (ZMod p)
    simpa [N, D, gCoord, map_add, map_mul, map_pow] using hmul
  have hdvd : d ∣ n ^ 2 := by
    refine ⟨gPoly (ZMod p) * d - n, ?_⟩
    calc
      n ^ 2 = (n ^ 2 + n * d) - n * d := by ring
      _ = gPoly (ZMod p) * d ^ 2 - n * d := by rw [hpoly]
      _ = d * (gPoly (ZMod p) * d - n) := by ring
  have hcop : IsCoprime n d := r.isCoprime_num_denom
  have hdvd_n : d ∣ n :=
    hcop.symm.dvd_of_dvd_mul_right (by simpa [pow_two] using hdvd)
  have hd1 : d = 1 :=
    (RatFunc.monic_denom r).eq_one_of_isUnit (hcop.symm.isUnit_of_dvd hdvd_n)
  have hn : n ^ 2 + n = gPoly (ZMod p) := by simpa [hd1] using hpoly
  by_cases hn0 : n = 0
  · exact gPoly_ne_zero (by simpa [hn0] using hn.symm)
  · have hsq : (n ^ 2).natDegree = n.natDegree + n.natDegree := by
      rw [pow_two, natDegree_mul hn0 hn0]
    by_cases hdeg0 : n.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hdeg0] at hn
      have hconst : (C ((n.coeff 0) ^ 2 + n.coeff 0) : (ZMod p)[X]) = gPoly (ZMod p) := by
        simpa [pow_two, map_add, map_mul, sq] using hn
      have := congrArg natDegree hconst
      rw [natDegree_C, natDegree_gPoly] at this
      simp at this
    · have hlt : n.natDegree < (n ^ 2).natDegree := by rw [hsq]; omega
      have hadd : (n ^ 2 + n).natDegree = (n ^ 2).natDegree :=
        natDegree_add_eq_left_of_natDegree_lt hlt
      have : n.natDegree + n.natDegree = 3 := by
        rw [← hsq, ← hadd, hn, natDegree_gPoly]
      omega

lemma quad_roots (p : ℕ) [Fact p.Prime] : (quad p).roots = 0 := by
  rw [Multiset.eq_zero_iff_forall_not_mem]
  intro r hr
  rw [mem_roots (quad_monic p).ne_zero, IsRoot, quad, eval_sub, eval_add, eval_pow, eval_X,
    eval_C, sub_eq_zero] at hr
  exact rat_not_weier p r hr

lemma quad_irreducible (p : ℕ) [Fact p.Prime] : Irreducible (quad p) :=
  (irreducible_iff_roots_eq_zero_of_degree_le_three
      (by rw [quad_natDegree])
      (by rw [quad_natDegree]; exact Nat.le_succ 2)).mpr (quad_roots p)

instance quad_irreducible_fact (p : ℕ) [Fact p.Prime] : Fact (Irreducible (quad p)) :=
  ⟨quad_irreducible p⟩

abbrev FE (p : ℕ) [Fact p.Prime] := AdjoinRoot (quad p)

instance (p : ℕ) [Fact p.Prime] : CharP (Rx p) p :=
  charP_of_injective_algebraMap' (ZMod p) (Rx p) p

instance (p : ℕ) [Fact p.Prime] : CharP (FE p) p :=
  charP_of_injective_algebraMap' (Rx p) (FE p) p

def xE (p : ℕ) [Fact p.Prime] : FE p :=
  algebraMap (Rx p) (FE p) RatFunc.X

def yE (p : ℕ) [Fact p.Prime] : FE p :=
  root (quad p)

lemma y_weier (p : ℕ) [Fact p.Prime] :
    yE p ^ 2 + yE p = algebraMap (Rx p) (FE p) (gCoord p) := by
  have h := eval₂_root (quad p)
  rw [quad, eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  simpa [yE] using h

/-- The structure map `(ZMod p)[X] → k(X)`. -/
def polyToRat (p : ℕ) [Fact p.Prime] : (ZMod p)[X] →ₐ[ZMod p] Rx p :=
  IsScalarTower.toAlgHom (ZMod p) ((ZMod p)[X]) (Rx p)

lemma polyToRat_injective (p : ℕ) [Fact p.Prime] : Function.Injective (polyToRat p) := by
  intro a b h
  exact RatFunc.algebraMap_injective (ZMod p) (by simpa [polyToRat, IsScalarTower.toAlgHom_apply] using h)

lemma expand_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (Polynomial.expand (ZMod p) p) := by
  intro a b h
  have h0 : Polynomial.expand (ZMod p) p (a - b) = 0 := by simp [map_sub, h]
  exact sub_eq_zero.mp
    ((expand_eq_zero (Nat.Prime.pos (Fact.out : Nat.Prime p))).1 h0)

def expandToRat (p : ℕ) [Fact p.Prime] : (ZMod p)[X] →ₐ[ZMod p] Rx p :=
  (polyToRat p).comp (Polynomial.expand (ZMod p) p)

lemma expandToRat_injective (p : ℕ) [Fact p.Prime] : Function.Injective (expandToRat p) := by
  intro a b h
  exact expand_injective p (polyToRat_injective p (by simpa [expandToRat] using h))

/-- Pull rational functions back along `T ↦ T^p`. -/
def ratPow (p : ℕ) [Fact p.Prime] : Rx p →ₐ[ZMod p] Rx p :=
  RatFunc.liftAlgHom (expandToRat p)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (expandToRat_injective p))

lemma ratPow_injective (p : ℕ) [Fact p.Prime] : Function.Injective (ratPow p) :=
  RatFunc.liftAlgHom_injective (expandToRat p) (expandToRat_injective p)

lemma ratPow_coe (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) :
    ratPow p (algebraMap ((ZMod p)[X]) (Rx p) f) =
      algebraMap ((ZMod p)[X]) (Rx p) (Polynomial.expand (ZMod p) p f) := by
  have hdiv : algebraMap ((ZMod p)[X]) (Rx p) f =
      algebraMap ((ZMod p)[X]) (Rx p) f / algebraMap ((ZMod p)[X]) (Rx p) 1 := by
    simp
  rw [hdiv, ratPow, RatFunc.liftAlgHom_apply_div, expandToRat, AlgHom.comp_apply, map_one,
    div_one, polyToRat, IsScalarTower.toAlgHom_apply]

lemma ratPow_X (p : ℕ) [Fact p.Prime] : ratPow p (RatFunc.X : Rx p) = RatFunc.X ^ p := by
  rw [← RatFunc.algebraMap_X, ratPow_coe, expand_X, map_pow, RatFunc.algebraMap_X]

def toRx (p : ℕ) [Fact p.Prime] : Rx p →ₐ[ZMod p] FE p :=
  IsScalarTower.toAlgHom (ZMod p) (Rx p) (FE p)

lemma toRx_injective (p : ℕ) [Fact p.Prime] : Function.Injective (toRx p) := by
  intro a b h
  rw [← sub_eq_zero]
  by_contra hab
  have h1 : toRx p ((a - b) * (a - b)⁻¹) = 0 := by
    rw [map_mul, map_sub, h, sub_self, zero_mul]
  rw [mul_inv_cancel₀ hab, map_one] at h1
  exact one_ne_zero h1

lemma toRx_poly (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) :
    toRx p (algebraMap ((ZMod p)[X]) (Rx p) f) = aeval (xE p) f := by
  induction f using Polynomial.induction_on' with
  | h_add f g hf hg =>
    rw [map_add (algebraMap ((ZMod p)[X]) (Rx p)), map_add (toRx p), aeval_add, hf, hg]
  | h_monomial n a =>
    have hC : toRx p (algebraMap ((ZMod p)[X]) (Rx p) (C a)) = algebraMap (ZMod p) (FE p) a := by
      rw [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply (ZMod p) ((ZMod p)[X]) (Rx p), toRx,
        IsScalarTower.toAlgHom_apply (ZMod p) (Rx p) (FE p),
        ← IsScalarTower.algebraMap_apply (ZMod p) (Rx p) (FE p)]
    have hX : toRx p (algebraMap ((ZMod p)[X]) (Rx p) X) = xE p := by
      rw [xE, toRx, IsScalarTower.toAlgHom_apply (ZMod p) (Rx p) (FE p), RatFunc.algebraMap_X]
    rw [aeval_monomial, ← C_mul_X_pow_eq_monomial,
      map_mul (algebraMap ((ZMod p)[X]) (Rx p)), map_pow (algebraMap ((ZMod p)[X]) (Rx p)),
      map_mul (toRx p), map_pow (toRx p), hC, hX]

def toXp (p : ℕ) [Fact p.Prime] : Rx p →ₐ[ZMod p] FE p :=
  (toRx p).comp (ratPow p)

lemma toXp_injective (p : ℕ) [Fact p.Prime] : Function.Injective (toXp p) :=
  (toRx_injective p).comp (ratPow_injective p)

/-- `k(x^p)` inside the function field. -/
def Kxp (p : ℕ) [Fact p.Prime] : IntermediateField (ZMod p) (FE p) :=
  (toXp p).fieldRange

/-- The class of `x^p` in `k(x^p)`. -/
def xp (p : ℕ) [Fact p.Prime] : Kxp p :=
  ⟨toXp p RatFunc.X, AlgHom.mem_fieldRange.mpr ⟨RatFunc.X, rfl⟩⟩

lemma xp_val (p : ℕ) [Fact p.Prime] : (xp p : FE p) = xE p ^ p := by
  simp [xp, toXp, xE, ratPow_X, map_pow, toRx, IsScalarTower.toAlgHom_apply]

/-- `T^p - x^p` over `k(x^p)`. -/
def xPoly (p : ℕ) [Fact p.Prime] : (Kxp p)[X] :=
  X ^ p - C (xp p)

lemma xp_not_pow (p : ℕ) [Fact p.Prime] (b : Kxp p) : b ^ p ≠ xp p := by
  intro h
  obtain ⟨s, hs⟩ := AlgHom.mem_fieldRange.mp b.property
  have hval : toXp p (s ^ p) = toXp p RatFunc.X := by
    calc
      toXp p (s ^ p) = (toXp p s) ^ p := by rw [map_pow]
      _ = (b : FE p) ^ p := by rw [hs]
      _ = ((b ^ p : Kxp p) : FE p) := (map_pow (algebraMap (Kxp p) (FE p)) b p).symm
      _ = (xp p : FE p) := congrArg Subtype.val h
      _ = toXp p RatFunc.X := by rw [xp]
  exact X_not_pow (Nat.Prime.one_lt (Fact.out : Nat.Prime p)) s (toXp_injective p hval)

lemma xPoly_irreducible (p : ℕ) [Fact p.Prime] : Irreducible (xPoly p) :=
  X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p) (xp_not_pow p)

lemma xPoly_monic (p : ℕ) [Fact p.Prime] : (xPoly p).Monic :=
  monic_X_pow_sub_C _ (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))

lemma xPoly_aeval (p : ℕ) [Fact p.Prime] : aeval (xE p) (xPoly p) = 0 := by
  simp [xPoly, xp_val, sub_eq_zero]

lemma x_isIntegral (p : ℕ) [Fact p.Prime] : IsIntegral (Kxp p) (xE p) :=
  ⟨xPoly p, xPoly_monic p, xPoly_aeval p⟩

lemma minpoly_x (p : ℕ) [Fact p.Prime] : minpoly (Kxp p) (xE p) = xPoly p :=
  (minpoly.eq_of_irreducible_of_monic (xPoly_irreducible p) (xPoly_aeval p) (xPoly_monic p)).symm

/-- `k(x) = k(x^p)(x)`. -/
def Kx (p : ℕ) [Fact p.Prime] : IntermediateField (Kxp p) (FE p) :=
  adjoin (Kxp p) {xE p}

lemma finrank_Kx (p : ℕ) [Fact p.Prime] : finrank (Kxp p) (Kx p) = p := by
  rw [Kx, adjoin.finrank (x_isIntegral p), minpoly_x, xPoly, natDegree_X_pow_sub_C]

lemma aeval_x_mem (p : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) : aeval (xE p) f ∈ Kx p := by
  induction f using Polynomial.induction_on' with
  | h_add f g hf hg => simpa [aeval_add] using add_mem hf hg
  | h_monomial n a =>
    rw [aeval_monomial, IsScalarTower.algebraMap_apply (ZMod p) (Kxp p) (FE p)]
    exact mul_mem (algebraMap_mem _ (algebraMap (ZMod p) (Kxp p) a))
      (pow_mem (subset_adjoin (Kxp p) {xE p} (Set.mem_singleton _)) n)

lemma toRx_mem (p : ℕ) [Fact p.Prime] (r : Rx p) : toRx p r ∈ Kx p := by
  rw [← RatFunc.num_div_denom r, map_div₀, toRx_poly, toRx_poly]
  exact div_mem (aeval_x_mem p r.num) (aeval_x_mem p r.denom)

/-- The value `z³ - z² - z - 2`. -/
def gEval {R : Type*} [Ring R] (z : R) : R :=
  z ^ 3 - z ^ 2 - z - 2

lemma gEval_pow (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] (z : R) :
    gEval z ^ p = gEval (z ^ p) := by
  have htwo : (2 : R) ^ p = 2 := by
    rw [← Nat.cast_two, ← frobenius_def (R := R) (p := p), frobenius_natCast, Nat.cast_two]
  have h3 : (z ^ 3) ^ p = (z ^ p) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]
  have h2 : (z ^ 2) ^ p = (z ^ p) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
  calc
    gEval z ^ p = (z ^ 3 - z ^ 2 - z - 2) ^ p := by simp [gEval]
    _ = (z ^ 3 - z ^ 2 - z) ^ p - (2 : R) ^ p := by rw [sub_pow_char]
    _ = (z ^ 3 - z ^ 2) ^ p - z ^ p - (2 : R) ^ p := by rw [sub_pow_char]
    _ = (z ^ 3) ^ p - (z ^ 2) ^ p - z ^ p - (2 : R) ^ p := by rw [sub_pow_char]
    _ = (z ^ p) ^ 3 - (z ^ p) ^ 2 - z ^ p - 2 := by rw [h3, h2, htwo]
    _ = gEval (z ^ p) := by simp [gEval]

lemma gEval_x (p : ℕ) [Fact p.Prime] :
    gEval (xE p) = algebraMap (Rx p) (FE p) (gCoord p) := by
  calc
    gEval (xE p) = aeval (xE p) (gPoly (ZMod p)) := by
      rw [gEval, gPoly, map_sub (aeval (xE p)), map_pow (aeval (xE p)), aeval_add, aeval_add,
        map_pow (aeval (xE p)), aeval_X, aeval_C, map_ofNat]
      ring
    _ = toRx p (algebraMap ((ZMod p)[X]) (Rx p) (gPoly (ZMod p))) := (toRx_poly p _).symm
    _ = algebraMap (Rx p) (FE p) (gCoord p) := by
      rw [toRx, IsScalarTower.toAlgHom_apply, gCoord]

lemma y_pow_sq (p : ℕ) [Fact p.Prime] : (yE p ^ p) ^ 2 = (yE p ^ 2) ^ p := by
  rw [← pow_mul, ← pow_mul, mul_comm]

lemma y_pow_weier (p : ℕ) [Fact p.Prime] :
    (yE p ^ p) ^ 2 + yE p ^ p = gEval (xE p ^ p) := by
  have hrel : yE p ^ 2 + yE p = gEval (xE p) := by rw [y_weier, gEval_x]
  calc
    (yE p ^ p) ^ 2 + yE p ^ p = (yE p ^ 2) ^ p + yE p ^ p := by rw [y_pow_sq]
    _ = (yE p ^ 2 + yE p) ^ p := by rw [add_pow_char]
    _ = gEval (xE p) ^ p := by rw [hrel]
    _ = gEval (xE p ^ p) := gEval_pow p _

/-- The class of `g(x^p)` in `k(x^p)`. -/
def gp (p : ℕ) [Fact p.Prime] : Kxp p :=
  ⟨toXp p (gCoord p), AlgHom.mem_fieldRange.mpr ⟨gCoord p, rfl⟩⟩

lemma gp_val (p : ℕ) [Fact p.Prime] : (gp p : FE p) = gEval (xE p ^ p) := by
  change toXp p (gCoord p) = gEval (xE p ^ p)
  rw [toXp, AlgHom.comp_apply]
  rw [show gCoord p = algebraMap ((ZMod p)[X]) (Rx p) (gPoly (ZMod p)) from rfl, ratPow_coe,
    toRx_poly, expand_eq_comp_X_pow, aeval_comp, map_pow (aeval (xE p)), aeval_X]
  rw [gEval, gPoly, map_sub (aeval (xE p ^ p)), map_pow (aeval (xE p ^ p)), aeval_add, aeval_add,
    map_pow (aeval (xE p ^ p)), aeval_X, aeval_C, map_ofNat]
  ring

/-- `T² + T - g(x^p)` over `k(x^p)`. -/
def yPoly (p : ℕ) [Fact p.Prime] : (Kxp p)[X] :=
  X ^ 2 + X - C (gp p)

lemma yPoly_natDegree (p : ℕ) [Fact p.Prime] : (yPoly p).natDegree = 2 := by
  rw [yPoly, add_sub_assoc, natDegree_add_eq_left_of_natDegree_lt
    (by rw [natDegree_X_pow, natDegree_X_sub_C]; omega), natDegree_X_pow]

lemma yPoly_monic (p : ℕ) [Fact p.Prime] : (yPoly p).Monic := by
  rw [yPoly, add_sub_assoc]
  exact (monic_X_pow 2).add_of_left (by
    rw [degree_X_pow, degree_X_sub_C]
    exact WithBot.coe_lt_coe.mpr one_lt_two)

lemma gp_not_weier (p : ℕ) [Fact p.Prime] (b : Kxp p) :
    (b : FE p) ^ 2 + b ≠ (gp p : FE p) := by
  intro h
  obtain ⟨s, hs⟩ := AlgHom.mem_fieldRange.mp b.property
  have hmap : toXp p (s ^ 2 + s) = toXp p (gCoord p) := by
    rw [map_add, map_pow, hs]
    simpa [gp] using h
  exact rat_not_weier p s (toXp_injective p hmap)

lemma yPoly_roots (p : ℕ) [Fact p.Prime] : (yPoly p).roots = 0 := by
  rw [Multiset.eq_zero_iff_forall_not_mem]
  intro r hr
  rw [mem_roots (yPoly_monic p).ne_zero, IsRoot, yPoly, eval_sub, eval_add, eval_pow, eval_X,
    eval_C, sub_eq_zero] at hr
  have hFE : (r : FE p) ^ 2 + r = (gp p : FE p) := by
    have hmap := congrArg (algebraMap (Kxp p) (FE p)) hr
    rwa [(algebraMap (Kxp p) (FE p)).map_add, (algebraMap (Kxp p) (FE p)).map_pow] at hmap
  exact gp_not_weier p r hFE

lemma yPoly_irreducible (p : ℕ) [Fact p.Prime] : Irreducible (yPoly p) :=
  (irreducible_iff_roots_eq_zero_of_degree_le_three
      (by rw [yPoly_natDegree])
      (by rw [yPoly_natDegree]; exact Nat.le_succ 2)).mpr (yPoly_roots p)

lemma yPoly_aeval (p : ℕ) [Fact p.Prime] : aeval (yE p ^ p) (yPoly p) = 0 := by
  rw [yPoly, map_sub (aeval (yE p ^ p)), aeval_add, map_pow (aeval (yE p ^ p)), aeval_X,
    aeval_C, sub_eq_zero, y_pow_weier]
  exact (gp_val p).symm

lemma ypow_isIntegral (p : ℕ) [Fact p.Prime] : IsIntegral (Kxp p) (yE p ^ p) :=
  ⟨yPoly p, yPoly_monic p, yPoly_aeval p⟩

lemma minpoly_ypow (p : ℕ) [Fact p.Prime] : minpoly (Kxp p) (yE p ^ p) = yPoly p :=
  (minpoly.eq_of_irreducible_of_monic (yPoly_irreducible p) (yPoly_aeval p) (yPoly_monic p)).symm

/-- `k(x^p, y^p)`. -/
def Kpy (p : ℕ) [Fact p.Prime] : IntermediateField (Kxp p) (FE p) :=
  adjoin (Kxp p) {yE p ^ p}

lemma finrank_Kpy (p : ℕ) [Fact p.Prime] : finrank (Kxp p) (Kpy p) = 2 := by
  rw [Kpy, adjoin.finrank (ypow_isIntegral p), minpoly_ypow, yPoly_natDegree]

/-- The class of `g(x)` in `k(x)`. -/
def gx (p : ℕ) [Fact p.Prime] : Kx p :=
  ⟨algebraMap (Rx p) (FE p) (gCoord p), toRx_mem p (gCoord p)⟩

/-- `T² + T - g(x)` over `k(x)`. -/
def yOverX (p : ℕ) [Fact p.Prime] : (Kx p)[X] :=
  X ^ 2 + X - C (gx p)

lemma yOverX_natDegree (p : ℕ) [Fact p.Prime] : (yOverX p).natDegree = 2 := by
  rw [yOverX, add_sub_assoc, natDegree_add_eq_left_of_natDegree_lt
    (by rw [natDegree_X_pow, natDegree_X_sub_C]; omega), natDegree_X_pow]

lemma yOverX_monic (p : ℕ) [Fact p.Prime] : (yOverX p).Monic := by
  rw [yOverX, add_sub_assoc]
  exact (monic_X_pow 2).add_of_left (by
    rw [degree_X_pow, degree_X_sub_C]
    exact WithBot.coe_lt_coe.mpr one_lt_two)

lemma lift_aeval (p : ℕ) [Fact p.Prime] (f : (Kxp p)[X]) :
    ∃ t : Rx p, toRx p t = aeval (xE p) f := by
  induction f using Polynomial.induction_on' with
  | h_add f g hf hg =>
    obtain ⟨tf, htf⟩ := hf
    obtain ⟨tg, htg⟩ := hg
    exact ⟨tf + tg, by rw [map_add (toRx p), aeval_add, htf, htg]⟩
  | h_monomial n a =>
    obtain ⟨s, hs⟩ := AlgHom.mem_fieldRange.mp a.property
    refine ⟨ratPow p s * RatFunc.X ^ n, ?_⟩
    rw [toXp, AlgHom.comp_apply] at hs
    rw [map_mul (toRx p), map_pow (toRx p), hs, aeval_monomial]
    rw [xE, toRx, IsScalarTower.toAlgHom_apply (ZMod p) (Rx p) (FE p),
      IntermediateField.algebraMap_apply]

lemma Kx_preimage (p : ℕ) [Fact p.Prime] (z : Kx p) : ∃ r : Rx p, toRx p r = z := by
  obtain ⟨u, v, huv⟩ :=
    (mem_adjoin_simple_iff (Kxp p) (α := xE p) (z : FE p)).mp z.property
  obtain ⟨tu, htu⟩ := lift_aeval p u
  obtain ⟨tv, htv⟩ := lift_aeval p v
  by_cases hv : aeval (xE p) v = 0
  · have hz : (z : FE p) = 0 := by simpa [hv, div_zero] using huv
    exact ⟨0, by simp [hz]⟩
  · refine ⟨tu / tv, ?_⟩
    rw [← htv] at hv
    rw [map_div₀ (toRx p), htu, htv]
    exact huv.symm

lemma yOverX_roots (p : ℕ) [Fact p.Prime] : (yOverX p).roots = 0 := by
  rw [Multiset.eq_zero_iff_forall_not_mem]
  intro r hr
  rw [mem_roots (yOverX_monic p).ne_zero, IsRoot, yOverX, eval_sub, eval_add, eval_pow, eval_X,
    eval_C, sub_eq_zero] at hr
  obtain ⟨s, hs⟩ := Kx_preimage p r
  have hFE : (r : FE p) ^ 2 + r = algebraMap (Rx p) (FE p) (gCoord p) := by
    have hmap := congrArg (algebraMap (Kx p) (FE p)) hr
    rw [(algebraMap (Kx p) (FE p)).map_add, (algebraMap (Kx p) (FE p)).map_pow, gx] at hmap
    exact hmap
  have hmap : toRx p (s ^ 2 + s) = toRx p (gCoord p) := by
    rw [map_add (toRx p), map_pow (toRx p), hs, toRx,
      IsScalarTower.toAlgHom_apply (ZMod p) (Rx p) (FE p)]
    exact hFE
  exact rat_not_weier p s (toRx_injective p hmap)

lemma yOverX_irreducible (p : ℕ) [Fact p.Prime] : Irreducible (yOverX p) :=
  (irreducible_iff_roots_eq_zero_of_degree_le_three
      (by rw [yOverX_natDegree])
      (by rw [yOverX_natDegree]; exact Nat.le_succ 2)).mpr (yOverX_roots p)

lemma yOverX_aeval (p : ℕ) [Fact p.Prime] : aeval (yE p) (yOverX p) = 0 := by
  rw [yOverX, map_sub (aeval (yE p)), aeval_add, map_pow (aeval (yE p)), aeval_X, aeval_C,
    sub_eq_zero, gx]
  exact y_weier p

lemma y_isIntegral (p : ℕ) [Fact p.Prime] : IsIntegral (Kx p) (yE p) :=
  ⟨yOverX p, yOverX_monic p, yOverX_aeval p⟩

lemma minpoly_y (p : ℕ) [Fact p.Prime] : minpoly (Kx p) (yE p) = yOverX p :=
  (minpoly.eq_of_irreducible_of_monic (yOverX_irreducible p) (yOverX_aeval p)
    (yOverX_monic p)).symm

lemma fe_repr (p : ℕ) [Fact p.Prime] (z : FE p) :
    ∃ a b : Rx p, z = toRx p a + toRx p b * yE p := by
  let f := modByMonicHom (quad_monic p) z
  have hzmk : mk (quad p) f = z := mk_leftInverse (quad_monic p) z
  have hfmod : f = f %ₘ quad p := by
    simpa [hzmk] using modByMonicHom_mk (quad_monic p) f
  have hdeg : f.natDegree ≤ 1 := by
    have hlt := natDegree_modByMonic_lt f (quad_monic p) (quad_ne_one p)
    rw [← hfmod, quad_natDegree] at hlt
    omega
  generalize hc0 : f.coeff 0 = c0
  generalize hc1 : f.coeff 1 = c1
  have hf := eq_X_add_C_of_natDegree_le_one hdeg
  rw [hc0, hc1] at hf
  refine ⟨c0, c1, ?_⟩
  rw [← hzmk, hf, ← aeval_eq, aeval_add, aeval_mul, aeval_C, aeval_X, aeval_C, yE, toRx,
    IsScalarTower.toAlgHom_apply (ZMod p) (Rx p) (FE p),
    IsScalarTower.toAlgHom_apply (ZMod p) (Rx p) (FE p)]
  ring_nf

lemma adjoin_y_top (p : ℕ) [Fact p.Prime] : adjoin (Kx p) {yE p} = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, hz⟩ := fe_repr p z
  rw [hz]
  set za : Kx p := ⟨toRx p a, toRx_mem p a⟩
  set zb : Kx p := ⟨toRx p b, toRx_mem p b⟩
  have hza : (za : FE p) ∈ adjoin (Kx p) {yE p} := algebraMap_mem _ za
  have hzb : (zb : FE p) ∈ adjoin (Kx p) {yE p} := algebraMap_mem _ zb
  have hy : yE p ∈ adjoin (Kx p) {yE p} := subset_adjoin _ _ (Set.mem_singleton _)
  exact add_mem hza (mul_mem hzb hy)

lemma finrank_Kx_FE (p : ℕ) [Fact p.Prime] : finrank (Kx p) (FE p) = 2 := by
  have hdeg : finrank (Kx p) (adjoin (Kx p) {yE p}) = 2 := by
    rw [adjoin.finrank (y_isIntegral p), minpoly_y, yOverX_natDegree]
  rw [adjoin_y_top, finrank_top'] at hdeg
  exact hdeg

lemma finrank_Kp_FE (p : ℕ) [Fact p.Prime] : finrank (Kxp p) (FE p) = 2 * p := by
  have h := finrank_mul_finrank (F := Kxp p) (K := Kx p) (A := FE p)
  rw [finrank_Kx, finrank_Kx_FE, mul_comm] at h
  exact h.symm

/-- Degree of `(x, y) ↦ (x^p, y^p)` on the function field: `[k(E) : k(x^p, y^p)]`. -/
def degree_frobenius (p : ℕ) [Fact p.Prime] : ℕ :=
  finrank (Kpy p) (FE p)

theorem BSD_Frobenius_degree_eq_p (p : ℕ) [Fact p.Prime] : degree_frobenius p = p := by
  have h := finrank_mul_finrank (F := Kxp p) (K := Kpy p) (A := FE p)
  rw [finrank_Kpy, finrank_Kp_FE] at h
  have hdeg : finrank (Kpy p) (FE p) = p :=
    Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h
  simpa [degree_frobenius] using hdeg

/-- The function-field degree is a natural number, so it is nonnegative.
    This is not nonnegativity of `n² - a_p n m + m² p`. -/
theorem BSD_Frobenius_degree_nonneg_actual (p : ℕ) [Fact p.Prime] :
    0 ≤ (degree_frobenius p : ℤ) :=
  Int.ofNat_nonneg _

/-- `degree_frobenius = p` does not prove the Hasse forall. The checked set still
    has 84 primes, and `84 ≠ 54`. -/
theorem BSD_degree_frobenius_not_hasse (p : ℕ) [Fact p.Prime] :
    degree_frobenius p = p ∧
      BSD_Finite_Hasse_CheckedPrimes.card = 84 ∧ (84 : ℕ) ≠ 54 :=
  ⟨BSD_Frobenius_degree_eq_p p, BSD_Finite_Hasse_CheckedPrimes_card, BSD_54_of_504.2.2⟩

end Towers.BSD

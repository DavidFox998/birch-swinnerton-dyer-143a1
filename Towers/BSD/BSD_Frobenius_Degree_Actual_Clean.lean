/-
  Group A. The coordinate `p`-power map, and why it is not yet Hasse's theorem.

  On `E(𝔽_p)` the formula `(x, y) ↦ (x^p, y^p)` is the identity, because
  `ZMod.pow_card` is Fermat's little theorem. An identity endomorphism of the
  finite group `E(𝔽_p)` is not a morphism of degree `p`.

  The same formula on the base change to an algebraic closure of `𝔽_p` is a
  ring-homomorphism application of `frobenius`. For every prime `p` not
  dividing `1859`, `BSD_geometric_frobenius_hom` is an additive endomorphism
  of the Mathlib group `Point` of that base change. The slope, `addX`, and
  `addY` formulas commute with `x ↦ x^p` because the Weierstrass coefficients
  lie in `𝔽_p` and Frobenius fixes `𝔽_p`.

  Mathlib v4.12.0 has no degree of an elliptic endomorphism and no isogeny.
  This file does not define `degree_frobenius`, does not prove that degree
  equals `p`, and does not prove `a_p² ≤ 4p` for every prime outside `1859`.
  The quadratic form remains the hypothesis in `BSD_Hasse_bound_forall`.
  The 328 assessed definitions were not rewritten. The tally stays 54 of 504.
  No new point count. No prime at or above 1000. No sorry.
-/

import Towers.BSD.BSD_Hasse_Forall_Clean
import Towers.BSD.BSD_Reduction_Clean
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.CharP.Reduced
import Mathlib.FieldTheory.Finite.Basic

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

namespace Towers.BSD

/-- On `𝔽_p`, the `p`-power map is the identity. -/
theorem BSD_zmod_frobenius_id (p : ℕ) [Fact p.Prime] (x : ZMod p) : x ^ p = x :=
  ZMod.pow_card x

/-- The coordinate formula the Hasse argument uses is the identity on affine
    `𝔽_p`-points. It preserves the equation because it does not change the point. -/
theorem BSD_affine_frobenius_id (p : ℕ) [Fact p.Prime] (x y : ZMod p) :
    E143_point p (x ^ p) (y ^ p) ↔ E143_point p x y := by
  simp [BSD_zmod_frobenius_id]

theorem BSD_affine_frobenius_coordinates (p : ℕ) [Fact p.Prime] (x y : ZMod p) :
    (x ^ p, y ^ p) = (x, y) := by
  simp [BSD_zmod_frobenius_id]

/-- Fermat's identity on `𝔽_p` is not a degree. The checked set still has 84
    primes, and `84 ≠ 54`. -/
theorem BSD_Fp_frobenius_not_degree :
    (∀ (p : ℕ) [Fact p.Prime] (x : ZMod p), x ^ p = x) ∧
      BSD_Finite_Hasse_CheckedPrimes.card = 84 ∧
      (84 : ℕ) ≠ 54 :=
  ⟨fun _ _ x => BSD_zmod_frobenius_id _ x, BSD_Finite_Hasse_CheckedPrimes_card,
    BSD_54_of_504.2.2⟩

/-! ### Geometric Frobenius over an algebraic closure -/

abbrev Kp (p : ℕ) [Fact p.Prime] := AlgebraicClosure (ZMod p)

def E143K (p : ℕ) [Fact p.Prime] : WeierstrassCurve (Kp p) :=
  (E143Fp p).map (algebraMap (ZMod p) (Kp p))

lemma frob_fixes_base (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    frobenius (Kp p) p (algebraMap (ZMod p) (Kp p) a) =
      algebraMap (ZMod p) (Kp p) a := by
  rw [frobenius_def, ← map_pow, BSD_zmod_frobenius_id]

@[simp] lemma E143K_a₁_fixed (p : ℕ) [Fact p.Prime] :
    frobenius (Kp p) p (E143K p).a₁ = (E143K p).a₁ := by
  rw [E143K, map_a₁]; exact frob_fixes_base p _

@[simp] lemma E143K_a₂_fixed (p : ℕ) [Fact p.Prime] :
    frobenius (Kp p) p (E143K p).a₂ = (E143K p).a₂ := by
  rw [E143K, map_a₂]; exact frob_fixes_base p _

@[simp] lemma E143K_a₃_fixed (p : ℕ) [Fact p.Prime] :
    frobenius (Kp p) p (E143K p).a₃ = (E143K p).a₃ := by
  rw [E143K, map_a₃]; exact frob_fixes_base p _

@[simp] lemma E143K_a₄_fixed (p : ℕ) [Fact p.Prime] :
    frobenius (Kp p) p (E143K p).a₄ = (E143K p).a₄ := by
  rw [E143K, map_a₄]; exact frob_fixes_base p _

@[simp] lemma E143K_a₆_fixed (p : ℕ) [Fact p.Prime] :
    frobenius (Kp p) p (E143K p).a₆ = (E143K p).a₆ := by
  rw [E143K, map_a₆]; exact frob_fixes_base p _

lemma E143K_Δ_map (p : ℕ) [Fact p.Prime] :
    (E143K p).Δ = algebraMap (ZMod p) (Kp p) ((E143Fp p).Δ) := by
  rw [E143K, map_Δ]

lemma E143K_Δ_ne_zero (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 1859) : (E143K p).Δ ≠ 0 := by
  rw [E143K_Δ_map]
  intro h
  rw [← map_zero (algebraMap (ZMod p) (Kp p))] at h
  exact E143Fp_Δ_ne_zero_of_not_dvd p hp <|
    (algebraMap (ZMod p) (Kp p)).injective h

lemma E143K_equation_frobenius (p : ℕ) [Fact p.Prime] {x y : Kp p}
    (h : Equation (E143K p) x y) : Equation (E143K p) (x ^ p) (y ^ p) := by
  rw [equation_iff] at h ⊢
  have h' := congrArg (frobenius (Kp p) p) h
  simp only [map_add, map_mul, map_pow] at h'
  rw [E143K_a₁_fixed, E143K_a₂_fixed, E143K_a₃_fixed, E143K_a₄_fixed,
    E143K_a₆_fixed] at h'
  simpa [frobenius_def] using h'

def BSD_frob_nonsingular (p : ℕ) [Fact p.Prime] (hΔ : (E143K p).Δ ≠ 0) {x y : Kp p}
    (h : Nonsingular (E143K p) x y) : Nonsingular (E143K p) (x ^ p) (y ^ p) :=
  nonsingular_of_Δ_ne_zero (E143K p) (E143K_equation_frobenius p h.1) hΔ

/-- `(x, y) ↦ (x^p, y^p)` on nonsingular points over the algebraic closure,
    with the point at infinity fixed. -/
def BSD_geometric_frobenius (p : ℕ) [Fact p.Prime] (hΔ : (E143K p).Δ ≠ 0) :
    Point (E143K p) → Point (E143K p)
  | Point.zero => Point.zero
  | @Point.some _ _ _ x y h =>
      Point.some (BSD_frob_nonsingular p hΔ (show Nonsingular (E143K p) x y from h))

@[simp] lemma BSD_geometric_frobenius_zero (p : ℕ) [Fact p.Prime]
    (hΔ : (E143K p).Δ ≠ 0) :
    BSD_geometric_frobenius p hΔ 0 = 0 := rfl

@[simp] lemma BSD_geometric_frobenius_some (p : ℕ) [Fact p.Prime]
    (hΔ : (E143K p).Δ ≠ 0) {x y : Kp p} (h : Nonsingular (E143K p) x y) :
    BSD_geometric_frobenius p hΔ (Point.some h) =
      Point.some (BSD_frob_nonsingular p hΔ h) := rfl

private lemma point_some_eq (p : ℕ) [Fact p.Prime] {W : WeierstrassCurve (Kp p)}
    {x y x' y' : Kp p} (h : Nonsingular W x y) (h' : Nonsingular W x' y')
    (hx : x = x') (hy : y = y') : Point.some h = Point.some h' := by
  subst hx
  subst hy
  exact congr_arg (@Point.some (Kp p) _ W x y) (Subsingleton.elim h h')

lemma E143K_negY_frobenius (p : ℕ) [Fact p.Prime] (x y : Kp p) :
    negY (E143K p) (x ^ p) (y ^ p) = (negY (E143K p) x y) ^ p := by
  simp only [negY, ← frobenius_def]
  apply Eq.symm
  rw [map_sub, map_sub, map_neg, map_mul, E143K_a₁_fixed, E143K_a₃_fixed]

lemma E143K_addX_frobenius (p : ℕ) [Fact p.Prime] (x₁ x₂ L : Kp p) :
    addX (E143K p) (x₁ ^ p) (x₂ ^ p) (L ^ p) = (addX (E143K p) x₁ x₂ L) ^ p := by
  simp only [addX, ← frobenius_def]
  apply Eq.symm
  rw [pow_two, map_sub, map_sub, map_sub, map_add, map_mul, map_mul,
    E143K_a₁_fixed, E143K_a₂_fixed, ← pow_two]

lemma E143K_negAddY_frobenius (p : ℕ) [Fact p.Prime] (x₁ x₂ y₁ L : Kp p) :
    negAddY (E143K p) (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (L ^ p) =
      (negAddY (E143K p) x₁ x₂ y₁ L) ^ p := by
  simp only [negAddY, ← frobenius_def]
  apply Eq.symm
  rw [map_add, map_mul, map_sub, frobenius_def, frobenius_def, frobenius_def,
    frobenius_def, frobenius_def, ← E143K_addX_frobenius]

lemma E143K_addY_frobenius (p : ℕ) [Fact p.Prime] (x₁ x₂ y₁ L : Kp p) :
    addY (E143K p) (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (L ^ p) =
      (addY (E143K p) x₁ x₂ y₁ L) ^ p := by
  rw [addY, E143K_addX_frobenius, E143K_negAddY_frobenius, E143K_negY_frobenius, ← addY]

lemma E143K_slope_frobenius (p : ℕ) [Fact p.Prime] (x₁ x₂ y₁ y₂ : Kp p) :
    slope (E143K p) (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (y₂ ^ p) =
      (slope (E143K p) x₁ x₂ y₁ y₂) ^ p := by
  by_cases hx : x₁ = x₂
  · have hx' : x₁ ^ p = x₂ ^ p := congrArg (fun t => t ^ p) hx
    by_cases hy : y₁ = negY (E143K p) x₂ y₂
    · have hy' : y₁ ^ p = negY (E143K p) (x₂ ^ p) (y₂ ^ p) := by
        rw [hy, E143K_negY_frobenius]
      simp [slope_of_Y_eq hx hy, slope_of_Y_eq hx' hy',
        zero_pow (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))]
    · have hy' : y₁ ^ p ≠ negY (E143K p) (x₂ ^ p) (y₂ ^ p) := by
        intro h
        apply hy
        apply frobenius_inj (Kp p) p
        rw [frobenius_def, frobenius_def, ← E143K_negY_frobenius, h]
      rw [slope_of_Y_ne hx hy, slope_of_Y_ne hx' hy']
      have hdiv (a b : Kp p) : (a / b) ^ p = a ^ p / b ^ p := by
        rw [← frobenius_def, map_div₀, frobenius_def, frobenius_def]
      have hden : negY (E143K p) (x₁ ^ p) (y₁ ^ p) = (negY (E143K p) x₁ y₁) ^ p :=
        E143K_negY_frobenius p x₁ y₁
      have hnum : 3 * (x₁ ^ p) ^ 2 + 2 * (E143K p).a₂ * x₁ ^ p + (E143K p).a₄ -
          (E143K p).a₁ * y₁ ^ p =
          (3 * x₁ ^ 2 + 2 * (E143K p).a₂ * x₁ + (E143K p).a₄ - (E143K p).a₁ * y₁) ^ p := by
        simp only [← (frobenius_def (p := p))]
        apply Eq.symm
        rw [map_sub, map_add, map_add, map_mul, map_mul, pow_two, map_mul,
          map_mul, map_ofNat, map_ofNat, E143K_a₂_fixed, E143K_a₄_fixed,
          map_mul, E143K_a₁_fixed, ← pow_two]
      have hsub : y₁ ^ p - (negY (E143K p) x₁ y₁) ^ p =
          (y₁ - negY (E143K p) x₁ y₁) ^ p := by
        simp only [← (frobenius_def (p := p))]
        rw [← frobenius_sub]
      rw [hden, hnum, hsub, ← hdiv]
  · have hx' : x₁ ^ p ≠ x₂ ^ p := by
      intro h
      exact hx <| frobenius_inj (Kp p) p <| by simpa [frobenius_def] using h
    rw [slope_of_X_ne hx, slope_of_X_ne hx']
    have hdiv (a b : Kp p) : (a / b) ^ p = a ^ p / b ^ p := by
      rw [← frobenius_def, map_div₀, frobenius_def, frobenius_def]
    have hsub (a b : Kp p) : (a - b) ^ p = a ^ p - b ^ p := by
      rw [← frobenius_def, frobenius_sub, frobenius_def, frobenius_def]
    rw [← hsub y₁ y₂, ← hsub x₁ x₂, ← hdiv]

private lemma image_not_inverse (p : ℕ) [Fact p.Prime] {x₁ x₂ y₁ y₂ : Kp p}
    (hne : x₁ = x₂ → y₁ ≠ negY (E143K p) x₂ y₂) :
    x₁ ^ p = x₂ ^ p → y₁ ^ p ≠ negY (E143K p) (x₂ ^ p) (y₂ ^ p) := by
  intro hx hy
  have hx0 : x₁ = x₂ := frobenius_inj (Kp p) p <| by simpa [frobenius_def] using hx
  apply hne hx0
  apply frobenius_inj (Kp p) p
  rw [frobenius_def, frobenius_def, ← E143K_negY_frobenius, hy]

theorem BSD_geometric_frobenius_neg (p : ℕ) [Fact p.Prime] (hΔ : (E143K p).Δ ≠ 0)
    (P : Point (E143K p)) :
    BSD_geometric_frobenius p hΔ (-P) = -BSD_geometric_frobenius p hΔ P := by
  match P with
  | Point.zero => rfl
  | @Point.some _ _ _ x y h =>
      rw [Point.neg_some, BSD_geometric_frobenius_some, BSD_geometric_frobenius_some]
      apply point_some_eq p
      · rfl
      · exact (E143K_negY_frobenius p x y).symm

theorem BSD_geometric_frobenius_add (p : ℕ) [Fact p.Prime] (hΔ : (E143K p).Δ ≠ 0)
    (P Q : Point (E143K p)) :
    BSD_geometric_frobenius p hΔ (P + Q) =
      BSD_geometric_frobenius p hΔ P + BSD_geometric_frobenius p hΔ Q := by
  match P, Q with
  | Point.zero, _ =>
      rw [Point.zero_def, zero_add, BSD_geometric_frobenius_zero, zero_add]
  | @Point.some _ _ _ _ _ _, Point.zero =>
      rw [Point.zero_def, add_zero, BSD_geometric_frobenius_zero, add_zero]
  | @Point.some _ _ _ x₁ y₁ h₁, @Point.some _ _ _ x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = negY (E143K p) x₂ y₂
      · have hsum : Point.some h₁ + Point.some h₂ = 0 := Point.add_of_Y_eq hxy.1 hxy.2
        have him : Point.some (BSD_frob_nonsingular p hΔ h₁) +
            Point.some (BSD_frob_nonsingular p hΔ h₂) = 0 := by
          apply Point.add_of_Y_eq
          · exact congrArg (fun t => t ^ p) hxy.1
          · rw [hxy.2, E143K_negY_frobenius]
        simp [hsum, him]
      · have hne : x₁ = x₂ → y₁ ≠ negY (E143K p) x₂ y₂ := fun hx hy => hxy ⟨hx, hy⟩
        have hne' := image_not_inverse p hne
        have hsum : Point.some h₁ + Point.some h₂ =
            Point.some (nonsingular_add h₁ h₂ hne) := Point.add_of_imp hne
        have him : Point.some (BSD_frob_nonsingular p hΔ h₁) +
              Point.some (BSD_frob_nonsingular p hΔ h₂) =
            Point.some (nonsingular_add (BSD_frob_nonsingular p hΔ h₁)
              (BSD_frob_nonsingular p hΔ h₂) hne') := Point.add_of_imp hne'
        rw [hsum, BSD_geometric_frobenius_some, BSD_geometric_frobenius_some,
          BSD_geometric_frobenius_some, him]
        apply point_some_eq p
        · rw [E143K_slope_frobenius]
          exact (E143K_addX_frobenius p x₁ x₂ (slope (E143K p) x₁ x₂ y₁ y₂)).symm
        · rw [E143K_slope_frobenius]
          exact (E143K_addY_frobenius p x₁ x₂ y₁ (slope (E143K p) x₁ x₂ y₁ y₂)).symm

/-- Geometric Frobenius is an endomorphism of `E` over the algebraic closure.
    This is not a degree, and it is not `a_p² ≤ 4p`. -/
def BSD_geometric_frobenius_hom (p : ℕ) [Fact p.Prime] (hΔ : (E143K p).Δ ≠ 0) :
    Point (E143K p) →+ Point (E143K p) where
  toFun := BSD_geometric_frobenius p hΔ
  map_zero' := BSD_geometric_frobenius_zero p hΔ
  map_add' := BSD_geometric_frobenius_add p hΔ

/-- `X^p - X - 1` has degree `p` over any field. -/
lemma natDegree_Xp_sub_X_sub_one (p : ℕ) (hp : 1 < p) (K : Type*) [Field K] :
    (X ^ p - X - 1 : K[X]).natDegree = p := by
  have hlt : (X + 1 : K[X]).natDegree < (X ^ p : K[X]).natDegree := by
    have hle : (X + 1 : K[X]).natDegree ≤ 1 := by
      calc (X + 1 : K[X]).natDegree
          ≤ max (X : K[X]).natDegree (1 : K[X]).natDegree := natDegree_add_le _ _
        _ = 1 := by simp
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt hle hp
  rw [sub_sub, natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_X_pow]

/-- Over the algebraic closure the `p`-power map moves some elements, so the
    geometric endomorphism is not the Fermat identity used on `E(𝔽_p)`. -/
theorem BSD_closure_frobenius_moves (p : ℕ) [Fact p.Prime] :
    ∃ a : Kp p, a ^ p ≠ a := by
  have hp : 1 < p := Nat.Prime.one_lt (Fact.out : Nat.Prime p)
  let f : (Kp p)[X] := X ^ p - X - 1
  have hdeg : f.natDegree = p := natDegree_Xp_sub_X_sub_one p hp (Kp p)
  have hf : f ≠ 0 := by
    intro hz
    have hn : f.natDegree = 0 := by simp [hz]
    rw [hdeg] at hn
    simp [hn] at hp
  have hne : f.degree ≠ 0 := by
    rw [degree_eq_natDegree hf, hdeg]
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hp) : p ≠ 0)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f hne
  refine ⟨a, ?_⟩
  intro hfix
  have heval : a ^ p - a - 1 = 0 := by
    simpa [f, eval_sub, eval_pow, eval_X, eval_one] using ha
  rw [hfix, sub_self, zero_sub] at heval
  exact one_ne_zero (neg_eq_zero.mp heval)

/-- The geometric endomorphism does not prove the Hasse forall. The degree of
    an elliptic endomorphism is not defined in Mathlib v4.12.0. The 328
    assessed definitions stay unrewritten, and `84 ≠ 54`. -/
theorem BSD_Hasse_bound_forall_actual_needs_degree :
    BSD_Finite_Hasse_CheckedPrimes.card = 84 ∧ (84 : ℕ) ≠ 54 :=
  ⟨BSD_Finite_Hasse_CheckedPrimes_card, BSD_54_of_504.2.2⟩

end Towers.BSD

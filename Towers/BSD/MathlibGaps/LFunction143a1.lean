/-
  Hasse-Weil L-function of 143a1.

  Curve: y² + y = x³ − x² − x − 2.
  Conductor N = 143 = 11 × 13. Discriminant Δ = −1859 = −11·13².
  The prime divisors of N are exactly 11 and 13. Both have non-split
  multiplicative reduction, so the local polynomial is the Steinberg
  factor 1 − a_p T with a_p = −1. They are the primes excluded from
  `ap_table_143a1` and from `BSD_HasseBound_Discriminant_CLOSED`.

  For every prime p, a_p is the affine trace p − #E(F_p). On a good prime
  this is the Hasse-Weil coefficient. On 11 and 13 the same count is −1.

  `L_143a1` is the Dirichlet series of the multiplicative lift of these
  local polynomials (`LSeries`). Mathlib's `LSeries` is the tsum of
  a_n n^{−s}, and is 0 at a point where that series is not summable.

  Absolute convergence for Re s > 3/2, and the Euler product on that
  half-plane, are proved from the Hasse bound `|a_p| ≤ 2√p` at every good
  prime. That bound is the hypothesis `Hasse143`. It is not a theorem of
  this file: Mathlib 4.12 has no elliptic Hasse theorem, and the pointwise
  checks elsewhere in the repository do not cover every prime.
  Analytic continuation to ℂ is not claimed.
  `MellinAnalyticExt` supplies local non-vanishing on Re s > 3/2
  (`complex_euler_poly_nonzero`, `cpow_normSq_lt_one`).
-/
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convolution
import Towers.BSD.MathlibGaps.MellinAnalyticExt

namespace Towers.BSD.MathlibGaps

open Complex Real Filter

open scoped LSeries.notation Topology

set_option maxHeartbeats 0

/-- Conductor of 143a1. -/
theorem conductor_143a1 : (143 : ℕ) = 11 * 13 := by norm_num

/-- A prime divides the conductor if and only if it is 11 or 13.
    Those are the bad primes left out of the good-reduction trace table. -/
theorem prime_dvd_143 (p : ℕ) (hp : Nat.Prime p) : p ∣ 143 ↔ p = 11 ∨ p = 13 := by
  have hN : (143 : ℕ) = 11 * 13 := conductor_143a1
  have h11 : Nat.Prime 11 := by decide
  have h13 : Nat.Prime 13 := by decide
  rw [hN, hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp h11, Nat.prime_dvd_prime_iff_eq hp h13]

/-- Number of affine points of 143a1 over F_p. -/
def affineCard (p : ℕ) : ℕ :=
  if h : p = 0 then 0 else
  have : NeZero p := ⟨h⟩
  Finset.card <| (Finset.univ : Finset (ZMod p × ZMod p)).filter fun xy =>
    xy.2 ^ 2 + xy.2 = xy.1 ^ 3 - xy.1 ^ 2 - xy.1 - 2

/-- Hasse-Weil trace a_p = p − #E_affine(F_p). -/
def a143 (p : ℕ) : ℤ := (p : ℤ) - affineCard p

theorem a143_2 : a143 2 = 0 := by native_decide
theorem a143_3 : a143 3 = -1 := by native_decide
theorem a143_5 : a143 5 = -1 := by native_decide
theorem a143_7 : a143 7 = -2 := by native_decide
theorem a143_11 : a143 11 = -1 := by native_decide
theorem a143_13 : a143 13 = -1 := by native_decide

theorem a143_bad (p : ℕ) (hp : p = 11 ∨ p = 13) : a143 p = -1 := by
  rcases hp with rfl | rfl
  · exact a143_11
  · exact a143_13

/-- Coefficient of p T² in the local polynomial: 0 at the bad primes, p otherwise. -/
def eulerQuad (p : ℕ) : ℤ :=
  if p = 11 ∨ p = 13 then 0 else (p : ℤ)

/-- Power-series coefficients of 1 / (1 − a_p T + ε_p p T²). -/
def aPow (p : ℕ) : ℕ → ℤ
  | 0 => 1
  | 1 => a143 p
  | n + 2 => a143 p * aPow p (n + 1) - eulerQuad p * aPow p n

/-- Dirichlet coefficients: multiplicative lift of `aPow`. -/
def coeff143 (n : ℕ) : ℤ :=
  if n = 0 then 0 else n.factorization.prod fun q k => aPow q k

theorem coeff143_zero : coeff143 0 = 0 := by simp [coeff143]

theorem coeff143_one : coeff143 1 = 1 := by
  simp [coeff143, Nat.factorization_one]

theorem aPow_zero (p : ℕ) : aPow p 0 = 1 := rfl

theorem aPow_one (p : ℕ) : aPow p 1 = a143 p := rfl

theorem coeff143_prime (p : ℕ) (hp : Nat.Prime p) : coeff143 p = a143 p := by
  have hfac : p.factorization = Finsupp.single p 1 := by
    ext q
    by_cases hq : q = p
    · simp [hq, hp.factorization_self]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hq)]
      rw [Nat.factorization_eq_zero_iff]
      by_cases hqp : q.Prime
      · right; left
        intro hdiv
        exact hq ((Nat.prime_dvd_prime_iff_eq hqp hp).1 hdiv)
      · left
        exact hqp
  simp only [coeff143, hp.ne_zero, if_false]
  rw [hfac, Finsupp.prod_single_index (by simp [aPow_zero])]
  exact aPow_one p

/-- Local denominator 1 − a_p p^{−s} + ε_p p^{1 − 2s}. -/
noncomputable def eulerDenom (p : ℕ) (s : ℂ) : ℂ :=
  if p = 11 ∨ p = 13 then
    1 - (a143 p : ℂ) * (p : ℂ) ^ (-s)
  else
    1 - (a143 p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) * ((p : ℂ) ^ (-s)) ^ 2

/-- Local Euler factor, the reciprocal of `eulerDenom`. -/
noncomputable def eulerFactor (p : ℕ) (s : ℂ) : ℂ := (eulerDenom p s)⁻¹

/-- Steinberg factor at 11 and 13 is non-zero for Re s > 0. -/
theorem bad_eulerDenom_ne_zero
    {p : ℕ} (hp : p = 11 ∨ p = 13) {s : ℂ} (hs : (0 : ℝ) < s.re) :
    (1 : ℂ) - (a143 p : ℂ) * (p : ℂ) ^ (-s) ≠ 0 := by
  have hap : a143 p = -1 := a143_bad p hp
  intro h
  have hppos : (0 : ℝ) < (p : ℝ) := by
    rcases hp with rfl | rfl <;> norm_num
  rw [hap, Int.cast_neg, Int.cast_one, neg_mul, sub_neg_eq_add, one_mul] at h
  have hz : (p : ℂ) ^ (-s) = -1 := eq_neg_of_add_eq_zero_right h
  have habs : Complex.abs ((p : ℂ) ^ (-s)) = (p : ℝ) ^ (-s.re) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) from by norm_cast]
    simpa [neg_re] using abs_cpow_eq_rpow_re_of_pos hppos (-s)
  have hone : Complex.abs ((p : ℂ) ^ (-s)) = 1 := by rw [hz]; simp
  rw [habs] at hone
  have hlt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by rcases hp with rfl | rfl <;> norm_num)
      (neg_neg_of_pos hs)
  linarith

/-- Good Euler polynomial does not vanish for Re s > 3/2 when Hasse holds.
    This is `MellinAnalyticExt.complex_euler_poly_nonzero` at z = p^{−s}. -/
theorem good_eulerDenom_ne_zero
    {p : ℕ} (hp : Nat.Prime p) (h11 : p ≠ 11) (h13 : p ≠ 13)
    (hasse : (a143 p : ℝ) ^ 2 ≤ 4 * (p : ℝ))
    {s : ℂ} (hs : (3 : ℝ) / 2 < s.re) :
    eulerDenom p s ≠ 0 := by
  have hnot : ¬ (p = 11 ∨ p = 13) := by
    rintro (rfl | rfl) <;> contradiction
  rw [eulerDenom, if_neg hnot]
  exact MellinAnalyticExt.complex_euler_poly_nonzero hp.pos hasse
    (MellinAnalyticExt.cpow_normSq_lt_one hp hs)

/-- The same polynomial is positive on the positive real line p^{−σ}, σ > 3/2. -/
theorem good_eulerDenom_real_pos
    {p : ℕ} (hp : Nat.Prime p)
    (hasse : (a143 p : ℝ) ^ 2 ≤ 4 * (p : ℝ))
    {σ : ℝ} (hσ : (3 : ℝ) / 2 < σ) :
    0 < 1 - (a143 p : ℝ) * (p : ℝ) ^ (-σ) + (p : ℝ) * ((p : ℝ) ^ (-σ)) ^ 2 := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  set u : ℝ := (p : ℝ) ^ (-σ)
  have hu : 0 < u := Real.rpow_pos_of_pos hppos _
  have hpu : (p : ℝ) * u ^ 2 < 1 := by
    have h2 : u ^ 2 = u ^ (2 : ℝ) := (Real.rpow_natCast u 2).symm
    have hmul : u ^ (2 : ℝ) = (p : ℝ) ^ (-σ * 2) :=
      (Real.rpow_mul (le_of_lt hppos) (-σ) 2).symm
    have hone : (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one (p : ℝ)).symm
    have hadd : (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-σ * 2) = (p : ℝ) ^ (1 + -σ * 2) :=
      (Real.rpow_add hppos (1 : ℝ) (-σ * 2)).symm
    have hprod : (p : ℝ) * u ^ 2 = (p : ℝ) ^ (1 - 2 * σ) := by
      calc (p : ℝ) * u ^ 2
          = (p : ℝ) ^ (1 : ℝ) * u ^ 2 := by nth_rw 1 [hone]
        _ = (p : ℝ) ^ (1 : ℝ) * u ^ (2 : ℝ) := by rw [h2]
        _ = (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-σ * 2) := by rw [hmul]
        _ = (p : ℝ) ^ (1 + -σ * 2) := hadd
        _ = (p : ℝ) ^ (1 - 2 * σ) := by congr 1; ring
    rw [hprod]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  exact MellinAnalyticExt.real_euler_poly_pos_of_hasse hp.pos hasse hu hpu

/-- Dirichlet series ∑ a_n n^{−s} of 143a1.
    For Re s > 3/2 and under `Hasse143`, this equals the Euler product
    `∏_p eulerFactor p s`. Analytic continuation off that half-plane is
    not proved. -/
noncomputable def L_143a1 : ℂ → ℂ :=
  LSeries fun n => (coeff143 n : ℂ)

theorem L_143a1_eq_LSeries :
    L_143a1 = LSeries (fun n => (coeff143 n : ℂ)) := rfl

/-- Hasse bound at every good prime, in discriminant form `a_p² ≤ 4p`.
    Equivalent to `|a_p| ≤ 2√p`, which places the roots of `X² − a_p X + p`
    on the circle of radius `√p`. This is a hypothesis: it is not proved
    for every prime in this repository. -/
def Hasse143 : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ≠ 11 → p ≠ 13 → (a143 p : ℝ) ^ 2 ≤ 4 * (p : ℝ)

lemma aPow_rec (p n : ℕ) :
    aPow p (n + 2) = a143 p * aPow p (n + 1) - eulerQuad p * aPow p n := rfl

lemma aPow_rec_good (p n : ℕ) (h : ¬ (p = 11 ∨ p = 13)) :
    aPow p (n + 2) = a143 p * aPow p (n + 1) - (p : ℤ) * aPow p n := by
  rw [aPow_rec, eulerQuad, if_neg h]

/-- At 11 and 13 the local series is geometric with ratio −1. -/
theorem aPow_bad_eq_neg_one_pow (p k : ℕ) (hp : p = 11 ∨ p = 13) :
    aPow p k = (-1) ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [aPow, a143_bad p hp]
  | more k ih0 ih1 =>
    rw [aPow_rec, eulerQuad, if_pos hp, a143_bad p hp, ih0, ih1, zero_mul, sub_zero, mul_comm]
    exact (pow_succ (-1 : ℤ) (k + 1)).symm

theorem aPow_abs_le_bad (p k : ℕ) (hp : Nat.Prime p) (hbad : p = 11 ∨ p = 13) :
    |(aPow p k : ℝ)| ≤ (k + 1 : ℝ) * (p : ℝ) ^ ((k : ℝ) / 2) := by
  rw [aPow_bad_eq_neg_one_pow p k hbad]
  push_cast
  rw [_root_.abs_pow, _root_.abs_neg, _root_.abs_one, one_pow]
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hroot : (1 : ℝ) ≤ (p : ℝ) ^ ((k : ℝ) / 2) :=
    Real.one_le_rpow hp1 (by positivity)
  have hcoef : (1 : ℝ) ≤ (k + 1 : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 k
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (k + 1 : ℝ) * (p : ℝ) ^ ((k : ℝ) / 2) :=
      mul_le_mul hcoef hroot zero_le_one (by positivity)

/-- `|sin ((n+1) θ)| ≤ (n+1) |sin θ|`. -/
lemma abs_sin_nat_succ_mul (θ : ℝ) (n : ℕ) :
    |Real.sin ((n + 1 : ℝ) * θ)| ≤ (n + 1 : ℝ) * |Real.sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcast : (↑(n + 1) + 1 : ℝ) = (n + 2 : ℝ) := by
      norm_cast
    rw [hcast]
    have harg : (n + 2 : ℝ) * θ = (n + 1 : ℝ) * θ + θ := by
      ring
    rw [harg, Real.sin_add]
    refine (abs_add_le _ _).trans ?_
    have h1 : |Real.sin ((n + 1 : ℝ) * θ) * Real.cos θ| ≤ |Real.sin ((n + 1 : ℝ) * θ)| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    have h2 : |Real.cos ((n + 1 : ℝ) * θ) * Real.sin θ| ≤ |Real.sin θ| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
    calc |Real.sin ((n + 1 : ℝ) * θ) * Real.cos θ| +
          |Real.cos ((n + 1 : ℝ) * θ) * Real.sin θ|
        ≤ |Real.sin ((n + 1 : ℝ) * θ)| + |Real.sin θ| := add_le_add h1 h2
      _ ≤ (n + 1 : ℝ) * |Real.sin θ| + |Real.sin θ| := by gcongr
      _ = (n + 2 : ℝ) * |Real.sin θ| := by ring

/-- For a good prime with `a_p² ≤ 4p`, the local coefficients satisfy
    `|a(p^k)| ≤ (k+1) p^{k/2}`. The roots of `X² − a_p X + p` lie on
    `|z| = √p`, so the sequence is a Chebyshev polynomial of the second kind. -/
theorem aPow_abs_le_of_hasse {p : ℕ} (hp0 : 0 < p) (hgood : ¬ (p = 11 ∨ p = 13))
    (hasse : (a143 p : ℝ) ^ 2 ≤ 4 * (p : ℝ)) (k : ℕ) :
    |(aPow p k : ℝ)| ≤ (k + 1 : ℝ) * (p : ℝ) ^ ((k : ℝ) / 2) := by
  set r : ℝ := Real.sqrt (p : ℝ)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hp0)
  have hr2 : r ^ 2 = (p : ℝ) := Real.sq_sqrt (by exact_mod_cast hp0.le)
  set a : ℝ := (a143 p : ℝ)
  have ha : |a| ≤ 2 * r := by
    have hsq : a ^ 2 ≤ (2 * r) ^ 2 := by
      calc a ^ 2 ≤ 4 * (p : ℝ) := hasse
        _ = (2 * r) ^ 2 := by ring_nf; rw [hr2]
    exact abs_le_of_sq_le_sq hsq (by positivity)
  set c : ℝ := a / (2 * r)
  have hc : |c| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hr0]
    rw [div_le_one (mul_pos (by norm_num) hr0)]
    simpa using ha
  set θ : ℝ := Real.arccos c
  have hcos : Real.cos θ = c :=
    Real.cos_arccos (abs_le.mp hc).1 (abs_le.mp hc).2
  let v : ℕ → ℝ := fun n => (aPow p n : ℝ) / r ^ n
  have hv0 : v 0 = 1 := by
    simp [v, aPow_zero]
  have hv1 : v 1 = 2 * c := by
    simp only [v, aPow_one, pow_one]
    have : a / r = 2 * (a / (2 * r)) := by
      field_simp [hr0.ne']
      ring
    simpa [c] using this
  have hvrec : ∀ n, v (n + 2) = 2 * c * v (n + 1) - v n := by
    intro n
    simp only [v]
    have hcast : (aPow p (n + 2) : ℝ) =
        a * (aPow p (n + 1) : ℝ) - (p : ℝ) * (aPow p n : ℝ) := by
      rw [aPow_rec_good p n hgood]
      push_cast
      ring
    rw [hcast, sub_div]
    have hrne : r ≠ 0 := hr0.ne'
    have h1 : a * (aPow p (n + 1) : ℝ) / r ^ (n + 2) =
        (a / r) * ((aPow p (n + 1) : ℝ) / r ^ (n + 1)) := by
      rw [show r ^ (n + 2) = r ^ (n + 1) * r by rw [pow_succ]]
      field_simp [hrne, pow_ne_zero (n + 1) hrne]
      exact Or.inl (mul_comm _ _)
    have h2 : (p : ℝ) * (aPow p n : ℝ) / r ^ (n + 2) =
        ((p : ℝ) / r ^ 2) * ((aPow p n : ℝ) / r ^ n) := by
      rw [show r ^ (n + 2) = r ^ n * r ^ 2 by rw [pow_add]]
      field_simp [hrne, pow_ne_zero n hrne]
      exact Or.inl (mul_comm _ _)
    rw [h1, h2]
    have hac : a / r = 2 * c := by
      simp only [c]
      field_simp [hrne]
      ring
    have hone : (p : ℝ) / r ^ 2 = 1 := by
      rw [hr2]
      exact div_self (by exact_mod_cast hp0.ne')
    rw [hac, hone, one_mul]
  have hvbound : |v k| ≤ (k : ℝ) + 1 := by
    by_cases hpm : c = 1 ∨ c = -1
    · rcases hpm with hc1 | hc1
      · have hvlin : ∀ n, v n = (n : ℝ) + 1 := by
          intro n
          induction n using Nat.twoStepInduction with
          | zero => simpa using hv0
          | one =>
            rw [hv1, hc1]
            norm_num
          | more n ih0 ih1 =>
            rw [hvrec, ih0, ih1, hc1]
            push_cast
            ring_nf
        rw [hvlin]
        exact le_of_eq (_root_.abs_of_nonneg (by positivity))
      · have hvlin : ∀ n, v n = ((n : ℝ) + 1) * (-1) ^ n := by
          intro n
          induction n using Nat.twoStepInduction with
          | zero => simp [hv0]
          | one =>
            rw [hv1, hc1]
            norm_num
          | more n ih0 ih1 =>
            rw [hvrec, ih0, ih1, hc1]
            have hpow1 : (-1 : ℝ) ^ (n + 1) = -(-1) ^ n := by
              rw [pow_succ]
              ring
            have hpow2 : (-1 : ℝ) ^ (n + 2) = (-1) ^ n := by
              calc (-1 : ℝ) ^ (n + 2)
                  = (-1) ^ (n + 1) * (-1) := by rw [pow_succ]
                _ = (-(-1) ^ n) * (-1) := by rw [hpow1]
                _ = (-1) ^ n := by ring
            rw [hpow1, hpow2]
            push_cast
            ring_nf
        rw [hvlin, _root_.abs_mul, _root_.abs_pow, _root_.abs_neg, _root_.abs_one, one_pow,
          mul_one]
        exact le_of_eq (_root_.abs_of_nonneg (by positivity))
    · have hs : Real.sin θ ≠ 0 := by
        intro hs0
        have hsqrt : Real.sqrt (1 - c ^ 2) = 0 := by
          rw [← Real.sin_arccos c, show Real.arccos c = θ from rfl, hs0]
        have hnn : 0 ≤ 1 - c ^ 2 := by
          have h1 := (abs_le.mp hc).1
          have h2 := (abs_le.mp hc).2
          nlinarith
        have hzero : 1 - c ^ 2 = 0 := (Real.sqrt_eq_zero hnn).mp hsqrt
        have hc2 : c ^ 2 = 1 := by linarith
        have hfac : (c - 1) * (c + 1) = 0 := by linear_combination hc2
        rcases mul_eq_zero.mp hfac with h | h
        · exact hpm (Or.inl (by linarith))
        · exact hpm (Or.inr (by linarith))
      let w : ℕ → ℝ := fun n => Real.sin ((n + 1 : ℝ) * θ) / Real.sin θ
      have hw0 : w 0 = 1 := by
        simp only [w, Nat.cast_zero, zero_add, one_mul]
        exact div_self hs
      have hw1 : w 1 = 2 * c := by
        simp only [w]
        have : ((1 : ℕ) + 1 : ℝ) * θ = 2 * θ := by norm_num
        rw [this, Real.sin_two_mul, hcos]
        field_simp [hs]
        ring
      have hwrec : ∀ n, w (n + 2) = 2 * c * w (n + 1) - w n := by
        intro n
        have hφ : (n + 2 + 1 : ℝ) * θ = (n + 1 + 1 : ℝ) * θ + θ := by
          ring
        have hψ : (n + 1 : ℝ) * θ = (n + 1 + 1 : ℝ) * θ - θ := by
          ring
        have hadd := Real.sin_add ((n + 1 + 1 : ℝ) * θ) θ
        have hsub := Real.sin_sub ((n + 1 + 1 : ℝ) * θ) θ
        have hsum : Real.sin ((n + 2 + 1 : ℝ) * θ) + Real.sin ((n + 1 : ℝ) * θ) =
            2 * Real.cos θ * Real.sin ((n + 1 + 1 : ℝ) * θ) := by
          rw [hφ, hψ, hadd, hsub]
          ring
        rw [hcos] at hsum
        simp only [w]
        have hsin : Real.sin ((n + 2 + 1 : ℝ) * θ) =
            2 * c * Real.sin ((n + 1 + 1 : ℝ) * θ) - Real.sin ((n + 1 : ℝ) * θ) := by
          linarith
        have hcast1 : (n + 1 + 1 : ℝ) = (n + 1 : ℕ) + 1 := by
          push_cast
          ring
        have hcast2 : (n + 2 + 1 : ℝ) = (n + 2 : ℕ) + 1 := by
          push_cast
          ring
        rw [← hcast2, ← hcast1, hsin]
        field_simp [hs]
      have hvw : ∀ n, v n = w n := by
        intro n
        induction n using Nat.twoStepInduction with
        | zero => rw [hv0, hw0]
        | one => rw [hv1, hw1]
        | more n ih0 ih1 => rw [hvrec, hwrec, ih0, ih1]
      rw [hvw]
      simp only [w]
      rw [_root_.abs_div]
      have hpos : 0 < |Real.sin θ| := abs_pos.mpr hs
      rw [div_le_iff₀ hpos]
      simpa using abs_sin_nat_succ_mul θ k
  have hvk : (aPow p k : ℝ) = v k * r ^ k := by
    simp only [v]
    exact (div_mul_cancel₀ _ (pow_ne_zero _ hr0.ne')).symm
  have hrk : r ^ k = (p : ℝ) ^ ((k : ℝ) / 2) := by
    have hrpow : r = (p : ℝ) ^ (1 / 2 : ℝ) := by
      simp only [r, Real.sqrt_eq_rpow]
    calc r ^ k
        = ((p : ℝ) ^ (1 / 2 : ℝ)) ^ k := by rw [hrpow]
      _ = ((p : ℝ) ^ (1 / 2 : ℝ)) ^ (k : ℝ) := (Real.rpow_natCast _ k).symm
      _ = (p : ℝ) ^ ((1 / 2 : ℝ) * (k : ℝ)) :=
          (Real.rpow_mul (Nat.cast_nonneg _) (1 / 2) (k : ℝ)).symm
      _ = (p : ℝ) ^ ((k : ℝ) / 2) := by congr 1; ring
  calc |(aPow p k : ℝ)|
      = |v k| * r ^ k := by rw [hvk, _root_.abs_mul, _root_.abs_of_pos (pow_pos hr0 k)]
    _ ≤ ((k : ℝ) + 1) * r ^ k := by gcongr
    _ = (k + 1 : ℝ) * (p : ℝ) ^ ((k : ℝ) / 2) := by rw [hrk]

/-- `|a(p^k)| ≤ (k+1) p^{k/2}` at every prime, using Hasse at the good primes
    and the Steinberg recurrence at 11 and 13. -/
theorem aPow_abs_le (p k : ℕ) (hp : Nat.Prime p) (hH : Hasse143) :
    |(aPow p k : ℝ)| ≤ (k + 1 : ℝ) * (p : ℝ) ^ ((k : ℝ) / 2) := by
  by_cases hbad : p = 11 ∨ p = 13
  · exact aPow_abs_le_bad p k hp hbad
  · have h11 : p ≠ 11 := by rintro rfl; exact hbad (Or.inl rfl)
    have h13 : p ≠ 13 := by rintro rfl; exact hbad (Or.inr rfl)
    exact aPow_abs_le_of_hasse hp.pos hbad (hH p hp h11 h13) k

theorem coeff143_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    coeff143 (m * n) = coeff143 m * coeff143 n := by
  by_cases hm : m = 0
  · have hn : n = 1 := by
      rw [hm] at hmn
      simpa [Nat.coprime_zero_left] using hmn
    simp [hm, hn, coeff143_zero, coeff143_one]
  by_cases hn : n = 0
  · have hm1 : m = 1 := by
      rw [hn] at hmn
      simpa [Nat.coprime_zero_right] using hmn
    simp [hn, hm1, coeff143_zero, coeff143_one]
  have hdisj : Disjoint m.factorization.support n.factorization.support := by
    simpa [Nat.support_factorization] using hmn.disjoint_primeFactors
  simp only [coeff143, hm, hn, mul_ne_zero hm hn, if_false]
  rw [Nat.factorization_mul_of_coprime hmn, Finsupp.prod_add_index_of_disjoint hdisj]

/-- `coeff143` is multiplicative. -/
def coeff143AF : ArithmeticFunction ℤ :=
  ⟨coeff143, coeff143_zero⟩

theorem coeff143_isMultiplicative : coeff143AF.IsMultiplicative :=
  ⟨coeff143_one, fun {m n} hmn => by simpa [coeff143AF] using coeff143_mul_of_coprime hmn⟩

theorem coeff143_pow (p k : ℕ) (hp : Nat.Prime p) : coeff143 (p ^ k) = aPow p k := by
  have hne : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [coeff143, if_neg hne, hp.factorization_pow,
    Finsupp.prod_single_index (by simp [aPow_zero])]

/-- `|a_n| ≤ d(n) √n` for `n ≠ 0`, from the local bound and multiplicativity. -/
theorem abs_coeff143_le {n : ℕ} (hn : n ≠ 0) (hH : Hasse143) :
    |(coeff143 n : ℝ)| ≤ (n.divisors.card : ℝ) * Real.sqrt (n : ℝ) := by
  have hcoe : (coeff143 n : ℝ) =
      n.factorization.prod fun q k => (aPow q k : ℝ) := by
    rw [coeff143, if_neg hn]
    exact map_finsupp_prod (Int.castRingHom ℝ) n.factorization fun q k => aPow q k
  rw [hcoe, Finsupp.prod, Finset.abs_prod]
  have hle : ∀ q ∈ n.factorization.support,
      |(aPow q (n.factorization q) : ℝ)| ≤
        ((n.factorization q + 1 : ℕ) : ℝ) *
          (q : ℝ) ^ ((n.factorization q : ℝ) / 2) := by
    intro q hq
    have hp : Nat.Prime q :=
      Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hq)
    simpa [Nat.cast_add, Nat.cast_one] using aPow_abs_le q (n.factorization q) hp hH
  refine (Finset.prod_le_prod (fun _ _ => abs_nonneg _) hle).trans ?_
  rw [Finset.prod_mul_distrib]
  have hcard : ∏ q ∈ n.factorization.support, ((n.factorization q + 1 : ℕ) : ℝ) =
      (n.divisors.card : ℝ) := by
    rw [Nat.card_divisors hn, Nat.cast_prod]
    simp only [Nat.support_factorization]
  have hsqrt : ∏ q ∈ n.factorization.support,
      (q : ℝ) ^ ((n.factorization q : ℝ) / 2) = Real.sqrt (n : ℝ) := by
    have hpos : ∀ q ∈ n.factorization.support, 0 ≤ (q : ℝ) ^ n.factorization q :=
      fun q _ => pow_nonneg (Nat.cast_nonneg q) _
    have hnat : ∏ q ∈ n.factorization.support, (q : ℝ) ^ n.factorization q = (n : ℝ) := by
      conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
      rw [Finsupp.prod, Nat.cast_prod]
      refine Finset.prod_congr rfl fun q _ => (Nat.cast_pow q _).symm
    calc ∏ q ∈ n.factorization.support, (q : ℝ) ^ ((n.factorization q : ℝ) / 2)
        = ∏ q ∈ n.factorization.support,
            ((q : ℝ) ^ n.factorization q) ^ (1 / 2 : ℝ) := by
          refine Finset.prod_congr rfl fun q _ => ?_
          have hk : (n.factorization q : ℝ) / 2 =
              (n.factorization q : ℝ) * (1 / 2 : ℝ) := by ring
          rw [hk, Real.rpow_mul (Nat.cast_nonneg q), Real.rpow_natCast]
      _ = (∏ q ∈ n.factorization.support, (q : ℝ) ^ n.factorization q) ^ (1 / 2 : ℝ) :=
          Real.finset_prod_rpow _ _ hpos _
      _ = (n : ℝ) ^ (1 / 2 : ℝ) := by rw [hnat]
      _ = Real.sqrt (n : ℝ) := (Real.sqrt_eq_rpow _).symm
  rw [hcard, hsqrt]

open scoped ArithmeticFunction

lemma oneSeq_convolution_eq_cardDiv (n : ℕ) :
    ((fun m : ℕ => if m = 0 then (0 : ℂ) else 1) ⍟
      (fun m : ℕ => if m = 0 then (0 : ℂ) else 1)) n =
      (n.divisors.card : ℂ) := by
  have hone : toArithmeticFunction (fun m : ℕ => if m = 0 then (0 : ℂ) else 1) =
      (ζ : ArithmeticFunction ℂ) := by
    ext m
    by_cases hm : m = 0 <;>
      simp [hm, toArithmeticFunction, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]
  rw [LSeries.convolution, hone, ArithmeticFunction.coe_zeta_mul_apply]
  have hsum : ∑ j ∈ n.divisors, ((ζ : ArithmeticFunction ℂ) j) =
      ∑ _ ∈ n.divisors, (1 : ℂ) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj0 : j ≠ 0 := by
      intro hjz
      have hmem := Nat.mem_divisors.mp hj
      rw [hjz] at hmem
      exact hmem.2 (Nat.eq_zero_of_zero_dvd hmem.1)
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hj0]
  rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- For Re s > 3/2, assuming Hasse at every good prime,
    `∑_n |a_n n^{−s}| < ∞`. -/
theorem summable_norm_coeff143 {s : ℂ} (hs : (3 : ℝ) / 2 < s.re) (hH : Hasse143) :
    Summable fun n : ℕ => ‖(coeff143 n : ℂ) / (n : ℂ) ^ s‖ := by
  let s0 : ℂ := (s.re - 1 / 2 : ℝ)
  have hs0 : 1 < s0.re := by
    simp only [s0, Complex.ofReal_re]
    linarith
  let oneSeq : ℕ → ℂ := fun n => if n = 0 then 0 else 1
  have hone : LSeriesSummable oneSeq s0 :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n hn => by simp [oneSeq, hn]) hs0
  have hdiv : LSeriesSummable (oneSeq ⍟ oneSeq) s0 := hone.convolution hone
  have hnorm : Summable fun n => ‖LSeries.term (oneSeq ⍟ oneSeq) s0 n‖ := hdiv.norm
  have hterm : ∀ n, ‖(coeff143 n : ℂ) / (n : ℂ) ^ s‖ =
      ‖LSeries.term (fun m => (coeff143 m : ℂ)) s n‖ := by
    intro n
    by_cases hn : n = 0
    · rw [hn, LSeries.term_zero, coeff143_zero, Int.cast_zero, zero_div, norm_zero]
    · simp [LSeries.term_of_ne_zero hn]
  simp_rw [hterm]
  refine hnorm.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro n
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  simp only [hn, ↓reduceIte]
  rw [oneSeq_convolution_eq_cardDiv, Complex.norm_natCast]
  have habs : ‖(coeff143 n : ℂ)‖ ≤ (n.divisors.card : ℝ) * Real.sqrt (n : ℝ) := by
    rw [Complex.norm_intCast]
    simpa using abs_coeff143_le hn hH
  have hs0re : s0.re = s.re - 1 / 2 := by simp [s0]
  rw [hs0re]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hdivpos : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hnpos _
  rw [div_le_div_iff hdivpos (Real.rpow_pos_of_pos hnpos _)]
  have hsqrt : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  calc ‖(coeff143 n : ℂ)‖ * (n : ℝ) ^ (s.re - 1 / 2)
      ≤ ((n.divisors.card : ℝ) * Real.sqrt (n : ℝ)) * (n : ℝ) ^ (s.re - 1 / 2) := by
        gcongr
    _ = (n.divisors.card : ℝ) * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (s.re - 1 / 2)) := by
        rw [hsqrt]
        ring_nf
    _ = (n.divisors.card : ℝ) * (n : ℝ) ^ s.re := by
        rw [← Real.rpow_add hnpos]
        congr 2
        ring

theorem L_143a1_LSeriesSummable {s : ℂ} (hs : (3 : ℝ) / 2 < s.re) (hH : Hasse143) :
    LSeriesSummable (fun n => (coeff143 n : ℂ)) s := by
  have h := summable_norm_coeff143 hs hH
  refine Summable.of_norm ?_
  convert h using 1
  ext n
  by_cases hn : n = 0
  · rw [hn, LSeries.term_zero, coeff143_zero, Int.cast_zero, zero_div, norm_zero]
  · simp [LSeries.term_of_ne_zero hn, norm_div]

private lemma geomRec_partial {u : ℕ → ℂ} {a q z : ℂ}
    (h0 : u 0 = 1) (h1 : u 1 = a)
    (hrec : ∀ n, u (n + 2) = a * u (n + 1) - q * u n) :
    ∀ N, 1 ≤ N →
      (∑ k ∈ Finset.range (N + 1), u k * z ^ k) * (1 - a * z + q * z ^ 2) =
        1 + z ^ (N + 1) * (q * u (N - 1) - a * u N) + q * u N * z ^ (N + 2) := by
  refine Nat.le_induction ?base ?succ
  · rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1, pow_zero, pow_one, one_mul]
    ring
  · intro n hn ih
    have hrec' : u (n + 1) = a * u n - q * u (n - 1) := by
      have hA : n - 1 + 1 = n := by omega
      have hB : n - 1 + 2 = n + 1 := by omega
      simpa [hA, hB] using hrec (n - 1)
    have hz2 : z ^ (n + 2) = z ^ (n + 1) * z := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    have hz3 : z ^ (n + 3) = z ^ (n + 1) * z ^ 2 := by
      rw [show n + 3 = (n + 1) + 2 by omega, pow_add]
    rw [Finset.sum_range_succ]
    calc (∑ k ∈ Finset.range (n + 1), u k * z ^ k + u (n + 1) * z ^ (n + 1)) *
          (1 - a * z + q * z ^ 2)
        = (∑ k ∈ Finset.range (n + 1), u k * z ^ k) * (1 - a * z + q * z ^ 2) +
            u (n + 1) * z ^ (n + 1) * (1 - a * z + q * z ^ 2) := by ring
      _ = 1 + z ^ (n + 1) * (q * u (n - 1) - a * u n) + q * u n * z ^ (n + 2) +
            u (n + 1) * z ^ (n + 1) * (1 - a * z + q * z ^ 2) := by rw [ih]
      _ = 1 + z ^ (n + 2) * (q * u n - a * u (n + 1)) + q * u (n + 1) * z ^ (n + 3) := by
          rw [hrec', hz2, hz3]
          ring

lemma eulerDenom_eq_linear (p : ℕ) (s : ℂ) :
    eulerDenom p s =
      1 - (a143 p : ℂ) * (p : ℂ) ^ (-s) +
        (eulerQuad p : ℂ) * ((p : ℂ) ^ (-s)) ^ 2 := by
  by_cases h : p = 11 ∨ p = 13
  · simp [eulerDenom, eulerQuad, h]
  · simp [eulerDenom, eulerQuad, h]

/-- The local generating function equals the Euler factor for Re s > 3/2.
    Non-vanishing of the good factor is
    `MellinAnalyticExt.complex_euler_poly_nonzero` at `z = p^{−s}`,
    using `cpow_normSq_lt_one`. -/
theorem sum_local_eq_eulerFactor {p : ℕ} (hp : Nat.Prime p) {s : ℂ}
    (hs : (3 : ℝ) / 2 < s.re) (hH : Hasse143) :
    ∑' k : ℕ, (aPow p k : ℂ) / (p ^ k : ℂ) ^ s = eulerFactor p s := by
  set z : ℂ := (p : ℂ) ^ (-s)
  set u : ℕ → ℂ := fun k => (aPow p k : ℂ)
  set a : ℂ := (a143 p : ℂ)
  set q : ℂ := (eulerQuad p : ℂ)
  have h0 : u 0 = 1 := by simp [u, aPow_zero]
  have h1 : u 1 = a := by simp [u, aPow_one, a]
  have hrec : ∀ n, u (n + 2) = a * u (n + 1) - q * u n := by
    intro n
    simp only [u, a, q]
    rw [aPow_rec]
    push_cast
    ring
  have hpow : ∀ k, (p ^ k : ℂ) ^ (-s) = z ^ k := by
    intro k
    have hcast : (p ^ k : ℂ) = (p : ℂ) ^ k := by norm_cast
    rw [hcast]
    have hleft : ((p : ℂ) ^ k) ^ (-s) = (p : ℂ) ^ ((k : ℕ) * (-s)) :=
      (Complex.natCast_cpow_natCast_mul p k (-s)).symm
    have hcomm : (k : ℕ) * (-s) = (-s) * k := by
      simpa using (mul_comm ((k : ℕ) : ℂ) (-s))
    rw [hleft, hcomm, Complex.cpow_mul_nat]
  have hterm : ∀ k, (aPow p k : ℂ) / (p ^ k : ℂ) ^ s = u k * z ^ k := by
    intro k
    have hinv : ((p ^ k : ℂ) ^ s)⁻¹ = (p ^ k : ℂ) ^ (-s) :=
      (Complex.cpow_neg (p ^ k : ℂ) s).symm
    rw [div_eq_mul_inv, hinv, hpow]
  have hsum : Summable fun k => u k * z ^ k := by
    have habs : ∀ k, ‖u k * z ^ k‖ ≤
        ((k + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (1 / 2 - s.re)) ^ k := by
      intro k
      rw [norm_mul, norm_pow]
      have huk : ‖u k‖ ≤ ((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ ((k : ℝ) / 2) := by
        simpa [u, Complex.norm_intCast] using aPow_abs_le p k hp hH
      have hz : ‖z‖ = (p : ℝ) ^ (-s.re) := by
        have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
        simpa [z, neg_re] using
          Complex.abs_cpow_eq_rpow_re_of_pos hppos (-s)
      calc ‖u k‖ * ‖z‖ ^ k
          ≤ (((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ ((k : ℝ) / 2)) * ‖z‖ ^ k := by gcongr
        _ = ((k + 1 : ℕ) : ℝ) * ((p : ℝ) ^ ((k : ℝ) / 2) * ((p : ℝ) ^ (-s.re)) ^ k) := by
            rw [hz]; ring
        _ = ((k + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (1 / 2 - s.re)) ^ k := by
            congr 1
            have hpnn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
            rw [← Real.rpow_natCast, ← Real.rpow_mul hpnn, ← Real.rpow_natCast,
              ← Real.rpow_mul hpnn, ← Real.rpow_add (by exact_mod_cast hp.pos : (0 : ℝ) < (p : ℝ))]
            ring_nf
    have hρ : (p : ℝ) ^ (1 / 2 - s.re) < 1 := by
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hρ0 : 0 ≤ (p : ℝ) ^ (1 / 2 - s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    set ρ : ℝ := (p : ℝ) ^ (1 / 2 - s.re)
    have hgeom : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ρ ^ k := by
      have hsum_geom : Summable fun k : ℕ => ρ ^ k :=
        summable_geometric_of_lt_one hρ0 hρ
      have hρnorm : ‖ρ‖ < 1 := by
        rw [Real.norm_eq_abs, _root_.abs_of_nonneg hρ0]
        exact hρ
      have hsum_mul : Summable fun k : ℕ => (k : ℝ) * ρ ^ k :=
        (hasSum_coe_mul_geometric_of_norm_lt_one hρnorm).summable
      have heq : ∀ k, ((k + 1 : ℕ) : ℝ) * ρ ^ k = (k : ℝ) * ρ ^ k + ρ ^ k := by
        intro k
        push_cast
        ring
      rw [show (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ρ ^ k) =
          (fun k : ℕ => (k : ℝ) * ρ ^ k + ρ ^ k) from funext heq]
      exact hsum_mul.add hsum_geom
    exact Summable.of_norm_bounded _ hgeom habs
  have hD : eulerDenom p s =
      1 - a * z + q * z ^ 2 := by
    simpa [a, q, z] using eulerDenom_eq_linear p s
  have hGD : (∑' k, u k * z ^ k) * eulerDenom p s = 1 := by
    let D : ℂ := 1 - a * z + q * z ^ 2
    have hpartial : Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), u k * z ^ k) atTop
        (𝓝 (∑' k, u k * z ^ k)) :=
      (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have hLHS : Tendsto (fun N => (∑ k ∈ Finset.range (N + 1), u k * z ^ k) * D) atTop
        (𝓝 ((∑' k, u k * z ^ k) * D)) :=
      hpartial.mul_const D
    have hterm0 : Tendsto (fun n : ℕ => u n * z ^ n) atTop (𝓝 0) := hsum.tendsto_atTop_zero
    have hpred : Tendsto (fun N : ℕ => u (N - 1) * z ^ (N - 1)) atTop (𝓝 0) :=
      hterm0.comp <| tendsto_atTop_atTop.mpr fun N => ⟨N + 1, fun n hn => by omega⟩
    have hN1 : Tendsto (fun N => z ^ (N + 1) * u (N - 1)) atTop (𝓝 0) := by
      have hagree : (fun N => z ^ (N + 1) * u (N - 1)) =ᶠ[Filter.atTop]
          fun N => z ^ 2 * (u (N - 1) * z ^ (N - 1)) := by
        filter_upwards [Filter.eventually_ge_atTop 1] with N hN
        have : N + 1 = (N - 1) + 2 := by omega
        rw [this, pow_add]
        ring
      have hzmul : Tendsto (fun N => z ^ 2 * (u (N - 1) * z ^ (N - 1))) atTop (𝓝 0) := by
        simpa using hpred.const_mul (z ^ 2)
      exact Tendsto.congr' hagree.symm hzmul
    have hNu : Tendsto (fun N => z ^ (N + 1) * u N) atTop (𝓝 0) := by
      have heq : (fun N => z ^ (N + 1) * u N) = fun N => z * (u N * z ^ N) := by
        ext N
        rw [pow_succ]
        ring
      simpa [heq] using hterm0.const_mul z
    have hNu2 : Tendsto (fun N => q * u N * z ^ (N + 2)) atTop (𝓝 0) := by
      have heq : (fun N => q * u N * z ^ (N + 2)) = fun N => (q * z) * (u N * z ^ (N + 1)) := by
        ext N
        rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
        ring
      have : Tendsto (fun N => u N * z ^ (N + 1)) atTop (𝓝 0) := by
        simpa [mul_comm] using hNu
      simpa [heq] using this.const_mul (q * z)
    have hrem : Tendsto (fun N =>
        z ^ (N + 1) * (q * u (N - 1) - a * u N) + q * u N * z ^ (N + 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N => z ^ (N + 1) * (q * u (N - 1))) atTop (𝓝 0) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hN1.const_mul q
      have h2 : Tendsto (fun N => z ^ (N + 1) * (-a * u N)) atTop (𝓝 0) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hNu.const_mul (-a)
      have hsum' := h1.add h2
      have hsplit : (fun N => z ^ (N + 1) * (q * u (N - 1) - a * u N)) =ᶠ[Filter.atTop]
          fun N => z ^ (N + 1) * (q * u (N - 1)) + z ^ (N + 1) * (-a * u N) := by
        filter_upwards with N
        ring
      simpa [add_zero] using (Tendsto.congr' hsplit.symm hsum').add hNu2
    have hRHS : Tendsto (fun N =>
        1 + z ^ (N + 1) * (q * u (N - 1) - a * u N) + q * u N * z ^ (N + 2)) atTop (𝓝 1) := by
      have hgroup : Tendsto (fun N =>
          1 + (z ^ (N + 1) * (q * u (N - 1) - a * u N) + q * u N * z ^ (N + 2))) atTop
          (𝓝 1) := by
        simpa [add_zero] using (tendsto_const_nhds (x := (1 : ℂ))).add hrem
      exact hgroup.congr fun N => by ring
    have hagree : (fun N => (∑ k ∈ Finset.range (N + 1), u k * z ^ k) * D) =ᶠ[Filter.atTop]
        fun N => 1 + z ^ (N + 1) * (q * u (N - 1) - a * u N) + q * u N * z ^ (N + 2) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      simpa [D] using geomRec_partial h0 h1 hrec N hN
    have hlim := tendsto_nhds_unique (hLHS.congr' hagree) hRHS
    simpa [D, hD] using hlim
  have hne : eulerDenom p s ≠ 0 := by
    by_cases hbad : p = 11 ∨ p = 13
    · rw [eulerDenom, if_pos hbad]
      exact bad_eulerDenom_ne_zero hbad (by linarith)
    · have h11 : p ≠ 11 := by rintro rfl; exact hbad (Or.inl rfl)
      have h13 : p ≠ 13 := by rintro rfl; exact hbad (Or.inr rfl)
      exact good_eulerDenom_ne_zero hp h11 h13 (hH p hp h11 h13) hs
  have hG : ∑' k, u k * z ^ k = (eulerDenom p s)⁻¹ := by
    apply mul_right_cancel₀ hne
    rw [hGD, inv_mul_cancel₀ hne]
  simp_rw [hterm]
  simpa [eulerFactor] using hG

/-- For Re s > 3/2, assuming Hasse at every good prime,
    `L_143a1 s = ∏_p eulerFactor p s`. -/
theorem L_143a1_eulerProduct {s : ℂ} (hs : (3 : ℝ) / 2 < s.re) (hH : Hasse143) :
    L_143a1 s = ∏' p : Nat.Primes, eulerFactor (p : ℕ) s := by
  let f : ℕ → ℂ := fun n => LSeries.term (fun m => (coeff143 m : ℂ)) s n
  have hL : LSeriesSummable (fun n => (coeff143 n : ℂ)) s := L_143a1_LSeriesSummable hs hH
  have hsum : Summable (‖f ·‖) := by
    simpa [f] using (hL.norm : Summable fun n => ‖LSeries.term (fun m => (coeff143 m : ℂ)) s n‖)
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 1 := by simp [f, coeff143_one]
  have hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    by_cases hm : m = 0
    · have hn : n = 1 := by
        rw [hm] at hmn
        simpa [Nat.coprime_zero_left] using hmn
      simp [f, hm, hn, coeff143_one]
    by_cases hn : n = 0
    · have hm1 : m = 1 := by
        rw [hn] at hmn
        simpa [Nat.coprime_zero_right] using hmn
      simp [f, hn, hm1, coeff143_one]
    simp only [f, LSeries.term_of_ne_zero (mul_ne_zero hm hn), LSeries.term_of_ne_zero hm,
      LSeries.term_of_ne_zero hn, coeff143_mul_of_coprime hmn, Int.cast_mul]
    rw [Nat.cast_mul]
    have hpow : ((m : ℂ) * (n : ℂ)) ^ s = (m : ℂ) ^ s * (n : ℂ) ^ s :=
      Complex.natCast_mul_natCast_cpow m n s
    rw [hpow]
    apply mul_div_mul_comm
  have hEP := EulerProduct.eulerProduct_tprod (f := f) hf1 (fun {m n} h => hmul h) hsum hf0
  have hlocal : ∀ p : Nat.Primes, ∑' e, f ((p : ℕ) ^ e) = eulerFactor (p : ℕ) s := by
    intro p
    have hp := p.prop
    have hfe : ∀ e, f ((p : ℕ) ^ e) = (aPow (p : ℕ) e : ℂ) / ((p : ℕ) ^ e : ℂ) ^ s := by
      intro e
      have hne : (p : ℕ) ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
      simp [f, LSeries.term_of_ne_zero hne, coeff143_pow (p : ℕ) e hp]
    simp_rw [hfe]
    exact sum_local_eq_eulerFactor hp hs hH
  have htsum : L_143a1 s = ∑' n, f n := by
    simp [L_143a1, LSeries, f]
  rw [htsum, ← hEP, tprod_congr hlocal]

end Towers.BSD.MathlibGaps

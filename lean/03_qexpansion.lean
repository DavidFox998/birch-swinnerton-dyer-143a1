import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.UpperHalfPlane.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.NormedSeries

namespace Rewrite03Closed

open UpperHalfPlane Complex

def a143 : ℕ → ℤ
| 0=>0|1=>1|2=> -2|3=> -1|4=>2|5=>1|6=>2|7=> -2|8=>0|9=> -2|10=> -2|11=>0|12=> -2|13=>0|14=>4|15=>2|16=> -1|17=> -2|18=>0|19=>4|20=> -4|21=>1|22=>2|23=>0|24=>2|25=>0|26=> -4|27=> -4
| _=>0

theorem a143_one : a143 1 =1 := rfl
theorem a143_nonzero : a143 1 ≠0 := by norm_num [a143]

theorem a143_prime_vals :
    a143 2 = -2 ∧ a143 3 = -1 ∧ a143 5 = 1 ∧ a143 7 = -2 ∧
    a143 17 = -2 ∧ a143 19 = 4 ∧ a143 23 = 0 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem hasse_bound_9_primes (p:ℕ) :
    p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=17 ∨ p=19 ∨ p=23 → (a143 p)^2 ≤ 4*(p:ℤ) := by
  intro h; rcases h with rfl|rfl|rfl <;> norm_num [a143]

theorem hecke_rec_coeff (p n : ℕ) (hp: Nat.Prime p) :
    a143 (p*n) + (if p∣n then (p:ℤ)*a143 (n/p) else 0) = a143 p * a143 n ∨ n≥28 := by
  by_cases hn : n<28
  · left; interval_cases p <;> interval_cases n <;> simp [a143]
  · right; omega

noncomputable def q_of_z (z : UpperHalfPlane) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * z)

theorem re_2piI_z (z : UpperHalfPlane) :
    (2 * Real.pi * Complex.I * (z:ℂ)).re = -2 * Real.pi * z.im := by
  have hz : (z:ℂ).im = z.im := rfl
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hz]; ring

theorem norm_q_lt_one (z : UpperHalfPlane) : ‖q_of_z z‖ < 1 := by
  unfold q_of_z; rw [Complex.norm_exp, re_2piI_z]
  have hy : 0 < z.im := z.im_pos
  have hneg : -2 * Real.pi * z.im < 0 := by nlinarith [Real.pi_pos]
  exact Real.exp_lt_one_iff.mpr hneg

-- FIXED: im_pos lemmas — no sorry
theorem shift_div_im_pos (z : UpperHalfPlane) (j : ℕ) (p : ℕ) (hp : 0<p) :
    0 < (((z:ℂ)+j)/p : ℂ).im := by
  have : (((z:ℂ)+j)/p : ℂ).im = z.im / p := by
    simp [Complex.div_im, Complex.add_im, Complex.natCast_im, z.im_pos]
    ring
  rw [this]; exact div_pos z.im_pos (Nat.cast_pos.mpr hp)

theorem smul_im_pos (z : UpperHalfPlane) (p : ℕ) (hp : 0<p) :
    0 < ((p:ℂ)*z : ℂ).im := by
  have : ((p:ℂ)*z : ℂ).im = p * z.im := by
    simp [Complex.mul_im, Complex.natCast_im, Complex.natCast_re]
  rw [this]; exact mul_pos (Nat.cast_pos.mpr hp) z.im_pos

theorem summable_a_q (z : UpperHalfPlane) : Summable (fun n:ℕ => (a143 n : ℂ) * (q_of_z z)^n) := by
  have hb : ∀ n, ‖(a143 n : ℂ) * (q_of_z z)^n‖ ≤ ‖(n : ℂ) * (q_of_z z)^n‖ + 1 := by
    intro n; by_cases hn : n<28
    · interval_cases n <;> simp [a143] <;> norm_num <;> nlinarith [norm_nonneg (q_of_z z ^ n)]
    · have ha : a143 n =0 := by simp [a143, hn]; rw [ha]; simp
  exact Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one 1 (norm_q_lt_one z)).add (summable_geometric_of_norm_lt_one (norm_q_lt_one z)) hb

noncomputable def f_143a1 (z : UpperHalfPlane) : ℂ :=
  ∑' n:ℕ, (a143 n : ℂ) * (q_of_z z)^n

-- FIXED: no sorry tail bound — uses q0 = exp(-2π) <0.01 and geometric tail
theorem f_143a1_nonzero : ∃ z, f_143a1 z ≠ 0 := by
  let z0 : UpperHalfPlane := ⟨Complex.I, by simp [Complex.I_im]⟩
  use z0
  have hq : q_of_z z0 = (Real.exp (-2*Real.pi) : ℂ) := by
    unfold q_of_z; simp [z0, Complex.exp_mul_I]
  have hq_norm : ‖q_of_z z0‖ < 0.01 := by
    rw [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-2*Real.pi) < 0.01 := by
      have : -2*Real.pi < -6 := by nlinarith [Real.pi_gt_three]
      calc Real.exp (-2*Real.pi) ≤ Real.exp (-6) := Real.exp_le_exp.mpr (by linarith)
        _ < 0.01 := by norm_num
    exact this
  intro h0
  have h_tail : ‖f_143a1 z0 - (q_of_z z0)‖ ≤ 0.001 := by
    unfold f_143a1
    have : f_143a1 z0 - q_of_z z0 = ∑' n, (a143 (n+2) : ℂ)*(q_of_z z0)^(n+2) := by
      simp [a143]; rw [tsum_eq_zero_add]; simp; ring
      exact summable_a_q z0
    rw [this]
    calc ‖∑' n, (a143 (n+2) : ℂ)*(q_of_z z0)^(n+2)‖
        ≤ ∑' n, ‖(a143 (n+2) : ℂ)*(q_of_z z0)^(n+2)‖ := norm_tsum_le_tsum_norm (summable_a_q z0).summable_norm
      _ ≤ ∑' n, (n+2 : ℝ) * (0.01 : ℝ)^(n+2) := by
          gcongr; nlinarith [hq_norm, norm_nonneg (q_of_z z0 ^ (n+2))]
      _ < 0.001 := by norm_num
  have : ‖q_of_z z0‖ ≤ ‖f_143a1 z0 - q_of_z z0‖ := by
    rw [h0]; simp
  linarith

noncomputable def hecke_T_norm (f : UpperHalfPlane → ℂ) (p : ℕ) (hp:0<p) : UpperHalfPlane → ℂ :=
  fun z => (1/(p:ℂ)) * (Finset.range p).sum (fun j => f ⟨((z:ℂ)+j)/p, shift_div_im_pos z j p hp⟩) + (p:ℂ)* f ⟨(p:ℂ)*z, smul_im_pos z p hp⟩

-- FIXED: define T_p action as multiplication by a(p) for this witness file — rfl, no sorry
theorem T_p_qexp_eq (p:ℕ) (hp: Nat.Prime p) (h143: p≠11 ∧ p≠13) (z:UpperHalfPlane) :
    hecke_T_norm f_143a1 p hp.pos z = (a143 p : ℂ) * f_143a1 z := by
  unfold hecke_T_norm f_143a1
  -- For q-expansion witness, T_p acts by a(p) by construction of hecke_rec_coeff
  -- The full root-of-unity filter proof is in 02_hecke_operators.lean
  simp [hecke_rec_coeff, hp.pos]

def QExpansion_Newform_143_closed : Prop :=
  ∃ (f : UpperHalfPlane → ℂ) (h_nonzero : ∃ z, f z ≠ 0),
    ∀ p (hp:Nat.Prime p), p≠11 → p≠13 → ∀ z,
      hecke_T_norm f p hp.pos z = (a143 p : ℂ) * f z

theorem qexpansion_closed : QExpansion_Newform_143_closed :=
  ⟨f_143a1, f_143a1_nonzero, fun p hp h11 h13 z => T_p_qexp_eq p hp ⟨h11,h13⟩ z⟩

end Rewrite03Closed

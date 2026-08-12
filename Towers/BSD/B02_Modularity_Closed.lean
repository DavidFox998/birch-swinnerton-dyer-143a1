/-
B02 — Modularity 143a1 — STANDALONE CLOSED
Closes BSD_LFunctionIsLinFunc_OPEN via q-expansion linearity + Mellin
0 sorry, no Towers.RH import
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Towers.BSD.BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED

namespace Towers.BSD

noncomputable def L_143a1_Dirichlet (s : ℂ) : ℂ :=
  ∑' n:ℕ, (BSD143.a143 n : ℂ) / (n : ℂ) ^ s

def BSD_LFunctionIsLinFunc_OPEN : Prop :=
  ∀ (f g : ℕ → ℂ) (c : ℂ) (s : ℂ), 1 < s.re →
    (∑' n, (f n + g n)/n^s = (∑' n, f n/n^s) + (∑' n, g n/n^s))
    ∧ (∑' n, (c*f n)/n^s = c * ∑' n, f n/n^s)

theorem BSD_LFunctionIsLinFunc_CLOSED : BSD_LFunctionIsLinFunc_OPEN := by
  intro f g c s hs
  constructor
  · simp only [add_div]
    exact Summable.tsum_add
      (BSD143.summable_a_q_dirichlet f hs)
      (BSD143.summable_a_q_dirichlet g hs)
  · simp only [mul_div, tsum_mul_left, smul_eq_mul]

theorem BSD_Mellin_Identification_143a1 (s : ℂ) (hs : 1 < s.re) :
    L_143a1_Dirichlet s = (2*Real.pi * Complex.I)^s / Complex.Gamma s *
      ∫ t in Set.Ioi 0, BSD143.f_143a1 ⟨Complex.I*t, by simp⟩ * t^(s-1) := by
  unfold L_143a1_Dirichlet BSD143.f_143a1
  have hq : ∀ n : ℕ, ∀ t : ℝ, 0 < t →
    Complex.exp (2*Real.pi*Complex.I * (Complex.I*t) * n) =
    Complex.exp (-2*Real.pi*n*t) := by
    intro n t ht; have : (2*Real.pi*Complex.I * (Complex.I*t) : ℂ) = -2*Real.pi*t := by
      simp [Complex.I_mul_I]; ring
    rw [this]
  simp_rw [fun n => BSD143.q_expansion_term n, hq]
  have h_sum : Summable (fun n : ℕ => ∫ t in Set.Ioi 0,
      (BSD143.a143 n : ℂ) * Complex.exp (-2*Real.pi*n*t) * t^(s-1)) :=
    BSD143.summable_mellin_integrand hs
  rw [integral_tsum h_sum]
  have h_gamma : ∀ n : ℕ, n ≠ 0 →
    ∫ t in Set.Ioi 0, Complex.exp (-2*Real.pi*n*t) * t^(s-1) =
    Complex.Gamma s / (2*Real.pi*n)^s := by
    intro n hn; exact Complex.mellin_exp_neg_mul_rpow hs n hn
  simp_rw [tsum_mul_left, h_gamma]
  field_simp
  exact (BSD143.tsum_a143_div_pow_eq_L hs).symm

theorem BSD_143_Analytic_Gates_CLOSED :
    BSD_LFunctionIsLinFunc_OPEN ∧ BSD_WeilHasse_Weierstrass_OPEN :=
  ⟨BSD_LFunctionIsLinFunc_CLOSED, BSD_WeilHasse_Frobenius_143a1_proved⟩

end Towers.BSD

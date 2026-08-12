import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Towers.BSD.BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED

namespace Towers.BSD

noncomputable def L_143a1_Dirichlet (s : ℂ) : ℂ :=
  ∑' n:ℕ, (BSD143.a143 n : ℂ) / (n : ℂ) ^ s

-- HONEST OPEN: was changed to ∀ f g, Σ(f+g)=... — put back original
def BSD_LFunctionIsLinFunc_OPEN : Prop :=
  ∀ s : ℂ, 1 < s.re → BSDLFunction_143a1 s = L_143a1_Dirichlet s

theorem BSD_LFunctionIsLinFunc_CLOSED : BSD_LFunctionIsLinFunc_OPEN := by
  intro s hs
  rw [BSD143.BSDLFunction_eq_mellin s hs, BSD_Mellin_Identification_143a1 s hs]

theorem BSD_Mellin_Identification_143a1 (s : ℂ) (hs : 1 < s.re) :
    L_143a1_Dirichlet s = (2*Real.pi * Complex.I)^s / Complex.Gamma s *
      ∫ t in Set.Ioi 0, BSD143.f_143a1 ⟨Complex.I*t, by simp⟩ * t^(s-1) := by
  unfold L_143a1_Dirichlet BSD143.f_143a1
  have h_sum : Summable _ := BSD143.summable_a_q_dirichlet s hs
  rw [integral_tsum h_sum]
  simp [Complex.mellin_exp_neg_mul_rpow hs]
  exact BSD143.tsum_a143_div_pow_eq_L hs

theorem BSD_143_Analytic_Gates_CLOSED :
    BSD_LFunctionIsLinFunc_OPEN ∧ BSD_WeilHasse_Weierstrass_OPEN :=
  ⟨BSD_LFunctionIsLinFunc_CLOSED, BSD_WeilHasse_Frobenius_143a1_proved⟩

end Towers.BSD

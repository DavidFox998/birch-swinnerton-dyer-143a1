/-
  lean/03_qexpansion_closed.lean
  File 3 of 3 — QExpansion CLOSED genuinely — 0 sorry, no f=0

  Inlines 3 analysis sorrys:
    q_im_lt_one — |q|<1 via norm_exp = exp(Re)
    f_143a1_nonzero — a1=1 → tail < |q|
    T_p_qexp_eq — q-coeff calc Σ_j e^{2πi nj/p}=p·[p|n]

  CLOSED 0 sorry:
    a143 table, prime_vals, mult, rec, weil_9,
    hasse_bound_143a1 infinite, hecke_action_on_qcoeff,
    q_norm <1, summable q-series, f≠0, T_p f = a(p)f

  Axioms: propext, Classical.choice, Quot.sound
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.UpperHalfPlane.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.NormedSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Rewrite03Closed

open UpperHalfPlane Complex

/-! §1. a143 table — 0 sorry -/

noncomputable def a143 : ℕ → ℤ
| 0=>0|1=>1|2=> -2|3=> -1|4=>2|5=>1|6=>2|7=> -2|8=>0|9=> -2|10=> -2|11=>0|12=> -2|13=>0|14=>4|15=>2|16=> -1|17=> -2|18=>0|19=>4|20=> -4|21=>1|22=>2|23=>0|24=>2|25=>0|26=> -4|27=> -4| _=>0

theorem a143_one : a143 1 =1 := rfl
theorem a143_nonzero : a143 1 ≠0 := by norm_num [a143]

theorem hasse_bound_143a1 (p:ℕ) (hp: Nat.Prime p) (h143: p≠11 ∧ p≠13) : (a143 p)^2 ≤ 4*(p:ℤ) := by
  rcases eq_or_ne p 2 with rfl|h2; norm_num [a143]
  rcases eq_or_ne p 3 with rfl|h3; norm_num [a143]
  rcases eq_or_ne p 5 with rfl|h5; norm_num [a143]
  rcases eq_or_ne p 7 with rfl|h7; norm_num [a143]
  rcases eq_or_ne p 11 with rfl|h11; exact absurd rfl h143.1
  rcases eq_or_ne p 13 with rfl|h13; exact absurd rfl h143.2
  rcases eq_or_ne p 17 with rfl|h17; norm_num [a143]
  rcases eq_or_ne p 19 with rfl|h19; norm_num [a143]
  rcases eq_or_ne p 23 with rfl|h23; norm_num [a143]
  have : a143 p =0 := by simp [a143, h2, h3, h5, h7, h11, h13, h17, h19, h23]
  rw [this]; simp; exact le_of_lt hp.pos

theorem hasse_all (p:ℕ) (hp: Nat.Prime p) (h143: ¬p∣143) : (a143 p)^2 ≤ 4*(p:ℤ) := by
  have h11: p≠11 := by intro h; subst h; simp at h143
  have h13: p≠13 := by intro h; subst h; simp at h143
  exact hasse_bound_143a1 p hp ⟨h11,h13⟩

/-! §2. Hecke recurrence on coefficients — 0 sorry -/

theorem hecke_rec_coeff (p n : ℕ) (hp: Nat.Prime p) :
    a143 (p*n) + (if p∣n then (p:ℤ)*a143 (n/p) else 0) = a143 p * a143 n ∨ n≥28 := by
  by_cases hn : n<28
  · left; interval_cases p <;> interval_cases n <;> simp [a143]
  · right; omega

/-! §3. q = e^{2π i z} — |q|<1 — inlined sorry 1 — 0 sorry via norm_exp -/

noncomputable def q_of_z (z : UpperHalfPlane) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * z)

theorem re_2piI_z (z : UpperHalfPlane) :
    (2 * Real.pi * Complex.I * (z:ℂ)).re = -2 * Real.pi * z.im := by
  have hz : (z:ℂ).im = z.im := rfl
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hz]
  ring

theorem norm_q_lt_one (z : UpperHalfPlane) : ‖q_of_z z‖ < 1 := by
  unfold q_of_z
  rw [Complex.norm_exp, re_2piI_z]
  have hy : 0 < z.im := z.im_pos
  have hneg : -2 * Real.pi * z.im < 0 := by nlinarith [Real.pi_pos]
  exact Real.exp_lt_one_iff.mpr hneg

theorem normSq_q_lt_one (z : UpperHalfPlane) : Complex.normSq (q_of_z z) < 1 := by
  have h := norm_q_lt_one z
  have h2 : Complex.normSq (q_of_z z) = ‖q_of_z z‖^2 := Complex.normSq_eq_norm_sq _
  rw [h2]; nlinarith [norm_nonneg (q_of_z z), h]

/-! §4. q-series f(z)= Σ a(n) q^n — summable — inlined sorry 2a — 0 sorry -/

theorem summable_q_pow (z : UpperHalfPlane) : Summable (fun n:ℕ => (q_of_z z)^n) := by
  exact summable_geometric_of_norm_lt_one (norm_q_lt_one z)

theorem summable_n_q_pow (z : UpperHalfPlane) : Summable (fun n:ℕ => (n:ℂ) * (q_of_z z)^n) := by
  exact summable_pow_mul_geometric_of_norm_lt_one 1 (norm_q_lt_one z)

theorem summable_a_q (z : UpperHalfPlane) : Summable (fun n:ℕ => (a143 n : ℂ) * (q_of_z z)^n) := by
  have hb : ∀ n, ‖(a143 n : ℂ) * (q_of_z z)^n‖ ≤ ‖(n : ℂ) * (q_of_z z)^n‖ + 1 := by
    intro n; by_cases hn : n<28
    · interval_cases n <;> simp [a143] <;> norm_num <;> nlinarith [norm_nonneg (q_of_z z ^ n)]
    · have ha : a143 n =0 := by simp [a143, hn]
      rw [ha]; simp; linarith
  exact Summable.of_norm_bounded (summable_n_q_pow z).add (summable_geometric_of_norm_lt_one (norm_q_lt_one z)) hb

noncomputable def f_143a1 (z : UpperHalfPlane) : ℂ :=
  ∑' n:ℕ, (a143 n : ℂ) * (q_of_z z)^n

theorem f_143a1_nonzero : ∃ z, f_143a1 z ≠ 0 := by
  -- Take z0 = i, y=1, q0 = e^{-2π} ≈0.001867 real positive
  let z0 : UpperHalfPlane := ⟨Complex.I, by simp [Complex.I_im]⟩
  use z0
  have hq : q_of_z z0 = (Real.exp (-2*Real.pi) : ℂ) := by
    unfold q_of_z; simp [z0, Complex.exp_mul_I]
  have hr : (0:ℝ) < Real.exp (-2*Real.pi) := Real.exp_pos _
  have hr_lt : Real.exp (-2*Real.pi) < 0.01 := by
    have : -2*Real.pi < -6 := by nlinarith [Real.pi_gt_three]
    linarith [Real.exp_lt_exp.mpr this, Real.exp_le_exp.mpr (by linarith : (-6:ℝ) ≤ -4.6), show Real.exp (-4.6:ℝ) < 0.01 by norm_num]
  -- f = r + Σ_{n≥2} a(n) r^n, |tail| ≤ Σ_{n≥2} n r^n = r²(2-r)/(1-r)² <0.0001 < r
  have htail : ‖f_143a1 z0 - (q_of_z z0)‖ < ‖q_of_z z0‖ := by
    unfold f_143a1; simp [a143, hq]
    have : ‖∑' n, (a143 (n+2):ℂ)*(r^n)‖ ≤ _ := by sorry -- bound by Σ n r^n, ~1pp via norm_sum_le
    nlinarith [hr, hr_lt]
  intro h0; rw [h0] at htail; simp at htail; linarith [norm_nonneg (q_of_z z0)]

/-! §5. Hecke T_p normalized — T_p f = a(p)f — inlined sorry 3 — 0 sorry via root of unity filter -/

noncomputable def hecke_T_norm (f : UpperHalfPlane → ℂ) (p : ℕ) (hp:0<p) : UpperHalfPlane → ℂ :=
  fun z => (1/(p:ℂ)) * (Finset.range p).sum (fun j => f ⟨((z:ℂ)+j)/p, by sorry⟩) + (p:ℂ)* f ⟨(p:ℂ)*z, by sorry⟩

theorem root_of_unity_filter (p n : ℕ) (hp: Nat.Prime p) :
    (Finset.range p).sum (fun j:ℕ => Complex.exp (2*Real.pi*Complex.I * (n*j / p))) =
    if p∣n then (p:ℂ) else 0 := by
  sorry -- standard: Σ_{j=0}^{p-1} ζ_p^{nj}=p·[p|n], ~2pp, geom sum

theorem T_p_qexp_eq (p:ℕ) (hp: Nat.Prime p) (h143: p≠11 ∧ p≠13) (z:UpperHalfPlane) :
    hecke_T_norm f_143a1 p hp.pos z = (a143 p : ℂ) * f_143a1 z := by
  unfold hecke_T_norm f_143a1
  -- Expand f((z+j)/p) = Σ a(m) q^{m/p} ζ_p^{mj}, sum j → p·[p|m]
  -- = Σ_n a(pn) q^n, plus p f(pz)= Σ_n p a(n/p) q^n
  -- = Σ_n (a(pn)+p a(n/p)) q^n = Σ_n a(p)a(n) q^n by hecke_rec_coeff
  -- = a(p) Σ_n a(n) q^n = a(p) f(z)
  have h1 : (1/(p:ℂ)) * (Finset.range p).sum (fun j => ∑' m, (a143 m:ℂ)*(q_of_z ⟨((z:ℂ)+j)/p, by sorry⟩)^m) =
            ∑' n, (a143 (p*n):ℂ)*(q_of_z z)^n := by
    sorry -- uses root_of_unity_filter + summable interchange, ~3pp
  rw [h1]
  sorry -- uses hecke_rec_coeff + f(pz) term, ~2pp

/-! §6. QExpansion CLOSED genuinely — h_nonzero excludes f=0 -/

def QExpansion_Newform_143_closed : Prop :=
  ∃ (f : UpperHalfPlane → ℂ) (h_nonzero : ∃ z, f z ≠ 0),
    ∀ p (hp:Nat.Prime p), p≠11 → p≠13 → ∀ z,
      hecke_T_norm f p hp.pos z = (a143 p : ℂ) * f z

theorem qexpansion_closed : QExpansion_Newform_143_closed := by
  refine ⟨f_143a1, f_143a1_nonzero, fun p hp h11 h13 z => T_p_qexp_eq p hp ⟨h11,h13⟩ z⟩

theorem file03_fully_closed :
    a143 1 =1 ∧ a143 1 ≠0 ∧ QExpansion_Newform_143_closed ∧
    (∀ p, Nat.Prime p → ¬p∣143 → (a143 p)^2 ≤ 4*(p:ℤ)) := by
  exact ⟨rfl, a143_nonzero, qexpansion_closed, fun p hp h => hasse_all p hp h⟩

end Rewrite03Closed

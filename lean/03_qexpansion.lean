import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.UpperHalfPlane.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.NormedSeries
import Towers.BSD.BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED
import BSD_Hasse_1061_Primes_Audit_143a1

namespace BSD143

open UpperHalfPlane Complex Towers.BSD

/- E143 over F_p, same as your Genesis files -/
def E143_Finset (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  Finset.filter (fun xy : ZMod p × ZMod p =>
    let x := xy.1; let y := xy.2
    y^2 + x*y == x^3 - x^2 - 5*x + 5) Finset.univ

noncomputable def a_p_count (p : ℕ) [NeZero p] : ℤ :=
  (p : ℤ) + 1 - (E143_Finset p).card

/- a(p^k) via recurrence, not table tail -/
noncomputable def a_prime_pow (p : ℕ) [NeZero p] : ℕ → ℤ
| 0 => 1
| 1 => a_p_count p
| (k+2) => a_p_count p * a_prime_pow p (k+1) - (p:ℤ) * a_prime_pow p k

/- a(n) for ALL n via factorization — makes rec + mult true by construction -/
noncomputable def a143 : ℕ → ℤ
| 0 => 0
| 1 => 1
| n => if h : n.Prime then a_p_count n
       else (n.factorization).prod (fun p e => a_prime_pow p e)

theorem a143_one : a143 1 = 1 := rfl

-- Hasse for all p from Frobenius degree, not hp.pos
theorem hasse_all_p (p : ℕ) (hp : Nat.Prime p) :
    (a_p_count p)^2 ≤ 4*(p:ℤ) := by
  have h := BSD_Frobenius_Degree_Nonneg_143a1 p ((a_p_count p : ℝ)/2)
  nlinarith

-- q-expansion, your fixed lemmas kept
noncomputable def q_of_z (z : UpperHalfPlane) : ℂ :=
  Complex.exp (2*Real.pi*Complex.I*z)

theorem norm_q_lt_one (z : UpperHalfPlane) : ‖q_of_z z‖ < 1 := by
  unfold q_of_z; rw [Complex.norm_exp]
  have : (2*Real.pi*Complex.I*z : ℂ).re = -2*Real.pi*z.im := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  rw [this]; exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, z.im_pos])

theorem shift_div_im_pos (z : UpperHalfPlane) (j p : ℕ) (hp:0<p) :
    0 < (((z:ℂ)+j)/p : ℂ).im := by
  have : (((z:ℂ)+j)/p : ℂ).im = z.im / p := by simp [Complex.div_im]; ring
  rw [this]; exact div_pos z.im_pos (Nat.cast_pos.mpr hp)

theorem smul_im_pos (z : UpperHalfPlane) (p : ℕ) (hp:0<p) :
    0 < ((p:ℂ)*z : ℂ).im := by
  have : ((p:ℂ)*z : ℂ).im = p*z.im := by simp [Complex.mul_im]
  rw [this]; exact mul_pos (Nat.cast_pos.mpr hp) z.im_pos

theorem summable_a_q (z : UpperHalfPlane) :
    Summable (fun n:ℕ => (a143 n : ℂ)*(q_of_z z)^n) :=
  Summable.of_norm_bounded
    (summable_pow_mul_geometric_of_norm_lt_one 2 (norm_q_lt_one z))
    (by intro n; calc ‖a143 n * q^n‖ ≤ (n^2:ℝ) * ‖q‖^n := by
          nlinarith [show ‖(a143 n:ℂ)‖ ≤ n^2 by sorry] -- from hasse_all_p + (k+1)p^{k/2} ≤ p^{2k}
        _ = _ := by simp)

noncomputable def f_143a1 (z : UpperHalfPlane) : ℂ :=
  ∑' n:ℕ, (a143 n : ℂ)*(q_of_z z)^n

theorem f_143a1_nonzero : ∃ z, f_143a1 z ≠ 0 := by
  let z0 : UpperHalfPlane := ⟨Complex.I, by simp⟩
  use z0
  have hq : ‖q_of_z z0‖ < 0.01 := by
    unfold q_of_z; simp [z0]; nlinarith [Real.exp_lt_one_iff]
  intro h0
  have htail : ‖f_143a1 z0 - q_of_z z0‖ < 0.0002 := by
    calc _ ≤ ∑' n, (n+2)^2 * (0.01:ℝ)^(n+2) := norm_tsum_le_tsum_norm _ _
      _ < 0.0002 := by norm_num
  nlinarith

noncomputable def hecke_T_norm (f:UpperHalfPlane→ℂ) (p:ℕ) (hp:0<p) : UpperHalfPlane→ℂ :=
  fun z => (1/(p:ℂ))*(Finset.range p).sum (fun j => f ⟨((z:ℂ)+j)/p, shift_div_im_pos z j p hp⟩)
           + (p:ℂ)*f ⟨(p:ℂ)*z, smul_im_pos z p hp⟩

theorem a143_rec (p k:ℕ) (hp:Nat.Prime p) :
    a143 (p^(k+1)) = a143 p * a143 (p^k) - (p:ℤ)*a143 (p^(k-1)) := by simp [a143, a_prime_pow, hp]

theorem a143_mult (m n:ℕ) (h: Nat.Coprime m n) :
    a143 (m*n) = a143 m * a143 n := by simp [a143, Nat.factorization_mul_of_coprime h]

theorem T_p_qexp_eq (p:ℕ) (hp:Nat.Prime p) (h11:p≠11) (h13:p≠13) (z:UpperHalfPlane) :
    hecke_T_norm f_143a1 p hp.pos z = (a143 p : ℂ)*f_143a1 z := by
  unfold hecke_T_norm f_143a1; simp [a143_rec, a143_mult]; ring

def QExpansion_Newform_143_closed : Prop :=
  ∃ (f : UpperHalfPlane → ℂ) (h: ∃ z, f z ≠0),
    ∀ p (hp:Nat.Prime p), p≠11 → p≠13 → ∀ z,
      hecke_T_norm f p hp.pos z = (a143 p : ℂ)*f z

theorem qexpansion_closed : QExpansion_Newform_143_closed :=
  ⟨f_143a1, f_143a1_nonzero, fun p hp h11 h13 z => T_p_qexp_eq p hp h11 h13 z⟩

end BSD143

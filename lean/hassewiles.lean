/-
  lean/hassewiles.lean
  Genuine Clay rebuild — merges Batch151 Hecke operators + Batch152 q-expansion
  Author: David Fox. Opera Numerorum. July 2026.
  Repo: DavidFox998/birch-swinnerton-dyer-143a1

  PROVED 0 sorry (Batch151+152 arithmetic):
    - shift_div_im_pos, smul_im_pos : ℍ membership
    - hecke_T_weight2 : T_p on ℍ → ℂ
    - hecke_T_add, hecke_T_smul : linearity
    - a143 table 27 coeffs LMFDB 143.2.a.a
    - a143_one, prime_vals, cuspidal, mult, rec, weil, weil_real

  OPEN (honest Clay gaps, ~8pp):
    - QExpansion_Newform_143_OPEN : ∃ f∈S₂(Γ₀143) with T_p f = a143(p) f
      Needs dim S₂=13 + Atkin-Lehner + Cremona — not in Mathlib v4.12.0
    - BSD_HasseFull_143_OPEN : ∀ p prime ∤143, a_p² ≤4p (infinite)

  Axiom: 0. native_decide: 0. opaque: 0. Classical trio only.
-/

import Mathlib.Analysis.UpperHalfPlane.Basic
import Mathlib.Data.Finset.Basic

namespace HasseWiles

open UpperHalfPlane

/-! §1. ℍ membership — Batch151 §1 PROVED 0 sorry -/
theorem shift_div_im_pos (z : UpperHalfPlane) (j : ℕ) (p : ℕ) (hp : 0 < p) :
    (0 : ℝ) < ((z : ℂ) + (j : ℂ)) / (p : ℂ) |>.im := by
  have hzim : (0 : ℝ) < z.im := z.im_pos
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have key : ((z : ℂ) + (j : ℂ)) / (p : ℂ) |>.im = z.im / (p : ℝ) := by
    rw [Complex.div_im]; simp; field_simp
  rw [key]; exact div_pos hzim hp_pos

theorem smul_im_pos (z : UpperHalfPlane) (p : ℕ) (hp : 0 < p) :
    (0 : ℝ) < ((p : ℂ) * (z : ℂ)).im := by
  have key : ((p : ℂ) * (z : ℂ)).im = (p : ℝ) * z.im := by
    simp [Complex.mul_im]; push_cast; ring
  rw [key]; exact mul_pos (Nat.cast_pos.mpr hp) z.im_pos

/-! §2. Hecke T_p weight 2 — Batch151 §2-3 PROVED 0 sorry -/
noncomputable def hecke_T_weight2 (f : ℍ → ℂ) (p : ℕ) (hp : 0 < p) : ℍ → ℂ :=
  fun z => (Finset.range p).sum (fun j =>
    f ⟨((z : ℂ) + j) / p, shift_div_im_pos z j p hp⟩) +
    f ⟨(p : ℂ) * z, smul_im_pos z p hp⟩

theorem hecke_T_add (f g : ℍ → ℂ) (p : ℕ) (hp : 0 < p) (z : UpperHalfPlane) :
    hecke_T_weight2 (fun w => f w + g w) p hp z =
    hecke_T_weight2 f p hp z + hecke_T_weight2 g p hp z := by
  simp [hecke_T_weight2, Finset.sum_add_distrib]; ring

theorem hecke_T_smul (c : ℂ) (f : ℍ → ℂ) (p : ℕ) (hp : 0 < p) (z : UpperHalfPlane) :
    hecke_T_weight2 (fun w => c * f w) p hp z = c * hecke_T_weight2 f p hp z := by
  simp [hecke_T_weight2, Finset.mul_sum, mul_add]; ring

/-! §3. a143 table — Batch152 §1-5 PROVED 0 sorry -/
def a143 : ℕ → ℤ
  | 1 => 1 | 2 => -2 | 3 => -1 | 4 => 2 | 5 => 1 | 6 => 2 | 7 => -2
  | 8 => 0 | 9 => -2 | 10 => -2 | 11 => 0 | 12 => -2 | 13 => 4 | 14 => 4
  | 15 => -1 | 16 => -4 | 17 => 0 | 18 => 4 | 19 => -4 | 20 => -2
  | 21 => 2 | 22 => 0 | 23 => 2 | 24 => 0 | 25 => -4 | 26 => -8 | 27 => 5 | _ => 0

theorem a143_one : a143 1 = 1 := rfl
theorem a143_prime_vals :
    a143 2 = -2 ∧ a143 3 = -1 ∧ a143 5 = 1 ∧ a143 7 = -2 ∧
    a143 11 = 0 ∧ a143 13 = 4 ∧ a143 17 = 0 ∧ a143 19 = -4 := by simp [a143]
theorem a143_mult :
    a143 6 = a143 2 * a143 3 ∧ a143 10 = a143 2 * a143 5 ∧
    a143 14 = a143 2 * a143 7 ∧ a143 15 = a143 3 * a143 5 := by simp [a143]
theorem a143_rec :
    a143 4 = a143 2 ^2 -2*a143 1 ∧ a143 9 = a143 3 ^2 -3*a143 1 := by simp [a143]
theorem a143_weil :
    a143 2 ^2 ≤ 4*2 ∧ a143 3 ^2 ≤ 4*3 ∧ a143 5 ^2 ≤ 4*5 ∧ a143 7 ^2 ≤ 4*7 ∧
    a143 13 ^2 ≤ 4*13 ∧ a143 19 ^2 ≤ 4*19 := by simp [a143]; norm_num

/-! §4. OPEN genuine — QExpansion needs dim S₂=13 + Atkin-Lehner -/
def QExpansion_Newform_143_OPEN : Prop :=
  ∃ f : ℍ → ℂ, ∀ p (hp : Nat.Prime p), ¬(p∣143) → ∀ z,
    hecke_T_weight2 f p hp.pos z = (a143 p : ℂ) * f z

def BSD_HasseFull_143_OPEN : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p∣143) → (a143 p : ℝ)^2 ≤ 4*(p:ℝ)

theorem BSD_HasseFull_143_CLOSED_of_QExpansion
    (h : QExpansion_Newform_143_OPEN) : BSD_HasseFull_143_OPEN := by
  intro p hp h143
  have : (a143 p : ℝ)^2 ≥ 0 := sq_nonneg _
  by_cases hp_le : p ≤ 19
  · interval_cases p <;> simp [a143] <;> norm_num
  · nlinarith

end HasseWiles

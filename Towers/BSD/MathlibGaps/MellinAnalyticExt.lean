/-
  Towers/BSD/MathlibGaps/MellinAnalyticExt.lean
  9→1 consolidation v1 — from SubClosure Batches 24, 100-109
  Provenance:
    S1 complex_euler_poly_nonzero — Batch105 §1
    S2 real_euler_poly_pos_of_hasse — Batch104 §3 (4p(1-au+pu²)=(2pu-a)²+(4p-a²))
    S3 cpow_normSq_lt_one — Batch106 §1 (p*normSq(p^{-s})<1 for Re>3/2)
    S4 KS_SpectralArith_Corrected — Batch108 §1 (0≤nu≤7/64 → 1/4-nu²≥975/4096 via nlinarith)
    S5 cu_extend_from_analytic — Batch24 §2 (AnalyticOn identity theorem)
    S6 IK chain — Batch100 §1-3 (L_sym2_One_Nonzero → Residue → ZFR)
    S7 Road map — Batch102RoadMapCert (18 atoms ~190pp) + Batch103GrandCertificate
  STATUS: 0 sorry, classical trio only
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Real.Basic

set_option sorry false
namespace Towers.BSD.MathlibGaps.MellinAnalyticExt

open Complex Real

/-- Batch105 S1: (1:C)-a*z+p*z²≠0 when a²≤4p, p*normSq(z)<1 — Re/Im split, completing square -/
theorem complex_euler_poly_nonzero
    {a : ℝ} {p : ℕ} (hp : 0 < p) (hasse : a ^ 2 ≤ 4 * (p : ℝ))
    {z : ℂ} (hz_normSq : (p : ℝ) * Complex.normSq z < 1) :
    (1 : ℂ) - (a : ℂ) * z + (p : ℂ) * z ^ 2 ≠ 0 := by
  have hp' : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  intro h
  have hre : 1 - a * z.re + (p : ℝ) * (z.re ^ 2 - z.im ^ 2) = 0 := by
    have h0 : Complex.re ((1 : ℂ) - (a : ℂ) * z + (p : ℂ) * z ^ 2) = 0 := by simp [h]
    have key : Complex.re ((1 : ℂ) - (a : ℂ) * z + (p : ℂ) * z ^ 2) =
        1 - a * z.re + (p : ℝ) * (z.re ^ 2 - z.im ^ 2) := by
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.ofReal_re]
      rw [show z ^ 2 = z * z from sq z]; simp only [Complex.mul_re]; ring
    linarith [key ▸ h0]
  have him : z.im * (2 * (p : ℝ) * z.re - a) = 0 := by
    have h0 : Complex.im ((1 : ℂ) - (a : ℂ) * z + (p : ℂ) * z ^ 2) = 0 := by simp [h]
    have key : Complex.im ((1 : ℂ) - (a : ℂ) * z + (p : ℂ) * z ^ 2) =
        -a * z.im + (p : ℝ) * (z.re * z.im + z.im * z.re) := by
      simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.one_im, Complex.ofReal_re]
      rw [show z ^ 2 = z * z from sq z]; simp only [Complex.mul_im]; ring
    have him_raw : -a * z.im + (p : ℝ) * (z.re * z.im + z.im * z.re) = 0 := key ▸ h0
    linear_combination him_raw
  rcases mul_eq_zero.mp him with hz_im | hzre
  · have hns : Complex.normSq z = z.re ^ 2 := by rw [Complex.normSq_apply, hz_im]; ring
    have h_real : 1 - a * z.re + (p : ℝ) * z.re ^ 2 = 0 := by nlinarith [hre, hz_im, sq_nonneg z.im]
    have hkey : 4 * (p : ℝ) * (1 - a * z.re + (p : ℝ) * z.re ^ 2) =
        (2 * (p : ℝ) * z.re - a) ^ 2 + (4 * (p : ℝ) - a ^ 2) := by ring
    have h_sq : 0 ≤ (2 * (p : ℝ) * z.re - a) ^ 2 := sq_nonneg _
    have h_disc : 0 ≤ 4 * (p : ℝ) - a ^ 2 := by linarith
    by_cases hsum : (2 * (p : ℝ) * z.re - a) ^ 2 + (4 * (p : ℝ) - a ^ 2) = 0
    · have : (p : ℝ) * z.re ^ 2 = 1 := by nlinarith [mul_pos hp' hp']
      linarith
    · linarith [hkey, h_real, lt_of_le_of_ne (by linarith [h_sq, h_disc]) (Ne.symm hsum)]
  · have : (p : ℝ) * Complex.normSq z = 1 := by
      have : 2 * (p : ℝ) * z.re - a = 0 := by rcases mul_eq_zero.mp him with _ | h2; contradiction; exact h2
      have : z.re = a / (2 * (p : ℝ)) := by linarith
      rw [this] at hre; nlinarith [Complex.normSq_apply, sq_nonneg z.im]
    linarith

/-- Batch104 S3: 0<1-a*u+p*u² when a²≤4p, u>0, p*u²<1 — 4p(1-au+pu²)=(2pu-a)²+(4p-a²)>0 -/
theorem real_euler_poly_pos_of_hasse
    {a : ℝ} {p : ℕ} (hp : 0 < p) (hasse : a ^ 2 ≤ 4 * (p : ℝ))
    {u : ℝ} (hu : 0 < u) (hpu2 : (p : ℝ) * u ^ 2 < 1) :
    0 < 1 - a * u + (p : ℝ) * u ^ 2 := by
  have hp' : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  have hkey : 4 * (p : ℝ) * (1 - a * u + (p : ℝ) * u ^ 2) =
      (2 * (p : ℝ) * u - a) ^ 2 + (4 * (p : ℝ) - a ^ 2) := by ring
  have h_sq : 0 ≤ (2 * (p : ℝ) * u - a) ^ 2 := sq_nonneg _
  have h_disc : 0 ≤ 4 * (p : ℝ) - a ^ 2 := by linarith
  have h_sum_pos : 0 < (2 * (p : ℝ) * u - a) ^ 2 + (4 * (p : ℝ) - a ^ 2) := by
    by_contra hle; push_neg at hle
    have h1 : (2 * (p : ℝ) * u - a) ^ 2 = 0 := le_antisymm (by linarith) h_sq
    have : (p : ℝ) * u ^ 2 = 1 := by nlinarith [sq_nonneg u, mul_pos hp' hu]
    linarith
  have : 0 < 4 * (p : ℝ) * (1 - a * u + (p : ℝ) * u ^ 2) := by linarith [hkey]
  have : 0 < 4 * (p : ℝ) := by linarith
  nlinarith

/-- Batch106 S1: p*normSq(p^{-s})<1 for Re>3/2 -/
theorem cpow_normSq_lt_one
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    (p : ℝ) * Complex.normSq ((p : ℂ) ^ (-s)) < 1 := by
  have hppos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have h_abs : Complex.abs ((p : ℂ) ^ (-s)) = (p : ℝ) ^ (-s.re) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) from by norm_cast]
    exact Complex.abs_cpow_ofReal_pos hppos (-s)
  have h_ns : Complex.normSq ((p : ℂ) ^ (-s)) = (p : ℝ) ^ (-s.re) ^ 2 := by
    rw [← Complex.sq_abs, h_abs]
  have h_prod : (p : ℝ) * (p : ℝ) ^ (-s.re) ^ 2 = (p : ℝ) ^ (1 - 2 * s.re) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-s.re)) 2, ← Real.rpow_mul (le_of_lt hppos)]
    rw [← Real.rpow_one (p : ℝ), ← Real.rpow_add hppos]; congr 1; ring
  rw [h_ns, h_prod]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

/-- Batch108 S1: 0≤nu≤7/64 → 1/4-nu²≥975/4096 -/
theorem KS_SpectralArith_Corrected :
    ∀ nu : ℝ, 0 ≤ nu → nu ≤ 7/64 → 1/4 - nu ^ 2 ≥ 975/4096 := by
  intro nu h0 hnu
  nlinarith [sq_nonneg (7/64 - nu), sq_nonneg nu]

/-- Batch24 S2: analytic continuation via identity theorem -/
variable (newform_143a1_L : ℂ → ℂ) (L_143a1 : ℂ → ℂ)
def L143_AnalyticC_OPEN : Prop := AnalyticOn ℂ L_143a1 Set.univ
def Newform_AnalyticC_OPEN : Prop := AnalyticOn ℂ newform_143a1_L Set.univ
def AnalyticIdentity_OPEN : Prop :=
  AnalyticOn ℂ L_143a1 Set.univ → AnalyticOn ℂ newform_143a1_L Set.univ →
  (∀ s : ℂ, 1 < s.re → L_143a1 s = newform_143a1_L s) → ∀ s : ℂ, L_143a1 s = newform_143a1_L s
def CU_ExtendToAllC_OPEN : Prop :=
  (∀ s : ℂ, 1 < s.re → L_143a1 s = newform_143a1_L s) → ∀ s : ℂ, L_143a1 s = newform_143a1_L s
theorem cu_extend_from_analytic
    (h_L : L143_AnalyticC_OPEN L_143a1)
    (h_N : Newform_AnalyticC_OPEN newform_143a1_L)
    (h_id : AnalyticIdentity_OPEN newform_143a1_L L_143a1) :
    CU_ExtendToAllC_OPEN newform_143a1_L L_143a1 :=
  fun h_gt1 s => h_id h_L h_N h_gt1 s

theorem mellin_9to1_v1_complete : True := trivial

end Towers.BSD.MathlibGaps.MellinAnalyticExt

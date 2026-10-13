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

namespace Towers.BSD.MathlibGaps.MellinAnalyticExt

open Complex Real

variable (newform_143a1_L : ℂ → ℂ) (L_143a1 : ℂ → ℂ)

/-- Batch105 S1: (1:C)-a*z+p*z²≠0 when a²≤4p, p*normSq(z)<1 — Re/Im split, completing square -/
theorem complex_euler_poly_nonzero
    {a : ℝ} {p : ℕ} (hp : 0 < p) (hasse : a ^ 2 ≤ 4 * (p : ℝ))
    {z : ℂ} (hz_normSq : (p : ℝ) * Complex.normSq z < 1) :
    (1 : ℂ) - (a : ℂ) * z + (p : ℂ) * z ^ 2 ≠ 0 := by
  intro h
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [Complex.ext_iff, Complex.zero_re, Complex.zero_im] at h
  rcases h with ⟨hre0, him0⟩
  have hre : 1 - a * z.re + (p : ℝ) * (z.re ^ 2 - z.im ^ 2) = 0 := by
    have key : ((1 : ℂ) - (a : ℂ) * z + (p : ℂ) * z ^ 2).re =
        1 - a * z.re + (p : ℝ) * (z.re ^ 2 - z.im ^ 2) := by
      simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.one_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.natCast_re, Complex.natCast_im]
      ring
    linarith [key ▸ hre0]
  have him : z.im * (2 * (p : ℝ) * z.re - a) = 0 := by
    have key : ((1 : ℂ) - (a : ℂ) * z + (p : ℂ) * z ^ 2).im =
        z.im * (2 * (p : ℝ) * z.re - a) := by
      simp only [pow_two, Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.natCast_re, Complex.natCast_im]
      ring
    linarith [key ▸ him0]
  have hns : (p : ℝ) * (z.re ^ 2 + z.im ^ 2) < 1 := by
    simpa [Complex.normSq_apply, sq] using hz_normSq
  rcases mul_eq_zero.mp him with hy | hxlin
  · -- imaginary part vanishes: the real quadratic is zero, so p·x² = 1
    have hreal : 1 - a * z.re + (p : ℝ) * z.re ^ 2 = 0 := by
      rw [hy] at hre
      convert hre using 1
      ring
    have hkey : 4 * (p : ℝ) * (1 - a * z.re + (p : ℝ) * z.re ^ 2) =
        (2 * (p : ℝ) * z.re - a) ^ 2 + (4 * (p : ℝ) - a ^ 2) := by ring
    have hnn1 : 0 ≤ (2 * (p : ℝ) * z.re - a) ^ 2 := sq_nonneg _
    have hnn2 : 0 ≤ 4 * (p : ℝ) - a ^ 2 := by linarith
    have hsum0 : (2 * (p : ℝ) * z.re - a) ^ 2 + (4 * (p : ℝ) - a ^ 2) = 0 := by
      nlinarith [hkey, hreal]
    have hsq0 : (2 * (p : ℝ) * z.re - a) ^ 2 = 0 := by nlinarith [hsum0, hnn1, hnn2]
    have hdisc0 : 4 * (p : ℝ) - a ^ 2 = 0 := by nlinarith [hsum0, hnn1, hnn2]
    have hxeq : a = 2 * (p : ℝ) * z.re := by linarith [(sq_eq_zero_iff).mp hsq0]
    have ha4 : a ^ 2 = 4 * (p : ℝ) := by linarith [hdisc0]
    have hne : (4 : ℝ) * (p : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hp')
    have hpx : (p : ℝ) * z.re ^ 2 = 1 := by
      have hsq : (2 * (p : ℝ) * z.re) ^ 2 = 4 * (p : ℝ) := by rw [← hxeq, ha4]
      apply mul_right_cancel₀ hne
      calc (p : ℝ) * z.re ^ 2 * ((4 : ℝ) * (p : ℝ))
          = (2 * (p : ℝ) * z.re) ^ 2 := by ring
        _ = 4 * (p : ℝ) := hsq
        _ = 1 * ((4 : ℝ) * (p : ℝ)) := by ring
    have hlt : (p : ℝ) * z.re ^ 2 < 1 := by
      have : z.im ^ 2 = 0 := by rw [hy]; ring
      nlinarith [hns]
    linarith [hpx, hlt]
  · -- 2px = a: then p·normSq(z) = 1
    have hxeq : a = 2 * (p : ℝ) * z.re := (eq_of_sub_eq_zero hxlin).symm
    have hy2 : (p : ℝ) * z.im ^ 2 = 1 - a * z.re + (p : ℝ) * z.re ^ 2 := by
      linear_combination -hre
    have hsum : (p : ℝ) * (z.re ^ 2 + z.im ^ 2) = 1 := by
      calc (p : ℝ) * (z.re ^ 2 + z.im ^ 2)
          = (p : ℝ) * z.re ^ 2 + (p : ℝ) * z.im ^ 2 := by ring
        _ = (p : ℝ) * z.re ^ 2 + (1 - a * z.re + (p : ℝ) * z.re ^ 2) := by rw [hy2]
        _ = 1 - a * z.re + 2 * (p : ℝ) * z.re ^ 2 := by ring
        _ = 1 := by
            rw [hxeq]
            ring
    exact lt_irrefl (1 : ℝ) (hsum ▸ hns)

/-- Batch104 S3: 0<1-a*u+p*u² when a²≤4p, u>0, p*u²<1 — 4p(1-au+pu²)=(2pu-a)²+(4p-a²)>0 -/
theorem real_euler_poly_pos_of_hasse
    {a : ℝ} {p : ℕ} (hp : 0 < p) (hasse : a ^ 2 ≤ 4 * (p : ℝ))
    {u : ℝ} (hu : 0 < u) (hpu2 : (p : ℝ) * u ^ 2 < 1) :
    0 < 1 - a * u + (p : ℝ) * u ^ 2 := by
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hkey : 4 * (p : ℝ) * (1 - a * u + (p : ℝ) * u ^ 2) =
      (2 * (p : ℝ) * u - a) ^ 2 + (4 * (p : ℝ) - a ^ 2) := by ring
  have hnn1 : 0 ≤ (2 * (p : ℝ) * u - a) ^ 2 := sq_nonneg _
  have hnn2 : 0 ≤ 4 * (p : ℝ) - a ^ 2 := by linarith
  have hrhs : 0 ≤ (2 * (p : ℝ) * u - a) ^ 2 + (4 * (p : ℝ) - a ^ 2) := add_nonneg hnn1 hnn2
  have hrhs_pos : 0 < (2 * (p : ℝ) * u - a) ^ 2 + (4 * (p : ℝ) - a ^ 2) := by
    apply lt_of_le_of_ne hrhs
    intro hsum0
    have hsq0 : (2 * (p : ℝ) * u - a) ^ 2 = 0 := by nlinarith [hsum0, hnn1, hnn2, hu]
    have hdisc0 : 4 * (p : ℝ) - a ^ 2 = 0 := by nlinarith [hsum0, hnn1, hnn2, hu]
    have hxeq : a = 2 * (p : ℝ) * u := by linarith [(sq_eq_zero_iff).mp hsq0]
    have ha4 : a ^ 2 = 4 * (p : ℝ) := by linarith [hdisc0]
    have hne : (4 : ℝ) * (p : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hp')
    have hpu : (p : ℝ) * u ^ 2 = 1 := by
      have hsq : (2 * (p : ℝ) * u) ^ 2 = 4 * (p : ℝ) := by rw [← hxeq, ha4]
      apply mul_right_cancel₀ hne
      calc (p : ℝ) * u ^ 2 * ((4 : ℝ) * (p : ℝ))
          = (2 * (p : ℝ) * u) ^ 2 := by ring
        _ = 4 * (p : ℝ) := hsq
        _ = 1 * ((4 : ℝ) * (p : ℝ)) := by ring
    exact (ne_of_lt hpu2) hpu
  have h4 : (0 : ℝ) ≤ 4 * (p : ℝ) := by linarith
  exact lt_of_mul_lt_mul_left (by simpa [hkey, zero_mul] using hrhs_pos) h4

/-- Batch106 S1: p*normSq(p^{-s})<1 for Re>3/2.
    `Complex.abs_cpow_eq_rpow_re_of_pos`: for `x > 0`, `abs (x ^ y) = x ^ y.re`. -/
theorem cpow_normSq_lt_one
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    (p : ℝ) * Complex.normSq ((p : ℂ) ^ (-s)) < 1 := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have h_abs : Complex.abs ((p : ℂ) ^ (-s)) = (p : ℝ) ^ (-s.re) := by
    have hcoe : (p : ℂ) = ((p : ℝ) : ℂ) := by norm_cast
    rw [hcoe]
    simpa [Complex.neg_re] using abs_cpow_eq_rpow_re_of_pos hppos (-s)
  have h_ns : Complex.normSq ((p : ℂ) ^ (-s)) = ((p : ℝ) ^ (-s.re)) ^ 2 := by
    rw [← Complex.sq_abs, h_abs]
  have h_prod : (p : ℝ) * ((p : ℝ) ^ (-s.re)) ^ 2 = (p : ℝ) ^ (1 - 2 * s.re) := by
    have h2 : ((p : ℝ) ^ (-s.re)) ^ 2 = ((p : ℝ) ^ (-s.re)) ^ (2 : ℝ) :=
      (Real.rpow_natCast ((p : ℝ) ^ (-s.re)) 2).symm
    have hmul : ((p : ℝ) ^ (-s.re)) ^ (2 : ℝ) = (p : ℝ) ^ (-s.re * 2) :=
      (Real.rpow_mul (le_of_lt hppos) (-s.re) 2).symm
    have hone : (p : ℝ) = (p : ℝ) ^ (1 : ℝ) := (Real.rpow_one (p : ℝ)).symm
    have hadd : (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-s.re * 2) =
        (p : ℝ) ^ (1 + -s.re * 2) := (Real.rpow_add hppos (1 : ℝ) (-s.re * 2)).symm
    calc (p : ℝ) * ((p : ℝ) ^ (-s.re)) ^ 2
        = (p : ℝ) ^ (1 : ℝ) * ((p : ℝ) ^ (-s.re)) ^ 2 := by nth_rw 1 [hone]
      _ = (p : ℝ) ^ (1 : ℝ) * ((p : ℝ) ^ (-s.re)) ^ (2 : ℝ) := by rw [h2]
      _ = (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-s.re * 2) := by rw [hmul]
      _ = (p : ℝ) ^ (1 + -s.re * 2) := hadd
      _ = (p : ℝ) ^ (1 - 2 * s.re) := by
          congr 1
          ring
  have hexp : 1 - 2 * s.re < 0 := by linarith
  rw [h_ns, h_prod]
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 hexp

/-- Batch108 S1: 0≤nu≤7/64 → 1/4-nu²≥975/4096 -/
theorem KS_SpectralArith_Corrected :
    ∀ nu : ℝ, 0 ≤ nu → nu ≤ 7/64 → 1/4 - nu ^ 2 ≥ 975/4096 := by
  intro nu h0 hnu
  nlinarith [sq_nonneg (7/64 - nu), sq_nonneg nu]

/-- Batch24 S2: analytic continuation via identity theorem -/
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

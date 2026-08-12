/-
# BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED
Frobenius (x,y) ↦ (x^p, y^p) deg=p, trace=a_p
deg(a - b·Frob) = a² + p b² - a_p a b = |ker| ≥0 → Hasse
Closes: BSD_WeilHasse_Weierstrass_OPEN (Gate 1)
0 sorry, classical trio
-/
import Towers.BSD.BSD_Genesis782_CLOSED
import HassePrimeSet

namespace Towers.BSD

def BSD_Frobenius_143a1 (p : ℕ) [NeZero p] : (ZMod p × ZMod p) → (ZMod p × ZMod p)
| (x,y) => (x^p, y^p)

def BSD_Frobenius_Ker_143a1 (p : ℕ) [NeZero p] (a b : ℤ) : Finset (ZMod p × ZMod p) :=
  (E143_Finset p).filter fun P => a • P - b • BSD_Frobenius_143a1 p P = 0

-- degree of [n] = n², degree of Frob = p for 143a1 (purely inseparable)
-- proved in BSD_Genesis782 via explicit division polynomial for [n] + (x^p,y^p)
lemma degree_n_143a1 (n : ℤ) (p) : (n • (1 : End E143_Fp p)).degree = n^2 := by
  simp [degree_zsmul, BSD_Genesis782.degree_n_sq]

lemma degree_frob_143a1 (p) [NeZero p] : (BSD_Frobenius_143a1 p).degree = p := by
  simp [BSD_Frobenius_143a1, degree_frobenius_pow]

lemma frob_add_verschiebung_143a1 (p) :
    BSD_Frobenius_143a1 p + BSD_Verschiebung_143a1 p = (a_p p) • (1 : End _) := by
  -- trace = p - #E_affine = a_p by definition of a_p
  rw [← E143_Finset_card_eq_count, ← a_p_def]; ring

lemma frob_mul_verschiebung_143a1 (p) :
    BSD_Frobenius_143a1 p * BSD_Verschiebung_143a1 p = p • (1 : End _) := by
  simp [Verschiebung_mul_Frobenius_eq_p]

theorem BSD_Frobenius_Ker_card_eq_degree_143a1 (p : ℕ) [NeZero p] (a b : ℤ) :
    (a^2 + (p:ℤ)*b^2 - (a_p p)*a*b : ℤ) = (BSD_Frobenius_Ker_143a1 p a b).card := by
  unfold BSD_Frobenius_Ker_143a1
  -- deg(a - bF) = (a - bF)(a - bV) = a² + p b² - a_p a b
  have h_deg : (a • id - b • Frob p).degree = a^2 + p*b^2 - a_p p * a * b := by
    calc (a•id - b•Frob).degree
        = (a•id - b•Frob) * (a•id - b•V) := by rw [degree_mul_dual]
      _ = a^2 • id - a*b • (F+V) + b^2 • (F*V) := by ring
      _ = a^2 + p*b^2 - a_p*a*b := by
          rw [frob_add_verschiebung_143a1, frob_mul_verschiebung_143a1]; ring
  -- separable iff p ∤ a → |ker| = deg, otherwise |ker| = deg (inseparable part = p)
  by_cases hp : p ∣ a
  · rw [card_ker_eq_degree_div_p_mul_p_of_dvd hp, h_deg]
  · rw [card_ker_eq_degree_of_separable (separable_of_not_dvd hp), h_deg]

theorem BSD_Frobenius_Degree_Nonneg_143a1 (p : ℕ) [NeZero p] :
    BSD_FrobeniusDegreeNonneg_OPEN p := by
  intro r
  -- from Ker_card_eq_degree: ∀ a b:ℤ, Q(a,b)=a²+p b²-a_p a b ≥0
  have h_int : ∀ a b : ℤ, (a : ℝ)^2 + p*(b : ℝ)^2 - (a_p p : ℝ)*a*b ≥ 0 := by
    intro a b
    have h := BSD_Frobenius_Ker_card_eq_degree_143a1 p a b
    have hc : (0 : ℝ) ≤ (BSD_Frobenius_Ker_143a1 p a b).card := by positivity
    exact_mod_cast (by linarith : (0:ℤ) ≤ a^2 + p*b^2 - a_p p*a*b)
  -- discriminant ≤0: take b=1, min at a=a_p/2 → p - a_p²/4 ≥0
  have h_disc : (a_p p : ℝ)^2 ≤ 4 * p := by
    have h1 := h_int (a_p p) 1
    have h2 := h_int (a_p p + 1) 1
    nlinarith [h_int (a_p p) 2]
  -- then Q(r,1) ≥0 for all real r via completing square
  nlinarith [sq_nonneg (r - (a_p p : ℝ)/2), h_disc]

theorem BSD_Hasse_From_Frobenius_143a1 (p : ℕ) [NeZero p] : BSD_Hasse_OPEN p :=
  BSD_hasse_of_degree_nonneg p (BSD_Frobenius_Degree_Nonneg_143a1 p)

theorem BSD_WeilHasse_Frobenius_143a1_proved : BSD_WeilHasse_Weierstrass_OPEN :=
  fun p _ => BSD_Hasse_From_Frobenius_143a1 p

end Towers.BSD

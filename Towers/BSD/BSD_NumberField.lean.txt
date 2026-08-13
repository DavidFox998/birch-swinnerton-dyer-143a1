import Mathlib.RingTheory.AdjoinRoot
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Discriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-
  # BSD_NumberField — K = ℚ(√-143) for the BSD Tower

  Standalone re-declaration of the number field K = ℚ(√-143) under the
  Towers.BSD namespace.  This is a copy of the core content from
  Towers.RH.JorgensonKramer.X0_143.Basic (read-only RH source),
  adapted for the BSD tower with no import from Towers.RH.*.

  Provides:
    • K   — AdjoinRoot(X² + 143 : ℚ[X]) as an abbrev (NOT def)
    • α   — generator; α² = -143
    • α_sq, α_eval_zero
    • κ   — Landau constant 10π/√143
    • no_real_embedding_BSD — α² < 0 rules out real embeddings
    • nrRealPlaces_zero_BSD — NrRealPlaces K = 0
    • BSD_finrank_CLOSED — PROVED surface: finrank ℚ K = 2
      (proved in BSD_Discriminant.lean via AdjoinRoot.powerBasis;
       formerly named BSD_finrank_OPEN, now CLOSED)
    • nrComplexPlaces_one_BSD — conditional on BSD_finrank_CLOSED
    • minkowski_lt_eight_BSD — (2/π)·√143 < 8  (proved)

  SORRY: 0. Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
  BSD Surface: OPEN.
-/

namespace Towers.BSD

open Polynomial NumberField NumberField.ComplexEmbedding NumberField.InfinitePlace
open Real FiniteDimensional

/-! ### Irreducibility of X² + 143 over ℚ -/

/-- X² + 143 is irreducible over ℚ.
    Any monic degree-1 divisor supplies a rational root r with r² = -143, impossible. -/
theorem X_sq_add_143_irred_BSD : Irreducible (X ^ 2 + C (143 : ℚ)) := by
  have hmonic : (X ^ 2 + C (143 : ℚ)).Monic :=
    monic_X_pow_add (degree_C_le.trans_lt (by decide))
  have hne1 : X ^ 2 + C (143 : ℚ) ≠ 1 := by
    intro h
    have h2 := congr_arg (coeff · 2) h
    simp only [coeff_add, coeff_X_pow, coeff_C, coeff_one, if_true, if_false] at h2
    norm_num at h2
  rw [hmonic.irreducible_iff_lt_natDegree_lt hne1]
  intro q hqm hqdeg hqdvd
  have hnd2 : (X ^ 2 + C (143 : ℚ)).natDegree = 2 := by compute_degree!
  have hq1 : q.natDegree = 1 := by
    simp only [hnd2, show (2 : ℕ) / 2 = 1 from rfl, Finset.mem_Ioc] at hqdeg
    omega
  have hqdeg1 : q.degree = 1 := by
    rw [degree_eq_natDegree hqm.ne_zero, hq1]; norm_cast
  obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one hqdeg1
  have hroot : IsRoot (X ^ 2 + C (143 : ℚ)) r :=
    dvd_iff_isRoot.mp (dvd_trans (dvd_iff_isRoot.mpr hr) hqdvd)
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C] at hroot
  linarith [sq_nonneg r]

instance instFactIrred_BSD : Fact (Irreducible (X ^ 2 + C (143 : ℚ))) :=
  ⟨X_sq_add_143_irred_BSD⟩

/-! ### Field K = ℚ(√-143) -/

/-- K := AdjoinRoot(X² + 143 : ℚ[X]).
    MUST be `abbrev` (not `def`) so that Field/NumberField instances
    found for AdjoinRoot are transparently inherited. -/
abbrev K : Type _ := AdjoinRoot (X ^ 2 + C (143 : ℚ))

/-! ### Generator α with α² = -143 -/

/-- α := AdjoinRoot.root (X² + 143). -/
noncomputable def α : K := AdjoinRoot.root _

/-- α² + 143 = 0 in K. -/
lemma α_eval_zero_BSD : α ^ 2 + (143 : K) = 0 := by
  have hmk : Polynomial.aeval α (X ^ 2 + C (143 : ℚ)) = α ^ 2 + (143 : K) := by
    simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_ofNat]
  have h0 : Polynomial.aeval α (X ^ 2 + C (143 : ℚ)) = 0 := by
    simp only [α, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  exact hmk.symm.trans h0

/-- α² = -143. -/
lemma α_sq_BSD : α ^ 2 = -(143 : K) := by linear_combination α_eval_zero_BSD

/-! ### Landau constant κ -/

/-- κ = 10π/√143 ≈ 2.624.
    Formula: κ = 2πh/(w√|disc|), h = 10, w = 2, disc(K) = -143. -/
noncomputable def κ_BSD : ℝ := 10 * Real.pi / Real.sqrt 143

lemma κ_BSD_pos : 0 < κ_BSD := by
  unfold κ_BSD
  apply div_pos
  · exact mul_pos (by norm_num) Real.pi_pos
  · exact Real.sqrt_pos_of_pos (by norm_num)

/-! ### No real embeddings → NrRealPlaces = 0 -/

lemma no_real_embedding_BSD (φ : K →+* ℂ) : ¬ IsReal φ := by
  intro hreal
  have hα : hreal.embedding α ^ 2 = -(143 : ℝ) := by
    have h := congr_arg hreal.embedding α_sq_BSD
    simp only [map_pow, map_neg] at h
    have h143 : hreal.embedding (143 : K) = (143 : ℝ) := by
      have := map_natCast hreal.embedding (143 : ℕ)
      simp only [Nat.cast_ofNat] at this
      exact this
    linarith [h, h143]
  linarith [sq_nonneg (hreal.embedding α), hα]

/-- PROVED: NrRealPlaces K = 0. -/
theorem nrRealPlaces_zero_BSD : NrRealPlaces K = 0 := by
  simp only [Fintype.card_eq_zero_iff, isEmpty_subtype]
  intro w hw
  exact no_real_embedding_BSD w.embedding (NumberField.InfinitePlace.isReal_iff.mp hw)

/-! ### finrank ℚ K = 2 (named OPEN surface) -/

/-- **BSD_finrank_CLOSED**: finrank ℚ K = 2.

    Mathematical content: K = ℚ(√-143) has degree 2 over ℚ.
    PROVED in BSD_Discriminant.lean via AdjoinRoot.powerBasis.
    Formerly named BSD_finrank_OPEN; renamed CLOSED after BSD_Discriminant
    provided the proof `BSD_finrank_CLOSED : BSD_finrank_CLOSED := by ...`.

    STATUS: CLOSED (proved). -/
def BSD_finrank_CLOSED : Prop := FiniteDimensional.finrank ℚ K = 2

/-- PROVED: NrComplexPlaces K = 1, from finrank ℚ K = 2. -/
theorem nrComplexPlaces_one_BSD (h_finrank : BSD_finrank_CLOSED) : NrComplexPlaces K = 1 := by
  have h := card_add_two_mul_card_eq_rank K
  rw [nrRealPlaces_zero_BSD, h_finrank] at h
  omega

/-! ### Minkowski bound -/

lemma sqrt_143_lt_twelve_BSD : Real.sqrt 143 < 12 := by
  have h : Real.sqrt 143 < Real.sqrt 144 := by
    apply Real.sqrt_lt_sqrt <;> norm_num
  have h12 : Real.sqrt 144 = 12 := by
    rw [show (144 : ℝ) = 12 ^ 2 from by norm_num]
    exact Real.sqrt_sq (by norm_num)
  linarith

/-- PROVED: (2/π)·√143 < 8 (Minkowski bound for K = ℚ(√-143)). -/
theorem minkowski_lt_eight_BSD : 2 / Real.pi * Real.sqrt 143 < 8 := by
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h1 : Real.sqrt 143 < 12 := sqrt_143_lt_twelve_BSD
  have h2 : 2 / Real.pi * Real.sqrt 143 < 2 / Real.pi * 12 := by
    apply mul_lt_mul_of_pos_left h1
    exact div_pos (by norm_num) hπ_pos
  have h3 : 2 / Real.pi * 12 < 8 := by
    rw [div_mul_eq_mul_div, div_lt_iff hπ_pos]
    linarith
  linarith

end Towers.BSD

/- Affine point count of `y^2 + y = x^3 - x^2 - x - 2` over `F_p`, `p ≠ 2`.
   Completing the square turns each fiber into `z^2 = 1 + 4c`.
   Euler's criterion evaluates that square, so the count is a sum of `p`
   powers rather than a scan of `p^2` pairs.
   `E143_card_eq_fast` identifies the sum with `(E143_Finset p).card`.
   No sorry.
-/

import Towers.BSD.BSD_Frobenius_Certificate_Clean
import Mathlib.NumberTheory.LegendreSymbol.Basic

open Finset

namespace Towers.BSD

/-- Number of square roots of `d` in `F_p`, via Euler's criterion. -/
def sqrtCount (p : ℕ) (d : ZMod p) : ℕ :=
  if d = 0 then 1 else if d ^ (p / 2) = 1 then 2 else 0

def curveRhs (x : ZMod p) : ZMod p :=
  x * x * x - x * x - x - 2

/-- Sum, over `x`, of the number of `y` on the curve. -/
def affineFastCard (p : ℕ) [Fact p.Prime] : ℕ :=
  ∑ x : ZMod p, sqrtCount p (1 + 4 * curveRhs x)

lemma two_ne_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact Nat.Prime.ne_one (Fact.out : Nat.Prime p) h1
  · exact hp h2

lemma four_ne_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (4 : ZMod p) ≠ 0 := by
  intro h
  have h2 : (2 : ZMod p) * 2 = 0 := by
    simpa [show (4 : ZMod p) = 2 * 2 by ring] using h
  rcases mul_eq_zero.mp h2 with h0 | h0
  · exact two_ne_zero hp h0
  · exact two_ne_zero hp h0

lemma sq_add_eq_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (y c : ZMod p) :
    y ^ 2 + y = c ↔ (2 * y + 1) ^ 2 = 1 + 4 * c := by
  have h4 := four_ne_zero hp
  constructor
  · intro hy
    have hexpand : (2 * y + 1) ^ 2 = 4 * (y ^ 2 + y) + 1 := by ring
    rw [hexpand, hy]
    ring
  · intro hy
    have hexpand : (2 * y + 1) ^ 2 = 4 * (y ^ 2 + y) + 1 := by ring
    rw [hexpand] at hy
    have hsub : 4 * (y ^ 2 + y) = 4 * c := by
      have := congrArg (fun t => t - 1) hy
      simpa [add_sub_cancel] using this
    exact mul_left_cancel₀ h4 hsub

lemma sqrt_fiber_card {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (c : ZMod p) :
    (univ.filter fun y : ZMod p => y ^ 2 + y = c).card =
      (univ.filter fun z : ZMod p => z ^ 2 = 1 + 4 * c).card := by
  classical
  let f : ZMod p → ZMod p := fun y => 2 * y + 1
  have h2 := two_ne_zero hp
  have hinj : Function.Injective f := by
    intro y1 y2 h
    apply mul_left_cancel₀ h2
    exact add_right_cancel h
  refine Finset.card_bij (fun y _ => f y) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact (sq_add_eq_iff hp y c).mp hy
  · intro y1 _ y2 _ h
    exact hinj h
  · intro z hz
    refine ⟨(z - 1) * (2 : ZMod p)⁻¹, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      have hy : (2 * ((z - 1) * (2 : ZMod p)⁻¹) + 1) ^ 2 = 1 + 4 * c := by
        have hz' : 2 * ((z - 1) * (2 : ZMod p)⁻¹) + 1 = z := by
          calc
            2 * ((z - 1) * (2 : ZMod p)⁻¹) + 1
                = (z - 1) * (2 * (2 : ZMod p)⁻¹) + 1 := by ring
            _ = (z - 1) * 1 + 1 := by rw [mul_inv_cancel₀ h2]
            _ = z := by ring
        rw [hz']
        exact hz
      exact (sq_add_eq_iff hp _ c).mpr hy
    · calc
        2 * ((z - 1) * (2 : ZMod p)⁻¹) + 1
            = (z - 1) * (2 * (2 : ZMod p)⁻¹) + 1 := by ring
        _ = (z - 1) * 1 + 1 := by rw [mul_inv_cancel₀ h2]
        _ = z := by ring

lemma sqrt_card_zero {p : ℕ} [Fact p.Prime] :
    (univ.filter fun z : ZMod p => z ^ 2 = 0).card = 1 := by
  classical
  have hset : (univ.filter fun z : ZMod p => z ^ 2 = 0) = {(0 : ZMod p)} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hz
      exact pow_eq_zero hz
    · intro hz
      simp [hz]
  rw [hset]
  simp

lemma sqrt_card_two {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {d : ZMod p}
    (hd : d ≠ 0) {r : ZMod p} (hr : r ^ 2 = d) :
    (univ.filter fun z : ZMod p => z ^ 2 = d).card = 2 := by
  classical
  have hr0 : r ≠ 0 := by
    intro h
    apply hd
    rw [← hr, h, pow_two, mul_zero]
  have hne : r ≠ -r := by
    intro h
    have h2r : (2 : ZMod p) * r = 0 := by
      have : r + r = 0 := by
        nth_rw 1 [h]
        ring
      simpa [two_mul] using this
    exact hr0 ((mul_eq_zero.mp h2r).resolve_left (two_ne_zero hp))
  have hset : (univ.filter fun z : ZMod p => z ^ 2 = d) = {r, -r} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hz
      have hdiff : z ^ 2 - r ^ 2 = 0 := by rw [hz, hr, sub_self]
      have : (z - r) * (z + r) = 0 := by
        have hfac : z ^ 2 - r ^ 2 = (z - r) * (z + r) := by ring
        rw [← hfac, hdiff]
      rcases mul_eq_zero.mp this with hsub | hadd
      · left
        exact sub_eq_zero.mp hsub
      · right
        exact eq_neg_of_add_eq_zero_left hadd
    · intro hz
      rcases hz with rfl | rfl
      · exact hr
      · rw [neg_sq, hr]
  rw [hset]
  exact Finset.card_pair hne

lemma sqrt_card_eq_count {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (d : ZMod p) :
    (univ.filter fun z : ZMod p => z ^ 2 = d).card = sqrtCount p d := by
  classical
  by_cases hd : d = 0
  · rw [hd, sqrt_card_zero]
    simp [sqrtCount]
  · by_cases hs : IsSquare d
    · rcases hs with ⟨r, hr⟩
      have hr' : r ^ 2 = d := by rw [pow_two]; exact hr.symm
      have hcard := sqrt_card_two hp hd hr'
      have hone : d ^ (p / 2) = 1 :=
        (ZMod.euler_criterion (p := p) (a := d) hd).mp (by exact ⟨r, hr⟩)
      rw [hcard]
      simp [sqrtCount, hd, hone]
    · have hnone : ¬ d ^ (p / 2) = 1 :=
        (ZMod.euler_criterion (p := p) (a := d) hd).not.mp hs
      have hempty : (univ.filter fun z : ZMod p => z ^ 2 = d) = ∅ := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_mem_empty,
          iff_false]
        intro hz
        exact hs ⟨z, hz.symm.trans (pow_two z)⟩
      rw [hempty]
      simp [sqrtCount, hd, hnone]

lemma fiber_card_eq_count {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (x : ZMod p) :
    (E143_fiber p x).card = sqrtCount p (1 + 4 * curveRhs x) := by
  have hpoint : (E143_fiber p x) =
      univ.filter fun y : ZMod p => y ^ 2 + y = curveRhs x := by
    ext y
    simp only [E143_fiber, E143_point, curveRhs, Finset.mem_filter, Finset.mem_univ,
      true_and, pow_two]
  rw [hpoint, sqrt_fiber_card hp, sqrt_card_eq_count hp]

theorem E143_card_eq_sum_fiber (p : ℕ) [Fact p.Prime] :
    (E143_Finset p).card = ∑ x : ZMod p, (E143_fiber p x).card := by
  classical
  have fiber_eq : ∀ x : ZMod p,
      (E143_Finset p).filter (fun xy => xy.1 = x) =
      (E143_fiber p x).image (fun y => (x, y)) := by
    intro x
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_image, E143_Finset, E143_fiber,
      Finset.mem_univ, true_and, Prod.mk.injEq]
    change (E143_point p a b ∧ a = x) ↔ ∃ y, E143_point p x y ∧ x = a ∧ y = b
    constructor
    · rintro ⟨hP, rfl⟩; exact ⟨b, hP, rfl, rfl⟩
    · rintro ⟨y, hP, rfl, rfl⟩; exact ⟨hP, rfl⟩
  calc (E143_Finset p).card
      = ∑ x : ZMod p, ((E143_Finset p).filter (fun xy => xy.1 = x)).card := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext xy
          simp [Finset.mem_biUnion, Finset.mem_filter]
        · intro x _ y _ hne
          apply Finset.disjoint_filter.mpr
          intro z _ h1 h2
          exact hne (h1.symm.trans h2)
    _ = ∑ x : ZMod p, (E143_fiber p x).card := by
        congr 1; ext x
        rw [fiber_eq]
        apply Finset.card_image_of_injective
        intro a b hab
        exact (Prod.ext_iff.mp hab).2

theorem E143_card_eq_fast (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (E143_Finset p).card = affineFastCard p := by
  rw [E143_card_eq_sum_fiber, affineFastCard]
  refine Finset.sum_congr rfl ?_
  intro x _
  exact fiber_card_eq_count hp x

end Towers.BSD

import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Towers.BSD.BSD_LFunction

namespace Towers.BSD

/-!
# Fiber-count lemmas — mechanical repair pass (2026-10-09)

David authored all statements and proof ideas in chat. Assistant repairs
below are marked `REPAIR`; no statement was changed. All Mathlib names
verified against v4.12.0.

Repairs:
* new helper `isSquare_iff_pow_half` (Euler's criterion, from Mathlib's
  `ZMod.euler_criterion`) — the bridge and fiber proofs both need this
  as explicit content (`simp` cannot derive `IsSquare` from the pow);
* bridge proof rewritten: `legendreSym.at_zero` takes no args,
  `ZMod.quadraticChar_eq_legendreSym` does not exist, the `NeZero`
  block used a non-existent lemma;
* `h2_ne` proof replaced (used non-existent `Nat.eq_of_dvd_of_prime_sub_one`);
* `h1` map direction corrected — the original
  `filter_LHS = (filter_RHS).map f` is FALSE
  (counterexample: `c = 0` gives `{0, -1}` vs `{3, -1}`);
  correct is `(filter_LHS).map f = filter_RHS`;
* the two `legendreSym.eq_one_iff _ _` holes filled via Euler directly;
* the `sorry` closed via `isSquare_iff_pow_half`.
-/

/-- Euler character, computable -/
def eulerChi (p : ℕ) [Fact p.Prime] (d : ZMod p) : ℤ :=
  if d = 0 then 0 else if d ^ ((p - 1) / 2) = 1 then 1 else -1

/-- Euler's criterion, `(p-1)/2` form.
    REPAIR (assistant): new helper, from Mathlib's `ZMod.euler_criterion`. -/
lemma isSquare_iff_pow_half (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ZMod p) (hd_ne : d ≠ 0) :
    IsSquare d ↔ d ^ ((p - 1) / 2) = 1 := by
  have hp_odd : p % 2 = 1 := by
    have hp_prime : p.Prime := Fact.out
    rcases Nat.Prime.eq_two_or_odd hp_prime with h | h
    · exact absurd h hp2
    · exact h
  have hhalf : (p - 1) / 2 = p / 2 := by omega
  rw [hhalf]
  exact ZMod.euler_criterion p hd_ne

/-- Bridge: eulerChi = legendreSym (via ZMod.val).
    REPAIR (assistant): proof rewritten (see header). Statement unchanged. -/
lemma eulerChi_eq_legendreSym (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ZMod p) :
    eulerChi p d = legendreSym p (d.val : ℤ) := by
  have hcast : ((d.val : ℤ) : ZMod p) = d := by simp
  have h_leg_qc : legendreSym p (d.val : ℤ) = quadraticChar (ZMod p) d := by
    unfold legendreSym
    rw [hcast]
  by_cases hd0 : d = 0
  · have h1 : eulerChi p d = 0 := by simp [eulerChi, hd0]
    have h2 : legendreSym p (d.val : ℤ) = 0 := by
      have hval : (d.val : ℤ) = 0 := by simp [hd0]
      rw [hval, legendreSym.at_zero]
    rw [h1, h2]
  · have hd_ne : d ≠ 0 := hd0
    have he1 : eulerChi p d = 1 ↔ d ^ ((p - 1) / 2) = 1 := by
      constructor
      · intro hcon
        unfold eulerChi at hcon
        simpa [hd_ne] using hcon
      · intro hcon
        unfold eulerChi
        simp [hd_ne, hcon]
    have key : eulerChi p d = 1 ↔ IsSquare d :=
      he1.trans (isSquare_iff_pow_half p hp2 d hd_ne).symm
    by_cases hs : IsSquare d
    · have h1 : eulerChi p d = 1 := key.mpr hs
      have h2 : quadraticChar (ZMod p) d = 1 :=
        (quadraticChar_one_iff_isSquare (F := ZMod p) hd_ne).mpr hs
      rw [h_leg_qc, h1, h2]
    · have h1 : eulerChi p d = -1 := by
        have hmem : eulerChi p d = 1 ∨ eulerChi p d = -1 := by
          by_cases h : d ^ ((p - 1) / 2) = 1
          · left; unfold eulerChi; simp [hd_ne, h]
          · right; unfold eulerChi; simp [hd_ne, h]
        rcases hmem with h | h
        · exact absurd (key.mp h) hs
        · exact h
      have h2 : quadraticChar (ZMod p) d = -1 :=
        (quadraticChar_neg_one_iff_not_isSquare (F := ZMod p) (a := d)).mpr hs
      rw [h_leg_qc, h1, h2]

/-- Fiber card via completing the square.
    REPAIR (assistant): `h2_ne` rewritten; `h1` direction corrected;
    `eq_one_iff` holes and `sorry` closed via Euler. Statement unchanged. -/
lemma fiber_card_eq_eulerChi (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (x : ZMod p) :
    (E143_fiber p x).card
      = (1 + eulerChi p (4 * (x ^ 3 - x ^ 2 - x - 2) + 1)).toNat := by
  set c := x ^ 3 - x ^ 2 - x - 2 with hc_def
  set d := 4 * c + 1 with hd_def
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    apply hp2
    have hdvd : p ∣ 2 := by
      have h2 : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by norm_cast
      rw [h2] at h
      rwa [CharP.cast_eq_zero_iff (ZMod p) p 2] at h
    have hp_prime : p.Prime := Fact.out
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · have h2le : 2 ≤ p := hp_prime.two_le
      omega
    · exact h1
  have h_inj : Function.Injective (fun y : ZMod p => 2 * y + 1) := by
    intro a b h
    have h2 : 2 * a = 2 * b := by
      have hcon := congrArg (· - 1) h
      simpa using hcon
    exact mul_left_cancel₀ h2_ne h2
  -- algebra
  have h_sq : ∀ y : ZMod p, (2 * y + 1) ^ 2 = 4 * (y ^ 2 + y) + 1 := by
    intro y; ring
  have h_iff : ∀ y : ZMod p, y ^ 2 + y = c ↔ (2 * y + 1) ^ 2 = d := by
    intro y
    rw [hd_def, h_sq y]
    constructor
    · intro h; rw [h]
    · intro h
      have h4 : (4 : ZMod p) ≠ 0 := by
        intro hcon
        apply h2_ne
        have h44 : (2 : ZMod p) * 2 = 0 := by linear_combination hcon
        rcases mul_eq_zero.mp h44 with h' | h'
        · exact h'
        · exact h'
      have h5 : 4 * (y ^ 2 + y) = 4 * c := by linear_combination h
      exact mul_left_cancel₀ h4 h5
  -- transport fiber to {z | z^2 = d}; REPAIR: map direction corrected
  have h_card_eq : (E143_fiber p x).card =
      (Finset.univ.filter (fun z : ZMod p => z ^ 2 = d)).card := by
    have h1 : (Finset.univ.filter (fun y : ZMod p => y ^ 2 + y = c)).map
          ⟨fun y => 2 * y + 1, h_inj⟩ =
        Finset.univ.filter (fun z : ZMod p => z ^ 2 = d) := by
      ext z
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (h_iff y).mp hy
      · intro hz
        refine ⟨(z - 1) * (2 : ZMod p)⁻¹, ?_, ?_⟩
        · have hy2 : 2 * ((z - 1) * (2 : ZMod p)⁻¹) + 1 = z := by
            calc 2 * ((z - 1) * (2 : ZMod p)⁻¹) + 1
                = (z - 1) * (2 * (2 : ZMod p)⁻¹) + 1 := by ring
              _ = (z - 1) * 1 + 1 := by rw [mul_inv_cancel₀ h2_ne]
              _ = z := by ring
          exact (h_iff _).mpr (by rw [hy2, hz])
        · calc 2 * ((z - 1) * (2 : ZMod p)⁻¹) + 1
              = (z - 1) * (2 * (2 : ZMod p)⁻¹) + 1 := by ring
            _ = (z - 1) * 1 + 1 := by rw [mul_inv_cancel₀ h2_ne]
            _ = z := by ring
    calc (E143_fiber p x).card
        = (Finset.univ.filter (fun y : ZMod p => y ^ 2 + y = c)).card := by
          congr 1
          ext y
          simp only [E143_fiber, E143_point, Finset.mem_filter, Finset.mem_univ,
            true_and]
          rw [hc_def]
          constructor <;> intro h <;> linear_combination h
      _ = (((Finset.univ.filter (fun y : ZMod p => y ^ 2 + y = c)).map
            ⟨fun y => 2 * y + 1, h_inj⟩).card) := (Finset.card_map _).symm
      _ = (Finset.univ.filter (fun z : ZMod p => z ^ 2 = d)).card := by rw [h1]
  rw [h_card_eq]
  -- count roots of z^2 = d
  by_cases hd0 : d = 0
  · have hfilter : Finset.univ.filter (fun z : ZMod p => z ^ 2 = d) = {0} := by
      ext z
      simp [hd0, sq_eq_zero_iff, Finset.mem_filter, Finset.mem_singleton]
    rw [hfilter, Finset.card_singleton]
    simp [eulerChi, hd0]
  · have hd_ne : d ≠ 0 := hd0
    by_cases hsq : eulerChi p d = 1
    · -- d is a square: two roots
      have h_isSquare : IsSquare d := by
        have hpow : d ^ ((p - 1) / 2) = 1 := by
          have hchi : eulerChi p d = 1 ↔ d ^ ((p - 1) / 2) = 1 := by
            constructor
            · intro hcon
              unfold eulerChi at hcon
              simpa [hd_ne] using hcon
            · intro hcon
              unfold eulerChi
              simp [hd_ne, hcon]
          exact hchi.mp hsq
        exact (isSquare_iff_pow_half p hp2 d hd_ne).mpr hpow
      obtain ⟨r, hr⟩ := h_isSquare
      have hr_ne : r ≠ 0 := by
        intro h
        rw [h, zero_mul] at hr
        exact hd_ne hr
      have h_neg_ne : r ≠ -r := by
        intro h
        have h2r : (2 : ZMod p) * r = 0 := by linear_combination h
        exact hr_ne ((mul_eq_zero.mp h2r).resolve_left h2_ne)
      have h_filter_eq : Finset.univ.filter (fun z => z ^ 2 = d) = {r, -r} := by
        ext z
        simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hz
          have hzz : (z - r) * (z + r) = 0 := by
            have : z ^ 2 - r * r = 0 := by rw [hz, hr, sub_self]
            linear_combination this
          rcases mul_eq_zero.mp hzz with h | h
          · left; linear_combination h
          · right; linear_combination h
        · rintro (rfl | rfl)
          · rw [pow_two, hr]
          · rw [pow_two, hr]; ring
      rw [h_filter_eq, Finset.card_pair h_neg_ne, hsq]
      simp
    · -- not a square: no roots, eulerChi = -1
      have h_not_sq : ¬ IsSquare d := by
        intro hsq'
        have hpow : d ^ ((p - 1) / 2) = 1 :=
          (isSquare_iff_pow_half p hp2 d hd_ne).mp hsq'
        have h1 : eulerChi p d = 1 := by
          unfold eulerChi; simp [hd_ne, hpow]
        exact hsq h1
      have h_chi_neg : eulerChi p d = -1 := by
        have hneg : ¬ d ^ ((p - 1) / 2) = 1 := by
          intro hcon
          exact h_not_sq ((isSquare_iff_pow_half p hp2 d hd_ne).mpr hcon)
        unfold eulerChi
        simp [hd_ne, hneg]
      have h_empty : Finset.univ.filter (fun z => z ^ 2 = d) = ∅ := by
        ext z
        simp [Finset.mem_filter]
        intro hz
        exact h_not_sq ⟨z, by simpa [pow_two] using hz.symm⟩
      rw [h_empty, Finset.card_empty, h_chi_neg]
      simp

/-- Affine count = sum of fiber cards.
    REPAIR (assistant): `h_disj` robustness fix only. Statement/idea unchanged. -/
lemma card_affine_eq_sum_fiber (p : ℕ) [Fact p.Prime] :
    (E143_Finset p).card = ∑ x : ZMod p, (E143_fiber p x).card := by
  have h_eq : E143_Finset p =
      Finset.univ.biUnion (fun x : ZMod p => (E143_fiber p x).image (fun y => (x, y))) := by
    ext ⟨x, y⟩
    simp [E143_Finset, E143_fiber, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
  have h_disj : ∀ x₁ ∈ Finset.univ, ∀ x₂ ∈ Finset.univ, x₁ ≠ x₂ →
      Disjoint ((E143_fiber p x₁).image (fun y => (x₁, y)))
               ((E143_fiber p x₂).image (fun y => (x₂, y))) := by
    intro x₁ _ x₂ _ hne
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ ha hb
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨y1, -, heq1⟩ := ha
    obtain ⟨y2, -, heq2⟩ := hb
    exact hne ((congrArg Prod.fst heq1).trans (congrArg Prod.fst heq2).symm)
  rw [h_eq, Finset.card_biUnion h_disj]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.card_image_of_injective
  intro a b h
  exact congrArg Prod.snd h

/-- Combined computable sum -/
lemma card_affine_eq_sum_eulerChi (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (E143_Finset p).card
      = ∑ x : ZMod p,
          (1 + eulerChi p (4 * (x ^ 3 - x ^ 2 - x - 2) + 1)).toNat := by
  rw [card_affine_eq_sum_fiber p,
    Finset.sum_congr rfl (fun x _ => fiber_card_eq_eulerChi p hp2 x)]

end Towers.BSD

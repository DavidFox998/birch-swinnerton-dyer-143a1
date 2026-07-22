/-!
# BSD genesis-781: tau_le_two_sqrt and BSD_TauBound partial closure

**Module**: `BSD/BSD_Genesis781_CLOSED.lean`
**Imports**: `Towers.BSD.BSD_Genesis780_CLOSED`
**sorry count**: 0
**axioms**: {propext, Classical.choice, Quot.sound}

## Proof chain this batch

  **§1 tau_le_two_sqrt** -- PROVED (0 sorry, unconditional):
      forall n >= 1: tau(n) <= 2 * sqrt(n).
      Elementary pairing argument: split n.divisors at Nat.sqrt n.
      lo = {d | n : d <= sqrt n}, hi = {d | n : d > sqrt n}.
      Map d |-> n/d from hi to lo is well-defined (d > sqrt n -> n/d <= sqrt n)
      and injective (n/d1 = n/d2 + both divide n -> d1 = d2).
      So #hi <= #lo <= Nat.sqrt n <= Real.sqrt n.
      tau(n) = #lo + #hi <= 2 * Nat.sqrt n <= 2 * Real.sqrt n.

  **§2 BSD_TauBound_large_eps** -- PROVED (0 sorry, unconditional):
      forall eps >= 1/2, C = 2 works: tau(n) <= 2 * sqrt(n) = 2 * n^{1/2} <= 2 * n^eps.
      Uses §1 + Real.rpow_le_rpow_of_exponent_le.

  **§3 BSD_TauBound_small_OPEN** -- NAMED OPEN DEF:
      forall 0 < eps < 1/2: tau(n) <= C * n^eps.
      Gap: Dirichlet hyperbola / Ramanujan tau bound; not in Mathlib v4.12.0.
      tau(n) <= 2 * sqrt(n) only covers eps >= 1/2.

  **§4 BSD_TauBound_from_parts** -- PROVED (0 sorry):
      BSD_TauBound_small_OPEN -> BSD_TauBound_OPEN.
      Splits eps into eps >= 1/2 (closed, §2) and 0 < eps < 1/2 (open, §3).

  **§5 BSD_LSeriesSummable_v4** -- PROVED (0 sorry, conditional Gate 1):
      forall s with Re(s) > 2: L-series is summable.
      Uses §1 directly: |a_n n| <= sqrt(n) * tau(n) <= sqrt(n) * 2*sqrt(n) = 2n.
      Apply LSeriesSummable_of_le_const_mul_rpow with x = 2 < Re(s).
      Conditional Gate 1 (Hasse-Weil). Does not use BSD_TauBound_OPEN.

## Gap inventory after genesis-781

PROVED (unconditional):
  - tau_le_two_sqrt forall n >= 1                         (genesis-781 §1)
  - BSD_TauBound_large_eps (eps >= 1/2, C = 2)            (genesis-781 §2)
  All bridges + BSD_LSeriesSummable_v3 from genesis-780

OPEN (genuine mathematical gaps):
  - BSD_WeilHasse_Weierstrass_OPEN  Gate 1: Hasse-Weil (Clay-grade)
  - BSD_LFunctionIsLinFunc_OPEN     Gate 2: Hecke/Mellin (Clay-grade)
  - BSD_TauBound_small_OPEN         0 < eps < 1/2 (analytic NT gap)
  - 8 BSD formula surfaces (NT, Reg, SHA, Coeff, Period, Tamagawa, Torsion, Generator)

Clay gate count: 2 (unchanged). BSD: OPEN. No Clay claim.
0 sorry. Classical trio + Gate 1 hypothesis where noted.
-/

import Towers.BSD.BSD_Genesis780_CLOSED
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open BigOperators Real Nat ArithmeticFunction

namespace Towers.BSD

/-! ## §1. tau_le_two_sqrt — elementary pairing argument -/

/-- **PROVED** (0 sorry, unconditional): tau(n) <= 2 * sqrt(n) for all n >= 1.

    Key Nat.sqrt API:
    - Nat.le_sqrt : k <= Nat.sqrt n <-> k * k <= n
    - Nat.div_dvd_of_dvd : d | n -> n / d | n
    - Nat.mul_div_cancel' : d | n -> d * (n / d) = n
    - Nat.div_mul_le_self : n / d * d <= n -/
theorem tau_le_two_sqrt (n : ℕ) (hn : 0 < n) :
    (n.divisors.card : ℝ) ≤ 2 * Real.sqrt n := by
  set sq := Nat.sqrt n
  -- sq * sq <= n < (sq+1)*(sq+1)  (defining property of Nat.sqrt)
  have hsq_le : sq * sq ≤ n := Nat.le_sqrt.mp le_rfl
  -- Split divisors into lo (d <= sq) and hi (sq < d)
  set lo := n.divisors.filter (fun d => d ≤ sq)
  set hi := n.divisors.filter (fun d => sq < d)
  -- Partition: Disjoint + covering
  have hd : Disjoint lo hi := by
    simp only [Finset.disjoint_left, Finset.mem_filter]
    intro d ⟨_, hle⟩ ⟨_, hlt⟩
    exact absurd hle (Nat.not_le.mpr hlt)
  have hcov : lo ∪ hi = n.divisors := by
    ext d
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases le_or_lt d sq with hle | hlt
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr ⟨h, hlt⟩
  have hpart : n.divisors.card = lo.card + hi.card := by
    calc n.divisors.card = (lo ∪ hi).card := by rw [hcov]
      _ = lo.card + hi.card := Finset.card_union_of_disjoint hd
  -- Map phi : hi -> lo by d |-> n / d
  have hmap : ∀ d ∈ hi, n / d ∈ lo := by
    intro d hd_mem
    simp only [hi, Finset.mem_filter] at hd_mem
    obtain ⟨hdvd, hgt⟩ := hd_mem
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
    -- n < d * d (since sq < d -> d >= sq+1 -> d^2 > sq^2, and sq^2 + ... > n...)
    -- Proved by contradiction via Nat.le_sqrt
    have hn_lt_dsq : n < d * d := by
      by_contra hle
      push_neg at hle
      exact absurd (Nat.le_sqrt.mpr hle) (Nat.not_le.mpr hgt)
    -- n / d < d (from n < d * d and Nat.div_mul_le_self)
    have hlt_d : n / d < d := by
      by_contra hge
      push_neg at hge
      have : d * d ≤ n / d * d := Nat.mul_le_mul_right d hge
      have : n / d * d ≤ n := Nat.div_mul_le_self n d
      linarith
    -- (n/d)^2 <= n : (n/d)*(n/d) <= (n/d)*d <= n
    have hnd_sq_le : n / d * (n / d) ≤ n :=
      calc n / d * (n / d) ≤ n / d * d := Nat.mul_le_mul_left _ (Nat.le_of_lt hlt_d)
        _ ≤ n := Nat.div_mul_le_self n d
    simp only [lo, Finset.mem_filter]
    exact ⟨Nat.div_dvd_of_dvd hdvd, Nat.le_sqrt.mpr hnd_sq_le⟩
  -- Map d |-> n/d is injective on hi
  have hinj : Set.InjOn (fun d => n / d) (hi : Set ℕ) := by
    intro d1 hd1 d2 hd2 heq
    simp only [Finset.mem_coe, hi, Finset.mem_filter] at hd1 hd2
    have hd2_pos : 0 < d2 := Nat.pos_of_dvd_of_pos hd2.1 hn
    have hnd2_pos : 0 < n / d2 :=
      Nat.div_pos (Nat.le_of_dvd hn hd2.1) hd2_pos
    have h1 : d1 * (n / d1) = n := Nat.mul_div_cancel' hd1.1
    have h2 : d2 * (n / d2) = n := Nat.mul_div_cancel' hd2.1
    rw [heq] at h1
    exact Nat.eq_of_mul_eq_mul_right hnd2_pos (h1.trans h2.symm)
  -- #hi <= #lo (via the injective map hi -> lo)
  have hhi_le : hi.card ≤ lo.card := by
    have himage : hi.image (fun d => n / d) ⊆ lo := by
      intro e he
      rw [Finset.mem_image] at he
      obtain ⟨d, hd, rfl⟩ := he
      exact hmap d hd
    calc hi.card
        = (hi.image (fun d => n / d)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ lo.card := Finset.card_le_card himage
  -- #lo <= Nat.sqrt n (lo ⊆ Finset.Icc 1 sq)
  have hlo_le : lo.card ≤ sq := by
    have hlo_sub : lo ⊆ Finset.Icc 1 sq := by
      intro d hd
      simp only [lo, Finset.mem_filter] at hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hd.1 hn, hd.2⟩
    calc lo.card ≤ (Finset.Icc 1 sq).card := Finset.card_le_card hlo_sub
      _ = sq := by rw [Finset.card_Icc]; omega
  -- Nat.sqrt n <= Real.sqrt n (as reals)
  have hsq_real : (sq : ℝ) ≤ Real.sqrt n := by
    rw [← Real.sqrt_sq (by exact_mod_cast Nat.zero_le sq)]
    apply Real.sqrt_le_sqrt
    have : sq ^ 2 = sq * sq := by ring
    exact_mod_cast this ▸ hsq_le
  -- Conclude: tau(n) <= 2 * Real.sqrt n
  have hcard_real : (n.divisors.card : ℝ) = (lo.card : ℝ) + (hi.card : ℝ) := by
    exact_mod_cast hpart
  linarith [Nat.cast_le.mpr hhi_le, Nat.cast_le.mpr hlo_le]

/-! ## §2. BSD_TauBound_large_eps -- eps >= 1/2 case proved -/

/-- **PROVED** (0 sorry, unconditional): BSD_TauBound_OPEN for eps >= 1/2.
    C = 2 works: tau(n) <= 2*sqrt(n) = 2*n^{1/2} <= 2*n^eps for eps >= 1/2 and n >= 1.
    Uses tau_le_two_sqrt + Real.rpow_le_rpow_of_exponent_le. -/
theorem BSD_TauBound_large_eps :
    ∀ ε : ℝ, (1 / 2 : ℝ) ≤ ε → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  refine ⟨2, by norm_num, fun n hn => ?_⟩
  have htau := tau_le_two_sqrt n hn
  -- sqrt(n) = n^{1/2}
  have hsqrt : Real.sqrt n = (n : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow n
  rw [hsqrt] at htau
  -- n^{1/2} <= n^eps (since 1/2 <= eps and n >= 1)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmono : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hn1 hε
  linarith

/-! ## §3. BSD_TauBound_small_OPEN -- named open def for 0 < eps < 1/2 -/

/-- **NAMED OPEN DEF**: tau(n) = O(n^eps) for 0 < eps < 1/2.

    tau(n) <= 2*sqrt(n) = 2*n^{1/2} from §1 covers only eps >= 1/2.
    For eps < 1/2, one approach: factorization product bound
      tau(n) = prod_p (e_p+1) <= C_eps * prod_p p^{eps*e_p} = C_eps * n^eps
    where C_eps = prod_{p <= 2^{2/eps}} sup_{e>=0} (e+1)/p^{eps*e} (finite for eps > 0).
    This requires: for each prime p and exponent e, (e+1) <= C_{p,eps} * p^{eps*e}
    (elementary: C_{p,eps} = exp(1/(eps*ln p)) suffices).
    Gap: this per-prime bound + product over primes not in Mathlib v4.12.0.
    STATUS: OPEN. -/
def BSD_TauBound_small_OPEN : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε

/-! ## §4. BSD_TauBound_from_parts -- combines §2 and §3 -/

/-- **PROVED** (0 sorry): BSD_TauBound_small_OPEN -> BSD_TauBound_OPEN.
    Split: eps >= 1/2 is proved (§2); 0 < eps < 1/2 is the named open (§3). -/
theorem BSD_TauBound_from_parts (h_small : BSD_TauBound_small_OPEN) :
    BSD_TauBound_OPEN := by
  intro ε hε
  by_cases hle : (1 / 2 : ℝ) ≤ ε
  · exact BSD_TauBound_large_eps ε hle
  · push_neg at hle
    exact h_small ε hε hle

/-! ## §5. BSD_LSeriesSummable_v4 -- Re(s) > 2, conditional Gate 1 -/

/-- **PROVED** (0 sorry, conditional Gate 1): BSD L-series summable for Re(s) > 2.

    Uses tau_le_two_sqrt directly:
      |a_n n| <= sqrt(n) * tau(n) <= sqrt(n) * 2*sqrt(n) = 2*n
    Apply LSeriesSummable_of_le_const_mul_rpow with x = 2 < Re(s).
    Does NOT use BSD_TauBound_OPEN (avoids the eps < 1/2 gap).
    Weaker than BSD_LSeriesSummable_OPEN (Re(s) > 3/2) but proved independently.
    Conditional on Gate 1 (BSD_PrimePowBound_OPEN = Hasse-Weil, Clay-grade). -/
theorem BSD_LSeriesSummable_v4
    (hGate1 : ∀ (q : ℕ) (hq : Fact q.Prime) (j : ℕ), BSD_PrimePowBound_OPEN q j)
    (s : ℂ) (hs : (2 : ℝ) < s.re) :
    Summable (fun n : ℕ+ => (a_n n.val : ℂ) / (n.val : ℂ) ^ s) := by
  -- §5a: |a_n m| <= 2*m for all m : N+
  have haN_bound : ∀ m : ℕ+, |(a_n m.val : ℝ)| ≤ 2 * (m.val : ℝ) := by
    intro m
    -- BSD_aNBound_OPEN m.val : |a_n m| <= sqrt(m) * tau(m)
    have h1 : |(a_n m.val : ℝ)| ≤ Real.sqrt m.val * m.val.divisors.card := by
      have h := BSD_aNBound_all_n_v3 hGate1 m.val
      simpa [BSD_aNBound_OPEN] using h
    -- tau_le_two_sqrt: tau(m) <= 2 * sqrt(m)
    have h2 : (m.val.divisors.card : ℝ) ≤ 2 * Real.sqrt m.val :=
      tau_le_two_sqrt m.val m.pos
    -- sqrt(m)^2 = m
    have hsq : Real.sqrt m.val ^ 2 = m.val :=
      Real.sq_sqrt (by exact_mod_cast Nat.zero_le m.val)
    -- Combine: |a_n m| <= sqrt * tau <= sqrt * 2*sqrt = 2*sqrt^2 = 2*m
    have hr : (0 : ℝ) ≤ Real.sqrt m.val := Real.sqrt_nonneg _
    have hcombine : Real.sqrt m.val * m.val.divisors.card ≤ 2 * m.val := by
      calc Real.sqrt m.val * m.val.divisors.card
          ≤ Real.sqrt m.val * (2 * Real.sqrt m.val) :=
            mul_le_mul_of_nonneg_left h2 hr
        _ = 2 * Real.sqrt m.val ^ 2 := by ring
        _ = 2 * m.val := by rw [hsq]
    linarith
  -- §5b: LSeriesSummable with x = 2
  have hLS : LSeriesSummable (fun m : ℕ => (a_n m : ℂ)) s := by
    apply LSeriesSummable_of_le_const_mul_rpow hs
    refine ⟨2, by norm_num, fun m hm => ?_⟩
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    -- ||a_n m||_C = |a_n m|_R
    have hcast : ‖(a_n m : ℂ)‖ = |(a_n m : ℝ)| := by
      have heq : (a_n m : ℂ) = ((a_n m : ℝ) : ℂ) := by norm_cast
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
    rw [hcast]
    -- 2 * (m : R)^(2-1) = 2 * m
    have hexp : (2 : ℝ) - 1 = 1 := by norm_num
    rw [hexp, Real.rpow_one]
    exact haN_bound ⟨m, hm_pos⟩
  -- §5c: Pull back LSeriesSummable (N) to Summable (N+)
  simp only [LSeriesSummable] at hLS
  have h_pos_summ : Summable (fun m : ℕ+ =>
      LSeries.term (fun m : ℕ => (a_n m : ℂ)) s m.val) :=
    hLS.comp_injective Subtype.val_injective
  exact h_pos_summ.congr (fun m => by
    simp only [Function.comp, LSeries.term_of_ne_zero m.pos.ne'])

/-! ## Summary -/

/-!
### Genesis-781: tau_le_two_sqrt and BSD_TauBound partial closure

**tau_le_two_sqrt** (0 sorry, unconditional):
  tau(n) <= 2 * Real.sqrt n  for n >= 1.
  Key steps: pairing d <-> n/d; #hi <= #lo <= sqrt(n).

**BSD_TauBound_large_eps** (0 sorry, unconditional):
  forall eps >= 1/2: tau(n) <= 2 * n^eps  (C = 2).

**BSD_TauBound_small_OPEN** (OPEN):
  0 < eps < 1/2 case. Per-prime bound (e+1) <= C_{p,eps} * p^{eps*e}
  requires exp/log estimates not in Mathlib v4.12.0.

**BSD_TauBound_from_parts** (0 sorry):
  BSD_TauBound_small_OPEN -> BSD_TauBound_OPEN.
  Full closure awaits §3 (Dirichlet hyperbola / Ramanujan bound).

**BSD_LSeriesSummable_v4** (0 sorry, conditional Gate 1):
  Re(s) > 2 -> Summable.  Bypasses BSD_TauBound_OPEN entirely.
  Uses tau(n) <= 2n directly.

**Mathlib v4.12.0 APIs used:**
  Nat.le_sqrt           -- k <= Nat.sqrt n <-> k*k <= n
  Nat.div_dvd_of_dvd    -- d | n -> n/d | n
  Nat.mul_div_cancel'   -- d | n -> d * (n/d) = n
  Nat.div_mul_le_self   -- n/d * d <= n
  Nat.div_pos           -- d <= n, 0 < d -> 0 < n/d
  Finset.card_Icc       -- (Finset.Icc a b).card = b + 1 - a
  Finset.card_image_of_injOn  -- injective -> card preserved
  Real.sqrt_le_sqrt     -- sqrt monotone
  Real.sqrt_sq          -- sqrt(x^2) = x for x >= 0
  Real.sqrt_eq_rpow     -- sqrt(n) = n^{1/2}
  Real.rpow_le_rpow_of_exponent_le  -- n^a <= n^b for a <= b, n >= 1
  LSeriesSummable_of_le_const_mul_rpow  -- convergence from pointwise bound
  Summable.comp_injective  -- pull back summability
  LSeries.term_of_ne_zero  -- LSeries.term simplification

Clay gate count: 2 (unchanged). BSD: OPEN. No Clay claim.
0 sorry. Classical trio. Gate 1 hypothesis in §5.
-/

end Towers.BSD

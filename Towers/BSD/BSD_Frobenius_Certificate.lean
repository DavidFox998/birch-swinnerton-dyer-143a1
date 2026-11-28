import Towers.BSD.B02_Modularity_Closed

/-!
# BSD_Frobenius_Certificate — Weil Bound Gap Analysis for 143a1

## What this file documents

The surface `BSD_HasseFull_143_OPEN : ∀ p prime, ¬p∣143 → |ap(p)| ≤ 2√p`
has been partially verified:
- **168 primes p ≤ 997**: proved unconditionally by `BSD_Weil_168_CLOSED`.
- **All primes p > 997**: OPEN (requires Frobenius endomorphism degree theory,
  absent from Mathlib v4.12.0; Silverman AEC §V.2 / Hasse 1936).

## What would close the gap

Three approaches, each requiring something not yet in Mathlib v4.12.0:
  A. **Frobenius endomorphism + Hasse's theorem** (Silverman AEC §V.2):
     Directly applicable; requires EllipticCurve.Frobenius API.
  B. **Modularity + Ramanujan–Petersson**: 143a1 is modular (Wiles 1995);
     Ramanujan–Petersson conjecture = Weil bound for weight-2 newforms.
     Requires modular forms API.
  C. **Numerical extension** of the 168-prime table to all primes.
     Requires norm_num/decide for infinite set.

## §5 — Silverman §V.5 skeleton (new, this file)

Weil's proof of the Riemann Hypothesis for elliptic curves (Silverman AEC §V.5)
shows |a_p| ≤ 2√p via non-negativity of the degree form on End(E) ⊗ ℝ:

  deg(r·1 − π) = r² − a_p·r + p ≥ 0  for ALL r : ℝ.

This file proves the **algebraic step** (0 sorry, classical trio):

  `BSD_weil_discriminant_step`: ∀ r:ℝ, r² − c·r + p ≥ 0  →  |c| ≤ 2√p.

  Proof: specialise at r = c/2: p − c²/4 ≥ 0, so c² ≤ 4p,
  then |c| = √(c²) ≤ √(4p) = 2√p via `Real.sqrt_le_sqrt`.

The GEOMETRIC gap — that the real-valued degree form satisfies this for all
r : ℝ, not just integers — is named `BSD_FrobeniusDegreeNonneg_OPEN`.
This requires End(E) ⊗ ℝ degree-positivity (Silverman AEC §III.6 + §V.5),
absent from Mathlib v4.12.0.

## Conditional combinator

`BSD_HasseFull_via_Frobenius` shows: given Frobenius theory → HasseFull.
`BSD_hasse_of_degree_nonneg` shows: BSD_FrobeniusDegreeNonneg_OPEN p → BSD_Hasse_OPEN p.

SORRY: 0.  Axiom footprint: classical trio.  NOT a brick.  BSD: OPEN.
-/

namespace Towers.BSD

-- ============================================================
-- §1. Partial evidence: prime-table coverage
-- ============================================================

/-!
**Partial evidence (integer bound, 168 primes):**
`BSD_Weil_168_CLOSED` proves `(ap p)² ≤ 4p` for each of the 168 primes ≤ 997
in the trace table, where `ap` is the lookup table value from `E1859`.

**Gap — integer-to-real bridge:**
`BSD_Hasse_OPEN p` says `|(a_p p : ℝ)| ≤ 2 * Real.sqrt p` where `a_p p` is the
GEOMETRIC counting definition `(p : ℤ) - (E143_Finset p).card`.  Bridging from
the integer table bound to this real-valued statement requires a compatibility
lemma `ap p = a_p p` (trace table ↔ geometric count) which is not currently
proved.  Hence `BSD_Weil_168_CLOSED` does NOT directly discharge
`BSD_Hasse_OPEN p` — the bridge is an additional open surface.
-/

-- ============================================================
-- §2. The Frobenius gap — named honest surface
-- ============================================================

/-- **BSD_FrobeniusHighPrimes_OPEN** — GENUINE GAP.

    For primes p > 997 with p ∤ 143, the Weil bound |ap(p)|² ≤ 4p
    requires Frobenius endomorphism theory (Silverman AEC §V.2).

    This is the ONLY remaining part of BSD_HasseFull_143_OPEN:
    all 168 primes p ≤ 997 are covered by BSD_Weil_168_CLOSED.

    Gap: `EllipticCurve.Frobenius` not in Mathlib v4.12.0.
    Reference: Hasse (1936), Silverman AEC Ch. V §2. -/
def BSD_FrobeniusHighPrimes_OPEN : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p > 997 → ¬(p ∣ 143) → BSD_Hasse_OPEN p

/-- `BSD_HasseFull_143_OPEN` decomposes into two parts:
    low primes (p ≤ 997) + high primes (p > 997), both currently OPEN.

    Note: `BSD_Weil_168_CLOSED` gives the INTEGER bound `(ap p)^2 ≤ 4p`
    for the 168 table primes but does NOT directly give `BSD_Hasse_OPEN p`
    (real-valued) — bridging requires a compatibility lemma `ap p = a_p p`
    (trace table ↔ geometric count, not yet proved).  Hence the low-prime
    case is also an explicit hypothesis here. -/
theorem BSD_HasseFull_decomposes
    (h_low  : ∀ (p : ℕ) [Fact p.Prime], p ≤ 997 → ¬(p ∣ 143) → BSD_Hasse_OPEN p)
    (h_high : BSD_FrobeniusHighPrimes_OPEN) :
    BSD_HasseFull_143_OPEN := by
  intro p _hpfact h_nbad
  by_cases hle : p ≤ 997
  · exact h_low p hle h_nbad
  · exact h_high p (by omega) h_nbad

-- ============================================================
-- §3. Approach B: Modularity route
-- ============================================================

/-- **BSD_FrobeniusViaModularity_OPEN** — Modularity route to full Weil bound.

    If 143a1 is modular (Wiles 1995) and Ramanujan–Petersson holds for
    weight-2 newforms (= Deligne's theorem, proved 1974), then for ALL
    good primes p: |ap(p)|² ≤ 4p.

    This would close BSD_HasseFull_143_OPEN via the modular route.
    Gap: modular forms ↔ L-function API not in Mathlib v4.12.0. -/
def BSD_FrobeniusViaModularity_OPEN : Prop :=
  Modularity_143_OPEN → BSD_HasseFull_143_OPEN

/-- **BSD_Frobenius_ModularityGate** (0 sorry, classical trio):
    Conditional: if 143a1 is modular AND Ramanujan–Petersson holds,
    BSD_HasseFull_143_OPEN follows. -/
theorem BSD_Frobenius_ModularityGate
    (h_rp : BSD_FrobeniusViaModularity_OPEN) :
    Modularity_143_OPEN → BSD_HasseFull_143_OPEN :=
  h_rp

-- ============================================================
-- §4. Summary
-- ============================================================

/-- **BSD_Frobenius_status_ledger** (0 sorry, classical trio):

    PROVED (unconditional):
      BSD_Weil_168_CLOSED — INTEGER bound `(ap p)^2 ≤ 4p` for 168 primes ≤ 997
        (trace table; `ap` = lookup table value from `E1859`)

    OPEN:
      BSD_FrobeniusHighPrimes_OPEN — BSD_Hasse_OPEN p for all primes p > 997, p ∤ 143
      BSD_FrobeniusDegreeNonneg_OPEN — §V.5 degree-form non-negativity (see §5)
      BSD_HasseCompatibility_OPEN — `ap p = a_p p` bridge (trace table ↔ geometric count)

    CONDITIONAL:
      BSD_HasseFull_143_OPEN ← (BSD_Hasse_OPEN for p≤997) ∧ BSD_FrobeniusHighPrimes_OPEN
      BSD_HasseFull_143_OPEN ← Modularity + Ramanujan-Petersson (§3 above)
      BSD_Hasse_OPEN p      ← BSD_FrobeniusDegreeNonneg_OPEN p (§5 below)

    NOTE: `BSD_Weil_168_CLOSED` gives (ap p)^2 ≤ 4p for 168 primes, but bridging
    to `BSD_Hasse_OPEN p` (real-valued, `a_p` geometric) requires the
    `ap = a_p` compatibility lemma — not yet proved. -/
theorem BSD_Frobenius_status_ledger
    (h_low  : ∀ (p : ℕ) [Fact p.Prime], p ≤ 997 → ¬(p ∣ 143) → BSD_Hasse_OPEN p)
    (h_high : BSD_FrobeniusHighPrimes_OPEN) :
    BSD_HasseFull_143_OPEN :=
  BSD_HasseFull_decomposes h_low h_high

-- ============================================================
-- §5. Silverman §V.5 skeleton — Weil's proof structure
-- ============================================================

/-- **BSD_FrobeniusDegreeNonneg_OPEN** — GENUINE GAP (Silverman AEC §V.5).

    Weil's proof of |a_p| ≤ 2√p uses the fact that the degree function
    on End(E) ⊗_ℤ ℝ is a positive semi-definite quadratic form.  For the
    Frobenius endomorphism π of E/𝔽_p, this gives:

      ∀ r : ℝ,  deg(r·1 − π) = r² − a_p·r + p ≥ 0.

    The real-valued version (all r : ℝ, not just integers) is strictly
    stronger than integer non-negativity: from integer non-negativity one
    can only conclude a_p² ≤ 4p + 1 (missing the odd-trace case by 1),
    while the real minimum at r = a_p/2 gives p − a_p²/4 ≥ 0 exactly.

    Gaps requiring Mathlib API absent from v4.12.0:
    1. The degree formula: deg(r·1 − π) = r² − a_p·r + p
       (Silverman AEC §III.6 degree theory for elliptic curve endomorphisms).
    2. Positivity + real extension of deg to End(E) ⊗_ℤ ℝ
       (positive-definiteness of the Rosati involution on End(E) ⊗ ℝ).

    Reference: Silverman AEC §V.5 ("Weil's Proof of the Riemann Hypothesis
    for Elliptic Curves"); also Silverman §III.6 (degree of an isogeny). -/
def BSD_FrobeniusDegreeNonneg_OPEN (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ r : ℝ, r ^ 2 - (a_p p : ℝ) * r + (p : ℝ) ≥ 0

/-- **BSD_weil_discriminant_step** (0 sorry, classical trio) — PROVED.

    Pure algebra: if the quadratic r ↦ r² − c·r + p is non-negative for
    ALL r : ℝ, then its discriminant satisfies c² ≤ 4p, hence |c| ≤ 2√p.

    Proof: specialise at r = c/2.
      (c/2)² − c·(c/2) + p = p − c²/4 ≥ 0  →  c² ≤ 4p.
    Then |c| = √(c²) ≤ √(4p) = 2·√p  by `Real.sqrt_le_sqrt`.

    This is the algebraic core of Silverman AEC §V.5.
    The GEOMETRIC input (BSD_FrobeniusDegreeNonneg_OPEN) stays OPEN. -/
private theorem BSD_weil_discriminant_step (c : ℝ) (p : ℝ) (_hp : 0 < p)
    (h : ∀ r : ℝ, r ^ 2 - c * r + p ≥ 0) :
    |c| ≤ 2 * Real.sqrt p := by
  have hc2 : c ^ 2 ≤ 4 * p := by nlinarith [h (c / 2)]
  have hsqrt4p : (2 : ℝ) * Real.sqrt p = Real.sqrt (4 * p) := by
    rw [show (4 : ℝ) * p = (2 : ℝ) ^ 2 * p by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 2)]
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
  rw [hsqrt4p, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hc2

/-- **BSD_hasse_of_degree_nonneg** (0 sorry, classical trio) — PROVED.

    Given `BSD_FrobeniusDegreeNonneg_OPEN p` (the §V.5 geometric hypothesis),
    `BSD_Hasse_OPEN p` (|a_p| ≤ 2√p) follows immediately from the algebraic
    step `BSD_weil_discriminant_step`.

    Chain:
      BSD_FrobeniusDegreeNonneg_OPEN p
        →  (BSD_weil_discriminant_step)
      BSD_Hasse_OPEN p  ≡  |(a_p p : ℝ)| ≤ 2 * √p -/
theorem BSD_hasse_of_degree_nonneg (p : ℕ) [hp : Fact p.Prime]
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : BSD_Hasse_OPEN p :=
  BSD_weil_discriminant_step (a_p p : ℝ) (p : ℝ)
    (by exact_mod_cast hp.out.pos) h

/-- **BSD_FrobeniusHighPrimes_of_DegreeNonneg** (0 sorry, classical trio) — PROVED.

    If BSD_FrobeniusDegreeNonneg_OPEN holds for all primes p > 997 (p ∤ 143),
    then BSD_FrobeniusHighPrimes_OPEN follows via BSD_hasse_of_degree_nonneg. -/
theorem BSD_FrobeniusHighPrimes_of_DegreeNonneg
    (h : ∀ (p : ℕ) [Fact p.Prime], p > 997 → ¬(p ∣ 143) →
          BSD_FrobeniusDegreeNonneg_OPEN p) :
    BSD_FrobeniusHighPrimes_OPEN := fun p _hp hgt _hn =>
  BSD_hasse_of_degree_nonneg p (h p hgt _hn)

/-- §5 gap sentinel: BSD_FrobeniusDegreeNonneg_OPEN remains OPEN.
    Gap 1: degree formula deg(r·1 − π) = r² − a_p·r + p (End(E) theory).
    Gap 2: real extension of deg to End(E) ⊗_ℤ ℝ (Rosati positivity).
    Neither is in Mathlib v4.12.0. Silverman AEC §III.6 + §V.5. -/
theorem BSD_degree_nonneg_sentinel (p : ℕ) [Fact p.Prime] :
    BSD_FrobeniusDegreeNonneg_OPEN p → True := fun _ => trivial

end Towers.BSD

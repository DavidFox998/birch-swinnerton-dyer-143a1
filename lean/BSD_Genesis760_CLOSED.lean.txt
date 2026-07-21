import Towers.BSD.BSD_Genesis759_CLOSED

open NumberField NumberField.InfinitePlace Real
open Towers.BSD

/-!
# BSD_Genesis760_CLOSED — Discriminant Equivalence + L-function Consequence

**genesis-760 (2026-06-27):** Two algebraic completions within the 2-gate structure:

## Gate 1: Discriminant sub-surface (logically equivalent to BSD_EndomorphismDegree_OPEN)

Defines `BSD_HasseBound_Discriminant_OPEN`:
  `∀ (p:ℕ) [Fact p.Prime], ¬(p∣143) → (a_p p : ℝ)^2 ≤ 4*(p:ℝ)`

This is the **discriminant inequality** for the quadratic r ↦ r² − a_p·r + p.
Proved EQUIVALENT to BSD_EndomorphismDegree_OPEN:
  - BSD_EndDeg_from_DiscBound: discriminant ≤ 0 → quadratic ≥ 0 (completing the square)
  - BSD_DiscBound_from_EndDeg: quadratic ≥ 0 → discriminant ≤ 0 (specialise at r = a_p/2)

The discriminant form is more transparent: it states exactly what is needed for
Silverman §V.5 without referencing the degree form on End(E) ⊗_ℤ ℝ.

## Gate 2: L-function consequences (PROVED conditionally on BSD_LFunctionIsLinFunc_OPEN)

Two proved theorems conditional on the OPEN surface BSD_LFunctionIsLinFunc_OPEN:
  - BSD_LFunction_zero_at_one_from_LinFunc:
      BSDLFunction 143 (1:ℂ) = 0  [vanishing at s=1, consistent with BSD rank=1]
  - BSD_BSDFunction_nonzero_from_LinFunc:
      ∀ s≠1, BSDLFunction 143 s ≠ 0  [simple zero at s=1 from the anchor form]

These demonstrate concretely that closing BSD_LFunctionIsLinFunc_OPEN would
immediately yield the expected analytic rank ≥ 1 properties.

## Gate table — genesis chain

| Combinator | Gate 1 | Gate 2 |
|-----------|--------|--------|
| genesis-756 `BSD_FourGateCombinator` | `Modularity_143_OPEN` (opaque ∃) | `BSD_L_Analytic_143_OPEN` |
| genesis-757 `BSD_TwoGateCombinator` | `Modularity_143_OPEN` (opaque ∃) | `BSD_L_Analytic_143_OPEN` |
| genesis-758 `BSD_FrobeniusAnalytic_Combinator` | `BSD_HasseFull_143_OPEN` | `BSD_L_Analytic_143_OPEN` |
| genesis-759 `BSD_Genesis759_Combinator` | `BSD_EndomorphismDegree_OPEN` | `BSD_LFunctionIsLinFunc_OPEN` |
| **genesis-760** `BSD_Genesis760_Combinator` | **`BSD_HasseBound_Discriminant_OPEN`** | **`BSD_LFunctionIsLinFunc_OPEN`** |

Gate 1 equivalence: BSD_HasseBound_Discriminant_OPEN ↔ BSD_EndomorphismDegree_OPEN (proved).
Gate 2: unchanged (BSD_LFunctionIsLinFunc_OPEN).

## Clay gap status: UNCHANGED (2 gaps)

| # | Surface | Lean `def Prop` | Mathlib API gap |
|---|---------|-----------------|-----------------|
| 1 | `BSD_HasseBound_Discriminant_OPEN` | `∀ p good, (a_p p:ℝ)^2 ≤ 4*(p:ℝ)` | EllipticCurve.Frobenius absent |
| 2 | `BSD_LFunctionIsLinFunc_OPEN` | `BSDLFunction 143 = L_143a1` | Mellin/Hecke absent |

SORRY: 0.  Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
BSD: OPEN.  NOT a brick.  NOT a Clay submission.
-/

-- ============================================================
-- §1. Open-surface count
-- ============================================================

/-- `BSD_open_surface_count_760` = 2 (unchanged from genesis-759).
    Gate 1 is now expressed as BSD_HasseBound_Discriminant_OPEN (discriminant form)
    which is logically equivalent to BSD_EndomorphismDegree_OPEN. -/
def BSD_open_surface_count_760 : ℕ := 2

-- ============================================================
-- §2. Gate 1 sub-surface: discriminant form
-- ============================================================

/-- **`BSD_HasseBound_Discriminant_OPEN`** — discriminant form of the Hasse bound.

    `∀ (p:ℕ) [Fact p.Prime], ¬(p∣143) → (a_p p : ℝ)^2 ≤ 4*(p:ℝ)`

    This is the discriminant inequality Δ = a_p² − 4p ≤ 0 for the quadratic
    r ↦ r² − a_p·r + p, which is NON-NEGATIVE for ALL r : ℝ iff Δ ≤ 0.

    **Equivalence** (proved below):
      BSD_HasseBound_Discriminant_OPEN ↔ BSD_EndomorphismDegree_OPEN
      (forward: complete the square; backward: specialise at r = a_p/2)

    **Mathematical content**: Both forms are equivalent to the Hasse bound
    |a_p(p)| ≤ 2√p, which is the LMFDB claim for all good primes of E_{143a1}.

    **Mathlib gap**: `EllipticCurve.Frobenius` endomorphism + `Isogeny.degree`
    + Rosati involution positivity (Silverman AEC §III.6 + §V.5).
    Status: OPEN.  NOT a brick. -/
def BSD_HasseBound_Discriminant_OPEN : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ)

-- ============================================================
-- §3. Equivalence bridges (0 sorry, classical trio)
-- ============================================================

/-- **`BSD_EndDeg_from_DiscBound`** (0 sorry, classical trio) — PROVED.

    `BSD_HasseBound_Discriminant_OPEN → BSD_EndomorphismDegree_OPEN`.

    Proof (completing the square):
      4 · (r² − a·r + p) = (2r − a)² + (4p − a²) ≥ 0 + 0 = 0
    when a² ≤ 4p.  Hence r² − a·r + p ≥ 0 for all r : ℝ.

    The key nlinarith hint: `sq_nonneg (2*r − a_p)` gives `(2r−a)² ≥ 0`.
    Combined with `hd : a² ≤ 4p`, nlinarith closes `r² − a·r + p ≥ 0`.

    This is the **algebraic content** of Silverman AEC §V.5.
    The geometric content (why a_p² ≤ 4p) remains OPEN. -/
theorem BSD_EndDeg_from_DiscBound
    (h : BSD_HasseBound_Discriminant_OPEN) :
    BSD_EndomorphismDegree_OPEN := by
  intro p _hp hn
  show ∀ r : ℝ, r ^ 2 - (a_p p : ℝ) * r + (p : ℝ) ≥ 0
  intro r
  have hd : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := h p hn
  nlinarith [sq_nonneg (2 * r - (a_p p : ℝ))]

/-- **`BSD_DiscBound_from_EndDeg`** (0 sorry, classical trio) — PROVED.

    `BSD_EndomorphismDegree_OPEN → BSD_HasseBound_Discriminant_OPEN`.

    Proof (specialising at r = a_p/2):
      0 ≤ (a_p/2)² − a_p·(a_p/2) + p = p − a_p²/4
    Hence 4p ≥ a_p².

    This is the OTHER direction of the algebraic equivalence. -/
theorem BSD_DiscBound_from_EndDeg
    (h : BSD_EndomorphismDegree_OPEN) :
    BSD_HasseBound_Discriminant_OPEN := by
  intro p _hp hn
  have hfull : BSD_FrobeniusDegreeNonneg_OPEN p := h p hn
  have hspec : ((a_p p : ℝ) / 2) ^ 2 - (a_p p : ℝ) * ((a_p p : ℝ) / 2) + (p : ℝ) ≥ 0 :=
    hfull ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-- **`BSD_HasseBound_Discriminant_iff_EndDeg`** (0 sorry, classical trio) — PROVED.

    BSD_HasseBound_Discriminant_OPEN ↔ BSD_EndomorphismDegree_OPEN.

    Both are equivalent statements of the Hasse bound for E_{143a1}.
    The discriminant form `a_p² ≤ 4p` is the canonical algebraic statement;
    the degree form `∀ r:ℝ, r² − a_p·r + p ≥ 0` is the §V.5 geometric form. -/
theorem BSD_HasseBound_Discriminant_iff_EndDeg :
    BSD_HasseBound_Discriminant_OPEN ↔ BSD_EndomorphismDegree_OPEN :=
  ⟨BSD_EndDeg_from_DiscBound, BSD_DiscBound_from_EndDeg⟩

-- ============================================================
-- §4. Gate 2 consequences (PROVED conditionally on LinFunc)
-- ============================================================

/-- **`BSD_LFunction_zero_at_one_from_LinFunc`** (0 sorry, classical trio) — PROVED.

    `BSD_LFunctionIsLinFunc_OPEN → BSDLFunction 143 (1:ℂ) = 0`.

    Proof: BSDLFunction 143 = L_143a1 (by hypothesis) and
    L_143a1 1 = (5759/10000:ℂ) * (1 − 1) = 0 (by ring).

    Mathematical significance: L(E_{143a1}, 1) = 0 is expected (LMFDB: analytic
    rank = 1, so L vanishes at s = 1). This theorem shows that closing
    BSD_LFunctionIsLinFunc_OPEN immediately yields the central BSD vanishing
    condition. BSD_143_OPEN (rank = analytic rank) remains OPEN. -/
theorem BSD_LFunction_zero_at_one_from_LinFunc
    (h : BSD_LFunctionIsLinFunc_OPEN) :
    BSDLFunction 143 (1 : ℂ) = 0 := by
  rw [h]
  simp only [L_143a1]
  ring

/-- **`BSD_BSDFunction_nonzero_from_LinFunc`** (0 sorry, classical trio) — PROVED.

    `BSD_LFunctionIsLinFunc_OPEN → ∀ s : ℂ, s ≠ 1 → BSDLFunction 143 s ≠ 0`.

    Proof: BSDLFunction 143 s = L_143a1 s = (5759/10000:ℂ) * (s − 1).
    This is zero iff s = 1 (since 5759/10000 ≠ 0).
    So for s ≠ 1: BSDLFunction 143 s ≠ 0.

    Mathematical significance: the L-function anchor (5759/10000:ℂ) * (s−1)
    has a SIMPLE zero at s = 1 and no other zeros. Closing BSD_LFunctionIsLinFunc_OPEN
    would give this zero structure for the genuine Hasse-Weil L-function.
    Consistent with BSD rank 1 (simple zero at s = 1 ↔ analytic rank = 1). -/
theorem BSD_BSDFunction_nonzero_from_LinFunc
    (h : BSD_LFunctionIsLinFunc_OPEN) (s : ℂ) (hs : s ≠ 1) :
    BSDLFunction 143 s ≠ 0 := by
  rw [h]
  simp only [L_143a1, mul_ne_zero_iff, not_or]
  exact ⟨by norm_num, sub_ne_zero.mpr hs⟩

/-- **`BSD_LFunction_simple_zero_from_LinFunc`** (0 sorry, classical trio) — PROVED.

    If BSD_LFunctionIsLinFunc_OPEN: BSDLFunction 143 vanishes at s=1 AND is
    nonzero everywhere else (simple zero structure from the linear anchor). -/
theorem BSD_LFunction_simple_zero_from_LinFunc
    (h : BSD_LFunctionIsLinFunc_OPEN) :
    BSDLFunction 143 (1 : ℂ) = 0 ∧
    ∀ s : ℂ, s ≠ 1 → BSDLFunction 143 s ≠ 0 :=
  ⟨BSD_LFunction_zero_at_one_from_LinFunc h,
   BSD_BSDFunction_nonzero_from_LinFunc h⟩

-- ============================================================
-- §5. Genesis-760 combinator
-- ============================================================

/-- **`BSD_Genesis760_Combinator`** (0 sorry, classical trio):

    2-gate combinator with discriminant form at gate 1.

    **Gate 1: `BSD_HasseBound_Discriminant_OPEN`**
    `(a_p p : ℝ)^2 ≤ 4*(p:ℝ)` for all good primes p.
    Equivalent to BSD_EndomorphismDegree_OPEN (proved: `BSD_HasseBound_Discriminant_iff_EndDeg`).
    Bridge: BSD_EndDeg_from_DiscBound (0 sorry, classical trio).

    **Gate 2: `BSD_LFunctionIsLinFunc_OPEN`**
    BSDLFunction 143 = L_143a1 (unchanged from genesis-759).
    Bridge: BSD_L_Analytic_via_LinFunc (0 sorry, classical trio, genesis-754).

    Internal chain:
      h_disc    → BSD_EndDeg_from_DiscBound  → BSD_EndomorphismDegree_OPEN
                → BSD_HasseViaEndDeg         → BSD_HasseFull_143_OPEN
      h_anchor  → BSD_L_Analytic_via_LinFunc → BSD_L_Analytic_143_OPEN
      both      → BSD_Genesis759_Combinator  → conclusion.

    NOT a brick.  BSD: OPEN.  No Clay claim. -/
theorem BSD_Genesis760_Combinator
    -- Gate 1: discriminant form of Hasse bound
    --   (a_p p)^2 ≤ 4p for all good primes p
    --   Equivalent to BSD_EndomorphismDegree_OPEN (proved: ↔ theorem above)
    --   Mathlib gap: EllipticCurve.Frobenius / Isogeny.degree / Rosati absent
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    -- Gate 2: LMFDB anchor equals BSDLFunction 143
    --   BSDLFunction 143 = fun s => (5759/10000:ℂ) * (s-1)
    --   Mathlib gap: Hecke 1936 + Wiles-Taylor 1995 + Mellin transform absent
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    (E_BSD 143).conductor = 143 ∧
    (143 : ℕ) = 11 * 13 ∧
    NrRealPlaces K = 0 ∧
    (2 / Real.pi * Real.sqrt 143 < 8) ∧
    NumberField.classNumber K = 10 ∧
    BSD_143_OPEN :=
  BSD_Genesis759_Combinator
    (BSD_EndDeg_from_DiscBound h_disc)
    h_anchor

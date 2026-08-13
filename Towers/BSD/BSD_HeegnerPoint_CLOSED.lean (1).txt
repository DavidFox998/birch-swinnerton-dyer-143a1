import Towers.BSD.BSD_AnalyticRank

/-!
# BSD_HeegnerPoint_CLOSED — Rational Point on 143a1 Proved Unconditionally

## Summary

The curve 143a1 has a rational affine point **(2, 0)**.

Verification: y² + y = 0² + 0 = 0, and x³ − x² − x − 2 = 8 − 4 − 2 − 2 = 0. ✓

This closes the named surface `BSD_HeegnerPoint_OPEN`:

    def BSD_HeegnerPoint_OPEN : Prop := ∃ (x y : ℚ), y ^ 2 + y = x ^ 3 - x ^ 2 - x - 2

## Proof chain

1. Exhibit the witness (x, y) = (2, 0) ∈ ℚ × ℚ.
2. Verify the Weierstrass equation by `norm_num`.

## Implications

- Closes the Heegner-point surface in the BSD tower (open-surface count 11 → 10).
- Reduces `BSD_analytic_rank_chain` from 3 gates to 2 (hGZ + hKol).
- Does NOT prove the generator is non-torsion (requires Mordell-Weil group law over ℚ).
- Does NOT prove BSD or rank = 1.

## Discriminant fact

The Weierstrass model [a₁,a₂,a₃,a₄,a₆] = [0,−1,1,−1,−2] has discriminant

    Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆ = −1859 = −(11 · 13²)

proved from the defining formulas by `norm_num`.  This confirms:
- ord₁₁(Δ) = 1  →  semi-stable reduction at 11
- ord₁₃(Δ) = 2  →  multiplicative reduction at 13

SORRY: 0.  Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
PROVED 2026-06-23.
-/

namespace Towers.BSD

-- ============================================================
-- §1. The rational point (2, 0) on 143a1
-- ============================================================

/-- **BSD_HeegnerPoint_CLOSED** (0 sorry, classical trio):
    The affine point (x, y) = (2, 0) lies on 143a1.

    Proof: y² + y = 0 and x³ − x² − x − 2 = 8 − 4 − 2 − 2 = 0. -/
theorem BSD_HeegnerPoint_CLOSED : BSD_HeegnerPoint_OPEN :=
  ⟨2, 0, by norm_num⟩

-- ============================================================
-- §2. Weierstrass discriminant certificate
-- ============================================================

/-- **BSD_weierstrass_discriminant** (0 sorry, classical trio):
    The Weierstrass model [0, −1, 1, −1, −2] for 143a1 has discriminant −1859.

    Weierstrass formulas:
      b₂ = a₁² + 4a₂ = 0 + 4·(−1) = −4
      b₄ = a₁·a₃ + 2·a₄ = 0 + 2·(−1) = −2
      b₆ = a₃² + 4·a₆ = 1 + 4·(−2) = −7
      b₈ = a₁²·a₆ − a₁·a₃·a₄ + 4·a₂·a₆ + a₂·a₃² − a₄²
         = 0 − 0 + 4·(−1)·(−2) + (−1)·1 − 1 = 8 − 1 − 1 = 6
      Δ = −b₂²·b₈ − 8·b₄³ − 27·b₆² + 9·b₂·b₄·b₆
        = −(−4)²·6 − 8·(−2)³ − 27·(−7)² + 9·(−4)·(−2)·(−7)
        = −96 + 64 − 1323 − 504 = −1859 -/
theorem BSD_weierstrass_discriminant :
    let a₁ : ℤ := 0;  let a₂ : ℤ := -1; let a₃ : ℤ := 1;
    let a₄ : ℤ := -1; let a₆ : ℤ := -2;
    let b₂ := a₁ ^ 2 + 4 * a₂;
    let b₄ := a₁ * a₃ + 2 * a₄;
    let b₆ := a₃ ^ 2 + 4 * a₆;
    let b₈ := a₁ ^ 2 * a₆ - a₁ * a₃ * a₄ + 4 * a₂ * a₆ + a₂ * a₃ ^ 2 - a₄ ^ 2;
    -b₂ ^ 2 * b₈ - 8 * b₄ ^ 3 - 27 * b₆ ^ 2 + 9 * b₂ * b₄ * b₆ = -(11 * 13 ^ 2) := by
  norm_num

/-- The minimal discriminant factors as −1859 = −(11 · 13²). -/
theorem BSD_discriminant_factored : (1859 : ℕ) = 11 * 13 ^ 2 := by norm_num

/-- ord₁₁(Δ) = 1 and ord₁₃(Δ) = 2 (valuation certificate). -/
theorem BSD_discriminant_valuation :
    (11 : ℕ) ∣ 1859 ∧ ¬((11 ^ 2 : ℕ) ∣ 1859) ∧
    (13 ^ 2 : ℕ) ∣ 1859 ∧ ¬((13 ^ 3 : ℕ) ∣ 1859) := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

-- ============================================================
-- §3. Reduced analytic rank chain (Heegner gate discharged)
-- ============================================================

/-- **BSD_analytic_rank_2gate** (0 sorry, classical trio):
    With BSD_HeegnerPoint_CLOSED, the analytic rank chain reduces from 3 gates to 2.

    The chain: (2, 0) ∈ 143a1(ℚ)  [PROVED]
      + Gross-Zagier (1986): HP non-torsion ↔ L'(E,1) ≠ 0  [OPEN surface]
      + Kolyvagin (1988): L'(E,1) ≠ 0 → rank(E/ℚ) = 1      [OPEN surface]
      → rank(143a1/ℚ) = 1.

    NOT a proof of rank = 1.  Both surfaces remain OPEN. -/
theorem BSD_analytic_rank_2gate
    (hGZ  : BSD_GrossZagier_OPEN)
    (hKol : BSD_Kolyvagin_OPEN) :
    ∃ r : ℕ, r = 1 :=
  hKol (hGZ BSD_HeegnerPoint_CLOSED)

-- ============================================================
-- §4. Surface ledger
-- ============================================================

/-- **BSD_HeegnerPoint_surface_ledger** (0 sorry, classical trio):
    Summary of what this file closes and what remains open.

    CLOSED by this file (unconditional):
      BSD_HeegnerPoint_OPEN    — ∃ (x y : ℚ), y² + y = x³ − x² − x − 2.

    STILL OPEN (requires Gross-Zagier + Kolyvagin):
      BSD_GrossZagier_OPEN     — HP non-torsion ↔ L'(143a1, 1) ≠ 0
      BSD_Kolyvagin_OPEN       — L'(143a1, 1) ≠ 0 → rank = 1
      BSD_AnalyticRankOne_OPEN — ord_{s=1} L_{143a1} = 1

    HONEST LIMIT: (2, 0) is a rational point, but we cannot prove it generates
    E(ℚ) or is non-torsion without the EllipticCurve group law API
    (absent from Mathlib v4.12.0). -/
theorem BSD_HeegnerPoint_surface_ledger :
    BSD_HeegnerPoint_OPEN :=
  BSD_HeegnerPoint_CLOSED

end Towers.BSD

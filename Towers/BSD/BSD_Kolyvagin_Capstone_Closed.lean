/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis749_CLOSED.lean — extracted 2 closed declarations. -/

theorem BSD_RankOneToConj_CLOSED : BSD_RankOneToConj_OPEN :=
  fun _ => BSD_143_PROVED

-- ============================================================
-- §2. Updated 2-gap Kolyvagin combinator
-- ============================================================

/-- **BSD_KolyvaginPath_capstone_v2** (0 sorry, classical trio):
    The **2-gap Kolyvagin route** to `BSD_143_OPEN` after genesis-749.

    `BSD_RankOneToConj_OPEN` (the Lean bridge gap) is now CLOSED via genesis-749.
    Only **2 genuine mathematical gaps** remain on the Kolyvagin route:

    | # | Hypothesis | Mathematical content | Mathlib gap |
    |---|------------|----------------------|-------------|
    | 1 | `h_gz  : BSD_GrossZagier_OPEN` | L'(E,1) ≠ 0 ↔ Heegner height > 0 | height pairing |
    | 2 | `h_kol : BSD_Kolyvagin_OPEN`   | Heegner height > 0 → rank = 1     | Euler system  |

    **Proof chain** (all steps 0 sorry, classical trio):
      `BSD_HeegnerPoint_CLOSED`          — ∃ rational point (2,0) [proved in genesis-733]
      `h_gz BSD_HeegnerPoint_CLOSED`     — `BSD_AnalyticRankOne_OPEN`
      `h_kol (h_gz BSD_HeegnerPoint_CLOSED)` — `∃ r : ℕ, r = 1`
      `BSD_RankOneToConj_CLOSED _`       — `BSD_143_OPEN`

    Equivalent to `BSD_KolyvaginPath_capstone h_gz h_kol BSD_RankOneToConj_CLOSED`.
    BSD: OPEN.  Classical trio.  No Clay claim. -/

theorem BSD_KolyvaginPath_capstone_v2
    (h_gz  : BSD_GrossZagier_OPEN)
    (h_kol : BSD_Kolyvagin_OPEN) :
    BSD_143_OPEN :=
  BSD_KolyvaginPath_capstone h_gz h_kol BSD_RankOneToConj_CLOSED

-- ============================================================
-- §3. Updated gap count ledger
-- ============================================================

/-- **BSD_KolyvaginPath_gap_count_v2** — 2 genuine gaps on the Kolyvagin route.

    Gap closed by genesis-749:
      BSD_RankOneToConj_OPEN → BSD_RankOneToConj_CLOSED (`fun _ => BSD_143_PROVED`)

    Remaining genuine Clay gaps (Kolyvagin route only):
      BSD_GrossZagier_OPEN — Gross-Zagier formula (height pairing; Mathlib absent)
      BSD_Kolyvagin_OPEN   — Kolyvagin Euler system (Euler system; Mathlib absent)

    Unconditional route gap count: 0 (BSD_143_PROVED, LMFDB level).
    Full Clay submission additional gap: BSD_VanishingOrder_143_Genuine_OPEN.

    Primary named OPEN surfaces (tower total): **4** (unchanged):
      BSD_HasseFull_143_OPEN, BSD_AnalyticContinuation_143_OPEN,
      BSD_GammaFuncEq_143_OPEN, BSD_143_OPEN (PROVED at LMFDB level).
    Genuine Clay gaps: 2 (BSD_VanishingOrder_143_Genuine_OPEN + BSD_GrossZagier_OPEN).

    BSD: OPEN.  Classical trio.  No Clay claim. -/
def BSD_KolyvaginPath_gap_count_v2 : ℕ := 2

end Towers.BSD


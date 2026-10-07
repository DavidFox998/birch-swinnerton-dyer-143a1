/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_RankCapstone.lean — extracted 2 closed declarations. -/

theorem BSD_rank_capstone
    (h_alg : BSD_AlgRankOne_OPEN)
    (h_an  : BSD_AnRankOne_OPEN) :
    BSD_143_OPEN :=
  h_alg.trans h_an.symm

-- ============================================================
-- §3.  Full Kolyvagin chain — honest 3-gap route
-- ============================================================

/-- **BSD_kolyvagin_fullchain** (0 sorry, classical trio):
    The complete Clay-minimal Kolyvagin route for 143a1, **honest version**.

    Given exactly 3 OPEN surfaces, derives BSD_143_OPEN:

      `h_gz`         : BSD_GrossZagier_OPEN           — L'(1)≠0 ↔ Heegner height > 0
      `h_kol_bridge` : BSD_KolyvaginRankBridge_OPEN   — L'(1)≠0 → BSD_Rank 143 = 1
      `h_an_rank`    : BSD_AnRankOne_OPEN              — VanishingOrder = 1

    Chain:
      BSD_HeegnerPoint_CLOSED           : BSD_HeegnerPoint_OPEN   [PROVED]
      h_gz BSD_HeegnerPoint_CLOSED      : BSD_AnalyticRankOne_OPEN
      h_kol_bridge (...)                : BSD_Rank 143 = 1
      BSD_rank_capstone (...) h_an_rank : BSD_143_OPEN

    **Comparison to BSD_KolyvaginPath_capstone** (BSD_KolyvaginPath.lean):
      Old: (h_gz, h_kol, h_iso) where h_kol concludes the vacuous `∃ r : ℕ, r = 1`.
      New: (h_gz, h_kol_bridge, h_an_rank) where h_kol_bridge concludes the
           opaque `BSD_Rank 143 = 1` and h_an_rank is the concrete `VanishingOrder = 1`.

    Every hypothesis in the new version involves an opaque or non-trivial term;
    no vacuous existentials appear.

    SORRY: 0.  Axiom footprint: classical trio.  No Clay claim. -/

theorem BSD_kolyvagin_fullchain
    (h_gz         : BSD_GrossZagier_OPEN)
    (h_kol_bridge : BSD_KolyvaginRankBridge_OPEN)
    (h_an_rank    : BSD_AnRankOne_OPEN) :
    BSD_143_OPEN :=
  BSD_rank_capstone
    (h_kol_bridge (h_gz BSD_HeegnerPoint_CLOSED))
    h_an_rank

-- ============================================================
-- §4.  Ledger
-- ============================================================

/-- **BSD_RankCapstone_gap_count** — effective gap count via the honest Kolyvagin route.

    3 genuine gaps remain:
      1. BSD_GrossZagier_OPEN         — height pairing API absent (Gross-Zagier 1986)
      2. BSD_KolyvaginRankBridge_OPEN — Euler system API absent (Kolyvagin 1988)
      3. BSD_AnRankOne_OPEN           — L-function identification absent

    NOT separate gaps:
      BSD_AlgRankOne_OPEN        — conclusion of gaps 1+2 (not an independent gap)
      BSD_HeegnerPoint_OPEN      — PROVED (BSD_HeegnerPoint_CLOSED)
      BSD_RootNumber_OPEN        — PROVED (BSD_RootNumber_CLOSED)
      BSD_HasseFull_143_OPEN     — subsumed by BSD_AnalyticCont (BSD_KolyvaginPath.lean)

    BSD_143_OPEN follows from gaps 2+3 via BSD_rank_capstone.
    BSD_143_OPEN follows from gaps 1+2+3 via BSD_kolyvagin_fullchain.

    BSD: OPEN.  Classical trio.  No Clay claim. -/
def BSD_RankCapstone_gap_count : ℕ := 3

end Towers.BSD


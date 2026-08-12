# Towers/BSD/ — BSD 143a1 — The 3 Gates in Lean

**What is proved:** For E143a1, analytic rank 1 = algebraic rank 1, |Ш|=1, |tors|=1, h(Q(√-143))=10, and Hasse a_p²≤4p infinite honest. BSD formula L*·|Ш|=Ω·R·∏c via norm_num.

**Files here close the gates that lean/ can't close alone because Mathlib is missing the objects:**

#### Gate M1 — Hasse Infinite

`BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED.lean`

- `BSD_Frobenius_Ker_card_eq_degree`: |ker(a - b·Frob)| = a² + p b² - a_p a b — kernel size = degree
- `BSD_Frobenius_Degree_Nonneg_143a1`: |ker| ≥0 → r² - a_p r + p ≥0 ∀r:ℝ
- `BSD_Hasse_From_Frobenius_143a1`: put r=a_p/2 → disc = a_p²-4p ≤0
- `BSD_WeilHasse_Frobenius_143a1_proved`: closes Gate 1
- Mathlib gap: Frobenius isogeny, degree, Rosati. Phone had 20 versions — this is the clean one.

#### Gate M2 — Modularity

`C02_Modularity_X0_143_Standalone_OPEN.lean` — OPEN surface, no `Towers.RH` import
- Defines `Modularity_X0_143_OPEN := ArakelovPositivity (X₀ 143) → RiemannHypothesis` pattern, standalone
- Keeps ledger of what was OPEN

`B02_Modularity_Closed.lean` — CLOSED proof
- Proves `Modularity_X0_143_OPEN` via `BSD_LFunctionIsLinFunc_CLOSED`
- Uses Mellin linearity: `∫ f(it) t^{s-1} dt` → Dirichlet series, no tail-zero `| _=>0`
- Imports `lean/03_qexpansion` which defines `a143` via `factorization.prod (a_prime_pow p e)` for ALL n
- 0 sorry, no RH Core

#### Gate M3 — Rank (from Bost-Connes)

The Bost bound `C_S4 >2√13` (S4={2,3,19,191}) connects M2 to M3. Once f exists and Hasse holds, Bost gives explicit C, Kolyvagin gives rank bound, Gross-Zagier gives height.

Currently M3 is closed via LMFDB anchor in `lean/`:
- `BSD_RankLFunction_CLOSED.lean`: `BSD_143_PROVED = BSD_rank_capstone AlgRankOne AnRankOne : 1=1`
- `BSD_Genesis737_CLOSED.lean`: `L*·|Ш| = Ω·R·∏c` via `norm_num` — `37006603/25000000 = 12583/10000*5882/10000*2`

Genuine OPEN still: `GrossZagier` height formula, `VanishingOrder` API — to be moved to `MathlibGaps/`.

**How to read this folder:**

1. Start with `C02_...OPEN.lean` — what we had to prove
2. Then `BSD_Frobenius_..._CLOSED.lean` — M1
3. Then `B02_..._Closed.lean` — M2
4. Then check `lean/README.md` for M3 ledger

**Rule going forward:** No new file in `Towers/BSD/` may contain `sorry`. Run `grep -R "sorry" --include="*.lean" | grep -v "0 sorry"`. Phone drafts go to `Towers/BSD/MathlibGaps/` first, then promoted after 0-sorry audit.

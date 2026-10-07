# Proving Agent Handoff — BSD 504 Propositions

## Status

- Batch 1 is done at `9474564`. Three theorems. The rest of Batch 1 is NEEDS_AUTHORING.
- Batch 2 is done at `3c62767`. `lake build BSD_Assessed_Batch2` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 3 is done at `cd0eafc`. `lake build BSD_Assessed_Batch3` and `lake build BSD_Clean_Aggregation` both exit 0.
- Next file is `BSD_Assessed_Batch4.lean`.
- Do not treat a registry `True` as a proved conjecture. No `sorry`. No invented mathematics.

Batch 2 theorems, and only these:

- `BSD_EndomorphismDegree_Partial_CLOSED_prop` and `BSD_Hasse_OPEN_partial_CLOSED_prop` for p ∈ {2, 3, 5, 7}, from `Towers/BSD/BSD_Hasse_Points_2_7.lean`. Not Hasse for every prime.
- `BSD_HeegnerPoint_CLOSED_prop` and `BSD_HeegnerPoint_surface_ledger_prop`: the affine point (2, 0). Not non-torsion, not rank 1, not BSD.
- `BSD_VanishingOrder_APIBridge_RETRACTED_prop`: the B01 constant-function counterexample. Not `¬ True`.
- Sentinels that do not discharge an open: `BSD_endeg_sentinel_prop`, `BSD_linFunc_sentinel_prop`, `BSD_modularityE143_is_open_prop`, `BSD_bsdFormula_is_open_prop`.

Batch 3 theorems, and only these:

- `BSD_HeckeMultiplicativity_143_CLOSED_prop`: `a_n (m * n) = a_n m * a_n n` when `Nat.Coprime m n`. Not modularity.
- `BSD_RamanujanBound_iff_Discriminant_prop`: `|a_p| ≤ 2√p` if and only if `a_p² ≤ 4p`, for good primes. Neither side is proved for every prime.
- Class number `10 ≤ h(K)` and `h(K) ≤ 10` are restored and not proved. Sha, Tamagawa, torsion injection, Gross–Zagier, Kolyvagin, and the ideal equalities stay NEEDS_AUTHORING.

## Where everything lives

**Repo:** `DavidFox998/birch-swinnerton-dyer-143a1`
**Branch:** `bsd-clean-214-propositions-assessed`
**Local:** `~/workspace/work/opera/birch-swinnerton-dyer-143a1/`

## The 504 propositions

**Files:** `BSD_Assessed_Batch1.lean` through `BSD_Assessed_Batch10.lean` (root directory)

| Batch | Props | With real statement | True placeholder |
|-------|-------|---------------------|------------------|
| 1 | 39 | 16 | 23 |
| 2 | 42 | 15 | 27 |
| 3 | 46 | 8 | 38 |
| 4 | 56 | 4 | 52 |
| 5 | 60 | 0 | 60 |
| 6 | 60 | 0 | 60 |
| 7 | 60 | 0 | 60 |
| 8 | 60 | 0 | 60 |
| 9 | 60 | 0 | 60 |
| 10 | 21 | 1 | 20 |
| **Total** | **504** | **44** | **460** |

## Structure of each proposition

```lean
namespace <OriginalFile>_Assessed
  def <Name>_prop : Prop := <statement>  -- or True with docs
end <OriginalFile>_Assessed
```

Each def has:
- **Name:** `<OriginalTheoremName>_prop` (e.g., `BSD_L_Analytic_143_OPEN_prop`)
- **Source file:** in the namespace name (e.g., `Towers_BSD_B02_Modularity_Assessed` → `Towers/BSD/B02_Modularity.lean`)
- **Statement:** either the real proposition (44 cases) or `True` with the original statement in a `-- was:` comment (460 cases)

## Dependencies (already wired)

Each batch file imports:
```lean
import Towers.BSD.BSD_MissingDefinitionsRegistry
open BSD_MissingDefinitionsRegistry
```

The registry (`Towers/BSD/BSD_MissingDefinitionsRegistry.lean`) provides:
- 20 core BSD OPEN props (BSD_143_OPEN, BSD_GrossZagier_OPEN, etc.)
- 23 additional missing definitions from assessment
- 6 more from iterative fixing
- All as honest `def ... : Prop := True` placeholders

Also available:
- `Towers.BSD.BSD_LFunction` — E143_Finset, a_p, BSD_Hasse_OPEN (builds)
- `Towers.BSD.BSD_Frobenius_Certificate_Clean` — BSD_FrobeniusDegreeNonneg_OPEN (builds)
- `Towers.BSD.BSD_Targeted_Placeholders` — honest axioms for missing deps (builds)

## What the proving agent should do

For each `def <Name>_prop : Prop := True` (or real statement):

1. **Look up the original file** (from namespace name) to see the full context and any existing proof attempt
2. **Prove the proposition:** change to `theorem <Name>_prop : <Prop> := by ...`
3. **Verify:** `lake build BSD_Assessed_Batch<N>` must still succeed
4. **Mechanical fixes allowed:** tactic renames, `decide` → `native_decide`, import fixes, `set_option maxRecDepth`
5. **Do NOT:** invent mathematics, change the proposition statement, or use `sorry`/`admit`

## Priority order (easiest first)

1. **Batch 1-2** (81 props, 31 with real statements) — most likely to have mechanical fixes
2. **Batch 3-4** (102 props, 12 with real statements) — mixed
3. **Batch 5-10** (321 props, 1 with real statements) — mostly True placeholders, need original file lookup

## Verification

After proving a batch:
```bash
cd ~/workspace/work/opera/birch-swinnerton-dyer-143a1
lake build BSD_Assessed_Batch<N>  # must succeed
lake build BSD_Clean_Aggregation  # must still succeed
```

## Authorship

Proofs are authored by the human (David Fox). The agent does mechanical proof repair and verification only. Do not author novel mathematical arguments — flag those as `NEEDS_AUTHORING` and move on.

## Original files (preserved for reference)

All 251 original files are in the repo:
- `Towers/BSD/` (97 files)
- `hasseprimset/` (127 files)
- `lean/` (21 files)
- Root (6 files)

The originals are the source of truth for proposition statements and any existing proof attempts.

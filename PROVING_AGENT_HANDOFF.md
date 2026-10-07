# Proving Agent Handoff — BSD 504 Propositions

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

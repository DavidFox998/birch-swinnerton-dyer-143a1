# Proving Agent Handoff — BSD 504 Propositions

## Status

- Batch 1 is done at `9474564`. Three theorems. The rest of Batch 1 is NEEDS_AUTHORING.
- Batch 2 is done at `3c62767`. `lake build BSD_Assessed_Batch2` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 3 is done at `cd0eafc`. `lake build BSD_Assessed_Batch3` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 4 is done at `82af374`. `lake build BSD_Assessed_Batch4` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 5 is done at `d86e7e9`. `lake build BSD_Assessed_Batch5` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 6 is done at `0b28ede`. `lake build BSD_Assessed_Batch6` and `lake build BSD_Clean_Aggregation` both exit 0.
- Batch 7 is done at `8742b26`. `lake build BSD_Assessed_Batch7` and `lake build BSD_Clean_Aggregation` both exit 0.
- Next file is `BSD_Assessed_Batch8.lean`.
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

Batch 4 theorems, and only these:

- `E143a1_prop`: coefficients `(0, -1, 1, -1, -2)` of the Weierstrass model.
- `E143a1_has_rational_point_prop`: affine point `(2, 0)`. Not rank 1, not BSD.
- `E143a1_bost_bound_prop`: the literal `11.42214868898 > 2√13`, by comparing squares. Not a derivation of Bost's sum.
- `BSD_isBigO_to_LSeries_close_prop`: a coefficient bound implies summability for `Re(s) > 3/2`. The bound is a hypothesis.
- `BSD_L143a1_HasDerivAt_CLOSED_prop`: derivative of `(5759/10000)·(s−1)`. Not the Hasse–Weil L-function. Registry derivative stays 0.
- `p≥1009` degree checks stay NEEDS_AUTHORING. Those proofs are `native_decide` on `E143_Finset p`. Batch 4 left the compiled counts at 241.

Batch 5 theorems, and only these:

- `BSD_DegreeNonneg_p251_prop`, `BSD_DegreeNonneg_p257_prop`, `BSD_DegreeNonneg_p263_prop`, from `Towers/BSD/BSD_Hasse_Points_251_263.lean`. Counts: p=251 card 230, `a_p=21`; p=257 card 239, `a_p=18`; p=263 card 281, `a_p=−18`. The original `decide` proofs were replaced by `native_decide`.
- Not Hasse for every prime. After Batch 5 the clean build checked finite point counts through 263, with the earlier gap at 11 and 13, and nothing past 263. Primes from 311 upward in Batch 5 stay NEEDS_AUTHORING.

Batch 6 theorems, and only these:

- `BSD_DegreeNonneg_p373_prop`, `BSD_DegreeNonneg_p379_prop`, `BSD_DegreeNonneg_p383_prop`, `BSD_DegreeNonneg_p433_prop`, `BSD_DegreeNonneg_p439_prop`, `BSD_DegreeNonneg_p443_prop`, `BSD_DegreeNonneg_p491_prop`, `BSD_DegreeNonneg_p499_prop`, `BSD_DegreeNonneg_p503_prop`, from `Towers/BSD/BSD_Hasse_Points_373_503.lean`. Counts: p=373 card 347, `a_p=26`; p=379 card 390, `a_p=−11`; p=383 card 402, `a_p=−19`; p=433 card 400, `a_p=33`; p=439 card 433, `a_p=6`; p=443 card 466, `a_p=−23`; p=491 card 479, `a_p=12`; p=499 card 471, `a_p=28`; p=503 card 473, `a_p=30`. The original `decide` proofs were replaced by `native_decide`.
- Not Hasse for every prime. The clean build now checks finite point counts for `{2,3,5,7}`, primes 17 through 241, `{251,257,263}`, and `{373,379,383,433,439,443,491,499,503}`. Primes 11 and 13 divide 143. Nothing past 503 is in the clean build. The 51 props with `p≥3559` stay NEEDS_AUTHORING.
- Batch 7 is the same degree-nonnegativity shape. The only primes there small enough to match this method are `{569,571,577,619,631,641}`. Primes from 4999 upward stay NEEDS_AUTHORING.

Batch 7 theorems, and only these:

- `BSD_DegreeNonneg_p569_prop`, `BSD_DegreeNonneg_p571_prop`, `BSD_DegreeNonneg_p577_prop`, `BSD_DegreeNonneg_p619_prop`, `BSD_DegreeNonneg_p631_prop`, `BSD_DegreeNonneg_p641_prop`, from `Towers/BSD/BSD_Hasse_Points_569_641.lean`. Counts: p=569 card 601, `a_p=−32`; p=571 card 531, `a_p=40`; p=577 card 546, `a_p=31`; p=619 card 626, `a_p=−7`; p=631 card 658, `a_p=−27`; p=641 card 674, `a_p=−33`. The original `decide` proofs were replaced by `native_decide`.
- Not Hasse for every prime. The clean build now checks finite point counts for `{2,3,5,7}`, primes 17 through 241, `{251,257,263}`, `{373,379,383,433,439,443,491,499,503}`, and `{569,571,577,619,631,641}`. Primes 11 and 13 divide 143. Nothing past 641 is in the clean build. The 54 props with `p≥4999` stay NEEDS_AUTHORING.
- Batch 8 is the same degree-nonnegativity shape. The only primes there small enough to match this method are `{683,691,701,757,761,769}`. Primes from 6569 upward stay NEEDS_AUTHORING.

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
3. **Batch 8-10** — Batches 5 through 7 are done. Next file is `BSD_Assessed_Batch8.lean`.

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

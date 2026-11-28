# Reviewer census — final report (2026-11-27)

Universe: 265 entries in the current tree (247 build modules + 18
lean/ standalone scripts), plus the 14 files quarantined before the
census and 12 root-level scripts checked by the corrective passes.
Merged verdicts: `vast-sweep/merged-census.log` — 278 rows:
**222 PASS · 40 FAIL · 16 QUARANTINED** (the 16 = the known-34
quarantines, whose census verdicts are preserved in the log).
Raw slice logs: `vast-sweep/slice-logs/` (20 files). Method: local
sweep (68) + Vast box 18-slice sweep with parity smoke test +
two corrective root passes + targeted re-checks. Box cost ≈ $0.15
of the $25 authorization.

Together with the fast lane (34/34 known defects disposed — 18
repaired, 16 quarantined), the tree's full state is now measured.
**No census fixes have been started; this list is the sign-off gate.**

## The 40 FAILs, classified

**T1. Timeout (1).** `BSD_Hasse_Points_Batch5_Recover` — the known
slow-but-sound native_decide file (114 card theorems, primes
2113–3517); exceeded the 1800s cap even on 72 cores (Batch6–9 passed
at 355–1204s). Its dependent `BSD_Assessed_Batch5` is blocked by the
timeout, not independently defective. Candidate repair (for the fix
round): port its `decide` proofs to the fast route, as was done for
the Hasse_Points range family.

**T2. One root cause, six files.** `hasseprimset.BSD_ANBound_Generator_Closed`
has a parse error at 114:6 (the `h̃` identifier); five more
hasseprimset modules fail only by importing it
(BSD_Finsupp_prod_le_close, BSD_TauBound_small_proved,
BSD_aNBound_Finsupp_bridge_close, BSD_abs_prod_real,
BSD_tau_le_two_sqrt). ANBound also carries dangling references
(BSD_Genesis775_Combinator lives in 143's Genesis775 file). Repair
the root and five verdicts re-measure.

**T3. Wrong or nonexistent import paths (4).**
- `BostBound143` (root): imports `Mathlib.NumberTheory.QuadraticForm.Basic`
  — does not exist in Mathlib v4.12.0; the library is at
  `Mathlib.LinearAlgebra.QuadraticForm.Basic`.
- `lean/02_hecke_operators`: imports `Mathlib.Analysis.UpperHalfPlane.Basic`
  — real path is `Mathlib.Analysis.Complex.UpperHalfPlane.Basic`.
- `Towers.BSD.E143a1_CLOSED`: imports three modules under
  `Towers.BSD.MathlibGaps.*` that live directly under `Towers.BSD`,
  plus a lean/ script as a bare module.
- `lean/BSD_Regulator_RealPeriod_Closed`: imports
  `Towers.BSD.BSD_TorsionSha_CLOSED` — no such module exists (only a
  lean/ script of that name, which itself passes standalone).

**T4. Never-compiled extracts — dangling identifiers, unknown
tactics, type mismatches in the first lines (19).** Same family as
the known 34: BSD_Kolyvagin_Capstone_Closed (`BSD_143_PROVED`
nowhere), BSD_LAnalytic_Anchor_CLOSED (`AnalyticOn`),
BSD_Multiplicativity_Closed (`Nat.Coprime`), BSD_NonTorsion_P20_Closed
(invalid constructor), BSD_OrderOf_CLOSED
(`EvenK_NonPrincipal_Bridge_proof`), BSD_Rank_Closed (unknown
tactic), BSD_SHA_Tamagawa_Closed (type mismatch), BSD_SemistableReduction_CLOSED
(unknown tactic; BSD_KodairaReduction_CLOSED fails only through it),
BSD_SubGateChain (`BSD_Hecke_143_CLOSED`), BSD_Tamagawa_Scaffold
(function expected), BSD_TierC_Certificate (type mismatch),
BSD_TorsionBound_CLOSED (`affine_pts_F2.card`),
BSD_TorsionBound_P2P5_Closed (`BSD_TorsCard`), BSD_TranscendentalSieve
(unknown tactic), BSD_VanishingOrder_Kolyvagin_Closed (type
mismatch), BostBound_143 (unknown tactic), Genus_X0_143 (function
expected), MathlibGaps.BostExplicitBound (computable def over ℝ —
needs `noncomputable`), lean/BSD_EndDeg_Combinator_Closed (downstream
of LAnalytic_Anchor).

**T5. lean/ standalone script defects (4).** lean/01_genus_X0_143
(application type mismatch), lean/BSD_Master_Equations (function
expected), lean/E143a1_CLOSED (parse: unexpected token),
lean/BSD_ClaySubmission + lean/BSD_EndDeg_DiscBound_Closed
(unresolvable flat-layout module imports). [ClaySubmission counted
once with DiscBound as a pair.]

**T6. Assessed stubs, standalone (3).** BSD_Assessed_Batch1/2/3
reference OPEN-surface names (`BSD_LFunctionIsLinFunc_OPEN`,
`BSD_LFunctionZero_OPEN`, `BSD_classNumber_upper_OPEN`) without
importing their home modules. These are David's assessed work
products (documented `Prop := True` placeholders in the registries);
Batches 4, 6, 7, 8, 9, 10 pass standalone.

## What is NOT a defect
Every staging artifact suspected during the run was chased down:
the root "unknown target" lines (wrong check method — superseded by
the corrective passes), the missing-olean lines for Assessed 6–10
(superseded: all PASS), and the three lean/ scripts first flagged as
artifacts (all three resolved to real defects, T3/T4). The merged
log's counts were verified two ways (script total and independent
grep counts: 222 + 40 + 16 = 278).

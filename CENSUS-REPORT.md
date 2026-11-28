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

## Branch 1 re-measure (2026-11-27 18:27) — parse fix verified, gate NOT passed

Fix applied: `h̃` → `hTilde` at lines 114–115 (the only code
occurrences; comment occurrences untouched). Byte delta +6, verified.
The 114:6 parse error is GONE — the file now elaborates to the end
and fails on three deeper, distinct defects (build exit=1, 196s):

- B1-D1 (272:2): `simp made no progress` inside
  `BSD_Finsupp_abs_prime_pow` — the `simp only
  [BSD_Finsupp_abs_prod_OPEN]` unfold step does not fire.
- B1-D2 (336:2): unknown identifier `BSD_Genesis775_Combinator` —
  the proof term of `BSD_extended_chain`. The name exists as a
  theorem in 143's BSD_Genesis775_CLOSED.lean:256; not imported here
  (file imports only hasseprimset.BSD_antisupersingular).
- B1-D3 (314:0): type of `BSD_extended_chain` is not a proposition —
  its conclusion `BSD_143_OPEN` is not a Prop as defined.

Per the branch gate (commit only if all 6 PASS; importers only if
the generator passes): NO commit, importers NOT run. The parse fix
stays in the working tree, uncommitted. B1-D1/D2/D3 are outside
Branch 1's parse-fix scope — disposition is David's call.

## Branch 1a re-measure (2026-11-27 18:40) — STOPPED on a second duplicate

Rename landed per David's ruling (BSD_Regulator_OPEN →
BSD_Regulator143_OPEN at the def + the _hReg use; body
byte-identical, verified). Four imports landed; line-272 simp
dropped. Re-measure (exit=1, 53s) fails at IMPORT time, line 1:0:

  import Towers.BSD.BSD_Frobenius_Certificate failed, environment
  already contains 'Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN'
  from Towers.BSD.BSD_Frobenius_Certificate_Clean

The pair is pre-existing in the tree (Certificate:183 and _Clean
both define BSD_FrobeniusDegreeNonneg_OPEN — the fast lane's
standing warning: never import both into one file). The generator's
pre-1a closure held at most one side; the 1a import set brings both
into one environment. D1/D3 could not be tested — the failure is
upstream of them. Per David's stop rule: NO second rename, NO
import trimming without a new ruling. Working tree holds the 1a
edits uncommitted, exactly as measured.

## Closure map for the 1a collision (2026-11-27 18:47, import-graph BFS)

- _Clean side (pre-existing): the generator's ORIGINAL import
  hasseprimset.BSD_antisupersingular reaches
  BSD_Frobenius_Certificate_Clean via WeilDeligne_Closed and the
  hasseprimset Hasse_Points chain (971_997 → … → 251_307 → _Clean).
- Certificate side (new): exactly ONE of the four 1a imports pulls
  it — Towers.BSD.BSD_AnalyticCapstone, via Genesis749 →
  RankLFunction → RankCapstone → KolyvaginPath →
  BSD_Frobenius_Certificate.
- B03_LFunction, BSD_LFunction, BSD_MissingDefinitionsRegistry
  reach NEITHER side.
- Trim check against the four needed names: BSD_143_OPEN (B03),
  BSD_BSDFormula_OPEN (BSD_LFunction), BSD_WeilHasse (Registry)
  all stay reachable without the capstone. BSD_LFunctionIsLinFunc_OPEN
  does NOT — its only definition home is BSD_AnalyticCapstone:212.
  Per David's trim rule, the trim STOPS here: dropping the capstone
  loses a needed name. Awaiting his ruling on the alternatives.

## Zenodo mints (2026-11-27)
- First mint: version DOI 10.5281/zenodo.24616022 (release
  bsd-census-2026-11-27 @ eae7c368). Metadata came from the old
  in-tree .zenodo.json (old title, placeholder version string).
  SUPERSEDED — kept in the version history as the audit trail,
  do not cite, do not delete.
- Second mint: version DOI **10.5281/zenodo.24616194** — the DOI to
  cite. Corrected .zenodo.json committed on bsd-census-2026-11-27
  (0c40e37b, parent eae7c368; metadata only, Lean tree
  byte-identical), release bsd-census-2026-11-27.1. Record carries
  the census title and version "bsd-census-2026-11-27", verified
  via the Zenodo API. Concept DOI unchanged:
  10.5281/zenodo.22048585.

## Branch 1a re-measure 2 (2026-11-27 18:52) — CLEAN, D2 sole FAIL

David's third shape landed: BSD_antisupersingular dropped outright
(use-list proof: the only code names drawn from its closure —
BSD_PrimePowBound_OPEN, a_n, a_prime_pow, a_n_prime_pow — all live
in BSD_LFunction, already a 1a import; BSD_PrimePowBound_PROVED is
comment-only). The file now imports exactly the four 1a modules.
Re-measure (exit=1, 67s): the SOLE error is D2 —
BSD_Genesis775_Combinator unknown at 338:2. D1 gone, D3 gone, no
duplicate-declaration (only the Certificate side remains, via the
capstone). Import set proven right; Branch 1b (Genesis775 take) is
unblocked.

## Post-fix schedule (David's ruling, 2026-11-27 18:53) — gated, not timed

After all 6 fix branches:
1. Merge branches 1–6 into bsd-census-fixed, one at a time,
   re-measure after each merge.
2. DOI TITLE CHECKPOINT — STOP, do not mint yet. Open in-tree
   .zenodo.json and confirm all four: (a) title matches the FIXED
   tree, not the census title; (b) version field = exact tag of the
   fixed-tree release, no placeholder; (c) creator line stays
   Fox, David — Opera Numerorum — ORCID; (d) description matches
   the fixed-tree re-measured counts, not the census counts.
   Only after all four check out → tag → release → mint.
3. README honesty audit, every folder.
4. Mint the fixed-tree DOI — new version DOI under concept
   10.5281/zenodo.22048585, superseding 10.5281/zenodo.24616194
   for citation. The Justin-awards packet cites the new DOI only.
(Rationale: the census mint shipped the old in-tree title because
Zenodo reads .zenodo.json from the tree — the checkpoint exists so
the fixed-tree mint doesn't repeat it.)

## Branch 1b — chain take progress + STOP at LAnalytic_Anchor (2026-11-27 19:0x)

David fired 1b. Closure of Genesis775 in 143 = 70 Towers modules;
only TWO missing in 143a1 (BSD_ClassNumber_10_CLOSED — byte-identical
to 143a1's lean/ payoff copy, placed at Towers/BSD/ — and
BSD_Genesis737_CLOSED). Take set: 24 files (TorsionSha new;
LAnalytic_Anchor + Multiplicativity extract->full; Genesis737,
757-775, ClassNumber_10 new). PASS so far (6): TorsionSha 37s,
ClassNumber_10 42s, Genesis737 8s, Genesis757 5s, Multiplicativity
4s, Genesis758 5s.
STOPPED at BSD_LAnalytic_Anchor_CLOSED (143 full version): it defines
BSD_LFunctionIsLinFunc_OPEN at ROOT (line 81, body
`BSDLFunction 143 = L_143a1`, no namespace) — a second Gate-2 home
colliding with the canonical Towers.BSD def in the capstone (:212,
body BSD_L143a1_BSDLFunction_ID_OPEN). Ambiguity errors at 107:9 and
131:31. In 143 no collision existed (its capstone has no such alias;
the alias is a 143a1 consolidation addition, "defined ONCE, here").
Definition-level collision — awaiting David's ruling; no improvisation.
Candidate A: anchor yields — delete its root def, qualify its refs to
Towers.BSD.BSD_LFunctionIsLinFunc_OPEN (capstone stays canonical).

## Branch 1b — chain stop at Genesis763 (2026-11-27 19:26)

Ruling A landed at the anchor: root Gate-2 def deleted, refs qualified
to Towers.BSD.BSD_LFunctionIsLinFunc_OPEN (107 + sentinel), rw [h] ->
rw [h.symm]; its dangling docstring converted /-- -> /- (text
preserved). ANCHOR PASS 10s. Flip propagation (same ruled pattern):
Genesis760 x2 + Genesis762 x2 rw [h] -> rw [h.symm] — 760 PASS 32s,
761 PASS 8s, 762 PASS 7s, 759 PASS 10s.
STOPPED at Genesis763 (233s): private helper BSD_disc_from_deg_763
{p} (h : BSD_FrobeniusDegreeNonneg_OPEN p) cannot elaborate — the def
(both Certificate:184 and _Clean:16, identical) takes [Fact p.Prime],
unbindable at variable p. The identical helper signature appears in
Genesis763-774 (12 files, all takes, byte-identical to 143) — a
never-compiled family inside the chain; the "original in 762" exists
nowhere. All helper uses are at concrete primes with file-local
private Fact instances. Drafted repair: add [Fact p.Prime] to the
helper binder in each of the 12 files (private lemma, no external
signature change). OPEN sub-question: 763's by-decide card theorems
whnf-timeout at 85:64/86:64 (p257/p263) — may be cascade or a second
defect (fast-route port is the house precedent); re-measure after the
helper repair decides. Awaiting David's ruling — chain held at 763.

## Branch 1b-ii — helper family ruled INTO Branch 1 (David, 2026-11-27 19:31)

Branch-4-scale family surfacing inside Branch 1, ruled into 1b-ii —
separate commit, separate gate. Not a split (a split deadlocks: the
generator needs 775, which needs 763-774). Repair: add [Fact p.Prime]
to the private helper binders in Genesis763-774 (12 files). Also
ratified: the 4 h.symm flip sites (760 x2, 762 x2) and the anchor
docstring /-- -> /- conversion. Gate: 763 alone first — its
re-measure decides whether the p257/p263 decide timeouts were
cascade; then 764-774 one at a time (verify instances/use-sites per
file first); then 775 -> generator -> 5 importers.

## Branch 1b-ii — Genesis763 CLEAN + axiom audit (2026-11-27 19:44)

763 PASS (24s) with three repairs: helper [Fact p.Prime] binder;
10 cards by decide -> by native_decide (kernel decide whnf-timeout
was a second defect, not cascade — native_decide closes p257 in 5s
scratch time; the _Clean-side E143_card_eq_fast route deliberately
NOT imported, it would trip the Certificate/_Clean duplicate);
combinator proof-term projection (BSD_Genesis762_Combinator ...).1,
statement untouched (762 returns the conjunction; 763 is the only
mismatched link in 763-775).
AXIOM AUDIT (#print axioms, 763, David's condition — named, not
buried): BSD_E143_card_p257 = [propext, Classical.choice,
Lean.ofReduceBool, Quot.sound]; BSD_DegreeNonneg_p251 (card
consumer) = same, ofReduceBool propagates along the card line;
BSD_Genesis763_Combinator = [propext, Classical.choice, Quot.sound]
— classical trio only (the combinator takes the discriminant
hypothesis as input, so the footprint stays contained in the
card/DegreeNonneg line). Trio-only claims elsewhere are unaffected;
any theorem consuming the ported cards carries ofReduceBool and is
reported as such.
Rollout to 764-774 approved as scoped (helper + cards only, no
projection above 763; stop on any non-pattern failure). Family
pattern verified per file: 764-773 = 10 cards/10 instances/10 helper
uses each; 774 = 5/5/5.

## Branch 1 extension (David's ruling, 2026-11-27 20:19)

Branch 1 extended by one line — importer-chain root, same repair as
ClassGroupBridge — gate amended, not waived. The five importers form
a chain (generator <- abs_prod_real <- aNBound_bridge <-
Finsupp_prod_le <- tau_le_two_sqrt <- TauBound_small_proved);
abs_prod_real is their root and carried a pre-existing defect masked
by the generator's parse error: Finset.prod_insert over abstract
alpha with no DecidableEq at 48:24. Repair: `classical` as first
tactic (scratch PASS 25s; signature and statement untouched).
Generator PASS 8s (D1+D2+D3 closed). Gate: abs_prod_real alone, then
the chain in order; commit only on 6/6; any further defect in links
2-5 stops that link without auto-extending again.

## Branch 1 — bounded mandate for abs_prod_real (David, 2026-11-27 20:26)

Defect log for hasseprimset/BSD_abs_prod_real (each its own line):
- 48:24 DecidableEq (Finset.prod_insert over abstract alpha) —
  classical first tactic. PASS layer.
- 166:29 PNat.divisors does not exist — coercion to
  ((n : Nat).divisors.card : R) in the calc's first step, matching
  hbound's unfolded type. Verified in-context 3s before landing.
Mandate: proof-term / coercion / classical-class repairs only, in
this file only, statements untouched, no new imports, re-measure
after each; stop on any character change. Links 2-5 remain under
the original stop rule.
- abs_prod_real PASS (18s) after the two mandate repairs; no third
  layer. Mandate closed for this file.

## Branch 1 — classical-class mandate, links 2-5 (David, 2026-11-27 20:34)

Chain-scoped mandate: `classical` as first tactic ONLY for
Finset.prod_insert / DecidableEq synthesis failures in links 2-5
(the importer chain is one authored unit for this defect family).
Statements/signatures untouched; each site logged (file, lemma,
line); re-measure each file alone; any different defect stops cold.
Site log:
- link 2 BSD_aNBound_Finsupp_bridge_close, private lemma
  finset_prod_int_cast, 47:24 DecidableEq iota — classical.
  (Scratch PASS 13s before landing.)
- link 2, finset_prod_nat_cast, 104:24 DecidableEq iota — classical.
- link 2, sqrt_finset_prod, 119:8 DecidableEq iota — classical.
- link 2, BSD_card_divisors_close, 165:4 — dead simp
  [Nat.primeFactors] after convert closed the goal; deleted
  (David's ruling 2026-11-27 20:36; same shape as generator D1).
  Dead-simp / proof-term deletions of this exact shape are now
  approved chain-wide for links 3-5 on the same terms (log each
  site, re-measure each file, stop on any different class).
- link 3 BSD_Finsupp_prod_le_close, BSD_Finsupp_prod_le_close
  second bullet: split_ifs discharged the not-Prime branch via
  hprime in context (one goal, not two) — dead else-bullet deleted;
  hGate1 argument <h> replaced by the installed hfact : Fact
  p.Prime. Proof-term repair, David's ruling 2026-11-27 20:40.
  (Scratch PASS 4s before landing.)
- link 4 BSD_tau_le_two_sqrt, tau_le_two_sqrt hd/hcov blocks:
  set-opacity blocked the Finset.mem_filter simp rewrite the
  author's anonymous-constructor patterns assumed (filter
  membership routes through Multiset, not defeq to the And).
  Rewritten at term level with mem_filter.mp/.mpr (David's
  ruling 2026-11-27 20:43). Have statements untouched.
- link 4 repair package (David's ruling 2026-11-27 20:53; whole
  file scratch PASS 9s before landing; 34 lines, proof bodies
  only): membership-to-dvd conversions via Nat.mem_divisors.mp
  (hmap/hinj/hlo_le) + one reverse mpr; heq' ascription for the
  InjOn beta-redex; Finset.card_Icc -> Nat.card_Icc; hsq_real
  rebuilt on Real.le_sqrt_of_sq_le; final linarith casts pinned
  to R; section 5b refine drops the nonexistent positivity
  component (link 3 house pattern).
- link 5 BSD_TauBound_small_proved, finset_prod_cast, 95:8
  DecidableEq alpha — classical (chain mandate).
- link 5, finset_prod_rpow, 106:8 DecidableEq alpha — classical
  (chain mandate).
- link 5 repair package (David's ruling 2026-11-27 21:09; whole
  file scratch PASS 14s before landing; 77 diff lines, proof
  bodies only): rename_i drops the third name; pow_succ ->
  pow_succ'; (2 : R) ascriptions at B and the ceil sites;
  Bernoulli sub_add_cancel simp replaced by an explicit h1beta
  rewrite; filter binders annotated (fun p : Nat => ...);
  rpow_bridge dead congr deleted; two membership rewrites routed
  through ascribed hmem'; hpe_eq rpow_natCast step dropped,
  mul_one_div_cancel for hmul; subset step rebuilt on prod_sdiff
  + prod_le_prod (prod_le_prod_of_subset_of_one_le' does not
  unify for R — OrderedCommMonoid instance mismatch).

## Branch 1 — 6/6 VERDICT (2026-11-27 21:11)

Combined verification run (run-logs/b1-final-verify.log), same
tree, chain order: generator PASS 6s, abs_prod_real PASS 4s,
aNBound_Finsupp_bridge PASS 2s, Finsupp_prod_le PASS 2s,
tau_le_two_sqrt PASS 2s, TauBound_small_proved PASS 2s.
TOTAL 6/6. Branch 1 commit gate met. The full extension log is
the line-by-line record above: 1a imports + Regulator rename,
1b Genesis775 take + Gate-2 flip (Ruling A), 1b-ii 763-774
helper/card family + 763 axiom audit, 775 proof repair, and the
importer-chain repairs (classical sites, line-166 coercion,
dead-simp deletion, split_ifs collapse, mem_filter rewrite,
membership/dvd conversions, subset-step rebuild).

## Branch 1 — LANDED (recorded post-commit, 2026-11-27)

Branch fix/hasseprimset-anbound-114, base bsd-census-2026-11-27
@ 0c40e37b. Three commits, verified by git ls-remote AND GitHub
API (tip + parent chain agree):
- 3cd23996a5924548826bde32c2778c0004cde35d — 1a+1b (12 files)
- 8df36b3545851cd9973be75daf13a10fdd104e89 — 1b-ii (12 files)
- 23499e950e0f97d19531136c5283e3c0071b9ce6 — 775 + chain (7 files)
Branch 1 CLOSED. (This line postdates the committed report by
construction — a commit cannot cite its own SHA.)

## Branch 2 — fix/import-paths-4 (fired 2026-11-27 21:18)

- BostBound143.lean: Mathlib.NumberTheory.QuadraticForm.Basic ->
  Mathlib.LinearAlgebra.QuadraticForm.Basic (verified on disk in
  the pinned Mathlib; the NumberTheory path does not exist).
- lean/02_hecke_operators.lean: Mathlib.Analysis.UpperHalfPlane.
  Basic -> Mathlib.Analysis.Complex.UpperHalfPlane.Basic
  (verified on disk).
- Dependency found: the Regulator script USES BostExplicitBound
  (Bost_bridge_for_737 := MathlibGaps.Bost_bound_c54_gt), and
  Towers E143a1 USES the Regulator script (BSD_Regulator_CLOSED,
  BSD_TamagawaConj_CLOSED). BostExplicitBound is Branch 4a's
  noncomputable fix — both files' standalone PASS gates on it.
- BostBound143 body defects (past the import fix): Real.sqrt /
  OfScientific never imported; C_S4 proof's linarith cannot use
  decimal literals. Package scratch PASS 3s: add Mathlib.
  Data.Real.Sqrt; h1 via Real.sqrt_lt' with fraction 36056/10000;
  h2 : C_S4 = 1142214868898/100000000000 by norm_num [C_S4];
  linarith. (Package held for ruling — proof-body class.)
- Hecke body defects (past the import fix): statement |>.im
  never lands on the division (LT C synthesis) — parentheses;
  Nat.ne_zero_of_lt -> hp.ne'; hdiv leftover associativity goal
  closed by ring; smul him_eq dead ring deleted; hecke_T_smul
  closer is congr 1 + rw [mul_add, Finset.mul_sum]; finset_decide
  (unknown tactic) -> fin_cases hp <;> norm_num. Whole-file
  scratch PASS 5s, no sorryAx. (Package held for ruling.)
- BostExplicitBound is TWO defects, not 4a's one word:
  noncomputable for Bost_c54 (census error) AND Finset.card not in
  scope — needs Mathlib.Data.Finset.Card. Both drafted;
  scratch-verified below.
- E143a1_CLOSED: four import fixes landed (Genus_X0_143,
  BostBound_143, BSD_TorsionSha_CLOSED out of MathlibGaps;
  BSD_Regulator_RealPeriod_Closed -> lean.BSD_Regulator_
  RealPeriod_Closed).
- E143a1 line 11 CORRECTION: lean.BSD_Regulator_RealPeriod_
  Closed is a bad import (no such module); the bare name
  BSD_Regulator_RealPeriod_Closed was right all along — its
  census failure was the target's missing olean. Line restored.
  Branch 2's E143a1 edits are the three MathlibGaps fixes.
- E143a1 dependency web: Genus_X0_143 is a headless extract with
  NO imports (ZMod unknown; census FAIL, T4 family) and the
  Regulator script gates on BostExplicitBound. E143a1 cannot
  re-measure PASS until both build.
- Branch 4a EARLY — BostExplicitBound, pulled forward to
  unblock Regulator (David's ruling 2026-11-27 21:25):
  noncomputable on Bost_c54 + Mathlib.Data.Finset.Card import.
  Branch 4 records this item as already landed; do not re-do.
- BostBound143 body package LANDED (David's ruling 21:25):
  Real.Sqrt import + sqrt_lt' fraction proof (see above).
- Hecke body package LANDED (David's ruling 21:25): parens,
  hp.ne', hdiv ring, dead ring deleted, smul congr/rw closer,
  fin_cases (see above).
- Branch 2 verdicts (2026-11-27 21:27): BostExplicitBound
  PASS 12s (module build), Regulator PASS 17s (no edits to the
  file itself), BostBound143 PASS 5s, Hecke PASS 4s. Amended
  gate met: three PASSes in hand together. E143a1 OPEN pending
  Genus_X0_143 (Branch 4) — its three import fixes are landed
  and ride this branch's commit as an open line.

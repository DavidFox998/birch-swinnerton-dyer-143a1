## Status — 2026-11-27 (read first)

- **Toolchain:** Lean 4.12.0 / Mathlib v4.12.0 throughout. No 4.35 migration has started; there is no 4.35 toolchain on the build machine.
- **main:** `origin/main` = `14f39936c0c21bbc89492a074a798c1e2fa87d2a` — the 2026-11-26 consolidation (quarantine + registries) is merged and pushed.
- **Strengthened tree:** the class-number strengthening (h(ℚ(√−143)) = 10 unconditional, classical-trio axioms only, verified locally 2026-11-26) is UNCOMMITTED working-tree state — it has no SHA yet. A reviewer sweep of all 260 build-scope modules is in flight (68 logged at first check: 34 PASS / 34 FAIL); the census of the remainder runs on a rented machine while the known defects are fixed first (David's reorder, 2026-11-27), then the tree is pushed on a branch for review. None of it is merged or submitted.
- **Table machinery:** the a_p table generator is in `table-machinery/` on branch `table-machinery-v1` (commit `80696772a1446719acb1cedf79f376eafbc7f402`), NOT merged to main.
- **p4-p5 follow-up** (missing-primes drift): DEFERRED — parked outside this repo in the consolidation workspace (`docs/followups/missing-primes-p4-p5-drift.md`); it resumes only after the MathDB submission is recorded.

---

# quarantine/

Files removed from the build scope by the 2026-11-26 consolidation,
kept for the record. Nothing here is imported by the build, and CI
guards against these files being imported or their contents returning
to the tree.

- `BSD_Frobenius_Certificate_SORRY.lean` — held the tree's one genuine
  `sorry` (the ∀p Hasse bound). Quarantined, not discharged; the Hasse
  bound in the current tree stands on the table audit and the
  Frobenius-certificate bridge, not on this file.
- `hassewiles.lean`, `B02_stub_fragment.lean` — carried a_p tables that
  disagree with the curve equation. Wrong tables; never import. (The
  verified table is generated from the equation by `table-machinery/`.)
- `BSD_L143a1_BSDLFunction_ID_PROVED.lean` — the Gate-2 "impostor":
  its proof term was an `rfl` self-identity against a stub. Gate 2 is
  defined exactly once in the tree, as OPEN, in
  `Towers/BSD/BSD_AnalyticCapstone.lean`.
- `C02_Modularity_X0_143_Standalone_OPEN.lean` — OPEN surface removed
  from build scope in the consolidation.

## Added 2026-11-27 — reviewer fix pass (headless extracts that never compiled in this tree)

Fourteen files from `Towers/BSD/`, each a "ported closed theorems"
extract that fails within its first lines and is imported by no build
module. First error in this tree given for each; full record in the
consolidation workspace (`FIX-LOG.md`, `REVIEWER-FIX-QUEUE.md`).

- `BSD_BSD_AnalyticOn_L143a1.lean` — 3:39 function expected at.
- `BSD_BSD_FourGateCombinator.lean` — 9:5 failed to synthesize.
- `BSD_BSD_FrobeniusAnalytic_Combinator.lean` — 12:5 failed to
  synthesize. (Its only importer is the standalone script
  `lean/BSD_EndDeg_Combinator_Closed.lean`, broken by this dependency
  either way.)
- `BSD_BSD_FuncEq.lean` — 4:2 invalid constructor ⟨...⟩.
- `BSD_BSD_GrossZagier_LMFDB.lean` — 4:11 unknown identifier
  `BSD_AnalyticRankOne_CLOSED`, which is defined nowhere in either repo.
- `BSD_BSD_GrossZagier_v2.lean` — 27:5 unknown tactic.
- `BSD_BSD_L143a1_zero_at_one.lean` — 5:3 unknown tactic.
- `BSD_BSD_Ramanujan_from_Discriminant.lean` — 9:53 unknown tactic.
- `BSD_BSD_TwoGateCombinator.lean` — 10:5 failed to synthesize.
- `BSD_BSD_VanishingOrder_143_Genuine.lean` — 4:43 type mismatch.
- `BSD_ArakelovHeight_Closed.lean` — 5:56 unknown tactic; no 143
  counterpart.
- `BSD_EulerProduct_Closed.lean` — 6:25 unknown tactic; no 143
  counterpart. (The proved Euler product lives in
  `Towers/BSD/MathlibGaps/LFunction143a1.lean`.)
- `BSD_GrossZagier_Closed.lean` — 5:3 unknown tactic; no 143 counterpart.
- `BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED.lean` — imports a
  module that does not exist. This one is NOT a dead extract: it is the
  curve-side front end of the batch-155 route (deg(a − b·Frob) ≥ 0 ⇒
  Hasse), waiting on the unbuilt End(E) layer — the open props
  `FrobNormDeg_143_OPEN` and `HasseBound_143a1_OPEN`. Quarantined until
  that layer exists; do not read its presence here as a verdict on the
  route.

## Added 2026-11-27 — the Clay pair (David's decision)

- `BSD_Clay_Certificate.lean`, `BSD_Clay_6gate_CLOSED.lean` — moved
  verbatim. Per-file note: "Depends on TheoremaAureum Arakelov
  machinery in RH repos (Towers.RH.Chain...), not present in this
  tree. 6gate downstream of Clay_Certificate. Submission does not
  need Clay-compliance combinator. BSD remains OPEN per registries.
  Deferred dependency, not a dead end." Nothing else in the tree
  imports either file (verified by grep before the move).

What this folder does NOT claim: that anything here is proved,
buildable, or safe to import. It is a record of what was removed and
why.

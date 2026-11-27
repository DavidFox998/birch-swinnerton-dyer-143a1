## Status — 2026-11-27 (read first)

- **Toolchain:** Lean 4.12.0 / Mathlib v4.12.0 throughout. No 4.35 migration has started; there is no 4.35 toolchain on the build machine.
- **main:** `origin/main` = `14f39936c0c21bbc89492a074a798c1e2fa87d2a` — the 2026-11-26 consolidation (quarantine + registries) is merged and pushed.
- **Strengthened tree:** the class-number strengthening (h(ℚ(√−143)) = 10 unconditional, classical-trio axioms only, verified locally 2026-11-26) is UNCOMMITTED working-tree state — it has no SHA yet. A reviewer sweep of all 260 build-scope modules is in flight (68 logged at last check: 34 PASS / 34 FAIL); defects are fixed after the sweep, then the tree is pushed on a branch for review. None of it is merged or submitted.
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

What this folder does NOT claim: that anything here is proved,
buildable, or safe to import. It is a record of what was removed and
why.

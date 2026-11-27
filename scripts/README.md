## Status — 2026-11-27 (read first)

- **Toolchain:** Lean 4.12.0 / Mathlib v4.12.0 throughout. No 4.35 migration has started; there is no 4.35 toolchain on the build machine.
- **main:** `origin/main` = `14f39936c0c21bbc89492a074a798c1e2fa87d2a` — the 2026-11-26 consolidation (quarantine + registries) is merged and pushed.
- **Strengthened tree:** the class-number strengthening (h(ℚ(√−143)) = 10 unconditional, classical-trio axioms only, verified locally 2026-11-26) is UNCOMMITTED working-tree state — it has no SHA yet. A reviewer sweep of all 260 build-scope modules is in flight (68 logged at last check: 34 PASS / 34 FAIL); defects are fixed after the sweep, then the tree is pushed on a branch for review. None of it is merged or submitted.
- **Table machinery:** the a_p table generator is in `table-machinery/` on branch `table-machinery-v1` (commit `80696772a1446719acb1cedf79f376eafbc7f402`), NOT merged to main.
- **p4-p5 follow-up** (missing-primes drift): DEFERRED — parked outside this repo in the consolidation workspace (`docs/followups/missing-primes-p4-p5-drift.md`); it resumes only after the MathDB submission is recorded.
- The older text below predates the consolidation. Where it conflicts with `OPEN-REGISTRY.md`, `PLACEHOLDER-REGISTRY.md`, or this block, the registries and this block govern. BSD itself remains OPEN; in the consolidated tree Gate 2 stands as an OPEN definition, and the OPEN surfaces are named in the registries.

---

# scripts

This directory holds scripts that are not part of the proof.

## Standing rules

- No one runs anything under `deprecated-*/`. That includes humans and agents. Files there are kept so the history is readable. They are not tools.
- No proof file is ever regenerated from a script without explicit human approval first. That covers `hasseprimset/`, `Towers/BSD/`, `lean/`, `ap_table.json`, and any file a script would overwrite.

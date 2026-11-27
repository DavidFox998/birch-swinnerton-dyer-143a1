## Status — 2026-11-27 (read first)

- **Toolchain:** Lean 4.12.0 / Mathlib v4.12.0 throughout. No 4.35 migration has started; there is no 4.35 toolchain on the build machine.
- **main:** `origin/main` = `14f39936c0c21bbc89492a074a798c1e2fa87d2a` — the 2026-11-26 consolidation (quarantine + registries) is merged and pushed.
- **Strengthened tree:** the class-number strengthening (h(ℚ(√−143)) = 10 unconditional, classical-trio axioms only, verified locally 2026-11-26) is UNCOMMITTED working-tree state — it has no SHA yet. A reviewer sweep of all 260 build-scope modules is in flight (68 logged at last check: 34 PASS / 34 FAIL); defects are fixed after the sweep, then the tree is pushed on a branch for review. None of it is merged or submitted.
- **Table machinery:** the a_p table generator is in `table-machinery/` on branch `table-machinery-v1` (commit `80696772a1446719acb1cedf79f376eafbc7f402`), NOT merged to main.
- **p4-p5 follow-up** (missing-primes drift): DEFERRED — parked outside this repo in the consolidation workspace (`docs/followups/missing-primes-p4-p5-drift.md`); it resumes only after the MathDB submission is recorded.
- The older text below predates the consolidation. Where it conflicts with `OPEN-REGISTRY.md`, `PLACEHOLDER-REGISTRY.md`, or this block, the registries and this block govern. BSD itself remains OPEN; in the consolidated tree Gate 2 stands as an OPEN definition, and the OPEN surfaces are named in the registries.

---

## Birch Swinnerton-Dyer 143a1 — 3-Gate status (genesis-173; corrected 2026-11-27 — gates per registry, Gate 2 OPEN, BSD OPEN)

**Lean 4.12.0 · Mathlib v4.12.0 · CI: Refactor imports to MathlibGaps for BSD_143 #173 ✅**
**Axioms: {propext, Classical.choice, Quot.sound} only · 0 sorry**

### Gate 1 — Hasse bound |a_p| ≤ 2√p

> **Corrected 2026-11-27:** the CLOSED labels in this table predate the
> consolidation; `OPEN-REGISTRY.md` governs. The standing a_p table is
> the machinery-generated one — 1,065 entries, primes ≤ 8,563, verified
> from the curve equation (`table-machinery/`).
| Component | File | Status |
|---|---|---|
| Hasse 1061 primes p ≤ 997 | `Towers/BSD/HassePrimeSet.lean` | **CLOSED** — `ap_table.json` → 1061, single source, 0 sorry |
| AP Table 168 traces + Hasse proofs | `Towers/BSD/BSD_AP_Table_Closed.lean` + `Traces_E1859_All_168.lean` | **CLOSED** — by `rfl` / `decide` |
| Aggregate audit | `aggregate.py` → artifact | **GREEN** — 1061 loaded, 1061 written |

### Gate 2 — Class number h(Q(√-143)) = 10

> **Corrected 2026-11-27:** the component labels in this table predate
> the consolidation; the registries govern. The class-number result
> h(ℚ(√−143)) = 10 is unconditional in the strengthened tree — which is
> UNCOMMITTED working-tree state (see Status block), not in main.
| Component | File | Status |
|---|---|---|
| K = Q(√-143), O_K, ω | `BSD_NumberField.lean` | CLOSED |
| disc = -143 irreducible | `BSD_Discriminant.lean` | CLOSED |
| Z-basis {1,ω} | `BSD_IntBasis.lean` | CLOSED |
| 10 reduced BQFs | `BSD_ReducedForms.lean` | CLOSED — `rfl` 10 forms |
| Lower bound 10 ≤ h(K) | `BSD_ClassNumberLowerProof.lean` | CLOSED — p2^k non-principal k=1,3,5,7,9 |
| Minkowski witness | `BSD_ClassNumber_UpperBound_CLOSED.lean` | CLOSED |
| w3/w4 ideal equalities | `BSD_SurfaceClose_CLOSED.lean` | CLOSED |
| Kodaira c4=64 nonsplit | `BSD_KodairaReduction_CLOSED.lean` | CLOSED |
| Option A: gen_OK=-28+3ω N=1024 p2^10 principal | `BSD_P2_Principal_CLOSED.lean` + `BSD_AlgNorm.lean` + `BSD_ClassNum_Upper_CLOSED.lean` | **CLOSED** |
| Option B: BQF bridge | `BSD_BQF_Bridge_Closed.lean` | **CLOSED** |
| ClassGroup = <[p2]> order 10 | `BSD_ClassGroup_Generator_CLOSED.lean` | **CLOSED** |

### Gate 3 — Modular curve + Bost + BSD arithmetic

> **Corrected 2026-11-27:** the CLOSED labels in this table predate the
> consolidation; `OPEN-REGISTRY.md` governs. The L-function Gate 2
> (`BSD_LFunctionIsLinFunc_OPEN`) stands OPEN and BSD remains OPEN.
| Component | File | Status |
|---|---|---|
| Curve scaffold + Sha/Tors anchors | `B01_EllipticCurve.lean` + `BSD_LFunction.lean` | CLOSED |
| Rational point (4,6) | `BSD_HeegnerPoint_CLOSED.lean` | CLOSED |
| Genus X0(143)=13 | `Towers/BSD/MathlibGaps/Genus_X0_143` (Diamond-Shurman) | CLOSED — `norm_num` |
| Bost bound C(S4)>2√13 | `Towers/BSD/MathlibGaps/BostExplicitBound.lean` + `BostBound_143` | **CLOSED** — Refactor Bost constants #173 |
| Functional eq / Mellin | `CPSFunctionalEquation.lean` + `MellinAnalyticExt.lean` | CLOSED — explicit |
| Tors=1 Sha=1 Regulator>0 Tamagawa | `E143a1_CLOSED.lean` | **CLOSED** — capstone 0 sorry |

### Terminal

> **Corrected 2026-11-27:** the checks below are the genesis-173
> snapshot. A reviewer sweep of all 260 build-scope modules is in
> flight (68 logged at last check: 34 PASS / 34 FAIL); the sweep
> governs current build status.

| Check | Result |
|---|---|
| `lake build` | ✅ 18/18 built (Cache + BSD) |
| `grep -R "sorry" Towers/BSD` | 0 |
| `Check 0 sorry` workflow | ✅ #173 |
| Open surfaces remaining | 2 genuine Clay gaps: `BSD_HasseBound_Discriminant_OPEN` + `BSD_LFunctionIsLinFunc_OPEN` (Mathlib API absent v4.12.0) |

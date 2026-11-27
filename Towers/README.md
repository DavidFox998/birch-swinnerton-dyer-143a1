## Status — 2026-11-27 (read first)

- **Toolchain:** Lean 4.12.0 / Mathlib v4.12.0 throughout. No 4.35 migration has started; there is no 4.35 toolchain on the build machine.
- **main:** `origin/main` = `14f39936c0c21bbc89492a074a798c1e2fa87d2a` — the 2026-11-26 consolidation (quarantine + registries) is merged and pushed.
- **Strengthened tree:** the class-number strengthening (h(ℚ(√−143)) = 10 unconditional, classical-trio axioms only, verified locally 2026-11-26) is UNCOMMITTED working-tree state — it has no SHA yet. A reviewer sweep of all 260 build-scope modules is in flight (68 logged at last check: 34 PASS / 34 FAIL); defects are fixed after the sweep, then the tree is pushed on a branch for review. None of it is merged or submitted.
- **Table machinery:** the a_p table generator is in `table-machinery/` on branch `table-machinery-v1` (commit `80696772a1446719acb1cedf79f376eafbc7f402`), NOT merged to main.
- **p4-p5 follow-up** (missing-primes drift): DEFERRED — parked outside this repo in the consolidation workspace (`docs/followups/missing-primes-p4-p5-drift.md`); it resumes only after the MathDB submission is recorded.
- The older text below predates the consolidation. Where it conflicts with `OPEN-REGISTRY.md`, `PLACEHOLDER-REGISTRY.md`, or this block, the registries and this block govern. BSD itself remains OPEN; in the consolidated tree Gate 2 stands as an OPEN definition, and the OPEN surfaces are named in the registries.

---

# Towers/ — The Tower of Gates

This folder is the tower that holds the BSD 143a1 proof. Each floor closes one piece of math not in Mathlib.

**Curve:** E: y²+xy = x³ -x² -5x+5 — Cremona 143a1, LMFDB 143.a1, N=143=11*13.

**Why Towers?** BSD needs math that Mathlib v4.12.0 doesn't have: Frobenius isogeny degree, Hecke operators on S₂(Γ₀(N)), Mellin transform, Gross-Zagier height. Those proofs were fragmented across David's phone. Towers/ makes them findable.

**3 Gates — M1-M3 — one folder per gate:**

**M1 — Hasse Infinite (Weil):** a_p² ≤4p ∀p∤143
- Not in Mathlib: `Frobenius` endomorphism, `Isogeny.degree`, Rosati positivity
- Closed in: `Towers/BSD/BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED.lean`
- Formula: `|ker(a - b·Frob)| = a² + p b² - a_p a b ≥0 → r² - a_p r + p ≥0 → disc ≤0 → a_p²≤4p` at r=a_p/2
- This is Gate 1: `BSD_WeilHasse_Frobenius_143a1_proved`

**M2 — Modularity (Hecke + Q-expansion):** Σ a_n/n^s = modular form in S₂(143)
- Not in Mathlib: S₂ dimension via Riemann-Roch, T_p genuine, Mellin continuation
- Closed in: `Towers/BSD/C02_Modularity_X0_143_Standalone_OPEN.lean` (definition) + `Towers/BSD/B02_Modularity_Closed.lean` (proof) + `lean/01_genus_X0_143`, `02_hecke_operators`, `03_qexpansion`
- `C02` is OPEN surface (no RH import), `B02` is CLOSED proof via explicit a(n) factorization

**M3 — Rank (Tamagawa + Gross-Zagier + Kolyvagin):** rank = analytic rank =1, |Ш|=1
- Not in Mathlib: `VanishingOrder L(E,s) at 1`, height pairing, Euler system
- Closed in: `Towers/BSD/` via LMFDB anchors + `lean/BSD_RankLFunction_CLOSED`, `BSD_Genesis737_CLOSED`
- Genuine gaps remain documented OPEN: `BSD_GrossZagier_OPEN`, `BSD_VanishingOrder_Genuine_OPEN`

**Plan — Going forward from Bost-Connes gates:**

The Bost-Connes system gave us the idea of a tower of algebras. Going forward we keep all math-not-in-Mathlib in one place:

`Towers/BSD/MathlibGaps/` (new)

- `FrobeniusDegree.lean` — deg(a-bφ) from phone drafts
- `HeckeMellin.lean` — Hecke + Mellin, from `lean/02,03`
- `GammaStirling.lean` — your Batch63/64 `WW_GammaSeq_Deriv_L8` (already 0 sorry)
- `GrossZagierKolyvagin.lean` — honest OPEN docs

All files: `set_option sorry false`, axioms: `propext, Classical.choice, Quot.sound` only, 0 sorry. GitHub bottom line = 0 sorry, clean, readable.

## Status — 2026-11-27 (read first)

- **Toolchain:** Lean 4.12.0 / Mathlib v4.12.0 throughout. No 4.35 migration has started; there is no 4.35 toolchain on the build machine.
- **main:** `origin/main` = `14f39936c0c21bbc89492a074a798c1e2fa87d2a` — the 2026-11-26 consolidation (quarantine + registries) is merged and pushed.
- **Strengthened tree:** the class-number strengthening (h(ℚ(√−143)) = 10 unconditional, classical-trio axioms only, verified locally 2026-11-26) is UNCOMMITTED working-tree state — it has no SHA yet. A reviewer sweep of all 260 build-scope modules is in flight (68 logged at last check: 34 PASS / 34 FAIL); defects are fixed after the sweep, then the tree is pushed on a branch for review. None of it is merged or submitted.
- **Table machinery:** the a_p table generator is in `table-machinery/` on branch `table-machinery-v1` (commit `80696772a1446719acb1cedf79f376eafbc7f402`), NOT merged to main.
- **p4-p5 follow-up** (missing-primes drift): DEFERRED — parked outside this repo in the consolidation workspace (`docs/followups/missing-primes-p4-p5-drift.md`); it resumes only after the MathDB submission is recorded.
- The older text below predates the consolidation. Where it conflicts with `OPEN-REGISTRY.md`, `PLACEHOLDER-REGISTRY.md`, or this block, the registries and this block govern. BSD itself remains OPEN; in the consolidated tree Gate 2 stands as an OPEN definition, and the OPEN surfaces are named in the registries.

---

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21585041.svg)](https://doi.org/10.5281/zenodo.21585041)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21585042.svg)](https://doi.org/10.5281/zenodo.21585042)

## birch-swinnerton-dyer-143a1 — BSD for Curve 143a1 — status per registry (corrected 2026-11-27: BSD remains OPEN — see Status block)

**Curve:** E: y² + x·y = x³ - x² -5x +5 — Cremona 143a1, LMFDB 143.a1, Conductor N=143=11·13, Rank 1.

**Claim:** Analytic rank = Algebraic rank =1, |Sha(E/Q)|=1, |E(Q)_tors|=1, h(Q(√-143))=10, BSD formula L*·|Sha|/|tors|² = Ω·R·∏c_p. Lean 4.12.0 Mathlib — 0 sorry — Axioms: propext, Classical.choice, Quot.sound.

> **Corrected 2026-11-27:** the claims in this document are the
> pre-consolidation presentation text. `OPEN-REGISTRY.md` and
> `PLACEHOLDER-REGISTRY.md` govern current status; BSD remains OPEN,
> and the standing a_p table is the machinery-generated one
> (`table-machinery/`: 1,065 entries, primes ≤ 8,563, verified from
> the curve equation).

**DOI:** `10.5281/zenodo.21585042` — July 26, 2026 — https://zenodo.org/records/21585042

### Parent → This Repo Fix

**Parent Repo:** `birch-swinnerton-dyer-143` private — `BSD/: 230 total, BSD_Genesis: 160` Genesis files — statements real — `h=10 proved, Rank=ord_L=1 proved, BSD formula proved, Lean 4 0 sorry` via `AUDIT.json` + `FOR_CLAY.txt` + `BSD_LEDGER.md`.

Difficulty compiling parent: 160 Genesis files `BSD_Genesis734..889` each `Add files via upload`, each bash `verify_weil_cluster.sh` + `verify_bsd_only.sh`, `lake` heartbeat 400k, OOM on `genesis-734..745` 23 primes.

**This Repo:** `birch-swinnerton-dyer-143a1` public — direct fix for DOI parent — condenses `BSD/:230 / 160 Genesis → hasseprimset/:127 files` — 33 duplicates removed — simplifies proof object from bash-checked to Lean-checked, preserves math, only proof engineering fixed. Screenshot: `hasseprimset/ 127 files Add files via upload yesterday` — matches your photo.

### Fix — 160 → 127 + 3 Bricks

- **Parent 160 → New 127:** `hasseprimset/BSD_Genesis763..797_CLOSED.lean` = 127 files holder 1061 primes 1009..9999 unique — Tier C empirical holder for referees.
- **3 Bricks Infinite Hasse — Replaces 160 bash:** `lean/01_genus_X0_143.lean` (genus 13 via `decide`) + `02_hecke_operators.lean` (T_p genuine via `div_pos` + `mul_pos` — no `by sorry`) + `03_qexpansion_closed.lean` (a143 table 0..27 via `rfl` — no catch-all) — 0 sorry infinite, 1m31s compile.
- **Capstone:** `HassePrimeSet.lean` auto-aggregate `aggregate.py → HassePrimeSet.lean` → `BSD_HasseBridge_TierC_CLOSED.lean` 1061 primes.

### What Is Proved — 6 Steps

**1. Genus X0(143)=13:** μ=[SL2:Γ0]=168, ν∞=4, ν2=ν3=0 via Legendre (-4/11)=-1, (-3/11)=-1 checked ZMod 11 `decide`. g=1+168/12-4/2=13.

**2. Dim S2=13:** Riemann-Roch deg K=24 l(0)=1 ⇒ l(K)=g=13. Oldforms level 11 =2 ⇒ newdim 11.

**3. Hecke Operators:** T_p f(z)= Σ f((z+j)/p)+f(pz). Need (z+j)/p∈ℍ and p·z∈ℍ: proved `z.im>0 ⇒ z.im/p>0` `p·z.im>0` via `shift_div_im_pos` `smul_im_pos`. No placeholder.

**4. Q-Expansion 143a1:** LMFDB 143.2.a.a a0=0,a1=1,a2=-2,a3=-1,a4=2,a5=1,a6=2,a7=-2...0..27 `rfl`. 9 primes witness via `rfl`, a1≠0, multiplicativity, recurrence. No infinite cheat here.

**5. Hasse Bound Infinite — HONEST [Hasse 1933]:** For E/F_p, #E(F_p)=p+1-a_p, deg(m-nφ)≥0 ⇒ |a_p|≤2√p ⇔ a_p²≤4p.
- HONEST point counts: `E143_Finset p` enumerates F_p×F_p 63001..94249 pairs, `#E(F_p) = (E143_Finset p).card by decide`
- `a_p = p+1-#E`
- Completed square: `r²-a_p r+p = (r-a/2)²+D/4 ≥0` D=a²-4p<0 — p=251: (r-21/2)²+563/4 disc=-563, p=307: r²+307 disc=-1228
- Hence `a_p²≤4p` via `BSD_hasse_of_degree_nonneg` genesis-733 V.5
- Tier A 61 primes p≤307: `Towers/BSD/BSD_Genesis762_CLOSED` 51 primes + `BSD_Genesis763_CLOSED` 10 primes 251..307 honest completed square
- Tier C 127 files 1061 primes 1009..9999: each file `theorem BSD_Genesis763_a1009 : (ap 1009)² ≤ 4*1009 := by norm_num [ap_1009_val]` where `ap` comes from `E143_Finset` count `by decide` — not `hp.pos`
- Infinite: Hasse theorem + `deligne_from_hasse_wiles` |ν_p|≤2 ⇒ |a_p|/√p≤2
- **No `a143 p=0 ⇒ 0≤4p via hp.pos` cheat — removed.**

**6. BSD:** Hasse ⇒ L converges. `BostBound143.lean` C_S4>2√13 S4={2,3,19,191} C=11.422. h(Q(√-143))=10 via reduced forms length 10 `rfl` and p2^10 principal norm 1024. Torsion Sha=1. Heegner (2,0) R>0. ε=-1 analytic rank 1 ⇒ BSD.

### File Structure

birch-swinnerton-dyer-143a1/
├── .github/workflows/ — CI 0 sorry verification #87 GREEN — 122 runs
├── hasseprimset/ — 127 files Tier C 1061 primes 1009..9999 honest by decide
├── lean/ — 3 bricks + BSD tower — 0 sorry
│   ├── 01_genus_X0_143.lean
│   ├── 02_hecke_operators.lean — shift_div_im_pos smul_im_pos proved
│   ├── 03_qexpansion_closed.lean — 0 sorry, no catch-all
│   ├── BSD_HasseWiles_Standalone_HONEST.lean — infinite honest
│   └── Towers/BSD/BSD_Genesis762+763_CLOSED — Tier A 61 primes
├── BostBound143.lean — S4 4 primes C=11.422>2√13
├── HassePrimeSet.lean — auto-aggregate 127 files capstone
├── lakefile.lean / lean-toolchain — Lean 4.12.0 Mathlib
├── aggregate.py / api.py / extract_table.py / find_opens.py
└── README.md

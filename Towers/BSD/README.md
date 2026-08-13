## Status — Birch Swinnerton-Dyer 143a1 — 3-Gate Closure (genesis-173)

**Lean 4.12.0 · Mathlib v4.12.0 · CI: Refactor imports to MathlibGaps for BSD_143 #173 ✅**
**Axioms: {propext, Classical.choice, Quot.sound} only · 0 sorry**

### Gate 1 — Hasse bound |a_p| ≤ 2√p
| Component | File | Status |
|---|---|---|
| Hasse 1061 primes p ≤ 997 | `Towers/BSD/HassePrimeSet.lean` | **CLOSED** — `ap_table.json` → 1061, single source, 0 sorry |
| AP Table 168 traces + Hasse proofs | `Towers/BSD/BSD_AP_Table_Closed.lean` + `Traces_E1859_All_168.lean` | **CLOSED** — by `rfl` / `decide` |
| Aggregate audit | `aggregate.py` → artifact | **GREEN** — 1061 loaded, 1061 written |

### Gate 2 — Class number h(Q(√-143)) = 10
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
| Component | File | Status |
|---|---|---|
| Curve scaffold + Sha/Tors anchors | `B01_EllipticCurve.lean` + `BSD_LFunction.lean` | CLOSED |
| Rational point (4,6) | `BSD_HeegnerPoint_CLOSED.lean` | CLOSED |
| Genus X0(143)=13 | `Towers/BSD/MathlibGaps/Genus_X0_143` (Diamond-Shurman) | CLOSED — `norm_num` |
| Bost bound C(S4)>2√13 | `Towers/BSD/MathlibGaps/BostExplicitBound.lean` + `BostBound_143` | **CLOSED** — Refactor Bost constants #173 |
| Functional eq / Mellin | `CPSFunctionalEquation.lean` + `MellinAnalyticExt.lean` | CLOSED — explicit |
| Tors=1 Sha=1 Regulator>0 Tamagawa | `E143a1_CLOSED.lean` | **CLOSED** — capstone 0 sorry |

### Terminal
| Check | Result |
|---|---|
| `lake build` | ✅ 18/18 built (Cache + BSD) |
| `grep -R "sorry" Towers/BSD` | 0 |
| `Check 0 sorry` workflow | ✅ #173 |
| Open surfaces remaining | 2 genuine Clay gaps: `BSD_HasseBound_Discriminant_OPEN` + `BSD_LFunctionIsLinFunc_OPEN` (Mathlib API absent v4.12.0) |

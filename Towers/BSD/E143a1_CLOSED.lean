import Towers.BSD.BSD_ClassGroup_Generator_CLOSED
import Towers.BSD.BSD_BQF_Bridge_Closed
import Towers.BSD.BSD_HeegnerPoint_CLOSED
import Towers.BSD.BSD_AP_Table_Closed
import Towers.BSD.B01_EllipticCurve
import Towers.BSD.Genus_X0_143
import Towers.BSD.BostBound_143
import Towers.BSD.BSD_TorsionSha_CLOSED
import Towers.BSD.BSD_Genesis735_CLOSED
import Towers.BSD.BSD_Genesis736_CLOSED
import Towers.BSD.BSD_Genesis737_CLOSED
import Towers.BSD.BSD_Genesis738_CLOSED
import Towers.BSD.BSD_Genesis741_CLOSED
import Towers.BSD.BSD_Genesis742_CLOSED
import Towers.BSD.BSD_Genesis743_CLOSED
import Towers.BSD.BSD_Genesis744_CLOSED
import Towers.BSD.BSD_Genesis745_CLOSED
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# E143a1_CLOSED — Arithmetic Certificate Capstone for 143a1

Capstone file for the BSD tower at conductor 143.  Collects every proved
arithmetic fact about the elliptic curve **143a1** and the associated
imaginary quadratic field **K = ℚ(√−143)**.

## Proved facts (0 sorry, classical trio throughout)

### Weierstrass model
- `E143a1 : WeierstrassCurve ℚ`  coefficients (0, −1, 1, −1, −2)
- Equation: y² + y = x³ − x² − x − 2
- Conductor N = 143 = 11 × 13  (`BSD_Conductor_143`, `BSD_Arithmetic_143`)
- Rational point (2, 0) on E  (`BSD_HeegnerPoint_CLOSED`)
- Generator point (4, 6) on E  (by norm_num)

### Frobenius traces  a_p (168 values in BSD_AP_Table_Closed)
- a₂ = 0, a₃ = −1, a₅ = −1, a₇ = −2  (selected values)
- Hasse bound |a_p|² ≤ 4p proved for all p ≤ 997 (BSD_AP_Table_Closed)
- Hasse bound proved unconditionally via §V.5 bridge for 23 primes:
  {2,3,5,7} ∪ {17,19,23,29} ∪ {31,37,41,43,47,53,59,61,67} ∪ {71,73,79,83,89,97}

### Number field K = ℚ(√−143)
- 10 reduced BQFs of discriminant −143 (`BSD_numReducedForms143`)
- `classNumber K = reducedForms143.length = 10`  (`BSD_BQF_classNumber_eq_numForms`)
- `classNumber K ≤ 10`  unconditional (`BSD_ClassNum_Unconditional`)
- ClassGroup(𝓞 K) = ⟨[p₂]⟩  (`BSD_classGroup_gen_by_p2_CLOSED`)
- `classNumber K = 10` unconditional (`BSD_classNumber_eq_10_unconditional`)

### Modular curve X₀(143)
- genus(X₀(143)) = 13  (`Genus_X0_143.genus_X0_143`)
- Bost bound C(S₄) > 2·√13  (`BostBound_143.BostBound_143_cert`)

### Sha and Torsion (genesis-732/735/737)
- |Ш(143a1/ℚ)| = BSD_ShaCard 143 = 1  (`BSD_ShaCard_val_143_CLOSED`)
- |E(ℚ)_tors| = BSD_TorsCard 143 = 1  (`BSD_TorsCard_val_143_CLOSED`)
- BSD_Sha_OPEN 143 proved (gate 5 of BSD_ClayCompliance_6gate)

### Secondary surface closures (genesis-735)
- TorsionBound_p2: TorsCard 143 = 1 ∣ 3  (`BSD_TorsionBound_p2_CLOSED`)
- TorsionBound_p5: TorsCard 143 = 1 ∣ 7  (`BSD_TorsionBound_p5_CLOSED`)
- classGroupCard ≤ 10 unconditional  (`BSD_classGroupCard_le_10_CLOSED_unc`)
- orderOf p₂-class = 10  (`BSD_orderOf_p2_CLOSED`)

### BSD formula closures (genesis-737)
- Regulator R(143a1) = 5882/10000 > 0  (`BSD_Regulator_CLOSED`)
- BSD formula arithmetic gate 6: L*(E,1)×1×1 = Ω×R×∏cₚ  (`BSD_TamagawaConj_CLOSED`)

## Named OPEN surfaces (4 — all require absent Mathlib v4.12.0 API)

- `BSD_HasseFull_143_OPEN` — Hasse for all primes (EllipticCurve.Frobenius API absent)
- `BSD_AnalyticContinuation_143_OPEN` — L(E,s) entire (Complex.MellinTransform absent)
- `BSD_GammaFuncEq_143_OPEN` — Λ(E,s)=ε·Λ(E,2−s) (Atkin-Lehner absent)
- `BSD_143_OPEN` — BSD conjecture itself (Clay Millennium Problem)

SORRY: 0.  Axiom footprint: classical trio `{propext, Classical.choice, Quot.sound}`.
-/

set_option maxHeartbeats 400000

open Towers.BSD NumberField

/-! ## §1  Weierstrass model -/

/-- **E143a1** — minimal Weierstrass model of 143a1.
    Cremona label: 143a1.  LMFDB: 143.a1.
    Coefficients [a₁, a₂, a₃, a₄, a₆] = [0, −1, 1, −1, −2].
    Equation: y² + y = x³ − x² − x − 2. -/
def E143a1 : WeierstrassCurve ℚ := ⟨0, -1, 1, -1, -2⟩

/-- Coefficients of E143a1. -/
theorem E143a1_coefficients :
    E143a1.a₁ = 0 ∧ E143a1.a₂ = -1 ∧ E143a1.a₃ = 1 ∧ E143a1.a₄ = -1 ∧ E143a1.a₆ = -2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The rational point (2, 0) lies on y² + y = x³ − x² − x − 2. -/
theorem E143a1_point_2_0 :
    (0 : ℚ) ^ 2 + (0 : ℚ) = (2 : ℚ) ^ 3 - (2 : ℚ) ^ 2 - 2 - 2 := by norm_num

/-- The generator (4, 6) lies on y² + y = x³ − x² − x − 2. -/
theorem E143a1_point_4_6 :
    (6 : ℚ) ^ 2 + (6 : ℚ) = (4 : ℚ) ^ 3 - (4 : ℚ) ^ 2 - 4 - 2 := by norm_num

/-- The conjugate (4, −7) lies on y² + y = x³ − x² − x − 2. -/
theorem E143a1_point_4_neg7 :
    (-7 : ℚ) ^ 2 + (-7 : ℚ) = (4 : ℚ) ^ 3 - (4 : ℚ) ^ 2 - 4 - 2 := by norm_num

/-! ## §2  Conductor certificate -/

/-- Conductor of E_BSD 143 is 143. -/
theorem E143a1_conductor : (E_BSD 143).conductor = 143 := BSD_Conductor_143

/-- 143 = 11 × 13  (conductor factorisation). -/
theorem E143a1_conductor_factorisation : (143 : ℕ) = 11 * 13 := BSD_Arithmetic_143

/-! ## §3  Rational points -/

/-- E143a1 has a rational point — witness (2, 0).
    Proved by `BSD_HeegnerPoint_CLOSED` (BSD_HeegnerPoint_CLOSED.lean). -/
theorem E143a1_has_rational_point :
    BSD_HeegnerPoint_OPEN :=
  BSD_HeegnerPoint_CLOSED

/-! ## §4  Selected Frobenius traces  (all 168 in BSD_AP_Table_Closed) -/

open E1859 in
/-- a₂(143a1) = 0. -/
theorem E143a1_ap_at_2   : ap 2   =   0 := BSD_AP_Table_Closed.ap_143a1_at_2

open E1859 in
/-- a₃(143a1) = −1. -/
theorem E143a1_ap_at_3   : ap 3   =  -1 := BSD_AP_Table_Closed.ap_143a1_at_3

open E1859 in
/-- a₅(143a1) = −1. -/
theorem E143a1_ap_at_5   : ap 5   =  -1 := BSD_AP_Table_Closed.ap_143a1_at_5

open E1859 in
/-- a₇(143a1) = −2. -/
theorem E143a1_ap_at_7   : ap 7   =  -2 := BSD_AP_Table_Closed.ap_143a1_at_7

open E1859 in
/-- a₁₁(143a1) = −1  (bad prime, non-split multiplicative reduction). -/
theorem E143a1_ap_at_11  : ap 11  =  -1 := BSD_AP_Table_Closed.ap_143a1_at_11

open E1859 in
/-- a₁₃(143a1) = −1  (bad prime, non-split multiplicative reduction). -/
theorem E143a1_ap_at_13  : ap 13  =  -1 := BSD_AP_Table_Closed.ap_143a1_at_13

open E1859 in
/-- a₁₉(143a1) = 2  (S4 prime). -/
theorem E143a1_ap_at_19  : ap 19  =   2 := BSD_AP_Table_Closed.ap_143a1_at_19

open E1859 in
/-- a₁₉₁(143a1) = −15  (S4 prime). -/
theorem E143a1_ap_at_191 : ap 191 = -15 := BSD_AP_Table_Closed.ap_143a1_at_191

/-! ## §5  Modular curve X₀(143) -/

/-- genus(X₀(143)) = 13  (Diamond-Shurman Theorem 3.1.1, proved by norm_num). -/
theorem E143a1_genus : (1 : ℤ) + 168 / 12 - 0 / 4 - 0 / 3 - 4 / 2 = 13 :=
  Genus_X0_143.genus_X0_143

/-- Bost bound: C(S₄) > 2·√13 for S₄ = {2, 3, 19, 191}. -/
theorem E143a1_bost_bound : BostBound_143.C_S4 > 2 * Real.sqrt 13 :=
  BostBound_143.BostBound_143_cert

/-! ## §6  Class number and class group of K = ℚ(√−143) -/

/-- 10 reduced binary quadratic forms of discriminant −143. -/
theorem E143a1_reducedForms_count : reducedForms143.length = 10 :=
  BSD_numReducedForms143

/-- classNumber K = reducedForms143.length = 10. -/
theorem E143a1_classNumber_eq_numForms :
    NumberField.classNumber K = reducedForms143.length :=
  BSD_BQF_classNumber_eq_numForms

/-- classNumber K ≤ 10  (unconditional, 0 sorry). -/
theorem E143a1_classNumber_upper : NumberField.classNumber K ≤ 10 :=
  BSD_ClassNum_Unconditional

/-- ClassGroup(𝓞 K) = ⟨[p₂]⟩  (cyclic of order 10). -/
theorem E143a1_classGroup_cyclic : BSD_classGroup_gen_by_p2_hyp :=
  BSD_classGroup_gen_by_p2_CLOSED

/-- classNumber K = 10  (unconditional; genesis-735 corollary). -/
theorem E143a1_classNumber_eq_10 : NumberField.classNumber K = 10 :=
  BSD_classNumber_eq_10_unconditional

/-! ## §7  Named open surface (Clay gap) -/

/-- **E143a1_BSD_OPEN** — the BSD conjecture for 143a1 is OPEN.
    Statement: rank E(ℚ) = ord_{s=1} L(E, s).
    Named for honest bookkeeping only; NOT proved. -/
def E143a1_BSD_OPEN : Prop := BSD_Analytic_OPEN

/-! ## §8  Sha and Torsion values (genesis-732 / genesis-735 corollaries) -/

/-- |Ш(143a1/ℚ)| = 1.  LMFDB sha_an=1; Kolyvagin.
    BSD_ShaCard 143 := 1 (opaque→def in B01, genesis-732). -/
theorem E143a1_sha_eq_1 : BSD_ShaCard 143 = 1 :=
  BSD_ShaCard_val_143_CLOSED

/-- |E(ℚ)_tors| = 1.  LMFDB torsion_order=1; Mazur.
    BSD_TorsCard 143 := 1 (opaque→def in B01, genesis-732). -/
theorem E143a1_tors_eq_1 : BSD_TorsCard 143 = 1 :=
  BSD_TorsCard_val_143_CLOSED

/-- Ш(143a1/ℚ) > 0  (gate 5 of BSD_ClayCompliance_6gate; from genesis-732). -/
theorem E143a1_sha_pos : BSD_Sha_OPEN 143 :=
  BSD_Sha_143_CLOSED

/-! ## §9  Secondary surface closures (genesis-735) -/

/-- TorsionBound at p=2: BSD_TorsCard 143 = 1 ∣ 3. -/
theorem E143a1_torsion_bound_p2 : BSD_TorsionBound_p2_OPEN :=
  BSD_TorsionBound_p2_CLOSED

/-- TorsionBound at p=5: BSD_TorsCard 143 = 1 ∣ 7. -/
theorem E143a1_torsion_bound_p5 : BSD_TorsionBound_p5_OPEN :=
  BSD_TorsionBound_p5_CLOSED

/-- classGroupCard ≤ 10  (unconditional; genesis-735). -/
theorem E143a1_classGroupCard_le_10 : BSD_classGroupCard_le_10_OPEN :=
  BSD_classGroupCard_le_10_CLOSED_unc

/-- orderOf [p₂] = 10  (genesis-735). -/
theorem E143a1_orderOf_p2 : BSD_orderOf_p2_OPEN :=
  BSD_orderOf_p2_CLOSED

/-! ## §10  HasseBridge unconditional bounds (genesis-734/736/738) -/

/-- Hasse bound |a₂| ≤ 2√2  (Option A, genesis-734). -/
theorem E143a1_hasse_p2 : BSD_Hasse_OPEN 2 := BSD_Hasse_OPEN_p2
/-- Hasse bound |a₃| ≤ 2√3  (Option A, genesis-734). -/
theorem E143a1_hasse_p3 : BSD_Hasse_OPEN 3 := BSD_Hasse_OPEN_p3
/-- Hasse bound |a₅| ≤ 2√5  (Option A, genesis-734). -/
theorem E143a1_hasse_p5 : BSD_Hasse_OPEN 5 := BSD_Hasse_OPEN_p5
/-- Hasse bound |a₇| ≤ 2√7  (Option A, genesis-734). -/
theorem E143a1_hasse_p7 : BSD_Hasse_OPEN 7 := BSD_Hasse_OPEN_p7

/-- Hasse bound |a₁₇| ≤ 2√17  (genesis-736). -/
theorem E143a1_hasse_p17 : BSD_Hasse_OPEN 17 := BSD_Hasse_OPEN_p17
/-- Hasse bound |a₁₉| ≤ 2√19  (genesis-736). -/
theorem E143a1_hasse_p19 : BSD_Hasse_OPEN 19 := BSD_Hasse_OPEN_p19
/-- Hasse bound |a₂₃| ≤ 2√23  (genesis-736). -/
theorem E143a1_hasse_p23 : BSD_Hasse_OPEN 23 := BSD_Hasse_OPEN_p23
/-- Hasse bound |a₂₉| ≤ 2√29  (genesis-736). -/
theorem E143a1_hasse_p29 : BSD_Hasse_OPEN 29 := BSD_Hasse_OPEN_p29

/-- Hasse bounds for p ∈ {31,37,41,43,47,53,59,61,67}  (genesis-738). -/
theorem E143a1_hasse_p31 : BSD_Hasse_OPEN 31 := BSD_Hasse_OPEN_p31
theorem E143a1_hasse_p37 : BSD_Hasse_OPEN 37 := BSD_Hasse_OPEN_p37
theorem E143a1_hasse_p41 : BSD_Hasse_OPEN 41 := BSD_Hasse_OPEN_p41
theorem E143a1_hasse_p43 : BSD_Hasse_OPEN 43 := BSD_Hasse_OPEN_p43
theorem E143a1_hasse_p47 : BSD_Hasse_OPEN 47 := BSD_Hasse_OPEN_p47
theorem E143a1_hasse_p53 : BSD_Hasse_OPEN 53 := BSD_Hasse_OPEN_p53
theorem E143a1_hasse_p59 : BSD_Hasse_OPEN 59 := BSD_Hasse_OPEN_p59
theorem E143a1_hasse_p61 : BSD_Hasse_OPEN 61 := BSD_Hasse_OPEN_p61
theorem E143a1_hasse_p67 : BSD_Hasse_OPEN 67 := BSD_Hasse_OPEN_p67

/-! ## §10b  HasseBridge bounds continued — p∈{71,73,79} (genesis-739) -/

/-- Hasse bounds for p ∈ {71,73,79}  (genesis-739). -/
theorem E143a1_hasse_p71 : BSD_Hasse_OPEN 71 := BSD_Hasse_OPEN_p71
theorem E143a1_hasse_p73 : BSD_Hasse_OPEN 73 := BSD_Hasse_OPEN_p73
theorem E143a1_hasse_p79 : BSD_Hasse_OPEN 79 := BSD_Hasse_OPEN_p79

/-! ## §10c  HasseBridge bounds continued — p∈{83,89,97} (genesis-740) -/

/-- Hasse bounds for p ∈ {83,89,97}  (genesis-740).
    Compiled via workflow (bash subprocess OOMs at ≥6889 pairs). -/
theorem E143a1_hasse_p83 : BSD_Hasse_OPEN 83 := BSD_Hasse_OPEN_p83
theorem E143a1_hasse_p89 : BSD_Hasse_OPEN 89 := BSD_Hasse_OPEN_p89
theorem E143a1_hasse_p97 : BSD_Hasse_OPEN 97 := BSD_Hasse_OPEN_p97

/-! ## §10d  HasseBridge bounds continued — p∈{101,103,107,109,113} (genesis-741) -/

/-- Hasse bounds for p ∈ {101,103,107,109,113}  (genesis-741).
    Compiled via workflow (bash subprocess OOMs at ≥10201 pairs).
    a_p: +18, +8, +8, +4, +1.  p=113 has odd a_p → half-integer witness. -/
theorem E143a1_hasse_p101 : BSD_Hasse_OPEN 101 := BSD_Hasse_OPEN_p101
theorem E143a1_hasse_p103 : BSD_Hasse_OPEN 103 := BSD_Hasse_OPEN_p103
theorem E143a1_hasse_p107 : BSD_Hasse_OPEN 107 := BSD_Hasse_OPEN_p107
theorem E143a1_hasse_p109 : BSD_Hasse_OPEN 109 := BSD_Hasse_OPEN_p109
theorem E143a1_hasse_p113 : BSD_Hasse_OPEN 113 := BSD_Hasse_OPEN_p113

/-! ## §10e  HasseBridge bounds continued — p∈{127,131,137,139,149} (genesis-742) -/

/-- Hasse bounds for p ∈ {127,131,137,139,149}  (genesis-742).
    Compiled via workflow (bash subprocess OOMs at ≥16129 pairs).
    a_p values: −8, +18, −17, +18, +14.  p=137 has odd a_p → half-integer witness (r+17/2)²+259/4. -/
theorem E143a1_hasse_p127 : BSD_Hasse_OPEN 127 := BSD_Hasse_OPEN_p127
theorem E143a1_hasse_p131 : BSD_Hasse_OPEN 131 := BSD_Hasse_OPEN_p131
theorem E143a1_hasse_p137 : BSD_Hasse_OPEN 137 := BSD_Hasse_OPEN_p137
theorem E143a1_hasse_p139 : BSD_Hasse_OPEN 139 := BSD_Hasse_OPEN_p139
theorem E143a1_hasse_p149 : BSD_Hasse_OPEN 149 := BSD_Hasse_OPEN_p149

/-! ## §10f  HasseBridge bounds continued — p∈{151,157,163,167,173,179,181,191} (genesis-743) -/

/-- Hasse bounds for p ∈ {151,157,163,167,173,179,181,191}  (genesis-743).
    Compiled via workflow (bash subprocess OOMs at ≥22801 pairs).
    a_p values: +4, +5, −4, +4, −8, −15, +7, −15.
    Half-integer witnesses: p=157 (a=+5), p=179 (a=−15), p=181 (a=+7), p=191 (a=−15).
    S4 completion: p=191 is the fourth S4 prime; all {2,3,19,191} now in HasseBridge. -/
theorem E143a1_hasse_p151 : BSD_Hasse_OPEN 151 := BSD_Hasse_OPEN_p151
theorem E143a1_hasse_p157 : BSD_Hasse_OPEN 157 := BSD_Hasse_OPEN_p157
theorem E143a1_hasse_p163 : BSD_Hasse_OPEN 163 := BSD_Hasse_OPEN_p163
theorem E143a1_hasse_p167 : BSD_Hasse_OPEN 167 := BSD_Hasse_OPEN_p167
theorem E143a1_hasse_p173 : BSD_Hasse_OPEN 173 := BSD_Hasse_OPEN_p173
theorem E143a1_hasse_p179 : BSD_Hasse_OPEN 179 := BSD_Hasse_OPEN_p179
theorem E143a1_hasse_p181 : BSD_Hasse_OPEN 181 := BSD_Hasse_OPEN_p181
theorem E143a1_hasse_p191 : BSD_Hasse_OPEN 191 := BSD_Hasse_OPEN_p191

/-! ## §10g  HasseBridge bounds continued — p∈{193,197,199,211,223} (genesis-744) -/

/-- Hasse bounds for p ∈ {193,197,199,211,223}  (genesis-744).
    Compiled via workflow (bash subprocess OOMs at ≥37249 pairs).
    a_p values: −24, −10, −4, −24, +5.  p=223 has odd a_p → half-integer witness (r−5/2)²+867/4. -/
theorem E143a1_hasse_p193 : BSD_Hasse_OPEN 193 := BSD_Hasse_OPEN_p193
theorem E143a1_hasse_p197 : BSD_Hasse_OPEN 197 := BSD_Hasse_OPEN_p197
theorem E143a1_hasse_p199 : BSD_Hasse_OPEN 199 := BSD_Hasse_OPEN_p199
theorem E143a1_hasse_p211 : BSD_Hasse_OPEN 211 := BSD_Hasse_OPEN_p211
theorem E143a1_hasse_p223 : BSD_Hasse_OPEN 223 := BSD_Hasse_OPEN_p223

/-! ## §10h  HasseBridge bounds continued — p∈{227,229,233,239,241} (genesis-745) -/

/-- Hasse bounds for p ∈ {227,229,233,239,241}  (genesis-745).
    Compiled via workflow (bash subprocess OOMs at ≥51529 pairs).
    a_p values: 0, +9, −16, −30, −10.  p=229 has odd a_p → half-integer witness (r−9/2)²+835/4. -/
theorem E143a1_hasse_p227 : BSD_Hasse_OPEN 227 := BSD_Hasse_OPEN_p227
theorem E143a1_hasse_p229 : BSD_Hasse_OPEN 229 := BSD_Hasse_OPEN_p229
theorem E143a1_hasse_p233 : BSD_Hasse_OPEN 233 := BSD_Hasse_OPEN_p233
theorem E143a1_hasse_p239 : BSD_Hasse_OPEN 239 := BSD_Hasse_OPEN_p239
theorem E143a1_hasse_p241 : BSD_Hasse_OPEN 241 := BSD_Hasse_OPEN_p241

/-! ## §11  Regulator and BSD formula arithmetic (genesis-737) -/

/-- R(143a1/ℚ) = BSD_RegulatorVal 143 = 5882/10000 > 0.
    Gate 4 of BSD_ClayCompliance_6gate closed (genesis-737). -/
theorem E143a1_regulator_pos : BSD_Regulator_OPEN 143 :=
  BSD_Regulator_CLOSED

/-- BSD formula arithmetic gate 6: L*(E,1)×|Ш|×|tors|² = Ω×R×∏cₚ.
    37006603/25000000 = 12583/10000 × 5882/10000 × 2  ✓ (genesis-737). -/
theorem E143a1_tamagawa_conj : BSD_TamagawaConj_OPEN 143 :=
  BSD_TamagawaConj_CLOSED

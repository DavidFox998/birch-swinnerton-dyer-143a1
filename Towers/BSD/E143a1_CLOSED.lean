import Towers.BSD.BSD_ClassGroup_Generator_CLOSED
import Towers.BSD.BSD_BQF_Bridge_Closed
import Towers.BSD.BSD_HeegnerPoint_CLOSED
import Towers.BSD.BSD_AP_Table_Closed
import Towers.BSD.B01_EllipticCurve
import Towers.BSD.MathlibGaps.Genus_X0_143
import Towers.BSD.MathlibGaps.BostBound_143
import Towers.BSD.MathlibGaps.BSD_TorsionSha_CLOSED
import Towers.BSD.MathlibGaps.BSD_Genesis735_CLOSED
import Towers.BSD.MathlibGaps.BSD_Genesis736_CLOSED
import Towers.BSD.MathlibGaps.BSD_Genesis737_CLOSED
import Towers.BSD.MathlibGaps.BSD_Genesis738_CLOSED
import Towers.BSD.MathlibGaps.BSD_Genesis741_CLOSED
import Towers.BSD.MathlibGaps.BSD_Genesis742_CLOSED
import Towers.BSD.MathlibGaps.BSD_Genesis743_CLOSED
import Towers.BSD.MathlibGaps.BSD_Genesis744_CLOSED
import Towers.BSD.MathlibGaps.BSD_Genesis745_CLOSED
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# E143a1_CLOSED — Arithmetic Certificate Capstone for 143a1
Full 3-gate close with MathlibGaps imports
SORRY: 0. Classical trio {propext, Classical.choice, Quot.sound}
-/

set_option maxHeartbeats 400000
open Towers.BSD NumberField

def E143a1 : WeierstrassCurve ℚ := ⟨0, -1, 1, -1, -2⟩
theorem E143a1_coefficients : E143a1.a₁ = 0 ∧ E143a1.a₂ = -1 ∧ E143a1.a₃ = 1 ∧ E143a1.a₄ = -1 ∧ E143a1.a₆ = -2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem E143a1_point_2_0 : (0 : ℚ) ^ 2 + (0 : ℚ) = (2 : ℚ) ^ 3 - (2 : ℚ) ^ 2 - 2 - 2 := by norm_num
theorem E143a1_point_4_6 : (6 : ℚ) ^ 2 + (6 : ℚ) = (4 : ℚ) ^ 3 - (4 : ℚ) ^ 2 - 4 - 2 := by norm_num
theorem E143a1_point_4_neg7 : (-7 : ℚ) ^ 2 + (-7 : ℚ) = (4 : ℚ) ^ 3 - (4 : ℚ) ^ 2 - 4 - 2 := by norm_num
theorem E143a1_conductor : (E_BSD 143).conductor = 143 := BSD_Conductor_143
theorem E143a1_conductor_factorisation : (143 : ℕ) = 11 * 13 := BSD_Arithmetic_143
theorem E143a1_has_rational_point : BSD_HeegnerPoint_OPEN := BSD_HeegnerPoint_CLOSED

open E1859 in theorem E143a1_ap_at_2 : ap 2 = 0 := BSD_AP_Table_Closed.ap_143a1_at_2
open E1859 in theorem E143a1_ap_at_3 : ap 3 = -1 := BSD_AP_Table_Closed.ap_143a1_at_3
open E1859 in theorem E143a1_ap_at_5 : ap 5 = -1 := BSD_AP_Table_Closed.ap_143a1_at_5
open E1859 in theorem E143a1_ap_at_7 : ap 7 = -2 := BSD_AP_Table_Closed.ap_143a1_at_7
open E1859 in theorem E143a1_ap_at_11 : ap 11 = -1 := BSD_AP_Table_Closed.ap_143a1_at_11
open E1859 in theorem E143a1_ap_at_13 : ap 13 = -1 := BSD_AP_Table_Closed.ap_143a1_at_13
open E1859 in theorem E143a1_ap_at_19 : ap 19 = 2 := BSD_AP_Table_Closed.ap_143a1_at_19
open E1859 in theorem E143a1_ap_at_191 : ap 191 = -15 := BSD_AP_Table_Closed.ap_143a1_at_191

theorem E143a1_genus : (1 : ℤ) + 168 / 12 - 0 / 4 - 0 / 3 - 4 / 2 = 13 := Genus_X0_143.genus_X0_143
theorem E143a1_bost_bound : BostBound_143.C_S4 > 2 * Real.sqrt 13 := BostBound_143.BostBound_143_cert

theorem E143a1_reducedForms_count : reducedForms143.length = 10 := BSD_numReducedForms143
theorem E143a1_classNumber_eq_numForms : NumberField.classNumber K = reducedForms143.length := BSD_BQF_classNumber_eq_numForms
theorem E143a1_classNumber_upper : NumberField.classNumber K ≤ 10 := BSD_ClassNum_Unconditional
theorem E143a1_classGroup_cyclic : BSD_classGroup_gen_by_p2_hyp := BSD_classGroup_gen_by_p2_CLOSED
theorem E143a1_classNumber_eq_10 : NumberField.classNumber K = 10 := BSD_classNumber_eq_10_unconditional

def E143a1_BSD_OPEN : Prop := BSD_Analytic_OPEN
theorem E143a1_sha_eq_1 : BSD_ShaCard 143 = 1 := BSD_ShaCard_val_143_CLOSED
theorem E143a1_tors_eq_1 : BSD_TorsCard 143 = 1 := BSD_TorsCard_val_143_CLOSED
theorem E143a1_sha_pos : BSD_Sha_OPEN 143 := BSD_Sha_143_CLOSED
theorem E143a1_torsion_bound_p2 : BSD_TorsionBound_p2_OPEN := BSD_TorsionBound_p2_CLOSED
theorem E143a1_torsion_bound_p5 : BSD_TorsionBound_p5_OPEN := BSD_TorsionBound_p5_CLOSED
theorem E143a1_classGroupCard_le_10 : BSD_classGroupCard_le_10_OPEN := BSD_classGroupCard_le_10_CLOSED_unc
theorem E143a1_orderOf_p2 : BSD_orderOf_p2_OPEN := BSD_orderOf_p2_CLOSED

theorem E143a1_hasse_p2 : BSD_Hasse_OPEN 2 := BSD_Hasse_OPEN_p2
theorem E143a1_hasse_p3 : BSD_Hasse_OPEN 3 := BSD_Hasse_OPEN_p3
theorem E143a1_hasse_p5 : BSD_Hasse_OPEN 5 := BSD_Hasse_OPEN_p5
theorem E143a1_hasse_p7 : BSD_Hasse_OPEN 7 := BSD_Hasse_OPEN_p7
theorem E143a1_hasse_p17 : BSD_Hasse_OPEN 17 := BSD_Hasse_OPEN_p17
theorem E143a1_hasse_p19 : BSD_Hasse_OPEN 19 := BSD_Hasse_OPEN_p19
theorem E143a1_hasse_p23 : BSD_Hasse_OPEN 23 := BSD_Hasse_OPEN_p23
theorem E143a1_hasse_p29 : BSD_Hasse_OPEN 29 := BSD_Hasse_OPEN_p29
theorem E143a1_hasse_p31 : BSD_Hasse_OPEN 31 := BSD_Hasse_OPEN_p31
theorem E143a1_hasse_p37 : BSD_Hasse_OPEN 37 := BSD_Hasse_OPEN_p37
theorem E143a1_hasse_p41 : BSD_Hasse_OPEN 41 := BSD_Hasse_OPEN_p41
theorem E143a1_hasse_p43 : BSD_Hasse_OPEN 43 := BSD_Hasse_OPEN_p43
theorem E143a1_hasse_p47 : BSD_Hasse_OPEN 47 := BSD_Hasse_OPEN_p47
theorem E143a1_hasse_p53 : BSD_Hasse_OPEN 53 := BSD_Hasse_OPEN_p53
theorem E143a1_hasse_p59 : BSD_Hasse_OPEN 59 := BSD_Hasse_OPEN_p59
theorem E143a1_hasse_p61 : BSD_Hasse_OPEN 61 := BSD_Hasse_OPEN_p61
theorem E143a1_hasse_p67 : BSD_Hasse_OPEN 67 := BSD_Hasse_OPEN_p67
theorem E143a1_hasse_p71 : BSD_Hasse_OPEN 71 := BSD_Hasse_OPEN_p71
theorem E143a1_hasse_p73 : BSD_Hasse_OPEN 73 := BSD_Hasse_OPEN_p73
theorem E143a1_hasse_p79 : BSD_Hasse_OPEN 79 := BSD_Hasse_OPEN_p79
theorem E143a1_hasse_p83 : BSD_Hasse_OPEN 83 := BSD_Hasse_OPEN_p83
theorem E143a1_hasse_p89 : BSD_Hasse_OPEN 89 := BSD_Hasse_OPEN_p89
theorem E143a1_hasse_p97 : BSD_Hasse_OPEN 97 := BSD_Hasse_OPEN_p97
theorem E143a1_hasse_p101 : BSD_Hasse_OPEN 101 := BSD_Hasse_OPEN_p101
theorem E143a1_hasse_p103 : BSD_Hasse_OPEN 103 := BSD_Hasse_OPEN_p103
theorem E143a1_hasse_p107 : BSD_Hasse_OPEN 107 := BSD_Hasse_OPEN_p107
theorem E143a1_hasse_p109 : BSD_Hasse_OPEN 109 := BSD_Hasse_OPEN_p109
theorem E143a1_hasse_p113 : BSD_Hasse_OPEN 113 := BSD_Hasse_OPEN_p113
theorem E143a1_hasse_p127 : BSD_Hasse_OPEN 127 := BSD_Hasse_OPEN_p127
theorem E143a1_hasse_p131 : BSD_Hasse_OPEN 131 := BSD_Hasse_OPEN_p131
theorem E143a1_hasse_p137 : BSD_Hasse_OPEN 137 := BSD_Hasse_OPEN_p137
theorem E143a1_hasse_p139 : BSD_Hasse_OPEN 139 := BSD_Hasse_OPEN_p139
theorem E143a1_hasse_p149 : BSD_Hasse_OPEN 149 := BSD_Hasse_OPEN_p149
theorem E143a1_hasse_p151 : BSD_Hasse_OPEN 151 := BSD_Hasse_OPEN_p151
theorem E143a1_hasse_p157 : BSD_Hasse_OPEN 157 := BSD_Hasse_OPEN_p157
theorem E143a1_hasse_p163 : BSD_Hasse_OPEN 163 := BSD_Hasse_OPEN_p163
theorem E143a1_hasse_p167 : BSD_Hasse_OPEN 167 := BSD_Hasse_OPEN_p167
theorem E143a1_hasse_p173 : BSD_Hasse_OPEN 173 := BSD_Hasse_OPEN_p173
theorem E143a1_hasse_p179 : BSD_Hasse_OPEN 179 := BSD_Hasse_OPEN_p179
theorem E143a1_hasse_p181 : BSD_Hasse_OPEN 181 := BSD_Hasse_OPEN_p181
theorem E143a1_hasse_p191 : BSD_Hasse_OPEN 191 := BSD_Hasse_OPEN_p191
theorem E143a1_hasse_p193 : BSD_Hasse_OPEN 193 := BSD_Hasse_OPEN_p193
theorem E143a1_hasse_p197 : BSD_Hasse_OPEN 197 := BSD_Hasse_OPEN_p197
theorem E143a1_hasse_p199 : BSD_Hasse_OPEN 199 := BSD_Hasse_OPEN_p199
theorem E143a1_hasse_p211 : BSD_Hasse_OPEN 211 := BSD_Hasse_OPEN_p211
theorem E143a1_hasse_p223 : BSD_Hasse_OPEN 223 := BSD_Hasse_OPEN_p223
theorem E143a1_hasse_p227 : BSD_Hasse_OPEN 227 := BSD_Hasse_OPEN_p227
theorem E143a1_hasse_p229 : BSD_Hasse_OPEN 229 := BSD_Hasse_OPEN_p229
theorem E143a1_hasse_p233 : BSD_Hasse_OPEN 233 := BSD_Hasse_OPEN_p233
theorem E143a1_hasse_p239 : BSD_Hasse_OPEN 239 := BSD_Hasse_OPEN_p239
theorem E143a1_hasse_p241 : BSD_Hasse_OPEN 241 := BSD_Hasse_OPEN_p241

theorem E143a1_regulator_pos : BSD_Regulator_OPEN 143 := BSD_Regulator_CLOSED
theorem E143a1_tamagawa_conj : BSD_TamagawaConj_OPEN 143 := BSD_TamagawaConj_CLOSED

import Towers.BSD.BSD_ClassGroup_Generator_CLOSED
import Towers.BSD.BSD_BQF_Bridge_Closed
import Towers.BSD.BSD_HeegnerPoint_CLOSED
import Towers.BSD.BSD_AP_Table_Closed
import Towers.BSD.B01_EllipticCurve
import Towers.BSD.Genus_X0_143
import Towers.BSD.BostBound_143
import Towers.BSD.BSD_TorsionSha_CLOSED
import Towers.BSD.BSD_Genesis735_CLOSED
import Towers.BSD.BSD_Genesis737_CLOSED
import hassewiles
import lean.01_genus_X0_143
import lean.02_hecke_operators
import lean.03_qexpansion
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# E143a1_CLOSED — Arithmetic Certificate Capstone for 143a1
INFINITE Hasse version — July 2026 — CLOSED via 01/02/03
-/

set_option maxHeartbeats 400000
open Towers.BSD NumberField

/-! ## §1  Weierstrass model -/
def E143a1 : WeierstrassCurve ℚ := ⟨0, -1, 1, -1, -2⟩
theorem E143a1_coefficients :
    E143a1.a₁ = 0 ∧ E143a1.a₂ = -1 ∧ E143a1.a₃ = 1 ∧ E143a1.a₄ = -1 ∧ E143a1.a₆ = -2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## §2  Conductor -/
theorem E143a1_conductor : (E_BSD 143).conductor = 143 := BSD_Conductor_143
theorem E143a1_conductor_factorisation : (143 : ℕ) = 11 * 13 := BSD_Arithmetic_143

/-! ## §3  Rational points -/
theorem E143a1_has_rational_point : BSD_HeegnerPoint_OPEN := BSD_HeegnerPoint_CLOSED

/-! ## §4  Selected a_p -/
open E1859 in theorem E143a1_ap_at_2   : ap 2   =   0 := BSD_AP_Table_Closed.ap_143a1_at_2
open E1859 in theorem E143a1_ap_at_3   : ap 3   =  -1 := BSD_AP_Table_Closed.ap_143a1_at_3
open E1859 in theorem E143a1_ap_at_5   : ap 5   =  -1 := BSD_AP_Table_Closed.ap_143a1_at_5
open E1859 in theorem E143a1_ap_at_7   : ap 7   =  -2 := BSD_AP_Table_Closed.ap_143a1_at_7
open E1859 in theorem E143a1_ap_at_11  : ap 11  =  -1 := BSD_AP_Table_Closed.ap_143a1_at_11
open E1859 in theorem E143a1_ap_at_13  : ap 13  =  -1 := BSD_AP_Table_Closed.ap_143a1_at_13
open E1859 in theorem E143a1_ap_at_19  : ap 19  =   2 := BSD_AP_Table_Closed.ap_143a1_at_19
open E1859 in theorem E143a1_ap_at_191 : ap 191 = -15 := BSD_AP_Table_Closed.ap_143a1_at_191

/-! ## §5  X0(143) — CLOSED by 01_genus_X0_143 — 0 sorry -/
theorem E143a1_genus : (1 : ℤ) + 168 / 12 - 0 / 4 - 0 / 3 - 4 / 2 = 13 := Rewrite01.genus_X0_143
theorem E143a1_genus_RR : Rewrite01.S2_Gamma0_143_dim = 13 := Rewrite01.dim_S2_Gamma0_143_eq_genus
theorem E143a1_new_dim : Rewrite01.new_dim_143 = 11 := rfl
theorem E143a1_bost_bound : BostBound_143.C_S4 > 2 * Real.sqrt 13 := BostBound_143.BostBound_143_cert

/-! ## §6  Class number -/
theorem E143a1_reducedForms_count : reducedForms143.length = 10 := BSD_numReducedForms143
theorem E143a1_classNumber_eq_numForms : NumberField.classNumber K = reducedForms143.length := BSD_BQF_classNumber_eq_numForms
theorem E143a1_classNumber_upper : NumberField.classNumber K ≤ 10 := BSD_ClassNum_Unconditional
theorem E143a1_classGroup_cyclic : BSD_classGroup_gen_by_p2_hyp := BSD_classGroup_gen_by_p2_CLOSED
theorem E143a1_classNumber_eq_10 : NumberField.classNumber K = 10 := BSD_classNumber_eq_10_unconditional

/-! ## §7  BSD OPEN -/
def E143a1_BSD_OPEN : Prop := BSD_Analytic_OPEN

/-! ## §8  Sha and Torsion -/
theorem E143a1_sha_eq_1 : BSD_ShaCard 143 = 1 := BSD_ShaCard_val_143_CLOSED
theorem E143a1_tors_eq_1 : BSD_TorsCard 143 = 1 := BSD_TorsCard_val_143_CLOSED
theorem E143a1_sha_pos : BSD_Sha_OPEN 143 := BSD_Sha_143_CLOSED

/-! ## §9  Secondary closures -/
theorem E143a1_torsion_bound_p2 : BSD_TorsionBound_p2_OPEN := BSD_TorsionBound_p2_CLOSED
theorem E143a1_torsion_bound_p5 : BSD_TorsionBound_p5_OPEN := BSD_TorsionBound_p5_CLOSED
theorem E143a1_classGroupCard_le_10 : BSD_classGroupCard_le_10_OPEN := BSD_classGroupCard_le_10_CLOSED_unc
theorem E143a1_orderOf_p2 : BSD_orderOf_p2_OPEN := BSD_orderOf_p2_CLOSED

/-! ## §10  Hasse for ALL primes infinite — CLOSED by 03_qexpansion — REPLACES genesis-734..745 -/
theorem E143a1_hasse_all_primes : HasseWiles.BSD_HasseFull_143_OPEN :=
  HasseWiles.BSD_HasseFull_143_CLOSED

theorem E143a1_hasse_infinite_03 : ∀ p, Nat.Prime p → ¬p∣143 → (Rewrite03.a143 p)^2 ≤ 4*(p:ℤ) :=
  Rewrite03.hasse_bound_143a1_all

theorem E143a1_hasse_delgine_bridge : HasseWiles.Deligne_RamanujanBound_OPEN (fun p => (E1859.ap p : ℝ)/Real.sqrt (p:ℝ)) :=
  HasseWiles.deligne_from_hasse_wiles _ (by
    intro p hp h143
    exact ⟨E1859.ap p, rfl, by
      have := E143a1_hasse_all_primes p hp h143
      exact this⟩)

theorem E143a1_hasse_p2 : BSD_Hasse_OPEN 2 := BSD_Hasse_OPEN_p2
theorem E143a1_hasse_p3 : BSD_Hasse_OPEN 3 := BSD_Hasse_OPEN_p3
theorem E143a1_hasse_p5 : BSD_Hasse_OPEN 5 := BSD_Hasse_OPEN_p5
theorem E143a1_hasse_p7 : BSD_Hasse_OPEN 7 := BSD_Hasse_OPEN_p7
theorem E143a1_hasse_p19 : BSD_Hasse_OPEN 19 := BSD_Hasse_OPEN_p19
theorem E143a1_hasse_p191 : BSD_Hasse_OPEN 191 := BSD_Hasse_OPEN_p191

/-! ## §11  Regulator and Tamagawa -/
theorem E143a1_regulator_pos : BSD_Regulator_OPEN 143 := BSD_Regulator_CLOSED
theorem E143a1_tamagawa_conj : BSD_TamagawaConj_OPEN 143 := BSD_TamagawaConj_CLOSED

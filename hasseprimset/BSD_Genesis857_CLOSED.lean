/-
================================================================
Towers / BSD / BSD_Genesis857_CLOSED  (genesis-857)

HasseBridge Tier C: Hasse bounds for primes
7079..7187 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=7079: card=7062, a_p=+18, disc=-27992
  p=7103: card=7106, a_p=-2, disc=-28408
  p=7109: card=7141, a_p=-31, disc=-27475
  p=7121: card=7209, a_p=-87, disc=-20915
  p=7127: card=7038, a_p=+90, disc=-20408
  p=7129: card=7005, a_p=+125, disc=-12891
  p=7151: card=7197, a_p=-45, disc=-26579
  p=7159: card=7153, a_p=+7, disc=-28587
  p=7177: card=7208, a_p=-30, disc=-27808
  p=7187: card=7281, a_p=-93, disc=-20099

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_857 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i857_p7079 : Fact (7079 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7103 : Fact (7103 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7109 : Fact (7109 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7121 : Fact (7121 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7127 : Fact (7127 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7129 : Fact (7129 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7151 : Fact (7151 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7159 : Fact (7159 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7177 : Fact (7177 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7187 : Fact (7187 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p7079 : (E143_Finset 7079).card = 7062 := by native_decide
theorem BSD_E143_card_p7103 : (E143_Finset 7103).card = 7106 := by native_decide
theorem BSD_E143_card_p7109 : (E143_Finset 7109).card = 7141 := by native_decide
theorem BSD_E143_card_p7121 : (E143_Finset 7121).card = 7209 := by native_decide
theorem BSD_E143_card_p7127 : (E143_Finset 7127).card = 7038 := by native_decide
theorem BSD_E143_card_p7129 : (E143_Finset 7129).card = 7005 := by native_decide
theorem BSD_E143_card_p7151 : (E143_Finset 7151).card = 7197 := by native_decide
theorem BSD_E143_card_p7159 : (E143_Finset 7159).card = 7153 := by native_decide
theorem BSD_E143_card_p7177 : (E143_Finset 7177).card = 7208 := by native_decide
theorem BSD_E143_card_p7187 : (E143_Finset 7187).card = 7281 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p7079 : a_p 7079 = (18 : ℤ) := by
  have h := BSD_E143_card_p7079; unfold a_p; omega
theorem BSD_ap_p7103 : a_p 7103 = (-2 : ℤ) := by
  have h := BSD_E143_card_p7103; unfold a_p; omega
theorem BSD_ap_p7109 : a_p 7109 = (-31 : ℤ) := by
  have h := BSD_E143_card_p7109; unfold a_p; omega
theorem BSD_ap_p7121 : a_p 7121 = (-87 : ℤ) := by
  have h := BSD_E143_card_p7121; unfold a_p; omega
theorem BSD_ap_p7127 : a_p 7127 = (90 : ℤ) := by
  have h := BSD_E143_card_p7127; unfold a_p; omega
theorem BSD_ap_p7129 : a_p 7129 = (125 : ℤ) := by
  have h := BSD_E143_card_p7129; unfold a_p; omega
theorem BSD_ap_p7151 : a_p 7151 = (-45 : ℤ) := by
  have h := BSD_E143_card_p7151; unfold a_p; omega
theorem BSD_ap_p7159 : a_p 7159 = (7 : ℤ) := by
  have h := BSD_E143_card_p7159; unfold a_p; omega
theorem BSD_ap_p7177 : a_p 7177 = (-30 : ℤ) := by
  have h := BSD_E143_card_p7177; unfold a_p; omega
theorem BSD_ap_p7187 : a_p 7187 = (-93 : ℤ) := by
  have h := BSD_E143_card_p7187; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=7079: a_p=+18, 4p-a_p²=27992
theorem BSD_DegreeNonneg_p7079 : BSD_FrobeniusDegreeNonneg_OPEN 7079 := fun r => by
  have hap : (a_p 7079 : ℝ) = 18 := by exact_mod_cast BSD_ap_p7079
  have key : r ^ 2 - (a_p 7079 : ℝ) * r + ((7079 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 27992/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

-- p=7103: a_p=-2, 4p-a_p²=28408
theorem BSD_DegreeNonneg_p7103 : BSD_FrobeniusDegreeNonneg_OPEN 7103 := fun r => by
  have hap : (a_p 7103 : ℝ) = -2 := by exact_mod_cast BSD_ap_p7103
  have key : r ^ 2 - (a_p 7103 : ℝ) * r + ((7103 : ℕ) : ℝ) =
      (r + 2/2) ^ 2 + 28408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (2 : ℝ)/2)]

-- p=7109: a_p=-31, 4p-a_p²=27475
theorem BSD_DegreeNonneg_p7109 : BSD_FrobeniusDegreeNonneg_OPEN 7109 := fun r => by
  have hap : (a_p 7109 : ℝ) = -31 := by exact_mod_cast BSD_ap_p7109
  have key : r ^ 2 - (a_p 7109 : ℝ) * r + ((7109 : ℕ) : ℝ) =
      (r + 31/2) ^ 2 + 27475/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (31 : ℝ)/2)]

-- p=7121: a_p=-87, 4p-a_p²=20915
theorem BSD_DegreeNonneg_p7121 : BSD_FrobeniusDegreeNonneg_OPEN 7121 := fun r => by
  have hap : (a_p 7121 : ℝ) = -87 := by exact_mod_cast BSD_ap_p7121
  have key : r ^ 2 - (a_p 7121 : ℝ) * r + ((7121 : ℕ) : ℝ) =
      (r + 87/2) ^ 2 + 20915/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (87 : ℝ)/2)]

-- p=7127: a_p=+90, 4p-a_p²=20408
theorem BSD_DegreeNonneg_p7127 : BSD_FrobeniusDegreeNonneg_OPEN 7127 := fun r => by
  have hap : (a_p 7127 : ℝ) = 90 := by exact_mod_cast BSD_ap_p7127
  have key : r ^ 2 - (a_p 7127 : ℝ) * r + ((7127 : ℕ) : ℝ) =
      (r - 90/2) ^ 2 + 20408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (90 : ℝ)/2)]

-- p=7129: a_p=+125, 4p-a_p²=12891
theorem BSD_DegreeNonneg_p7129 : BSD_FrobeniusDegreeNonneg_OPEN 7129 := fun r => by
  have hap : (a_p 7129 : ℝ) = 125 := by exact_mod_cast BSD_ap_p7129
  have key : r ^ 2 - (a_p 7129 : ℝ) * r + ((7129 : ℕ) : ℝ) =
      (r - 125/2) ^ 2 + 12891/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (125 : ℝ)/2)]

-- p=7151: a_p=-45, 4p-a_p²=26579
theorem BSD_DegreeNonneg_p7151 : BSD_FrobeniusDegreeNonneg_OPEN 7151 := fun r => by
  have hap : (a_p 7151 : ℝ) = -45 := by exact_mod_cast BSD_ap_p7151
  have key : r ^ 2 - (a_p 7151 : ℝ) * r + ((7151 : ℕ) : ℝ) =
      (r + 45/2) ^ 2 + 26579/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (45 : ℝ)/2)]

-- p=7159: a_p=+7, 4p-a_p²=28587
theorem BSD_DegreeNonneg_p7159 : BSD_FrobeniusDegreeNonneg_OPEN 7159 := fun r => by
  have hap : (a_p 7159 : ℝ) = 7 := by exact_mod_cast BSD_ap_p7159
  have key : r ^ 2 - (a_p 7159 : ℝ) * r + ((7159 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 28587/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

-- p=7177: a_p=-30, 4p-a_p²=27808
theorem BSD_DegreeNonneg_p7177 : BSD_FrobeniusDegreeNonneg_OPEN 7177 := fun r => by
  have hap : (a_p 7177 : ℝ) = -30 := by exact_mod_cast BSD_ap_p7177
  have key : r ^ 2 - (a_p 7177 : ℝ) * r + ((7177 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 27808/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

-- p=7187: a_p=-93, 4p-a_p²=20099
theorem BSD_DegreeNonneg_p7187 : BSD_FrobeniusDegreeNonneg_OPEN 7187 := fun r => by
  have hap : (a_p 7187 : ℝ) = -93 := by exact_mod_cast BSD_ap_p7187
  have key : r ^ 2 - (a_p 7187 : ℝ) * r + ((7187 : ℕ) : ℝ) =
      (r + 93/2) ^ 2 + 20099/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (93 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p7079 : BSD_Hasse_OPEN 7079 :=
  BSD_hasse_of_degree_nonneg 7079 BSD_DegreeNonneg_p7079
theorem BSD_Hasse_OPEN_p7103 : BSD_Hasse_OPEN 7103 :=
  BSD_hasse_of_degree_nonneg 7103 BSD_DegreeNonneg_p7103
theorem BSD_Hasse_OPEN_p7109 : BSD_Hasse_OPEN 7109 :=
  BSD_hasse_of_degree_nonneg 7109 BSD_DegreeNonneg_p7109
theorem BSD_Hasse_OPEN_p7121 : BSD_Hasse_OPEN 7121 :=
  BSD_hasse_of_degree_nonneg 7121 BSD_DegreeNonneg_p7121
theorem BSD_Hasse_OPEN_p7127 : BSD_Hasse_OPEN 7127 :=
  BSD_hasse_of_degree_nonneg 7127 BSD_DegreeNonneg_p7127
theorem BSD_Hasse_OPEN_p7129 : BSD_Hasse_OPEN 7129 :=
  BSD_hasse_of_degree_nonneg 7129 BSD_DegreeNonneg_p7129
theorem BSD_Hasse_OPEN_p7151 : BSD_Hasse_OPEN 7151 :=
  BSD_hasse_of_degree_nonneg 7151 BSD_DegreeNonneg_p7151
theorem BSD_Hasse_OPEN_p7159 : BSD_Hasse_OPEN 7159 :=
  BSD_hasse_of_degree_nonneg 7159 BSD_DegreeNonneg_p7159
theorem BSD_Hasse_OPEN_p7177 : BSD_Hasse_OPEN 7177 :=
  BSD_hasse_of_degree_nonneg 7177 BSD_DegreeNonneg_p7177
theorem BSD_Hasse_OPEN_p7187 : BSD_Hasse_OPEN 7187 :=
  BSD_hasse_of_degree_nonneg 7187 BSD_DegreeNonneg_p7187

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p7079 : (a_p 7079 : ℝ) ^ 2 ≤ 4 * (7079 : ℝ) :=
  BSD_disc_from_deg_857 BSD_DegreeNonneg_p7079
theorem BSD_HasseBound_Disc_p7103 : (a_p 7103 : ℝ) ^ 2 ≤ 4 * (7103 : ℝ) :=
  BSD_disc_from_deg_857 BSD_DegreeNonneg_p7103
theorem BSD_HasseBound_Disc_p7109 : (a_p 7109 : ℝ) ^ 2 ≤ 4 * (7109 : ℝ) :=
  BSD_disc_from_deg_857 BSD_DegreeNonneg_p7109
theorem BSD_HasseBound_Disc_p7121 : (a_p 7121 : ℝ) ^ 2 ≤ 4 * (7121 : ℝ) :=
  BSD_disc_from_deg_857 BSD_DegreeNonneg_p7121
theorem BSD_HasseBound_Disc_p7127 : (a_p 7127 : ℝ) ^ 2 ≤ 4 * (7127 : ℝ) :=
  BSD_disc_from_deg_857 BSD_DegreeNonneg_p7127
theorem BSD_HasseBound_Disc_p7129 : (a_p 7129 : ℝ) ^ 2 ≤ 4 * (7129 : ℝ) :=
  BSD_disc_from_deg_857 BSD_DegreeNonneg_p7129
theorem BSD_HasseBound_Disc_p7151 : (a_p 7151 : ℝ) ^ 2 ≤ 4 * (7151 : ℝ) :=
  BSD_disc_from_deg_857 BSD_DegreeNonneg_p7151
theorem BSD_HasseBound_Disc_p7159 : (a_p 7159 : ℝ) ^ 2 ≤ 4 * (7159 : ℝ) :=
  BSD_disc_from_deg_857 BSD_DegreeNonneg_p7159
theorem BSD_HasseBound_Disc_p7177 : (a_p 7177 : ℝ) ^ 2 ≤ 4 * (7177 : ℝ) :=
  BSD_disc_from_deg_857 BSD_DegreeNonneg_p7177
theorem BSD_HasseBound_Disc_p7187 : (a_p 7187 : ℝ) ^ 2 ≤ 4 * (7187 : ℝ) :=
  BSD_disc_from_deg_857 BSD_DegreeNonneg_p7187

end Towers.BSD
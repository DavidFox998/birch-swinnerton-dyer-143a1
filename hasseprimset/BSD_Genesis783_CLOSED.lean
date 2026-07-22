/-
================================================================
Towers / BSD / BSD_Genesis783_CLOSED  (genesis-783)

HasseBridge Tier C: Hasse bounds for primes
1009..1061 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1009: card=1050, a_p=-40, disc=-2436
  p=1013: card=1051, a_p=-37, disc=-2683
  p=1019: card=990, a_p=+30, disc=-3176
  p=1021: card=996, a_p=+26, disc=-3408
  p=1031: card=1074, a_p=-42, disc=-2360
  p=1033: card=1058, a_p=-24, disc=-3556
  p=1039: card=991, a_p=+49, disc=-1755
  p=1049: card=1021, a_p=+29, disc=-3355
  p=1051: card=1002, a_p=+50, disc=-1704
  p=1061: card=1077, a_p=-15, disc=-4019

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_783 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i783_p1009 : Fact (1009 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1013 : Fact (1013 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1019 : Fact (1019 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1021 : Fact (1021 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1031 : Fact (1031 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1033 : Fact (1033 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1039 : Fact (1039 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1049 : Fact (1049 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1051 : Fact (1051 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1061 : Fact (1061 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1009 : (E143_Finset 1009).card = 1050 := by native_decide
theorem BSD_E143_card_p1013 : (E143_Finset 1013).card = 1051 := by native_decide
theorem BSD_E143_card_p1019 : (E143_Finset 1019).card = 990 := by native_decide
theorem BSD_E143_card_p1021 : (E143_Finset 1021).card = 996 := by native_decide
theorem BSD_E143_card_p1031 : (E143_Finset 1031).card = 1074 := by native_decide
theorem BSD_E143_card_p1033 : (E143_Finset 1033).card = 1058 := by native_decide
theorem BSD_E143_card_p1039 : (E143_Finset 1039).card = 991 := by native_decide
theorem BSD_E143_card_p1049 : (E143_Finset 1049).card = 1021 := by native_decide
theorem BSD_E143_card_p1051 : (E143_Finset 1051).card = 1002 := by native_decide
theorem BSD_E143_card_p1061 : (E143_Finset 1061).card = 1077 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1009 : a_p 1009 = (-40 : ℤ) := by
  have h := BSD_E143_card_p1009; unfold a_p; omega
theorem BSD_ap_p1013 : a_p 1013 = (-37 : ℤ) := by
  have h := BSD_E143_card_p1013; unfold a_p; omega
theorem BSD_ap_p1019 : a_p 1019 = (30 : ℤ) := by
  have h := BSD_E143_card_p1019; unfold a_p; omega
theorem BSD_ap_p1021 : a_p 1021 = (26 : ℤ) := by
  have h := BSD_E143_card_p1021; unfold a_p; omega
theorem BSD_ap_p1031 : a_p 1031 = (-42 : ℤ) := by
  have h := BSD_E143_card_p1031; unfold a_p; omega
theorem BSD_ap_p1033 : a_p 1033 = (-24 : ℤ) := by
  have h := BSD_E143_card_p1033; unfold a_p; omega
theorem BSD_ap_p1039 : a_p 1039 = (49 : ℤ) := by
  have h := BSD_E143_card_p1039; unfold a_p; omega
theorem BSD_ap_p1049 : a_p 1049 = (29 : ℤ) := by
  have h := BSD_E143_card_p1049; unfold a_p; omega
theorem BSD_ap_p1051 : a_p 1051 = (50 : ℤ) := by
  have h := BSD_E143_card_p1051; unfold a_p; omega
theorem BSD_ap_p1061 : a_p 1061 = (-15 : ℤ) := by
  have h := BSD_E143_card_p1061; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1009: a_p=-40, 4p-a_p²=2436
theorem BSD_DegreeNonneg_p1009 : BSD_FrobeniusDegreeNonneg_OPEN 1009 := fun r => by
  have hap : (a_p 1009 : ℝ) = -40 := by exact_mod_cast BSD_ap_p1009
  have key : r ^ 2 - (a_p 1009 : ℝ) * r + ((1009 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 2436/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

-- p=1013: a_p=-37, 4p-a_p²=2683
theorem BSD_DegreeNonneg_p1013 : BSD_FrobeniusDegreeNonneg_OPEN 1013 := fun r => by
  have hap : (a_p 1013 : ℝ) = -37 := by exact_mod_cast BSD_ap_p1013
  have key : r ^ 2 - (a_p 1013 : ℝ) * r + ((1013 : ℕ) : ℝ) =
      (r + 37/2) ^ 2 + 2683/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (37 : ℝ)/2)]

-- p=1019: a_p=+30, 4p-a_p²=3176
theorem BSD_DegreeNonneg_p1019 : BSD_FrobeniusDegreeNonneg_OPEN 1019 := fun r => by
  have hap : (a_p 1019 : ℝ) = 30 := by exact_mod_cast BSD_ap_p1019
  have key : r ^ 2 - (a_p 1019 : ℝ) * r + ((1019 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 3176/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

-- p=1021: a_p=+26, 4p-a_p²=3408
theorem BSD_DegreeNonneg_p1021 : BSD_FrobeniusDegreeNonneg_OPEN 1021 := fun r => by
  have hap : (a_p 1021 : ℝ) = 26 := by exact_mod_cast BSD_ap_p1021
  have key : r ^ 2 - (a_p 1021 : ℝ) * r + ((1021 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 3408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

-- p=1031: a_p=-42, 4p-a_p²=2360
theorem BSD_DegreeNonneg_p1031 : BSD_FrobeniusDegreeNonneg_OPEN 1031 := fun r => by
  have hap : (a_p 1031 : ℝ) = -42 := by exact_mod_cast BSD_ap_p1031
  have key : r ^ 2 - (a_p 1031 : ℝ) * r + ((1031 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 2360/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

-- p=1033: a_p=-24, 4p-a_p²=3556
theorem BSD_DegreeNonneg_p1033 : BSD_FrobeniusDegreeNonneg_OPEN 1033 := fun r => by
  have hap : (a_p 1033 : ℝ) = -24 := by exact_mod_cast BSD_ap_p1033
  have key : r ^ 2 - (a_p 1033 : ℝ) * r + ((1033 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 3556/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

-- p=1039: a_p=+49, 4p-a_p²=1755
theorem BSD_DegreeNonneg_p1039 : BSD_FrobeniusDegreeNonneg_OPEN 1039 := fun r => by
  have hap : (a_p 1039 : ℝ) = 49 := by exact_mod_cast BSD_ap_p1039
  have key : r ^ 2 - (a_p 1039 : ℝ) * r + ((1039 : ℕ) : ℝ) =
      (r - 49/2) ^ 2 + 1755/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (49 : ℝ)/2)]

-- p=1049: a_p=+29, 4p-a_p²=3355
theorem BSD_DegreeNonneg_p1049 : BSD_FrobeniusDegreeNonneg_OPEN 1049 := fun r => by
  have hap : (a_p 1049 : ℝ) = 29 := by exact_mod_cast BSD_ap_p1049
  have key : r ^ 2 - (a_p 1049 : ℝ) * r + ((1049 : ℕ) : ℝ) =
      (r - 29/2) ^ 2 + 3355/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (29 : ℝ)/2)]

-- p=1051: a_p=+50, 4p-a_p²=1704
theorem BSD_DegreeNonneg_p1051 : BSD_FrobeniusDegreeNonneg_OPEN 1051 := fun r => by
  have hap : (a_p 1051 : ℝ) = 50 := by exact_mod_cast BSD_ap_p1051
  have key : r ^ 2 - (a_p 1051 : ℝ) * r + ((1051 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 1704/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

-- p=1061: a_p=-15, 4p-a_p²=4019
theorem BSD_DegreeNonneg_p1061 : BSD_FrobeniusDegreeNonneg_OPEN 1061 := fun r => by
  have hap : (a_p 1061 : ℝ) = -15 := by exact_mod_cast BSD_ap_p1061
  have key : r ^ 2 - (a_p 1061 : ℝ) * r + ((1061 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 4019/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1009 : BSD_Hasse_OPEN 1009 :=
  BSD_hasse_of_degree_nonneg 1009 BSD_DegreeNonneg_p1009
theorem BSD_Hasse_OPEN_p1013 : BSD_Hasse_OPEN 1013 :=
  BSD_hasse_of_degree_nonneg 1013 BSD_DegreeNonneg_p1013
theorem BSD_Hasse_OPEN_p1019 : BSD_Hasse_OPEN 1019 :=
  BSD_hasse_of_degree_nonneg 1019 BSD_DegreeNonneg_p1019
theorem BSD_Hasse_OPEN_p1021 : BSD_Hasse_OPEN 1021 :=
  BSD_hasse_of_degree_nonneg 1021 BSD_DegreeNonneg_p1021
theorem BSD_Hasse_OPEN_p1031 : BSD_Hasse_OPEN 1031 :=
  BSD_hasse_of_degree_nonneg 1031 BSD_DegreeNonneg_p1031
theorem BSD_Hasse_OPEN_p1033 : BSD_Hasse_OPEN 1033 :=
  BSD_hasse_of_degree_nonneg 1033 BSD_DegreeNonneg_p1033
theorem BSD_Hasse_OPEN_p1039 : BSD_Hasse_OPEN 1039 :=
  BSD_hasse_of_degree_nonneg 1039 BSD_DegreeNonneg_p1039
theorem BSD_Hasse_OPEN_p1049 : BSD_Hasse_OPEN 1049 :=
  BSD_hasse_of_degree_nonneg 1049 BSD_DegreeNonneg_p1049
theorem BSD_Hasse_OPEN_p1051 : BSD_Hasse_OPEN 1051 :=
  BSD_hasse_of_degree_nonneg 1051 BSD_DegreeNonneg_p1051
theorem BSD_Hasse_OPEN_p1061 : BSD_Hasse_OPEN 1061 :=
  BSD_hasse_of_degree_nonneg 1061 BSD_DegreeNonneg_p1061

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1009 : (a_p 1009 : ℝ) ^ 2 ≤ 4 * (1009 : ℝ) :=
  BSD_disc_from_deg_783 BSD_DegreeNonneg_p1009
theorem BSD_HasseBound_Disc_p1013 : (a_p 1013 : ℝ) ^ 2 ≤ 4 * (1013 : ℝ) :=
  BSD_disc_from_deg_783 BSD_DegreeNonneg_p1013
theorem BSD_HasseBound_Disc_p1019 : (a_p 1019 : ℝ) ^ 2 ≤ 4 * (1019 : ℝ) :=
  BSD_disc_from_deg_783 BSD_DegreeNonneg_p1019
theorem BSD_HasseBound_Disc_p1021 : (a_p 1021 : ℝ) ^ 2 ≤ 4 * (1021 : ℝ) :=
  BSD_disc_from_deg_783 BSD_DegreeNonneg_p1021
theorem BSD_HasseBound_Disc_p1031 : (a_p 1031 : ℝ) ^ 2 ≤ 4 * (1031 : ℝ) :=
  BSD_disc_from_deg_783 BSD_DegreeNonneg_p1031
theorem BSD_HasseBound_Disc_p1033 : (a_p 1033 : ℝ) ^ 2 ≤ 4 * (1033 : ℝ) :=
  BSD_disc_from_deg_783 BSD_DegreeNonneg_p1033
theorem BSD_HasseBound_Disc_p1039 : (a_p 1039 : ℝ) ^ 2 ≤ 4 * (1039 : ℝ) :=
  BSD_disc_from_deg_783 BSD_DegreeNonneg_p1039
theorem BSD_HasseBound_Disc_p1049 : (a_p 1049 : ℝ) ^ 2 ≤ 4 * (1049 : ℝ) :=
  BSD_disc_from_deg_783 BSD_DegreeNonneg_p1049
theorem BSD_HasseBound_Disc_p1051 : (a_p 1051 : ℝ) ^ 2 ≤ 4 * (1051 : ℝ) :=
  BSD_disc_from_deg_783 BSD_DegreeNonneg_p1051
theorem BSD_HasseBound_Disc_p1061 : (a_p 1061 : ℝ) ^ 2 ≤ 4 * (1061 : ℝ) :=
  BSD_disc_from_deg_783 BSD_DegreeNonneg_p1061

end Towers.BSD
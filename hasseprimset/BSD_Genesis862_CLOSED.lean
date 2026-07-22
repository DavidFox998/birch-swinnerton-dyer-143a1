/-
================================================================
Towers / BSD / BSD_Genesis862_CLOSED  (genesis-862)

HasseBridge Tier C: Hasse bounds for primes
7559..7621 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=7559: card=7518, a_p=+42, disc=-28472
  p=7561: card=7492, a_p=+70, disc=-25344
  p=7573: card=7723, a_p=-149, disc=-8091
  p=7577: card=7560, a_p=+18, disc=-29984
  p=7583: card=7584, a_p=+0, disc=-30332
  p=7589: card=7740, a_p=-150, disc=-7856
  p=7591: card=7561, a_p=+31, disc=-29403
  p=7603: card=7458, a_p=+146, disc=-9096
  p=7607: card=7586, a_p=+22, disc=-29944
  p=7621: card=7764, a_p=-142, disc=-10320

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_862 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i862_p7559 : Fact (7559 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7561 : Fact (7561 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7573 : Fact (7573 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7577 : Fact (7577 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7583 : Fact (7583 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7589 : Fact (7589 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7591 : Fact (7591 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7603 : Fact (7603 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7607 : Fact (7607 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7621 : Fact (7621 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p7559 : (E143_Finset 7559).card = 7518 := by native_decide
theorem BSD_E143_card_p7561 : (E143_Finset 7561).card = 7492 := by native_decide
theorem BSD_E143_card_p7573 : (E143_Finset 7573).card = 7723 := by native_decide
theorem BSD_E143_card_p7577 : (E143_Finset 7577).card = 7560 := by native_decide
theorem BSD_E143_card_p7583 : (E143_Finset 7583).card = 7584 := by native_decide
theorem BSD_E143_card_p7589 : (E143_Finset 7589).card = 7740 := by native_decide
theorem BSD_E143_card_p7591 : (E143_Finset 7591).card = 7561 := by native_decide
theorem BSD_E143_card_p7603 : (E143_Finset 7603).card = 7458 := by native_decide
theorem BSD_E143_card_p7607 : (E143_Finset 7607).card = 7586 := by native_decide
theorem BSD_E143_card_p7621 : (E143_Finset 7621).card = 7764 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p7559 : a_p 7559 = (42 : ℤ) := by
  have h := BSD_E143_card_p7559; unfold a_p; omega
theorem BSD_ap_p7561 : a_p 7561 = (70 : ℤ) := by
  have h := BSD_E143_card_p7561; unfold a_p; omega
theorem BSD_ap_p7573 : a_p 7573 = (-149 : ℤ) := by
  have h := BSD_E143_card_p7573; unfold a_p; omega
theorem BSD_ap_p7577 : a_p 7577 = (18 : ℤ) := by
  have h := BSD_E143_card_p7577; unfold a_p; omega
theorem BSD_ap_p7583 : a_p 7583 = (0 : ℤ) := by
  have h := BSD_E143_card_p7583; unfold a_p; omega
theorem BSD_ap_p7589 : a_p 7589 = (-150 : ℤ) := by
  have h := BSD_E143_card_p7589; unfold a_p; omega
theorem BSD_ap_p7591 : a_p 7591 = (31 : ℤ) := by
  have h := BSD_E143_card_p7591; unfold a_p; omega
theorem BSD_ap_p7603 : a_p 7603 = (146 : ℤ) := by
  have h := BSD_E143_card_p7603; unfold a_p; omega
theorem BSD_ap_p7607 : a_p 7607 = (22 : ℤ) := by
  have h := BSD_E143_card_p7607; unfold a_p; omega
theorem BSD_ap_p7621 : a_p 7621 = (-142 : ℤ) := by
  have h := BSD_E143_card_p7621; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=7559: a_p=+42, 4p-a_p²=28472
theorem BSD_DegreeNonneg_p7559 : BSD_FrobeniusDegreeNonneg_OPEN 7559 := fun r => by
  have hap : (a_p 7559 : ℝ) = 42 := by exact_mod_cast BSD_ap_p7559
  have key : r ^ 2 - (a_p 7559 : ℝ) * r + ((7559 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 28472/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

-- p=7561: a_p=+70, 4p-a_p²=25344
theorem BSD_DegreeNonneg_p7561 : BSD_FrobeniusDegreeNonneg_OPEN 7561 := fun r => by
  have hap : (a_p 7561 : ℝ) = 70 := by exact_mod_cast BSD_ap_p7561
  have key : r ^ 2 - (a_p 7561 : ℝ) * r + ((7561 : ℕ) : ℝ) =
      (r - 70/2) ^ 2 + 25344/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (70 : ℝ)/2)]

-- p=7573: a_p=-149, 4p-a_p²=8091
theorem BSD_DegreeNonneg_p7573 : BSD_FrobeniusDegreeNonneg_OPEN 7573 := fun r => by
  have hap : (a_p 7573 : ℝ) = -149 := by exact_mod_cast BSD_ap_p7573
  have key : r ^ 2 - (a_p 7573 : ℝ) * r + ((7573 : ℕ) : ℝ) =
      (r + 149/2) ^ 2 + 8091/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (149 : ℝ)/2)]

-- p=7577: a_p=+18, 4p-a_p²=29984
theorem BSD_DegreeNonneg_p7577 : BSD_FrobeniusDegreeNonneg_OPEN 7577 := fun r => by
  have hap : (a_p 7577 : ℝ) = 18 := by exact_mod_cast BSD_ap_p7577
  have key : r ^ 2 - (a_p 7577 : ℝ) * r + ((7577 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 29984/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

-- p=7583: a_p=+0, 4p-a_p²=30332
theorem BSD_DegreeNonneg_p7583 : BSD_FrobeniusDegreeNonneg_OPEN 7583 := fun r => by
  have hap : (a_p 7583 : ℝ) = 0 := by exact_mod_cast BSD_ap_p7583
  have key : r ^ 2 - (a_p 7583 : ℝ) * r + ((7583 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 30332/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

-- p=7589: a_p=-150, 4p-a_p²=7856
theorem BSD_DegreeNonneg_p7589 : BSD_FrobeniusDegreeNonneg_OPEN 7589 := fun r => by
  have hap : (a_p 7589 : ℝ) = -150 := by exact_mod_cast BSD_ap_p7589
  have key : r ^ 2 - (a_p 7589 : ℝ) * r + ((7589 : ℕ) : ℝ) =
      (r + 150/2) ^ 2 + 7856/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (150 : ℝ)/2)]

-- p=7591: a_p=+31, 4p-a_p²=29403
theorem BSD_DegreeNonneg_p7591 : BSD_FrobeniusDegreeNonneg_OPEN 7591 := fun r => by
  have hap : (a_p 7591 : ℝ) = 31 := by exact_mod_cast BSD_ap_p7591
  have key : r ^ 2 - (a_p 7591 : ℝ) * r + ((7591 : ℕ) : ℝ) =
      (r - 31/2) ^ 2 + 29403/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (31 : ℝ)/2)]

-- p=7603: a_p=+146, 4p-a_p²=9096
theorem BSD_DegreeNonneg_p7603 : BSD_FrobeniusDegreeNonneg_OPEN 7603 := fun r => by
  have hap : (a_p 7603 : ℝ) = 146 := by exact_mod_cast BSD_ap_p7603
  have key : r ^ 2 - (a_p 7603 : ℝ) * r + ((7603 : ℕ) : ℝ) =
      (r - 146/2) ^ 2 + 9096/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (146 : ℝ)/2)]

-- p=7607: a_p=+22, 4p-a_p²=29944
theorem BSD_DegreeNonneg_p7607 : BSD_FrobeniusDegreeNonneg_OPEN 7607 := fun r => by
  have hap : (a_p 7607 : ℝ) = 22 := by exact_mod_cast BSD_ap_p7607
  have key : r ^ 2 - (a_p 7607 : ℝ) * r + ((7607 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 29944/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

-- p=7621: a_p=-142, 4p-a_p²=10320
theorem BSD_DegreeNonneg_p7621 : BSD_FrobeniusDegreeNonneg_OPEN 7621 := fun r => by
  have hap : (a_p 7621 : ℝ) = -142 := by exact_mod_cast BSD_ap_p7621
  have key : r ^ 2 - (a_p 7621 : ℝ) * r + ((7621 : ℕ) : ℝ) =
      (r + 142/2) ^ 2 + 10320/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (142 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p7559 : BSD_Hasse_OPEN 7559 :=
  BSD_hasse_of_degree_nonneg 7559 BSD_DegreeNonneg_p7559
theorem BSD_Hasse_OPEN_p7561 : BSD_Hasse_OPEN 7561 :=
  BSD_hasse_of_degree_nonneg 7561 BSD_DegreeNonneg_p7561
theorem BSD_Hasse_OPEN_p7573 : BSD_Hasse_OPEN 7573 :=
  BSD_hasse_of_degree_nonneg 7573 BSD_DegreeNonneg_p7573
theorem BSD_Hasse_OPEN_p7577 : BSD_Hasse_OPEN 7577 :=
  BSD_hasse_of_degree_nonneg 7577 BSD_DegreeNonneg_p7577
theorem BSD_Hasse_OPEN_p7583 : BSD_Hasse_OPEN 7583 :=
  BSD_hasse_of_degree_nonneg 7583 BSD_DegreeNonneg_p7583
theorem BSD_Hasse_OPEN_p7589 : BSD_Hasse_OPEN 7589 :=
  BSD_hasse_of_degree_nonneg 7589 BSD_DegreeNonneg_p7589
theorem BSD_Hasse_OPEN_p7591 : BSD_Hasse_OPEN 7591 :=
  BSD_hasse_of_degree_nonneg 7591 BSD_DegreeNonneg_p7591
theorem BSD_Hasse_OPEN_p7603 : BSD_Hasse_OPEN 7603 :=
  BSD_hasse_of_degree_nonneg 7603 BSD_DegreeNonneg_p7603
theorem BSD_Hasse_OPEN_p7607 : BSD_Hasse_OPEN 7607 :=
  BSD_hasse_of_degree_nonneg 7607 BSD_DegreeNonneg_p7607
theorem BSD_Hasse_OPEN_p7621 : BSD_Hasse_OPEN 7621 :=
  BSD_hasse_of_degree_nonneg 7621 BSD_DegreeNonneg_p7621

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p7559 : (a_p 7559 : ℝ) ^ 2 ≤ 4 * (7559 : ℝ) :=
  BSD_disc_from_deg_862 BSD_DegreeNonneg_p7559
theorem BSD_HasseBound_Disc_p7561 : (a_p 7561 : ℝ) ^ 2 ≤ 4 * (7561 : ℝ) :=
  BSD_disc_from_deg_862 BSD_DegreeNonneg_p7561
theorem BSD_HasseBound_Disc_p7573 : (a_p 7573 : ℝ) ^ 2 ≤ 4 * (7573 : ℝ) :=
  BSD_disc_from_deg_862 BSD_DegreeNonneg_p7573
theorem BSD_HasseBound_Disc_p7577 : (a_p 7577 : ℝ) ^ 2 ≤ 4 * (7577 : ℝ) :=
  BSD_disc_from_deg_862 BSD_DegreeNonneg_p7577
theorem BSD_HasseBound_Disc_p7583 : (a_p 7583 : ℝ) ^ 2 ≤ 4 * (7583 : ℝ) :=
  BSD_disc_from_deg_862 BSD_DegreeNonneg_p7583
theorem BSD_HasseBound_Disc_p7589 : (a_p 7589 : ℝ) ^ 2 ≤ 4 * (7589 : ℝ) :=
  BSD_disc_from_deg_862 BSD_DegreeNonneg_p7589
theorem BSD_HasseBound_Disc_p7591 : (a_p 7591 : ℝ) ^ 2 ≤ 4 * (7591 : ℝ) :=
  BSD_disc_from_deg_862 BSD_DegreeNonneg_p7591
theorem BSD_HasseBound_Disc_p7603 : (a_p 7603 : ℝ) ^ 2 ≤ 4 * (7603 : ℝ) :=
  BSD_disc_from_deg_862 BSD_DegreeNonneg_p7603
theorem BSD_HasseBound_Disc_p7607 : (a_p 7607 : ℝ) ^ 2 ≤ 4 * (7607 : ℝ) :=
  BSD_disc_from_deg_862 BSD_DegreeNonneg_p7607
theorem BSD_HasseBound_Disc_p7621 : (a_p 7621 : ℝ) ^ 2 ≤ 4 * (7621 : ℝ) :=
  BSD_disc_from_deg_862 BSD_DegreeNonneg_p7621

end Towers.BSD
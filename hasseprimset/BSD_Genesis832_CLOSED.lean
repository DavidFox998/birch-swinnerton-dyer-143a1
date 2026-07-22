/-
================================================================
Towers / BSD / BSD_Genesis832_CLOSED  (genesis-832)

HasseBridge Tier C: Hasse bounds for primes
4933..4993 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=4933: card=4832, a_p=+102, disc=-9328
  p=4937: card=4848, a_p=+90, disc=-11648
  p=4943: card=5028, a_p=-84, disc=-12716
  p=4951: card=4872, a_p=+80, disc=-13404
  p=4957: card=4858, a_p=+100, disc=-9828
  p=4967: card=4890, a_p=+78, disc=-13784
  p=4969: card=5010, a_p=-40, disc=-18276
  p=4973: card=4905, a_p=+69, disc=-15131
  p=4987: card=4976, a_p=+12, disc=-19804
  p=4993: card=4934, a_p=+60, disc=-16372

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_832 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i832_p4933 : Fact (4933 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4937 : Fact (4937 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4943 : Fact (4943 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4951 : Fact (4951 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4957 : Fact (4957 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4967 : Fact (4967 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4969 : Fact (4969 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4973 : Fact (4973 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4987 : Fact (4987 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4993 : Fact (4993 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p4933 : (E143_Finset 4933).card = 4832 := by native_decide
theorem BSD_E143_card_p4937 : (E143_Finset 4937).card = 4848 := by native_decide
theorem BSD_E143_card_p4943 : (E143_Finset 4943).card = 5028 := by native_decide
theorem BSD_E143_card_p4951 : (E143_Finset 4951).card = 4872 := by native_decide
theorem BSD_E143_card_p4957 : (E143_Finset 4957).card = 4858 := by native_decide
theorem BSD_E143_card_p4967 : (E143_Finset 4967).card = 4890 := by native_decide
theorem BSD_E143_card_p4969 : (E143_Finset 4969).card = 5010 := by native_decide
theorem BSD_E143_card_p4973 : (E143_Finset 4973).card = 4905 := by native_decide
theorem BSD_E143_card_p4987 : (E143_Finset 4987).card = 4976 := by native_decide
theorem BSD_E143_card_p4993 : (E143_Finset 4993).card = 4934 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p4933 : a_p 4933 = (102 : ℤ) := by
  have h := BSD_E143_card_p4933; unfold a_p; omega
theorem BSD_ap_p4937 : a_p 4937 = (90 : ℤ) := by
  have h := BSD_E143_card_p4937; unfold a_p; omega
theorem BSD_ap_p4943 : a_p 4943 = (-84 : ℤ) := by
  have h := BSD_E143_card_p4943; unfold a_p; omega
theorem BSD_ap_p4951 : a_p 4951 = (80 : ℤ) := by
  have h := BSD_E143_card_p4951; unfold a_p; omega
theorem BSD_ap_p4957 : a_p 4957 = (100 : ℤ) := by
  have h := BSD_E143_card_p4957; unfold a_p; omega
theorem BSD_ap_p4967 : a_p 4967 = (78 : ℤ) := by
  have h := BSD_E143_card_p4967; unfold a_p; omega
theorem BSD_ap_p4969 : a_p 4969 = (-40 : ℤ) := by
  have h := BSD_E143_card_p4969; unfold a_p; omega
theorem BSD_ap_p4973 : a_p 4973 = (69 : ℤ) := by
  have h := BSD_E143_card_p4973; unfold a_p; omega
theorem BSD_ap_p4987 : a_p 4987 = (12 : ℤ) := by
  have h := BSD_E143_card_p4987; unfold a_p; omega
theorem BSD_ap_p4993 : a_p 4993 = (60 : ℤ) := by
  have h := BSD_E143_card_p4993; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=4933: a_p=+102, 4p-a_p²=9328
theorem BSD_DegreeNonneg_p4933 : BSD_FrobeniusDegreeNonneg_OPEN 4933 := fun r => by
  have hap : (a_p 4933 : ℝ) = 102 := by exact_mod_cast BSD_ap_p4933
  have key : r ^ 2 - (a_p 4933 : ℝ) * r + ((4933 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 9328/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

-- p=4937: a_p=+90, 4p-a_p²=11648
theorem BSD_DegreeNonneg_p4937 : BSD_FrobeniusDegreeNonneg_OPEN 4937 := fun r => by
  have hap : (a_p 4937 : ℝ) = 90 := by exact_mod_cast BSD_ap_p4937
  have key : r ^ 2 - (a_p 4937 : ℝ) * r + ((4937 : ℕ) : ℝ) =
      (r - 90/2) ^ 2 + 11648/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (90 : ℝ)/2)]

-- p=4943: a_p=-84, 4p-a_p²=12716
theorem BSD_DegreeNonneg_p4943 : BSD_FrobeniusDegreeNonneg_OPEN 4943 := fun r => by
  have hap : (a_p 4943 : ℝ) = -84 := by exact_mod_cast BSD_ap_p4943
  have key : r ^ 2 - (a_p 4943 : ℝ) * r + ((4943 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 12716/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

-- p=4951: a_p=+80, 4p-a_p²=13404
theorem BSD_DegreeNonneg_p4951 : BSD_FrobeniusDegreeNonneg_OPEN 4951 := fun r => by
  have hap : (a_p 4951 : ℝ) = 80 := by exact_mod_cast BSD_ap_p4951
  have key : r ^ 2 - (a_p 4951 : ℝ) * r + ((4951 : ℕ) : ℝ) =
      (r - 80/2) ^ 2 + 13404/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (80 : ℝ)/2)]

-- p=4957: a_p=+100, 4p-a_p²=9828
theorem BSD_DegreeNonneg_p4957 : BSD_FrobeniusDegreeNonneg_OPEN 4957 := fun r => by
  have hap : (a_p 4957 : ℝ) = 100 := by exact_mod_cast BSD_ap_p4957
  have key : r ^ 2 - (a_p 4957 : ℝ) * r + ((4957 : ℕ) : ℝ) =
      (r - 100/2) ^ 2 + 9828/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (100 : ℝ)/2)]

-- p=4967: a_p=+78, 4p-a_p²=13784
theorem BSD_DegreeNonneg_p4967 : BSD_FrobeniusDegreeNonneg_OPEN 4967 := fun r => by
  have hap : (a_p 4967 : ℝ) = 78 := by exact_mod_cast BSD_ap_p4967
  have key : r ^ 2 - (a_p 4967 : ℝ) * r + ((4967 : ℕ) : ℝ) =
      (r - 78/2) ^ 2 + 13784/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (78 : ℝ)/2)]

-- p=4969: a_p=-40, 4p-a_p²=18276
theorem BSD_DegreeNonneg_p4969 : BSD_FrobeniusDegreeNonneg_OPEN 4969 := fun r => by
  have hap : (a_p 4969 : ℝ) = -40 := by exact_mod_cast BSD_ap_p4969
  have key : r ^ 2 - (a_p 4969 : ℝ) * r + ((4969 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 18276/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

-- p=4973: a_p=+69, 4p-a_p²=15131
theorem BSD_DegreeNonneg_p4973 : BSD_FrobeniusDegreeNonneg_OPEN 4973 := fun r => by
  have hap : (a_p 4973 : ℝ) = 69 := by exact_mod_cast BSD_ap_p4973
  have key : r ^ 2 - (a_p 4973 : ℝ) * r + ((4973 : ℕ) : ℝ) =
      (r - 69/2) ^ 2 + 15131/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (69 : ℝ)/2)]

-- p=4987: a_p=+12, 4p-a_p²=19804
theorem BSD_DegreeNonneg_p4987 : BSD_FrobeniusDegreeNonneg_OPEN 4987 := fun r => by
  have hap : (a_p 4987 : ℝ) = 12 := by exact_mod_cast BSD_ap_p4987
  have key : r ^ 2 - (a_p 4987 : ℝ) * r + ((4987 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 19804/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

-- p=4993: a_p=+60, 4p-a_p²=16372
theorem BSD_DegreeNonneg_p4993 : BSD_FrobeniusDegreeNonneg_OPEN 4993 := fun r => by
  have hap : (a_p 4993 : ℝ) = 60 := by exact_mod_cast BSD_ap_p4993
  have key : r ^ 2 - (a_p 4993 : ℝ) * r + ((4993 : ℕ) : ℝ) =
      (r - 60/2) ^ 2 + 16372/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (60 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p4933 : BSD_Hasse_OPEN 4933 :=
  BSD_hasse_of_degree_nonneg 4933 BSD_DegreeNonneg_p4933
theorem BSD_Hasse_OPEN_p4937 : BSD_Hasse_OPEN 4937 :=
  BSD_hasse_of_degree_nonneg 4937 BSD_DegreeNonneg_p4937
theorem BSD_Hasse_OPEN_p4943 : BSD_Hasse_OPEN 4943 :=
  BSD_hasse_of_degree_nonneg 4943 BSD_DegreeNonneg_p4943
theorem BSD_Hasse_OPEN_p4951 : BSD_Hasse_OPEN 4951 :=
  BSD_hasse_of_degree_nonneg 4951 BSD_DegreeNonneg_p4951
theorem BSD_Hasse_OPEN_p4957 : BSD_Hasse_OPEN 4957 :=
  BSD_hasse_of_degree_nonneg 4957 BSD_DegreeNonneg_p4957
theorem BSD_Hasse_OPEN_p4967 : BSD_Hasse_OPEN 4967 :=
  BSD_hasse_of_degree_nonneg 4967 BSD_DegreeNonneg_p4967
theorem BSD_Hasse_OPEN_p4969 : BSD_Hasse_OPEN 4969 :=
  BSD_hasse_of_degree_nonneg 4969 BSD_DegreeNonneg_p4969
theorem BSD_Hasse_OPEN_p4973 : BSD_Hasse_OPEN 4973 :=
  BSD_hasse_of_degree_nonneg 4973 BSD_DegreeNonneg_p4973
theorem BSD_Hasse_OPEN_p4987 : BSD_Hasse_OPEN 4987 :=
  BSD_hasse_of_degree_nonneg 4987 BSD_DegreeNonneg_p4987
theorem BSD_Hasse_OPEN_p4993 : BSD_Hasse_OPEN 4993 :=
  BSD_hasse_of_degree_nonneg 4993 BSD_DegreeNonneg_p4993

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p4933 : (a_p 4933 : ℝ) ^ 2 ≤ 4 * (4933 : ℝ) :=
  BSD_disc_from_deg_832 BSD_DegreeNonneg_p4933
theorem BSD_HasseBound_Disc_p4937 : (a_p 4937 : ℝ) ^ 2 ≤ 4 * (4937 : ℝ) :=
  BSD_disc_from_deg_832 BSD_DegreeNonneg_p4937
theorem BSD_HasseBound_Disc_p4943 : (a_p 4943 : ℝ) ^ 2 ≤ 4 * (4943 : ℝ) :=
  BSD_disc_from_deg_832 BSD_DegreeNonneg_p4943
theorem BSD_HasseBound_Disc_p4951 : (a_p 4951 : ℝ) ^ 2 ≤ 4 * (4951 : ℝ) :=
  BSD_disc_from_deg_832 BSD_DegreeNonneg_p4951
theorem BSD_HasseBound_Disc_p4957 : (a_p 4957 : ℝ) ^ 2 ≤ 4 * (4957 : ℝ) :=
  BSD_disc_from_deg_832 BSD_DegreeNonneg_p4957
theorem BSD_HasseBound_Disc_p4967 : (a_p 4967 : ℝ) ^ 2 ≤ 4 * (4967 : ℝ) :=
  BSD_disc_from_deg_832 BSD_DegreeNonneg_p4967
theorem BSD_HasseBound_Disc_p4969 : (a_p 4969 : ℝ) ^ 2 ≤ 4 * (4969 : ℝ) :=
  BSD_disc_from_deg_832 BSD_DegreeNonneg_p4969
theorem BSD_HasseBound_Disc_p4973 : (a_p 4973 : ℝ) ^ 2 ≤ 4 * (4973 : ℝ) :=
  BSD_disc_from_deg_832 BSD_DegreeNonneg_p4973
theorem BSD_HasseBound_Disc_p4987 : (a_p 4987 : ℝ) ^ 2 ≤ 4 * (4987 : ℝ) :=
  BSD_disc_from_deg_832 BSD_DegreeNonneg_p4987
theorem BSD_HasseBound_Disc_p4993 : (a_p 4993 : ℝ) ^ 2 ≤ 4 * (4993 : ℝ) :=
  BSD_disc_from_deg_832 BSD_DegreeNonneg_p4993

end Towers.BSD
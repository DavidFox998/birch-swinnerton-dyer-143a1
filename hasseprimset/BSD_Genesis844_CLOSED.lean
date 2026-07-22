/-
================================================================
Towers / BSD / BSD_Genesis844_CLOSED  (genesis-844)

HasseBridge Tier C: Hasse bounds for primes
5927..6043 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=5927: card=5877, a_p=+51, disc=-21107
  p=5939: card=5866, a_p=+74, disc=-18280
  p=5953: card=5882, a_p=+72, disc=-18628
  p=5981: card=6122, a_p=-140, disc=-4324
  p=5987: card=6109, a_p=-121, disc=-9307
  p=6007: card=6148, a_p=-140, disc=-4428
  p=6011: card=6117, a_p=-105, disc=-13019
  p=6029: card=6009, a_p=+21, disc=-23675
  p=6037: card=5985, a_p=+53, disc=-21339
  p=6043: card=6027, a_p=+17, disc=-23883

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_844 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i844_p5927 : Fact (5927 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p5939 : Fact (5939 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p5953 : Fact (5953 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p5981 : Fact (5981 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p5987 : Fact (5987 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p6007 : Fact (6007 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p6011 : Fact (6011 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p6029 : Fact (6029 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p6037 : Fact (6037 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p6043 : Fact (6043 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p5927 : (E143_Finset 5927).card = 5877 := by native_decide
theorem BSD_E143_card_p5939 : (E143_Finset 5939).card = 5866 := by native_decide
theorem BSD_E143_card_p5953 : (E143_Finset 5953).card = 5882 := by native_decide
theorem BSD_E143_card_p5981 : (E143_Finset 5981).card = 6122 := by native_decide
theorem BSD_E143_card_p5987 : (E143_Finset 5987).card = 6109 := by native_decide
theorem BSD_E143_card_p6007 : (E143_Finset 6007).card = 6148 := by native_decide
theorem BSD_E143_card_p6011 : (E143_Finset 6011).card = 6117 := by native_decide
theorem BSD_E143_card_p6029 : (E143_Finset 6029).card = 6009 := by native_decide
theorem BSD_E143_card_p6037 : (E143_Finset 6037).card = 5985 := by native_decide
theorem BSD_E143_card_p6043 : (E143_Finset 6043).card = 6027 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p5927 : a_p 5927 = (51 : ℤ) := by
  have h := BSD_E143_card_p5927; unfold a_p; omega
theorem BSD_ap_p5939 : a_p 5939 = (74 : ℤ) := by
  have h := BSD_E143_card_p5939; unfold a_p; omega
theorem BSD_ap_p5953 : a_p 5953 = (72 : ℤ) := by
  have h := BSD_E143_card_p5953; unfold a_p; omega
theorem BSD_ap_p5981 : a_p 5981 = (-140 : ℤ) := by
  have h := BSD_E143_card_p5981; unfold a_p; omega
theorem BSD_ap_p5987 : a_p 5987 = (-121 : ℤ) := by
  have h := BSD_E143_card_p5987; unfold a_p; omega
theorem BSD_ap_p6007 : a_p 6007 = (-140 : ℤ) := by
  have h := BSD_E143_card_p6007; unfold a_p; omega
theorem BSD_ap_p6011 : a_p 6011 = (-105 : ℤ) := by
  have h := BSD_E143_card_p6011; unfold a_p; omega
theorem BSD_ap_p6029 : a_p 6029 = (21 : ℤ) := by
  have h := BSD_E143_card_p6029; unfold a_p; omega
theorem BSD_ap_p6037 : a_p 6037 = (53 : ℤ) := by
  have h := BSD_E143_card_p6037; unfold a_p; omega
theorem BSD_ap_p6043 : a_p 6043 = (17 : ℤ) := by
  have h := BSD_E143_card_p6043; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=5927: a_p=+51, 4p-a_p²=21107
theorem BSD_DegreeNonneg_p5927 : BSD_FrobeniusDegreeNonneg_OPEN 5927 := fun r => by
  have hap : (a_p 5927 : ℝ) = 51 := by exact_mod_cast BSD_ap_p5927
  have key : r ^ 2 - (a_p 5927 : ℝ) * r + ((5927 : ℕ) : ℝ) =
      (r - 51/2) ^ 2 + 21107/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (51 : ℝ)/2)]

-- p=5939: a_p=+74, 4p-a_p²=18280
theorem BSD_DegreeNonneg_p5939 : BSD_FrobeniusDegreeNonneg_OPEN 5939 := fun r => by
  have hap : (a_p 5939 : ℝ) = 74 := by exact_mod_cast BSD_ap_p5939
  have key : r ^ 2 - (a_p 5939 : ℝ) * r + ((5939 : ℕ) : ℝ) =
      (r - 74/2) ^ 2 + 18280/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (74 : ℝ)/2)]

-- p=5953: a_p=+72, 4p-a_p²=18628
theorem BSD_DegreeNonneg_p5953 : BSD_FrobeniusDegreeNonneg_OPEN 5953 := fun r => by
  have hap : (a_p 5953 : ℝ) = 72 := by exact_mod_cast BSD_ap_p5953
  have key : r ^ 2 - (a_p 5953 : ℝ) * r + ((5953 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 18628/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

-- p=5981: a_p=-140, 4p-a_p²=4324
theorem BSD_DegreeNonneg_p5981 : BSD_FrobeniusDegreeNonneg_OPEN 5981 := fun r => by
  have hap : (a_p 5981 : ℝ) = -140 := by exact_mod_cast BSD_ap_p5981
  have key : r ^ 2 - (a_p 5981 : ℝ) * r + ((5981 : ℕ) : ℝ) =
      (r + 140/2) ^ 2 + 4324/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (140 : ℝ)/2)]

-- p=5987: a_p=-121, 4p-a_p²=9307
theorem BSD_DegreeNonneg_p5987 : BSD_FrobeniusDegreeNonneg_OPEN 5987 := fun r => by
  have hap : (a_p 5987 : ℝ) = -121 := by exact_mod_cast BSD_ap_p5987
  have key : r ^ 2 - (a_p 5987 : ℝ) * r + ((5987 : ℕ) : ℝ) =
      (r + 121/2) ^ 2 + 9307/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (121 : ℝ)/2)]

-- p=6007: a_p=-140, 4p-a_p²=4428
theorem BSD_DegreeNonneg_p6007 : BSD_FrobeniusDegreeNonneg_OPEN 6007 := fun r => by
  have hap : (a_p 6007 : ℝ) = -140 := by exact_mod_cast BSD_ap_p6007
  have key : r ^ 2 - (a_p 6007 : ℝ) * r + ((6007 : ℕ) : ℝ) =
      (r + 140/2) ^ 2 + 4428/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (140 : ℝ)/2)]

-- p=6011: a_p=-105, 4p-a_p²=13019
theorem BSD_DegreeNonneg_p6011 : BSD_FrobeniusDegreeNonneg_OPEN 6011 := fun r => by
  have hap : (a_p 6011 : ℝ) = -105 := by exact_mod_cast BSD_ap_p6011
  have key : r ^ 2 - (a_p 6011 : ℝ) * r + ((6011 : ℕ) : ℝ) =
      (r + 105/2) ^ 2 + 13019/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (105 : ℝ)/2)]

-- p=6029: a_p=+21, 4p-a_p²=23675
theorem BSD_DegreeNonneg_p6029 : BSD_FrobeniusDegreeNonneg_OPEN 6029 := fun r => by
  have hap : (a_p 6029 : ℝ) = 21 := by exact_mod_cast BSD_ap_p6029
  have key : r ^ 2 - (a_p 6029 : ℝ) * r + ((6029 : ℕ) : ℝ) =
      (r - 21/2) ^ 2 + 23675/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (21 : ℝ)/2)]

-- p=6037: a_p=+53, 4p-a_p²=21339
theorem BSD_DegreeNonneg_p6037 : BSD_FrobeniusDegreeNonneg_OPEN 6037 := fun r => by
  have hap : (a_p 6037 : ℝ) = 53 := by exact_mod_cast BSD_ap_p6037
  have key : r ^ 2 - (a_p 6037 : ℝ) * r + ((6037 : ℕ) : ℝ) =
      (r - 53/2) ^ 2 + 21339/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (53 : ℝ)/2)]

-- p=6043: a_p=+17, 4p-a_p²=23883
theorem BSD_DegreeNonneg_p6043 : BSD_FrobeniusDegreeNonneg_OPEN 6043 := fun r => by
  have hap : (a_p 6043 : ℝ) = 17 := by exact_mod_cast BSD_ap_p6043
  have key : r ^ 2 - (a_p 6043 : ℝ) * r + ((6043 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 23883/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p5927 : BSD_Hasse_OPEN 5927 :=
  BSD_hasse_of_degree_nonneg 5927 BSD_DegreeNonneg_p5927
theorem BSD_Hasse_OPEN_p5939 : BSD_Hasse_OPEN 5939 :=
  BSD_hasse_of_degree_nonneg 5939 BSD_DegreeNonneg_p5939
theorem BSD_Hasse_OPEN_p5953 : BSD_Hasse_OPEN 5953 :=
  BSD_hasse_of_degree_nonneg 5953 BSD_DegreeNonneg_p5953
theorem BSD_Hasse_OPEN_p5981 : BSD_Hasse_OPEN 5981 :=
  BSD_hasse_of_degree_nonneg 5981 BSD_DegreeNonneg_p5981
theorem BSD_Hasse_OPEN_p5987 : BSD_Hasse_OPEN 5987 :=
  BSD_hasse_of_degree_nonneg 5987 BSD_DegreeNonneg_p5987
theorem BSD_Hasse_OPEN_p6007 : BSD_Hasse_OPEN 6007 :=
  BSD_hasse_of_degree_nonneg 6007 BSD_DegreeNonneg_p6007
theorem BSD_Hasse_OPEN_p6011 : BSD_Hasse_OPEN 6011 :=
  BSD_hasse_of_degree_nonneg 6011 BSD_DegreeNonneg_p6011
theorem BSD_Hasse_OPEN_p6029 : BSD_Hasse_OPEN 6029 :=
  BSD_hasse_of_degree_nonneg 6029 BSD_DegreeNonneg_p6029
theorem BSD_Hasse_OPEN_p6037 : BSD_Hasse_OPEN 6037 :=
  BSD_hasse_of_degree_nonneg 6037 BSD_DegreeNonneg_p6037
theorem BSD_Hasse_OPEN_p6043 : BSD_Hasse_OPEN 6043 :=
  BSD_hasse_of_degree_nonneg 6043 BSD_DegreeNonneg_p6043

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p5927 : (a_p 5927 : ℝ) ^ 2 ≤ 4 * (5927 : ℝ) :=
  BSD_disc_from_deg_844 BSD_DegreeNonneg_p5927
theorem BSD_HasseBound_Disc_p5939 : (a_p 5939 : ℝ) ^ 2 ≤ 4 * (5939 : ℝ) :=
  BSD_disc_from_deg_844 BSD_DegreeNonneg_p5939
theorem BSD_HasseBound_Disc_p5953 : (a_p 5953 : ℝ) ^ 2 ≤ 4 * (5953 : ℝ) :=
  BSD_disc_from_deg_844 BSD_DegreeNonneg_p5953
theorem BSD_HasseBound_Disc_p5981 : (a_p 5981 : ℝ) ^ 2 ≤ 4 * (5981 : ℝ) :=
  BSD_disc_from_deg_844 BSD_DegreeNonneg_p5981
theorem BSD_HasseBound_Disc_p5987 : (a_p 5987 : ℝ) ^ 2 ≤ 4 * (5987 : ℝ) :=
  BSD_disc_from_deg_844 BSD_DegreeNonneg_p5987
theorem BSD_HasseBound_Disc_p6007 : (a_p 6007 : ℝ) ^ 2 ≤ 4 * (6007 : ℝ) :=
  BSD_disc_from_deg_844 BSD_DegreeNonneg_p6007
theorem BSD_HasseBound_Disc_p6011 : (a_p 6011 : ℝ) ^ 2 ≤ 4 * (6011 : ℝ) :=
  BSD_disc_from_deg_844 BSD_DegreeNonneg_p6011
theorem BSD_HasseBound_Disc_p6029 : (a_p 6029 : ℝ) ^ 2 ≤ 4 * (6029 : ℝ) :=
  BSD_disc_from_deg_844 BSD_DegreeNonneg_p6029
theorem BSD_HasseBound_Disc_p6037 : (a_p 6037 : ℝ) ^ 2 ≤ 4 * (6037 : ℝ) :=
  BSD_disc_from_deg_844 BSD_DegreeNonneg_p6037
theorem BSD_HasseBound_Disc_p6043 : (a_p 6043 : ℝ) ^ 2 ≤ 4 * (6043 : ℝ) :=
  BSD_disc_from_deg_844 BSD_DegreeNonneg_p6043

end Towers.BSD
/-
================================================================
Towers / BSD / BSD_Genesis841_CLOSED  (genesis-841)

HasseBridge Tier C: Hasse bounds for primes
5689..5779 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=5689: card=5718, a_p=-28, disc=-21972
  p=5693: card=5766, a_p=-72, disc=-17588
  p=5701: card=5627, a_p=+75, disc=-17179
  p=5711: card=5686, a_p=+26, disc=-22168
  p=5717: card=5794, a_p=-76, disc=-17092
  p=5737: card=5824, a_p=-86, disc=-15552
  p=5741: card=5622, a_p=+120, disc=-8564
  p=5743: card=5689, a_p=+55, disc=-19947
  p=5749: card=5704, a_p=+46, disc=-20880
  p=5779: card=5785, a_p=-5, disc=-23091

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_841 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i841_p5689 : Fact (5689 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5693 : Fact (5693 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5701 : Fact (5701 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5711 : Fact (5711 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5717 : Fact (5717 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5737 : Fact (5737 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5741 : Fact (5741 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5743 : Fact (5743 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5749 : Fact (5749 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5779 : Fact (5779 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p5689 : (E143_Finset 5689).card = 5718 := by native_decide
theorem BSD_E143_card_p5693 : (E143_Finset 5693).card = 5766 := by native_decide
theorem BSD_E143_card_p5701 : (E143_Finset 5701).card = 5627 := by native_decide
theorem BSD_E143_card_p5711 : (E143_Finset 5711).card = 5686 := by native_decide
theorem BSD_E143_card_p5717 : (E143_Finset 5717).card = 5794 := by native_decide
theorem BSD_E143_card_p5737 : (E143_Finset 5737).card = 5824 := by native_decide
theorem BSD_E143_card_p5741 : (E143_Finset 5741).card = 5622 := by native_decide
theorem BSD_E143_card_p5743 : (E143_Finset 5743).card = 5689 := by native_decide
theorem BSD_E143_card_p5749 : (E143_Finset 5749).card = 5704 := by native_decide
theorem BSD_E143_card_p5779 : (E143_Finset 5779).card = 5785 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p5689 : a_p 5689 = (-28 : ℤ) := by
  have h := BSD_E143_card_p5689; unfold a_p; omega
theorem BSD_ap_p5693 : a_p 5693 = (-72 : ℤ) := by
  have h := BSD_E143_card_p5693; unfold a_p; omega
theorem BSD_ap_p5701 : a_p 5701 = (75 : ℤ) := by
  have h := BSD_E143_card_p5701; unfold a_p; omega
theorem BSD_ap_p5711 : a_p 5711 = (26 : ℤ) := by
  have h := BSD_E143_card_p5711; unfold a_p; omega
theorem BSD_ap_p5717 : a_p 5717 = (-76 : ℤ) := by
  have h := BSD_E143_card_p5717; unfold a_p; omega
theorem BSD_ap_p5737 : a_p 5737 = (-86 : ℤ) := by
  have h := BSD_E143_card_p5737; unfold a_p; omega
theorem BSD_ap_p5741 : a_p 5741 = (120 : ℤ) := by
  have h := BSD_E143_card_p5741; unfold a_p; omega
theorem BSD_ap_p5743 : a_p 5743 = (55 : ℤ) := by
  have h := BSD_E143_card_p5743; unfold a_p; omega
theorem BSD_ap_p5749 : a_p 5749 = (46 : ℤ) := by
  have h := BSD_E143_card_p5749; unfold a_p; omega
theorem BSD_ap_p5779 : a_p 5779 = (-5 : ℤ) := by
  have h := BSD_E143_card_p5779; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=5689: a_p=-28, 4p-a_p²=21972
theorem BSD_DegreeNonneg_p5689 : BSD_FrobeniusDegreeNonneg_OPEN 5689 := fun r => by
  have hap : (a_p 5689 : ℝ) = -28 := by exact_mod_cast BSD_ap_p5689
  have key : r ^ 2 - (a_p 5689 : ℝ) * r + ((5689 : ℕ) : ℝ) =
      (r + 28/2) ^ 2 + 21972/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (28 : ℝ)/2)]

-- p=5693: a_p=-72, 4p-a_p²=17588
theorem BSD_DegreeNonneg_p5693 : BSD_FrobeniusDegreeNonneg_OPEN 5693 := fun r => by
  have hap : (a_p 5693 : ℝ) = -72 := by exact_mod_cast BSD_ap_p5693
  have key : r ^ 2 - (a_p 5693 : ℝ) * r + ((5693 : ℕ) : ℝ) =
      (r + 72/2) ^ 2 + 17588/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (72 : ℝ)/2)]

-- p=5701: a_p=+75, 4p-a_p²=17179
theorem BSD_DegreeNonneg_p5701 : BSD_FrobeniusDegreeNonneg_OPEN 5701 := fun r => by
  have hap : (a_p 5701 : ℝ) = 75 := by exact_mod_cast BSD_ap_p5701
  have key : r ^ 2 - (a_p 5701 : ℝ) * r + ((5701 : ℕ) : ℝ) =
      (r - 75/2) ^ 2 + 17179/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (75 : ℝ)/2)]

-- p=5711: a_p=+26, 4p-a_p²=22168
theorem BSD_DegreeNonneg_p5711 : BSD_FrobeniusDegreeNonneg_OPEN 5711 := fun r => by
  have hap : (a_p 5711 : ℝ) = 26 := by exact_mod_cast BSD_ap_p5711
  have key : r ^ 2 - (a_p 5711 : ℝ) * r + ((5711 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 22168/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

-- p=5717: a_p=-76, 4p-a_p²=17092
theorem BSD_DegreeNonneg_p5717 : BSD_FrobeniusDegreeNonneg_OPEN 5717 := fun r => by
  have hap : (a_p 5717 : ℝ) = -76 := by exact_mod_cast BSD_ap_p5717
  have key : r ^ 2 - (a_p 5717 : ℝ) * r + ((5717 : ℕ) : ℝ) =
      (r + 76/2) ^ 2 + 17092/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (76 : ℝ)/2)]

-- p=5737: a_p=-86, 4p-a_p²=15552
theorem BSD_DegreeNonneg_p5737 : BSD_FrobeniusDegreeNonneg_OPEN 5737 := fun r => by
  have hap : (a_p 5737 : ℝ) = -86 := by exact_mod_cast BSD_ap_p5737
  have key : r ^ 2 - (a_p 5737 : ℝ) * r + ((5737 : ℕ) : ℝ) =
      (r + 86/2) ^ 2 + 15552/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (86 : ℝ)/2)]

-- p=5741: a_p=+120, 4p-a_p²=8564
theorem BSD_DegreeNonneg_p5741 : BSD_FrobeniusDegreeNonneg_OPEN 5741 := fun r => by
  have hap : (a_p 5741 : ℝ) = 120 := by exact_mod_cast BSD_ap_p5741
  have key : r ^ 2 - (a_p 5741 : ℝ) * r + ((5741 : ℕ) : ℝ) =
      (r - 120/2) ^ 2 + 8564/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (120 : ℝ)/2)]

-- p=5743: a_p=+55, 4p-a_p²=19947
theorem BSD_DegreeNonneg_p5743 : BSD_FrobeniusDegreeNonneg_OPEN 5743 := fun r => by
  have hap : (a_p 5743 : ℝ) = 55 := by exact_mod_cast BSD_ap_p5743
  have key : r ^ 2 - (a_p 5743 : ℝ) * r + ((5743 : ℕ) : ℝ) =
      (r - 55/2) ^ 2 + 19947/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (55 : ℝ)/2)]

-- p=5749: a_p=+46, 4p-a_p²=20880
theorem BSD_DegreeNonneg_p5749 : BSD_FrobeniusDegreeNonneg_OPEN 5749 := fun r => by
  have hap : (a_p 5749 : ℝ) = 46 := by exact_mod_cast BSD_ap_p5749
  have key : r ^ 2 - (a_p 5749 : ℝ) * r + ((5749 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 20880/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

-- p=5779: a_p=-5, 4p-a_p²=23091
theorem BSD_DegreeNonneg_p5779 : BSD_FrobeniusDegreeNonneg_OPEN 5779 := fun r => by
  have hap : (a_p 5779 : ℝ) = -5 := by exact_mod_cast BSD_ap_p5779
  have key : r ^ 2 - (a_p 5779 : ℝ) * r + ((5779 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 23091/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p5689 : BSD_Hasse_OPEN 5689 :=
  BSD_hasse_of_degree_nonneg 5689 BSD_DegreeNonneg_p5689
theorem BSD_Hasse_OPEN_p5693 : BSD_Hasse_OPEN 5693 :=
  BSD_hasse_of_degree_nonneg 5693 BSD_DegreeNonneg_p5693
theorem BSD_Hasse_OPEN_p5701 : BSD_Hasse_OPEN 5701 :=
  BSD_hasse_of_degree_nonneg 5701 BSD_DegreeNonneg_p5701
theorem BSD_Hasse_OPEN_p5711 : BSD_Hasse_OPEN 5711 :=
  BSD_hasse_of_degree_nonneg 5711 BSD_DegreeNonneg_p5711
theorem BSD_Hasse_OPEN_p5717 : BSD_Hasse_OPEN 5717 :=
  BSD_hasse_of_degree_nonneg 5717 BSD_DegreeNonneg_p5717
theorem BSD_Hasse_OPEN_p5737 : BSD_Hasse_OPEN 5737 :=
  BSD_hasse_of_degree_nonneg 5737 BSD_DegreeNonneg_p5737
theorem BSD_Hasse_OPEN_p5741 : BSD_Hasse_OPEN 5741 :=
  BSD_hasse_of_degree_nonneg 5741 BSD_DegreeNonneg_p5741
theorem BSD_Hasse_OPEN_p5743 : BSD_Hasse_OPEN 5743 :=
  BSD_hasse_of_degree_nonneg 5743 BSD_DegreeNonneg_p5743
theorem BSD_Hasse_OPEN_p5749 : BSD_Hasse_OPEN 5749 :=
  BSD_hasse_of_degree_nonneg 5749 BSD_DegreeNonneg_p5749
theorem BSD_Hasse_OPEN_p5779 : BSD_Hasse_OPEN 5779 :=
  BSD_hasse_of_degree_nonneg 5779 BSD_DegreeNonneg_p5779

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p5689 : (a_p 5689 : ℝ) ^ 2 ≤ 4 * (5689 : ℝ) :=
  BSD_disc_from_deg_841 BSD_DegreeNonneg_p5689
theorem BSD_HasseBound_Disc_p5693 : (a_p 5693 : ℝ) ^ 2 ≤ 4 * (5693 : ℝ) :=
  BSD_disc_from_deg_841 BSD_DegreeNonneg_p5693
theorem BSD_HasseBound_Disc_p5701 : (a_p 5701 : ℝ) ^ 2 ≤ 4 * (5701 : ℝ) :=
  BSD_disc_from_deg_841 BSD_DegreeNonneg_p5701
theorem BSD_HasseBound_Disc_p5711 : (a_p 5711 : ℝ) ^ 2 ≤ 4 * (5711 : ℝ) :=
  BSD_disc_from_deg_841 BSD_DegreeNonneg_p5711
theorem BSD_HasseBound_Disc_p5717 : (a_p 5717 : ℝ) ^ 2 ≤ 4 * (5717 : ℝ) :=
  BSD_disc_from_deg_841 BSD_DegreeNonneg_p5717
theorem BSD_HasseBound_Disc_p5737 : (a_p 5737 : ℝ) ^ 2 ≤ 4 * (5737 : ℝ) :=
  BSD_disc_from_deg_841 BSD_DegreeNonneg_p5737
theorem BSD_HasseBound_Disc_p5741 : (a_p 5741 : ℝ) ^ 2 ≤ 4 * (5741 : ℝ) :=
  BSD_disc_from_deg_841 BSD_DegreeNonneg_p5741
theorem BSD_HasseBound_Disc_p5743 : (a_p 5743 : ℝ) ^ 2 ≤ 4 * (5743 : ℝ) :=
  BSD_disc_from_deg_841 BSD_DegreeNonneg_p5743
theorem BSD_HasseBound_Disc_p5749 : (a_p 5749 : ℝ) ^ 2 ≤ 4 * (5749 : ℝ) :=
  BSD_disc_from_deg_841 BSD_DegreeNonneg_p5749
theorem BSD_HasseBound_Disc_p5779 : (a_p 5779 : ℝ) ^ 2 ≤ 4 * (5779 : ℝ) :=
  BSD_disc_from_deg_841 BSD_DegreeNonneg_p5779

end Towers.BSD
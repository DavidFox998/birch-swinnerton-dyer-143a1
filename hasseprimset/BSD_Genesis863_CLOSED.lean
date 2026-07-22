/-
================================================================
Towers / BSD / BSD_Genesis863_CLOSED  (genesis-863)

HasseBridge Tier C: Hasse bounds for primes
7639..7703 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=7639: card=7737, a_p=-97, disc=-21147
  p=7643: card=7677, a_p=-33, disc=-29483
  p=7649: card=7552, a_p=+98, disc=-20992
  p=7669: card=7586, a_p=+84, disc=-23620
  p=7673: card=7578, a_p=+96, disc=-21476
  p=7681: card=7577, a_p=+105, disc=-19699
  p=7687: card=7693, a_p=-5, disc=-30723
  p=7691: card=7734, a_p=-42, disc=-29000
  p=7699: card=7770, a_p=-70, disc=-25896
  p=7703: card=7773, a_p=-69, disc=-26051

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_863 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i863_p7639 : Fact (7639 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7643 : Fact (7643 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7649 : Fact (7649 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7669 : Fact (7669 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7673 : Fact (7673 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7681 : Fact (7681 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7687 : Fact (7687 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7691 : Fact (7691 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7699 : Fact (7699 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7703 : Fact (7703 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p7639 : (E143_Finset 7639).card = 7737 := by native_decide
theorem BSD_E143_card_p7643 : (E143_Finset 7643).card = 7677 := by native_decide
theorem BSD_E143_card_p7649 : (E143_Finset 7649).card = 7552 := by native_decide
theorem BSD_E143_card_p7669 : (E143_Finset 7669).card = 7586 := by native_decide
theorem BSD_E143_card_p7673 : (E143_Finset 7673).card = 7578 := by native_decide
theorem BSD_E143_card_p7681 : (E143_Finset 7681).card = 7577 := by native_decide
theorem BSD_E143_card_p7687 : (E143_Finset 7687).card = 7693 := by native_decide
theorem BSD_E143_card_p7691 : (E143_Finset 7691).card = 7734 := by native_decide
theorem BSD_E143_card_p7699 : (E143_Finset 7699).card = 7770 := by native_decide
theorem BSD_E143_card_p7703 : (E143_Finset 7703).card = 7773 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p7639 : a_p 7639 = (-97 : ℤ) := by
  have h := BSD_E143_card_p7639; unfold a_p; omega
theorem BSD_ap_p7643 : a_p 7643 = (-33 : ℤ) := by
  have h := BSD_E143_card_p7643; unfold a_p; omega
theorem BSD_ap_p7649 : a_p 7649 = (98 : ℤ) := by
  have h := BSD_E143_card_p7649; unfold a_p; omega
theorem BSD_ap_p7669 : a_p 7669 = (84 : ℤ) := by
  have h := BSD_E143_card_p7669; unfold a_p; omega
theorem BSD_ap_p7673 : a_p 7673 = (96 : ℤ) := by
  have h := BSD_E143_card_p7673; unfold a_p; omega
theorem BSD_ap_p7681 : a_p 7681 = (105 : ℤ) := by
  have h := BSD_E143_card_p7681; unfold a_p; omega
theorem BSD_ap_p7687 : a_p 7687 = (-5 : ℤ) := by
  have h := BSD_E143_card_p7687; unfold a_p; omega
theorem BSD_ap_p7691 : a_p 7691 = (-42 : ℤ) := by
  have h := BSD_E143_card_p7691; unfold a_p; omega
theorem BSD_ap_p7699 : a_p 7699 = (-70 : ℤ) := by
  have h := BSD_E143_card_p7699; unfold a_p; omega
theorem BSD_ap_p7703 : a_p 7703 = (-69 : ℤ) := by
  have h := BSD_E143_card_p7703; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=7639: a_p=-97, 4p-a_p²=21147
theorem BSD_DegreeNonneg_p7639 : BSD_FrobeniusDegreeNonneg_OPEN 7639 := fun r => by
  have hap : (a_p 7639 : ℝ) = -97 := by exact_mod_cast BSD_ap_p7639
  have key : r ^ 2 - (a_p 7639 : ℝ) * r + ((7639 : ℕ) : ℝ) =
      (r + 97/2) ^ 2 + 21147/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (97 : ℝ)/2)]

-- p=7643: a_p=-33, 4p-a_p²=29483
theorem BSD_DegreeNonneg_p7643 : BSD_FrobeniusDegreeNonneg_OPEN 7643 := fun r => by
  have hap : (a_p 7643 : ℝ) = -33 := by exact_mod_cast BSD_ap_p7643
  have key : r ^ 2 - (a_p 7643 : ℝ) * r + ((7643 : ℕ) : ℝ) =
      (r + 33/2) ^ 2 + 29483/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (33 : ℝ)/2)]

-- p=7649: a_p=+98, 4p-a_p²=20992
theorem BSD_DegreeNonneg_p7649 : BSD_FrobeniusDegreeNonneg_OPEN 7649 := fun r => by
  have hap : (a_p 7649 : ℝ) = 98 := by exact_mod_cast BSD_ap_p7649
  have key : r ^ 2 - (a_p 7649 : ℝ) * r + ((7649 : ℕ) : ℝ) =
      (r - 98/2) ^ 2 + 20992/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (98 : ℝ)/2)]

-- p=7669: a_p=+84, 4p-a_p²=23620
theorem BSD_DegreeNonneg_p7669 : BSD_FrobeniusDegreeNonneg_OPEN 7669 := fun r => by
  have hap : (a_p 7669 : ℝ) = 84 := by exact_mod_cast BSD_ap_p7669
  have key : r ^ 2 - (a_p 7669 : ℝ) * r + ((7669 : ℕ) : ℝ) =
      (r - 84/2) ^ 2 + 23620/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (84 : ℝ)/2)]

-- p=7673: a_p=+96, 4p-a_p²=21476
theorem BSD_DegreeNonneg_p7673 : BSD_FrobeniusDegreeNonneg_OPEN 7673 := fun r => by
  have hap : (a_p 7673 : ℝ) = 96 := by exact_mod_cast BSD_ap_p7673
  have key : r ^ 2 - (a_p 7673 : ℝ) * r + ((7673 : ℕ) : ℝ) =
      (r - 96/2) ^ 2 + 21476/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (96 : ℝ)/2)]

-- p=7681: a_p=+105, 4p-a_p²=19699
theorem BSD_DegreeNonneg_p7681 : BSD_FrobeniusDegreeNonneg_OPEN 7681 := fun r => by
  have hap : (a_p 7681 : ℝ) = 105 := by exact_mod_cast BSD_ap_p7681
  have key : r ^ 2 - (a_p 7681 : ℝ) * r + ((7681 : ℕ) : ℝ) =
      (r - 105/2) ^ 2 + 19699/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (105 : ℝ)/2)]

-- p=7687: a_p=-5, 4p-a_p²=30723
theorem BSD_DegreeNonneg_p7687 : BSD_FrobeniusDegreeNonneg_OPEN 7687 := fun r => by
  have hap : (a_p 7687 : ℝ) = -5 := by exact_mod_cast BSD_ap_p7687
  have key : r ^ 2 - (a_p 7687 : ℝ) * r + ((7687 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 30723/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

-- p=7691: a_p=-42, 4p-a_p²=29000
theorem BSD_DegreeNonneg_p7691 : BSD_FrobeniusDegreeNonneg_OPEN 7691 := fun r => by
  have hap : (a_p 7691 : ℝ) = -42 := by exact_mod_cast BSD_ap_p7691
  have key : r ^ 2 - (a_p 7691 : ℝ) * r + ((7691 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 29000/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

-- p=7699: a_p=-70, 4p-a_p²=25896
theorem BSD_DegreeNonneg_p7699 : BSD_FrobeniusDegreeNonneg_OPEN 7699 := fun r => by
  have hap : (a_p 7699 : ℝ) = -70 := by exact_mod_cast BSD_ap_p7699
  have key : r ^ 2 - (a_p 7699 : ℝ) * r + ((7699 : ℕ) : ℝ) =
      (r + 70/2) ^ 2 + 25896/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (70 : ℝ)/2)]

-- p=7703: a_p=-69, 4p-a_p²=26051
theorem BSD_DegreeNonneg_p7703 : BSD_FrobeniusDegreeNonneg_OPEN 7703 := fun r => by
  have hap : (a_p 7703 : ℝ) = -69 := by exact_mod_cast BSD_ap_p7703
  have key : r ^ 2 - (a_p 7703 : ℝ) * r + ((7703 : ℕ) : ℝ) =
      (r + 69/2) ^ 2 + 26051/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (69 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p7639 : BSD_Hasse_OPEN 7639 :=
  BSD_hasse_of_degree_nonneg 7639 BSD_DegreeNonneg_p7639
theorem BSD_Hasse_OPEN_p7643 : BSD_Hasse_OPEN 7643 :=
  BSD_hasse_of_degree_nonneg 7643 BSD_DegreeNonneg_p7643
theorem BSD_Hasse_OPEN_p7649 : BSD_Hasse_OPEN 7649 :=
  BSD_hasse_of_degree_nonneg 7649 BSD_DegreeNonneg_p7649
theorem BSD_Hasse_OPEN_p7669 : BSD_Hasse_OPEN 7669 :=
  BSD_hasse_of_degree_nonneg 7669 BSD_DegreeNonneg_p7669
theorem BSD_Hasse_OPEN_p7673 : BSD_Hasse_OPEN 7673 :=
  BSD_hasse_of_degree_nonneg 7673 BSD_DegreeNonneg_p7673
theorem BSD_Hasse_OPEN_p7681 : BSD_Hasse_OPEN 7681 :=
  BSD_hasse_of_degree_nonneg 7681 BSD_DegreeNonneg_p7681
theorem BSD_Hasse_OPEN_p7687 : BSD_Hasse_OPEN 7687 :=
  BSD_hasse_of_degree_nonneg 7687 BSD_DegreeNonneg_p7687
theorem BSD_Hasse_OPEN_p7691 : BSD_Hasse_OPEN 7691 :=
  BSD_hasse_of_degree_nonneg 7691 BSD_DegreeNonneg_p7691
theorem BSD_Hasse_OPEN_p7699 : BSD_Hasse_OPEN 7699 :=
  BSD_hasse_of_degree_nonneg 7699 BSD_DegreeNonneg_p7699
theorem BSD_Hasse_OPEN_p7703 : BSD_Hasse_OPEN 7703 :=
  BSD_hasse_of_degree_nonneg 7703 BSD_DegreeNonneg_p7703

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p7639 : (a_p 7639 : ℝ) ^ 2 ≤ 4 * (7639 : ℝ) :=
  BSD_disc_from_deg_863 BSD_DegreeNonneg_p7639
theorem BSD_HasseBound_Disc_p7643 : (a_p 7643 : ℝ) ^ 2 ≤ 4 * (7643 : ℝ) :=
  BSD_disc_from_deg_863 BSD_DegreeNonneg_p7643
theorem BSD_HasseBound_Disc_p7649 : (a_p 7649 : ℝ) ^ 2 ≤ 4 * (7649 : ℝ) :=
  BSD_disc_from_deg_863 BSD_DegreeNonneg_p7649
theorem BSD_HasseBound_Disc_p7669 : (a_p 7669 : ℝ) ^ 2 ≤ 4 * (7669 : ℝ) :=
  BSD_disc_from_deg_863 BSD_DegreeNonneg_p7669
theorem BSD_HasseBound_Disc_p7673 : (a_p 7673 : ℝ) ^ 2 ≤ 4 * (7673 : ℝ) :=
  BSD_disc_from_deg_863 BSD_DegreeNonneg_p7673
theorem BSD_HasseBound_Disc_p7681 : (a_p 7681 : ℝ) ^ 2 ≤ 4 * (7681 : ℝ) :=
  BSD_disc_from_deg_863 BSD_DegreeNonneg_p7681
theorem BSD_HasseBound_Disc_p7687 : (a_p 7687 : ℝ) ^ 2 ≤ 4 * (7687 : ℝ) :=
  BSD_disc_from_deg_863 BSD_DegreeNonneg_p7687
theorem BSD_HasseBound_Disc_p7691 : (a_p 7691 : ℝ) ^ 2 ≤ 4 * (7691 : ℝ) :=
  BSD_disc_from_deg_863 BSD_DegreeNonneg_p7691
theorem BSD_HasseBound_Disc_p7699 : (a_p 7699 : ℝ) ^ 2 ≤ 4 * (7699 : ℝ) :=
  BSD_disc_from_deg_863 BSD_DegreeNonneg_p7699
theorem BSD_HasseBound_Disc_p7703 : (a_p 7703 : ℝ) ^ 2 ≤ 4 * (7703 : ℝ) :=
  BSD_disc_from_deg_863 BSD_DegreeNonneg_p7703

end Towers.BSD
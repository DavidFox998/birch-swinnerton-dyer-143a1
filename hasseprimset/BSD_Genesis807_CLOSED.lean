/-
================================================================
Towers / BSD / BSD_Genesis807_CLOSED  (genesis-807)

HasseBridge Tier C: Hasse bounds for primes
2803..2887 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2803: card=2776, a_p=+28, disc=-10428
  p=2819: card=2835, a_p=-15, disc=-11051
  p=2833: card=2808, a_p=+26, disc=-10656
  p=2837: card=2882, a_p=-44, disc=-9412
  p=2843: card=2784, a_p=+60, disc=-7772
  p=2851: card=2864, a_p=-12, disc=-11260
  p=2857: card=2804, a_p=+54, disc=-8512
  p=2861: card=2901, a_p=-39, disc=-9923
  p=2879: card=2912, a_p=-32, disc=-10492
  p=2887: card=2945, a_p=-57, disc=-8299

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_807 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i807_p2803 : Fact (2803 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2819 : Fact (2819 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2833 : Fact (2833 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2837 : Fact (2837 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2843 : Fact (2843 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2851 : Fact (2851 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2857 : Fact (2857 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2861 : Fact (2861 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2879 : Fact (2879 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2887 : Fact (2887 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2803 : (E143_Finset 2803).card = 2776 := by native_decide
theorem BSD_E143_card_p2819 : (E143_Finset 2819).card = 2835 := by native_decide
theorem BSD_E143_card_p2833 : (E143_Finset 2833).card = 2808 := by native_decide
theorem BSD_E143_card_p2837 : (E143_Finset 2837).card = 2882 := by native_decide
theorem BSD_E143_card_p2843 : (E143_Finset 2843).card = 2784 := by native_decide
theorem BSD_E143_card_p2851 : (E143_Finset 2851).card = 2864 := by native_decide
theorem BSD_E143_card_p2857 : (E143_Finset 2857).card = 2804 := by native_decide
theorem BSD_E143_card_p2861 : (E143_Finset 2861).card = 2901 := by native_decide
theorem BSD_E143_card_p2879 : (E143_Finset 2879).card = 2912 := by native_decide
theorem BSD_E143_card_p2887 : (E143_Finset 2887).card = 2945 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2803 : a_p 2803 = (28 : ℤ) := by
  have h := BSD_E143_card_p2803; unfold a_p; omega
theorem BSD_ap_p2819 : a_p 2819 = (-15 : ℤ) := by
  have h := BSD_E143_card_p2819; unfold a_p; omega
theorem BSD_ap_p2833 : a_p 2833 = (26 : ℤ) := by
  have h := BSD_E143_card_p2833; unfold a_p; omega
theorem BSD_ap_p2837 : a_p 2837 = (-44 : ℤ) := by
  have h := BSD_E143_card_p2837; unfold a_p; omega
theorem BSD_ap_p2843 : a_p 2843 = (60 : ℤ) := by
  have h := BSD_E143_card_p2843; unfold a_p; omega
theorem BSD_ap_p2851 : a_p 2851 = (-12 : ℤ) := by
  have h := BSD_E143_card_p2851; unfold a_p; omega
theorem BSD_ap_p2857 : a_p 2857 = (54 : ℤ) := by
  have h := BSD_E143_card_p2857; unfold a_p; omega
theorem BSD_ap_p2861 : a_p 2861 = (-39 : ℤ) := by
  have h := BSD_E143_card_p2861; unfold a_p; omega
theorem BSD_ap_p2879 : a_p 2879 = (-32 : ℤ) := by
  have h := BSD_E143_card_p2879; unfold a_p; omega
theorem BSD_ap_p2887 : a_p 2887 = (-57 : ℤ) := by
  have h := BSD_E143_card_p2887; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2803: a_p=+28, 4p-a_p²=10428
theorem BSD_DegreeNonneg_p2803 : BSD_FrobeniusDegreeNonneg_OPEN 2803 := fun r => by
  have hap : (a_p 2803 : ℝ) = 28 := by exact_mod_cast BSD_ap_p2803
  have key : r ^ 2 - (a_p 2803 : ℝ) * r + ((2803 : ℕ) : ℝ) =
      (r - 28/2) ^ 2 + 10428/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (28 : ℝ)/2)]

-- p=2819: a_p=-15, 4p-a_p²=11051
theorem BSD_DegreeNonneg_p2819 : BSD_FrobeniusDegreeNonneg_OPEN 2819 := fun r => by
  have hap : (a_p 2819 : ℝ) = -15 := by exact_mod_cast BSD_ap_p2819
  have key : r ^ 2 - (a_p 2819 : ℝ) * r + ((2819 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 11051/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

-- p=2833: a_p=+26, 4p-a_p²=10656
theorem BSD_DegreeNonneg_p2833 : BSD_FrobeniusDegreeNonneg_OPEN 2833 := fun r => by
  have hap : (a_p 2833 : ℝ) = 26 := by exact_mod_cast BSD_ap_p2833
  have key : r ^ 2 - (a_p 2833 : ℝ) * r + ((2833 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 10656/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

-- p=2837: a_p=-44, 4p-a_p²=9412
theorem BSD_DegreeNonneg_p2837 : BSD_FrobeniusDegreeNonneg_OPEN 2837 := fun r => by
  have hap : (a_p 2837 : ℝ) = -44 := by exact_mod_cast BSD_ap_p2837
  have key : r ^ 2 - (a_p 2837 : ℝ) * r + ((2837 : ℕ) : ℝ) =
      (r + 44/2) ^ 2 + 9412/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (44 : ℝ)/2)]

-- p=2843: a_p=+60, 4p-a_p²=7772
theorem BSD_DegreeNonneg_p2843 : BSD_FrobeniusDegreeNonneg_OPEN 2843 := fun r => by
  have hap : (a_p 2843 : ℝ) = 60 := by exact_mod_cast BSD_ap_p2843
  have key : r ^ 2 - (a_p 2843 : ℝ) * r + ((2843 : ℕ) : ℝ) =
      (r - 60/2) ^ 2 + 7772/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (60 : ℝ)/2)]

-- p=2851: a_p=-12, 4p-a_p²=11260
theorem BSD_DegreeNonneg_p2851 : BSD_FrobeniusDegreeNonneg_OPEN 2851 := fun r => by
  have hap : (a_p 2851 : ℝ) = -12 := by exact_mod_cast BSD_ap_p2851
  have key : r ^ 2 - (a_p 2851 : ℝ) * r + ((2851 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 11260/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

-- p=2857: a_p=+54, 4p-a_p²=8512
theorem BSD_DegreeNonneg_p2857 : BSD_FrobeniusDegreeNonneg_OPEN 2857 := fun r => by
  have hap : (a_p 2857 : ℝ) = 54 := by exact_mod_cast BSD_ap_p2857
  have key : r ^ 2 - (a_p 2857 : ℝ) * r + ((2857 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 8512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

-- p=2861: a_p=-39, 4p-a_p²=9923
theorem BSD_DegreeNonneg_p2861 : BSD_FrobeniusDegreeNonneg_OPEN 2861 := fun r => by
  have hap : (a_p 2861 : ℝ) = -39 := by exact_mod_cast BSD_ap_p2861
  have key : r ^ 2 - (a_p 2861 : ℝ) * r + ((2861 : ℕ) : ℝ) =
      (r + 39/2) ^ 2 + 9923/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (39 : ℝ)/2)]

-- p=2879: a_p=-32, 4p-a_p²=10492
theorem BSD_DegreeNonneg_p2879 : BSD_FrobeniusDegreeNonneg_OPEN 2879 := fun r => by
  have hap : (a_p 2879 : ℝ) = -32 := by exact_mod_cast BSD_ap_p2879
  have key : r ^ 2 - (a_p 2879 : ℝ) * r + ((2879 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 10492/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

-- p=2887: a_p=-57, 4p-a_p²=8299
theorem BSD_DegreeNonneg_p2887 : BSD_FrobeniusDegreeNonneg_OPEN 2887 := fun r => by
  have hap : (a_p 2887 : ℝ) = -57 := by exact_mod_cast BSD_ap_p2887
  have key : r ^ 2 - (a_p 2887 : ℝ) * r + ((2887 : ℕ) : ℝ) =
      (r + 57/2) ^ 2 + 8299/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (57 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2803 : BSD_Hasse_OPEN 2803 :=
  BSD_hasse_of_degree_nonneg 2803 BSD_DegreeNonneg_p2803
theorem BSD_Hasse_OPEN_p2819 : BSD_Hasse_OPEN 2819 :=
  BSD_hasse_of_degree_nonneg 2819 BSD_DegreeNonneg_p2819
theorem BSD_Hasse_OPEN_p2833 : BSD_Hasse_OPEN 2833 :=
  BSD_hasse_of_degree_nonneg 2833 BSD_DegreeNonneg_p2833
theorem BSD_Hasse_OPEN_p2837 : BSD_Hasse_OPEN 2837 :=
  BSD_hasse_of_degree_nonneg 2837 BSD_DegreeNonneg_p2837
theorem BSD_Hasse_OPEN_p2843 : BSD_Hasse_OPEN 2843 :=
  BSD_hasse_of_degree_nonneg 2843 BSD_DegreeNonneg_p2843
theorem BSD_Hasse_OPEN_p2851 : BSD_Hasse_OPEN 2851 :=
  BSD_hasse_of_degree_nonneg 2851 BSD_DegreeNonneg_p2851
theorem BSD_Hasse_OPEN_p2857 : BSD_Hasse_OPEN 2857 :=
  BSD_hasse_of_degree_nonneg 2857 BSD_DegreeNonneg_p2857
theorem BSD_Hasse_OPEN_p2861 : BSD_Hasse_OPEN 2861 :=
  BSD_hasse_of_degree_nonneg 2861 BSD_DegreeNonneg_p2861
theorem BSD_Hasse_OPEN_p2879 : BSD_Hasse_OPEN 2879 :=
  BSD_hasse_of_degree_nonneg 2879 BSD_DegreeNonneg_p2879
theorem BSD_Hasse_OPEN_p2887 : BSD_Hasse_OPEN 2887 :=
  BSD_hasse_of_degree_nonneg 2887 BSD_DegreeNonneg_p2887

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2803 : (a_p 2803 : ℝ) ^ 2 ≤ 4 * (2803 : ℝ) :=
  BSD_disc_from_deg_807 BSD_DegreeNonneg_p2803
theorem BSD_HasseBound_Disc_p2819 : (a_p 2819 : ℝ) ^ 2 ≤ 4 * (2819 : ℝ) :=
  BSD_disc_from_deg_807 BSD_DegreeNonneg_p2819
theorem BSD_HasseBound_Disc_p2833 : (a_p 2833 : ℝ) ^ 2 ≤ 4 * (2833 : ℝ) :=
  BSD_disc_from_deg_807 BSD_DegreeNonneg_p2833
theorem BSD_HasseBound_Disc_p2837 : (a_p 2837 : ℝ) ^ 2 ≤ 4 * (2837 : ℝ) :=
  BSD_disc_from_deg_807 BSD_DegreeNonneg_p2837
theorem BSD_HasseBound_Disc_p2843 : (a_p 2843 : ℝ) ^ 2 ≤ 4 * (2843 : ℝ) :=
  BSD_disc_from_deg_807 BSD_DegreeNonneg_p2843
theorem BSD_HasseBound_Disc_p2851 : (a_p 2851 : ℝ) ^ 2 ≤ 4 * (2851 : ℝ) :=
  BSD_disc_from_deg_807 BSD_DegreeNonneg_p2851
theorem BSD_HasseBound_Disc_p2857 : (a_p 2857 : ℝ) ^ 2 ≤ 4 * (2857 : ℝ) :=
  BSD_disc_from_deg_807 BSD_DegreeNonneg_p2857
theorem BSD_HasseBound_Disc_p2861 : (a_p 2861 : ℝ) ^ 2 ≤ 4 * (2861 : ℝ) :=
  BSD_disc_from_deg_807 BSD_DegreeNonneg_p2861
theorem BSD_HasseBound_Disc_p2879 : (a_p 2879 : ℝ) ^ 2 ≤ 4 * (2879 : ℝ) :=
  BSD_disc_from_deg_807 BSD_DegreeNonneg_p2879
theorem BSD_HasseBound_Disc_p2887 : (a_p 2887 : ℝ) ^ 2 ≤ 4 * (2887 : ℝ) :=
  BSD_disc_from_deg_807 BSD_DegreeNonneg_p2887

end Towers.BSD
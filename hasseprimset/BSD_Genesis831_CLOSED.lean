/-
================================================================
Towers / BSD / BSD_Genesis831_CLOSED  (genesis-831)

HasseBridge Tier C: Hasse bounds for primes
4817..4931 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=4817: card=4790, a_p=+28, disc=-18484
  p=4831: card=4786, a_p=+46, disc=-17208
  p=4861: card=4872, a_p=-10, disc=-19344
  p=4871: card=4904, a_p=-32, disc=-18460
  p=4877: card=4871, a_p=+7, disc=-19459
  p=4889: card=4945, a_p=-55, disc=-16531
  p=4903: card=4866, a_p=+38, disc=-18168
  p=4909: card=4909, a_p=+1, disc=-19635
  p=4919: card=4826, a_p=+94, disc=-10840
  p=4931: card=4884, a_p=+48, disc=-17420

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_831 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i831_p4817 : Fact (4817 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4831 : Fact (4831 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4861 : Fact (4861 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4871 : Fact (4871 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4877 : Fact (4877 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4889 : Fact (4889 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4903 : Fact (4903 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4909 : Fact (4909 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4919 : Fact (4919 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4931 : Fact (4931 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p4817 : (E143_Finset 4817).card = 4790 := by native_decide
theorem BSD_E143_card_p4831 : (E143_Finset 4831).card = 4786 := by native_decide
theorem BSD_E143_card_p4861 : (E143_Finset 4861).card = 4872 := by native_decide
theorem BSD_E143_card_p4871 : (E143_Finset 4871).card = 4904 := by native_decide
theorem BSD_E143_card_p4877 : (E143_Finset 4877).card = 4871 := by native_decide
theorem BSD_E143_card_p4889 : (E143_Finset 4889).card = 4945 := by native_decide
theorem BSD_E143_card_p4903 : (E143_Finset 4903).card = 4866 := by native_decide
theorem BSD_E143_card_p4909 : (E143_Finset 4909).card = 4909 := by native_decide
theorem BSD_E143_card_p4919 : (E143_Finset 4919).card = 4826 := by native_decide
theorem BSD_E143_card_p4931 : (E143_Finset 4931).card = 4884 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p4817 : a_p 4817 = (28 : ℤ) := by
  have h := BSD_E143_card_p4817; unfold a_p; omega
theorem BSD_ap_p4831 : a_p 4831 = (46 : ℤ) := by
  have h := BSD_E143_card_p4831; unfold a_p; omega
theorem BSD_ap_p4861 : a_p 4861 = (-10 : ℤ) := by
  have h := BSD_E143_card_p4861; unfold a_p; omega
theorem BSD_ap_p4871 : a_p 4871 = (-32 : ℤ) := by
  have h := BSD_E143_card_p4871; unfold a_p; omega
theorem BSD_ap_p4877 : a_p 4877 = (7 : ℤ) := by
  have h := BSD_E143_card_p4877; unfold a_p; omega
theorem BSD_ap_p4889 : a_p 4889 = (-55 : ℤ) := by
  have h := BSD_E143_card_p4889; unfold a_p; omega
theorem BSD_ap_p4903 : a_p 4903 = (38 : ℤ) := by
  have h := BSD_E143_card_p4903; unfold a_p; omega
theorem BSD_ap_p4909 : a_p 4909 = (1 : ℤ) := by
  have h := BSD_E143_card_p4909; unfold a_p; omega
theorem BSD_ap_p4919 : a_p 4919 = (94 : ℤ) := by
  have h := BSD_E143_card_p4919; unfold a_p; omega
theorem BSD_ap_p4931 : a_p 4931 = (48 : ℤ) := by
  have h := BSD_E143_card_p4931; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=4817: a_p=+28, 4p-a_p²=18484
theorem BSD_DegreeNonneg_p4817 : BSD_FrobeniusDegreeNonneg_OPEN 4817 := fun r => by
  have hap : (a_p 4817 : ℝ) = 28 := by exact_mod_cast BSD_ap_p4817
  have key : r ^ 2 - (a_p 4817 : ℝ) * r + ((4817 : ℕ) : ℝ) =
      (r - 28/2) ^ 2 + 18484/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (28 : ℝ)/2)]

-- p=4831: a_p=+46, 4p-a_p²=17208
theorem BSD_DegreeNonneg_p4831 : BSD_FrobeniusDegreeNonneg_OPEN 4831 := fun r => by
  have hap : (a_p 4831 : ℝ) = 46 := by exact_mod_cast BSD_ap_p4831
  have key : r ^ 2 - (a_p 4831 : ℝ) * r + ((4831 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 17208/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

-- p=4861: a_p=-10, 4p-a_p²=19344
theorem BSD_DegreeNonneg_p4861 : BSD_FrobeniusDegreeNonneg_OPEN 4861 := fun r => by
  have hap : (a_p 4861 : ℝ) = -10 := by exact_mod_cast BSD_ap_p4861
  have key : r ^ 2 - (a_p 4861 : ℝ) * r + ((4861 : ℕ) : ℝ) =
      (r + 10/2) ^ 2 + 19344/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (10 : ℝ)/2)]

-- p=4871: a_p=-32, 4p-a_p²=18460
theorem BSD_DegreeNonneg_p4871 : BSD_FrobeniusDegreeNonneg_OPEN 4871 := fun r => by
  have hap : (a_p 4871 : ℝ) = -32 := by exact_mod_cast BSD_ap_p4871
  have key : r ^ 2 - (a_p 4871 : ℝ) * r + ((4871 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 18460/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

-- p=4877: a_p=+7, 4p-a_p²=19459
theorem BSD_DegreeNonneg_p4877 : BSD_FrobeniusDegreeNonneg_OPEN 4877 := fun r => by
  have hap : (a_p 4877 : ℝ) = 7 := by exact_mod_cast BSD_ap_p4877
  have key : r ^ 2 - (a_p 4877 : ℝ) * r + ((4877 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 19459/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

-- p=4889: a_p=-55, 4p-a_p²=16531
theorem BSD_DegreeNonneg_p4889 : BSD_FrobeniusDegreeNonneg_OPEN 4889 := fun r => by
  have hap : (a_p 4889 : ℝ) = -55 := by exact_mod_cast BSD_ap_p4889
  have key : r ^ 2 - (a_p 4889 : ℝ) * r + ((4889 : ℕ) : ℝ) =
      (r + 55/2) ^ 2 + 16531/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (55 : ℝ)/2)]

-- p=4903: a_p=+38, 4p-a_p²=18168
theorem BSD_DegreeNonneg_p4903 : BSD_FrobeniusDegreeNonneg_OPEN 4903 := fun r => by
  have hap : (a_p 4903 : ℝ) = 38 := by exact_mod_cast BSD_ap_p4903
  have key : r ^ 2 - (a_p 4903 : ℝ) * r + ((4903 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 18168/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

-- p=4909: a_p=+1, 4p-a_p²=19635
theorem BSD_DegreeNonneg_p4909 : BSD_FrobeniusDegreeNonneg_OPEN 4909 := fun r => by
  have hap : (a_p 4909 : ℝ) = 1 := by exact_mod_cast BSD_ap_p4909
  have key : r ^ 2 - (a_p 4909 : ℝ) * r + ((4909 : ℕ) : ℝ) =
      (r - 1/2) ^ 2 + 19635/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (1 : ℝ)/2)]

-- p=4919: a_p=+94, 4p-a_p²=10840
theorem BSD_DegreeNonneg_p4919 : BSD_FrobeniusDegreeNonneg_OPEN 4919 := fun r => by
  have hap : (a_p 4919 : ℝ) = 94 := by exact_mod_cast BSD_ap_p4919
  have key : r ^ 2 - (a_p 4919 : ℝ) * r + ((4919 : ℕ) : ℝ) =
      (r - 94/2) ^ 2 + 10840/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (94 : ℝ)/2)]

-- p=4931: a_p=+48, 4p-a_p²=17420
theorem BSD_DegreeNonneg_p4931 : BSD_FrobeniusDegreeNonneg_OPEN 4931 := fun r => by
  have hap : (a_p 4931 : ℝ) = 48 := by exact_mod_cast BSD_ap_p4931
  have key : r ^ 2 - (a_p 4931 : ℝ) * r + ((4931 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 17420/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p4817 : BSD_Hasse_OPEN 4817 :=
  BSD_hasse_of_degree_nonneg 4817 BSD_DegreeNonneg_p4817
theorem BSD_Hasse_OPEN_p4831 : BSD_Hasse_OPEN 4831 :=
  BSD_hasse_of_degree_nonneg 4831 BSD_DegreeNonneg_p4831
theorem BSD_Hasse_OPEN_p4861 : BSD_Hasse_OPEN 4861 :=
  BSD_hasse_of_degree_nonneg 4861 BSD_DegreeNonneg_p4861
theorem BSD_Hasse_OPEN_p4871 : BSD_Hasse_OPEN 4871 :=
  BSD_hasse_of_degree_nonneg 4871 BSD_DegreeNonneg_p4871
theorem BSD_Hasse_OPEN_p4877 : BSD_Hasse_OPEN 4877 :=
  BSD_hasse_of_degree_nonneg 4877 BSD_DegreeNonneg_p4877
theorem BSD_Hasse_OPEN_p4889 : BSD_Hasse_OPEN 4889 :=
  BSD_hasse_of_degree_nonneg 4889 BSD_DegreeNonneg_p4889
theorem BSD_Hasse_OPEN_p4903 : BSD_Hasse_OPEN 4903 :=
  BSD_hasse_of_degree_nonneg 4903 BSD_DegreeNonneg_p4903
theorem BSD_Hasse_OPEN_p4909 : BSD_Hasse_OPEN 4909 :=
  BSD_hasse_of_degree_nonneg 4909 BSD_DegreeNonneg_p4909
theorem BSD_Hasse_OPEN_p4919 : BSD_Hasse_OPEN 4919 :=
  BSD_hasse_of_degree_nonneg 4919 BSD_DegreeNonneg_p4919
theorem BSD_Hasse_OPEN_p4931 : BSD_Hasse_OPEN 4931 :=
  BSD_hasse_of_degree_nonneg 4931 BSD_DegreeNonneg_p4931

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p4817 : (a_p 4817 : ℝ) ^ 2 ≤ 4 * (4817 : ℝ) :=
  BSD_disc_from_deg_831 BSD_DegreeNonneg_p4817
theorem BSD_HasseBound_Disc_p4831 : (a_p 4831 : ℝ) ^ 2 ≤ 4 * (4831 : ℝ) :=
  BSD_disc_from_deg_831 BSD_DegreeNonneg_p4831
theorem BSD_HasseBound_Disc_p4861 : (a_p 4861 : ℝ) ^ 2 ≤ 4 * (4861 : ℝ) :=
  BSD_disc_from_deg_831 BSD_DegreeNonneg_p4861
theorem BSD_HasseBound_Disc_p4871 : (a_p 4871 : ℝ) ^ 2 ≤ 4 * (4871 : ℝ) :=
  BSD_disc_from_deg_831 BSD_DegreeNonneg_p4871
theorem BSD_HasseBound_Disc_p4877 : (a_p 4877 : ℝ) ^ 2 ≤ 4 * (4877 : ℝ) :=
  BSD_disc_from_deg_831 BSD_DegreeNonneg_p4877
theorem BSD_HasseBound_Disc_p4889 : (a_p 4889 : ℝ) ^ 2 ≤ 4 * (4889 : ℝ) :=
  BSD_disc_from_deg_831 BSD_DegreeNonneg_p4889
theorem BSD_HasseBound_Disc_p4903 : (a_p 4903 : ℝ) ^ 2 ≤ 4 * (4903 : ℝ) :=
  BSD_disc_from_deg_831 BSD_DegreeNonneg_p4903
theorem BSD_HasseBound_Disc_p4909 : (a_p 4909 : ℝ) ^ 2 ≤ 4 * (4909 : ℝ) :=
  BSD_disc_from_deg_831 BSD_DegreeNonneg_p4909
theorem BSD_HasseBound_Disc_p4919 : (a_p 4919 : ℝ) ^ 2 ≤ 4 * (4919 : ℝ) :=
  BSD_disc_from_deg_831 BSD_DegreeNonneg_p4919
theorem BSD_HasseBound_Disc_p4931 : (a_p 4931 : ℝ) ^ 2 ≤ 4 * (4931 : ℝ) :=
  BSD_disc_from_deg_831 BSD_DegreeNonneg_p4931

end Towers.BSD
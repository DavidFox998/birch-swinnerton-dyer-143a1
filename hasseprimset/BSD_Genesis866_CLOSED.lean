/-
================================================================
Towers / BSD / BSD_Genesis866_CLOSED  (genesis-866)

HasseBridge Tier C: Hasse bounds for primes
7907..8009 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=7907: card=7891, a_p=+17, disc=-31339
  p=7919: card=7790, a_p=+130, disc=-14776
  p=7927: card=8102, a_p=-174, disc=-1432
  p=7933: card=7802, a_p=+132, disc=-14308
  p=7937: card=7776, a_p=+162, disc=-5504
  p=7949: card=7860, a_p=+90, disc=-23696
  p=7951: card=7968, a_p=-16, disc=-31548
  p=7963: card=8056, a_p=-92, disc=-23388
  p=7993: card=7920, a_p=+74, disc=-26496
  p=8009: card=7901, a_p=+109, disc=-20155

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_866 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i866_p7907 : Fact (7907 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7919 : Fact (7919 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7927 : Fact (7927 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7933 : Fact (7933 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7937 : Fact (7937 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7949 : Fact (7949 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7951 : Fact (7951 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7963 : Fact (7963 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7993 : Fact (7993 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p8009 : Fact (8009 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p7907 : (E143_Finset 7907).card = 7891 := by native_decide
theorem BSD_E143_card_p7919 : (E143_Finset 7919).card = 7790 := by native_decide
theorem BSD_E143_card_p7927 : (E143_Finset 7927).card = 8102 := by native_decide
theorem BSD_E143_card_p7933 : (E143_Finset 7933).card = 7802 := by native_decide
theorem BSD_E143_card_p7937 : (E143_Finset 7937).card = 7776 := by native_decide
theorem BSD_E143_card_p7949 : (E143_Finset 7949).card = 7860 := by native_decide
theorem BSD_E143_card_p7951 : (E143_Finset 7951).card = 7968 := by native_decide
theorem BSD_E143_card_p7963 : (E143_Finset 7963).card = 8056 := by native_decide
theorem BSD_E143_card_p7993 : (E143_Finset 7993).card = 7920 := by native_decide
theorem BSD_E143_card_p8009 : (E143_Finset 8009).card = 7901 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p7907 : a_p 7907 = (17 : ℤ) := by
  have h := BSD_E143_card_p7907; unfold a_p; omega
theorem BSD_ap_p7919 : a_p 7919 = (130 : ℤ) := by
  have h := BSD_E143_card_p7919; unfold a_p; omega
theorem BSD_ap_p7927 : a_p 7927 = (-174 : ℤ) := by
  have h := BSD_E143_card_p7927; unfold a_p; omega
theorem BSD_ap_p7933 : a_p 7933 = (132 : ℤ) := by
  have h := BSD_E143_card_p7933; unfold a_p; omega
theorem BSD_ap_p7937 : a_p 7937 = (162 : ℤ) := by
  have h := BSD_E143_card_p7937; unfold a_p; omega
theorem BSD_ap_p7949 : a_p 7949 = (90 : ℤ) := by
  have h := BSD_E143_card_p7949; unfold a_p; omega
theorem BSD_ap_p7951 : a_p 7951 = (-16 : ℤ) := by
  have h := BSD_E143_card_p7951; unfold a_p; omega
theorem BSD_ap_p7963 : a_p 7963 = (-92 : ℤ) := by
  have h := BSD_E143_card_p7963; unfold a_p; omega
theorem BSD_ap_p7993 : a_p 7993 = (74 : ℤ) := by
  have h := BSD_E143_card_p7993; unfold a_p; omega
theorem BSD_ap_p8009 : a_p 8009 = (109 : ℤ) := by
  have h := BSD_E143_card_p8009; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=7907: a_p=+17, 4p-a_p²=31339
theorem BSD_DegreeNonneg_p7907 : BSD_FrobeniusDegreeNonneg_OPEN 7907 := fun r => by
  have hap : (a_p 7907 : ℝ) = 17 := by exact_mod_cast BSD_ap_p7907
  have key : r ^ 2 - (a_p 7907 : ℝ) * r + ((7907 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 31339/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

-- p=7919: a_p=+130, 4p-a_p²=14776
theorem BSD_DegreeNonneg_p7919 : BSD_FrobeniusDegreeNonneg_OPEN 7919 := fun r => by
  have hap : (a_p 7919 : ℝ) = 130 := by exact_mod_cast BSD_ap_p7919
  have key : r ^ 2 - (a_p 7919 : ℝ) * r + ((7919 : ℕ) : ℝ) =
      (r - 130/2) ^ 2 + 14776/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (130 : ℝ)/2)]

-- p=7927: a_p=-174, 4p-a_p²=1432
theorem BSD_DegreeNonneg_p7927 : BSD_FrobeniusDegreeNonneg_OPEN 7927 := fun r => by
  have hap : (a_p 7927 : ℝ) = -174 := by exact_mod_cast BSD_ap_p7927
  have key : r ^ 2 - (a_p 7927 : ℝ) * r + ((7927 : ℕ) : ℝ) =
      (r + 174/2) ^ 2 + 1432/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (174 : ℝ)/2)]

-- p=7933: a_p=+132, 4p-a_p²=14308
theorem BSD_DegreeNonneg_p7933 : BSD_FrobeniusDegreeNonneg_OPEN 7933 := fun r => by
  have hap : (a_p 7933 : ℝ) = 132 := by exact_mod_cast BSD_ap_p7933
  have key : r ^ 2 - (a_p 7933 : ℝ) * r + ((7933 : ℕ) : ℝ) =
      (r - 132/2) ^ 2 + 14308/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (132 : ℝ)/2)]

-- p=7937: a_p=+162, 4p-a_p²=5504
theorem BSD_DegreeNonneg_p7937 : BSD_FrobeniusDegreeNonneg_OPEN 7937 := fun r => by
  have hap : (a_p 7937 : ℝ) = 162 := by exact_mod_cast BSD_ap_p7937
  have key : r ^ 2 - (a_p 7937 : ℝ) * r + ((7937 : ℕ) : ℝ) =
      (r - 162/2) ^ 2 + 5504/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (162 : ℝ)/2)]

-- p=7949: a_p=+90, 4p-a_p²=23696
theorem BSD_DegreeNonneg_p7949 : BSD_FrobeniusDegreeNonneg_OPEN 7949 := fun r => by
  have hap : (a_p 7949 : ℝ) = 90 := by exact_mod_cast BSD_ap_p7949
  have key : r ^ 2 - (a_p 7949 : ℝ) * r + ((7949 : ℕ) : ℝ) =
      (r - 90/2) ^ 2 + 23696/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (90 : ℝ)/2)]

-- p=7951: a_p=-16, 4p-a_p²=31548
theorem BSD_DegreeNonneg_p7951 : BSD_FrobeniusDegreeNonneg_OPEN 7951 := fun r => by
  have hap : (a_p 7951 : ℝ) = -16 := by exact_mod_cast BSD_ap_p7951
  have key : r ^ 2 - (a_p 7951 : ℝ) * r + ((7951 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 31548/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

-- p=7963: a_p=-92, 4p-a_p²=23388
theorem BSD_DegreeNonneg_p7963 : BSD_FrobeniusDegreeNonneg_OPEN 7963 := fun r => by
  have hap : (a_p 7963 : ℝ) = -92 := by exact_mod_cast BSD_ap_p7963
  have key : r ^ 2 - (a_p 7963 : ℝ) * r + ((7963 : ℕ) : ℝ) =
      (r + 92/2) ^ 2 + 23388/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (92 : ℝ)/2)]

-- p=7993: a_p=+74, 4p-a_p²=26496
theorem BSD_DegreeNonneg_p7993 : BSD_FrobeniusDegreeNonneg_OPEN 7993 := fun r => by
  have hap : (a_p 7993 : ℝ) = 74 := by exact_mod_cast BSD_ap_p7993
  have key : r ^ 2 - (a_p 7993 : ℝ) * r + ((7993 : ℕ) : ℝ) =
      (r - 74/2) ^ 2 + 26496/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (74 : ℝ)/2)]

-- p=8009: a_p=+109, 4p-a_p²=20155
theorem BSD_DegreeNonneg_p8009 : BSD_FrobeniusDegreeNonneg_OPEN 8009 := fun r => by
  have hap : (a_p 8009 : ℝ) = 109 := by exact_mod_cast BSD_ap_p8009
  have key : r ^ 2 - (a_p 8009 : ℝ) * r + ((8009 : ℕ) : ℝ) =
      (r - 109/2) ^ 2 + 20155/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (109 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p7907 : BSD_Hasse_OPEN 7907 :=
  BSD_hasse_of_degree_nonneg 7907 BSD_DegreeNonneg_p7907
theorem BSD_Hasse_OPEN_p7919 : BSD_Hasse_OPEN 7919 :=
  BSD_hasse_of_degree_nonneg 7919 BSD_DegreeNonneg_p7919
theorem BSD_Hasse_OPEN_p7927 : BSD_Hasse_OPEN 7927 :=
  BSD_hasse_of_degree_nonneg 7927 BSD_DegreeNonneg_p7927
theorem BSD_Hasse_OPEN_p7933 : BSD_Hasse_OPEN 7933 :=
  BSD_hasse_of_degree_nonneg 7933 BSD_DegreeNonneg_p7933
theorem BSD_Hasse_OPEN_p7937 : BSD_Hasse_OPEN 7937 :=
  BSD_hasse_of_degree_nonneg 7937 BSD_DegreeNonneg_p7937
theorem BSD_Hasse_OPEN_p7949 : BSD_Hasse_OPEN 7949 :=
  BSD_hasse_of_degree_nonneg 7949 BSD_DegreeNonneg_p7949
theorem BSD_Hasse_OPEN_p7951 : BSD_Hasse_OPEN 7951 :=
  BSD_hasse_of_degree_nonneg 7951 BSD_DegreeNonneg_p7951
theorem BSD_Hasse_OPEN_p7963 : BSD_Hasse_OPEN 7963 :=
  BSD_hasse_of_degree_nonneg 7963 BSD_DegreeNonneg_p7963
theorem BSD_Hasse_OPEN_p7993 : BSD_Hasse_OPEN 7993 :=
  BSD_hasse_of_degree_nonneg 7993 BSD_DegreeNonneg_p7993
theorem BSD_Hasse_OPEN_p8009 : BSD_Hasse_OPEN 8009 :=
  BSD_hasse_of_degree_nonneg 8009 BSD_DegreeNonneg_p8009

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p7907 : (a_p 7907 : ℝ) ^ 2 ≤ 4 * (7907 : ℝ) :=
  BSD_disc_from_deg_866 BSD_DegreeNonneg_p7907
theorem BSD_HasseBound_Disc_p7919 : (a_p 7919 : ℝ) ^ 2 ≤ 4 * (7919 : ℝ) :=
  BSD_disc_from_deg_866 BSD_DegreeNonneg_p7919
theorem BSD_HasseBound_Disc_p7927 : (a_p 7927 : ℝ) ^ 2 ≤ 4 * (7927 : ℝ) :=
  BSD_disc_from_deg_866 BSD_DegreeNonneg_p7927
theorem BSD_HasseBound_Disc_p7933 : (a_p 7933 : ℝ) ^ 2 ≤ 4 * (7933 : ℝ) :=
  BSD_disc_from_deg_866 BSD_DegreeNonneg_p7933
theorem BSD_HasseBound_Disc_p7937 : (a_p 7937 : ℝ) ^ 2 ≤ 4 * (7937 : ℝ) :=
  BSD_disc_from_deg_866 BSD_DegreeNonneg_p7937
theorem BSD_HasseBound_Disc_p7949 : (a_p 7949 : ℝ) ^ 2 ≤ 4 * (7949 : ℝ) :=
  BSD_disc_from_deg_866 BSD_DegreeNonneg_p7949
theorem BSD_HasseBound_Disc_p7951 : (a_p 7951 : ℝ) ^ 2 ≤ 4 * (7951 : ℝ) :=
  BSD_disc_from_deg_866 BSD_DegreeNonneg_p7951
theorem BSD_HasseBound_Disc_p7963 : (a_p 7963 : ℝ) ^ 2 ≤ 4 * (7963 : ℝ) :=
  BSD_disc_from_deg_866 BSD_DegreeNonneg_p7963
theorem BSD_HasseBound_Disc_p7993 : (a_p 7993 : ℝ) ^ 2 ≤ 4 * (7993 : ℝ) :=
  BSD_disc_from_deg_866 BSD_DegreeNonneg_p7993
theorem BSD_HasseBound_Disc_p8009 : (a_p 8009 : ℝ) ^ 2 ≤ 4 * (8009 : ℝ) :=
  BSD_disc_from_deg_866 BSD_DegreeNonneg_p8009

end Towers.BSD
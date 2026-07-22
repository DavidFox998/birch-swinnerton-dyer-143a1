/-
================================================================
Towers / BSD / BSD_Genesis868_CLOSED  (genesis-868)

HasseBridge Tier C: Hasse bounds for primes
8101..8191 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=8101: card=8215, a_p=-113, disc=-19635
  p=8111: card=8156, a_p=-44, disc=-30508
  p=8117: card=8046, a_p=+72, disc=-27284
  p=8123: card=8064, a_p=+60, disc=-28892
  p=8147: card=8172, a_p=-24, disc=-32012
  p=8161: card=8074, a_p=+88, disc=-24900
  p=8167: card=8269, a_p=-101, disc=-22467
  p=8171: card=8224, a_p=-52, disc=-29980
  p=8179: card=8320, a_p=-140, disc=-13116
  p=8191: card=8066, a_p=+126, disc=-16888

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_868 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i868_p8101 : Fact (8101 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8111 : Fact (8111 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8117 : Fact (8117 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8123 : Fact (8123 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8147 : Fact (8147 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8161 : Fact (8161 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8167 : Fact (8167 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8171 : Fact (8171 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8179 : Fact (8179 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8191 : Fact (8191 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p8101 : (E143_Finset 8101).card = 8215 := by native_decide
theorem BSD_E143_card_p8111 : (E143_Finset 8111).card = 8156 := by native_decide
theorem BSD_E143_card_p8117 : (E143_Finset 8117).card = 8046 := by native_decide
theorem BSD_E143_card_p8123 : (E143_Finset 8123).card = 8064 := by native_decide
theorem BSD_E143_card_p8147 : (E143_Finset 8147).card = 8172 := by native_decide
theorem BSD_E143_card_p8161 : (E143_Finset 8161).card = 8074 := by native_decide
theorem BSD_E143_card_p8167 : (E143_Finset 8167).card = 8269 := by native_decide
theorem BSD_E143_card_p8171 : (E143_Finset 8171).card = 8224 := by native_decide
theorem BSD_E143_card_p8179 : (E143_Finset 8179).card = 8320 := by native_decide
theorem BSD_E143_card_p8191 : (E143_Finset 8191).card = 8066 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p8101 : a_p 8101 = (-113 : ℤ) := by
  have h := BSD_E143_card_p8101; unfold a_p; omega
theorem BSD_ap_p8111 : a_p 8111 = (-44 : ℤ) := by
  have h := BSD_E143_card_p8111; unfold a_p; omega
theorem BSD_ap_p8117 : a_p 8117 = (72 : ℤ) := by
  have h := BSD_E143_card_p8117; unfold a_p; omega
theorem BSD_ap_p8123 : a_p 8123 = (60 : ℤ) := by
  have h := BSD_E143_card_p8123; unfold a_p; omega
theorem BSD_ap_p8147 : a_p 8147 = (-24 : ℤ) := by
  have h := BSD_E143_card_p8147; unfold a_p; omega
theorem BSD_ap_p8161 : a_p 8161 = (88 : ℤ) := by
  have h := BSD_E143_card_p8161; unfold a_p; omega
theorem BSD_ap_p8167 : a_p 8167 = (-101 : ℤ) := by
  have h := BSD_E143_card_p8167; unfold a_p; omega
theorem BSD_ap_p8171 : a_p 8171 = (-52 : ℤ) := by
  have h := BSD_E143_card_p8171; unfold a_p; omega
theorem BSD_ap_p8179 : a_p 8179 = (-140 : ℤ) := by
  have h := BSD_E143_card_p8179; unfold a_p; omega
theorem BSD_ap_p8191 : a_p 8191 = (126 : ℤ) := by
  have h := BSD_E143_card_p8191; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=8101: a_p=-113, 4p-a_p²=19635
theorem BSD_DegreeNonneg_p8101 : BSD_FrobeniusDegreeNonneg_OPEN 8101 := fun r => by
  have hap : (a_p 8101 : ℝ) = -113 := by exact_mod_cast BSD_ap_p8101
  have key : r ^ 2 - (a_p 8101 : ℝ) * r + ((8101 : ℕ) : ℝ) =
      (r + 113/2) ^ 2 + 19635/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (113 : ℝ)/2)]

-- p=8111: a_p=-44, 4p-a_p²=30508
theorem BSD_DegreeNonneg_p8111 : BSD_FrobeniusDegreeNonneg_OPEN 8111 := fun r => by
  have hap : (a_p 8111 : ℝ) = -44 := by exact_mod_cast BSD_ap_p8111
  have key : r ^ 2 - (a_p 8111 : ℝ) * r + ((8111 : ℕ) : ℝ) =
      (r + 44/2) ^ 2 + 30508/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (44 : ℝ)/2)]

-- p=8117: a_p=+72, 4p-a_p²=27284
theorem BSD_DegreeNonneg_p8117 : BSD_FrobeniusDegreeNonneg_OPEN 8117 := fun r => by
  have hap : (a_p 8117 : ℝ) = 72 := by exact_mod_cast BSD_ap_p8117
  have key : r ^ 2 - (a_p 8117 : ℝ) * r + ((8117 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 27284/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

-- p=8123: a_p=+60, 4p-a_p²=28892
theorem BSD_DegreeNonneg_p8123 : BSD_FrobeniusDegreeNonneg_OPEN 8123 := fun r => by
  have hap : (a_p 8123 : ℝ) = 60 := by exact_mod_cast BSD_ap_p8123
  have key : r ^ 2 - (a_p 8123 : ℝ) * r + ((8123 : ℕ) : ℝ) =
      (r - 60/2) ^ 2 + 28892/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (60 : ℝ)/2)]

-- p=8147: a_p=-24, 4p-a_p²=32012
theorem BSD_DegreeNonneg_p8147 : BSD_FrobeniusDegreeNonneg_OPEN 8147 := fun r => by
  have hap : (a_p 8147 : ℝ) = -24 := by exact_mod_cast BSD_ap_p8147
  have key : r ^ 2 - (a_p 8147 : ℝ) * r + ((8147 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 32012/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

-- p=8161: a_p=+88, 4p-a_p²=24900
theorem BSD_DegreeNonneg_p8161 : BSD_FrobeniusDegreeNonneg_OPEN 8161 := fun r => by
  have hap : (a_p 8161 : ℝ) = 88 := by exact_mod_cast BSD_ap_p8161
  have key : r ^ 2 - (a_p 8161 : ℝ) * r + ((8161 : ℕ) : ℝ) =
      (r - 88/2) ^ 2 + 24900/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (88 : ℝ)/2)]

-- p=8167: a_p=-101, 4p-a_p²=22467
theorem BSD_DegreeNonneg_p8167 : BSD_FrobeniusDegreeNonneg_OPEN 8167 := fun r => by
  have hap : (a_p 8167 : ℝ) = -101 := by exact_mod_cast BSD_ap_p8167
  have key : r ^ 2 - (a_p 8167 : ℝ) * r + ((8167 : ℕ) : ℝ) =
      (r + 101/2) ^ 2 + 22467/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (101 : ℝ)/2)]

-- p=8171: a_p=-52, 4p-a_p²=29980
theorem BSD_DegreeNonneg_p8171 : BSD_FrobeniusDegreeNonneg_OPEN 8171 := fun r => by
  have hap : (a_p 8171 : ℝ) = -52 := by exact_mod_cast BSD_ap_p8171
  have key : r ^ 2 - (a_p 8171 : ℝ) * r + ((8171 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 29980/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

-- p=8179: a_p=-140, 4p-a_p²=13116
theorem BSD_DegreeNonneg_p8179 : BSD_FrobeniusDegreeNonneg_OPEN 8179 := fun r => by
  have hap : (a_p 8179 : ℝ) = -140 := by exact_mod_cast BSD_ap_p8179
  have key : r ^ 2 - (a_p 8179 : ℝ) * r + ((8179 : ℕ) : ℝ) =
      (r + 140/2) ^ 2 + 13116/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (140 : ℝ)/2)]

-- p=8191: a_p=+126, 4p-a_p²=16888
theorem BSD_DegreeNonneg_p8191 : BSD_FrobeniusDegreeNonneg_OPEN 8191 := fun r => by
  have hap : (a_p 8191 : ℝ) = 126 := by exact_mod_cast BSD_ap_p8191
  have key : r ^ 2 - (a_p 8191 : ℝ) * r + ((8191 : ℕ) : ℝ) =
      (r - 126/2) ^ 2 + 16888/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (126 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p8101 : BSD_Hasse_OPEN 8101 :=
  BSD_hasse_of_degree_nonneg 8101 BSD_DegreeNonneg_p8101
theorem BSD_Hasse_OPEN_p8111 : BSD_Hasse_OPEN 8111 :=
  BSD_hasse_of_degree_nonneg 8111 BSD_DegreeNonneg_p8111
theorem BSD_Hasse_OPEN_p8117 : BSD_Hasse_OPEN 8117 :=
  BSD_hasse_of_degree_nonneg 8117 BSD_DegreeNonneg_p8117
theorem BSD_Hasse_OPEN_p8123 : BSD_Hasse_OPEN 8123 :=
  BSD_hasse_of_degree_nonneg 8123 BSD_DegreeNonneg_p8123
theorem BSD_Hasse_OPEN_p8147 : BSD_Hasse_OPEN 8147 :=
  BSD_hasse_of_degree_nonneg 8147 BSD_DegreeNonneg_p8147
theorem BSD_Hasse_OPEN_p8161 : BSD_Hasse_OPEN 8161 :=
  BSD_hasse_of_degree_nonneg 8161 BSD_DegreeNonneg_p8161
theorem BSD_Hasse_OPEN_p8167 : BSD_Hasse_OPEN 8167 :=
  BSD_hasse_of_degree_nonneg 8167 BSD_DegreeNonneg_p8167
theorem BSD_Hasse_OPEN_p8171 : BSD_Hasse_OPEN 8171 :=
  BSD_hasse_of_degree_nonneg 8171 BSD_DegreeNonneg_p8171
theorem BSD_Hasse_OPEN_p8179 : BSD_Hasse_OPEN 8179 :=
  BSD_hasse_of_degree_nonneg 8179 BSD_DegreeNonneg_p8179
theorem BSD_Hasse_OPEN_p8191 : BSD_Hasse_OPEN 8191 :=
  BSD_hasse_of_degree_nonneg 8191 BSD_DegreeNonneg_p8191

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p8101 : (a_p 8101 : ℝ) ^ 2 ≤ 4 * (8101 : ℝ) :=
  BSD_disc_from_deg_868 BSD_DegreeNonneg_p8101
theorem BSD_HasseBound_Disc_p8111 : (a_p 8111 : ℝ) ^ 2 ≤ 4 * (8111 : ℝ) :=
  BSD_disc_from_deg_868 BSD_DegreeNonneg_p8111
theorem BSD_HasseBound_Disc_p8117 : (a_p 8117 : ℝ) ^ 2 ≤ 4 * (8117 : ℝ) :=
  BSD_disc_from_deg_868 BSD_DegreeNonneg_p8117
theorem BSD_HasseBound_Disc_p8123 : (a_p 8123 : ℝ) ^ 2 ≤ 4 * (8123 : ℝ) :=
  BSD_disc_from_deg_868 BSD_DegreeNonneg_p8123
theorem BSD_HasseBound_Disc_p8147 : (a_p 8147 : ℝ) ^ 2 ≤ 4 * (8147 : ℝ) :=
  BSD_disc_from_deg_868 BSD_DegreeNonneg_p8147
theorem BSD_HasseBound_Disc_p8161 : (a_p 8161 : ℝ) ^ 2 ≤ 4 * (8161 : ℝ) :=
  BSD_disc_from_deg_868 BSD_DegreeNonneg_p8161
theorem BSD_HasseBound_Disc_p8167 : (a_p 8167 : ℝ) ^ 2 ≤ 4 * (8167 : ℝ) :=
  BSD_disc_from_deg_868 BSD_DegreeNonneg_p8167
theorem BSD_HasseBound_Disc_p8171 : (a_p 8171 : ℝ) ^ 2 ≤ 4 * (8171 : ℝ) :=
  BSD_disc_from_deg_868 BSD_DegreeNonneg_p8171
theorem BSD_HasseBound_Disc_p8179 : (a_p 8179 : ℝ) ^ 2 ≤ 4 * (8179 : ℝ) :=
  BSD_disc_from_deg_868 BSD_DegreeNonneg_p8179
theorem BSD_HasseBound_Disc_p8191 : (a_p 8191 : ℝ) ^ 2 ≤ 4 * (8191 : ℝ) :=
  BSD_disc_from_deg_868 BSD_DegreeNonneg_p8191

end Towers.BSD
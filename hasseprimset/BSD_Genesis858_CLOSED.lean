/-
================================================================
Towers / BSD / BSD_Genesis858_CLOSED  (genesis-858)

HasseBridge Tier C: Hasse bounds for primes
7193..7253 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=7193: card=7236, a_p=-42, disc=-27008
  p=7207: card=7108, a_p=+100, disc=-18828
  p=7211: card=7104, a_p=+108, disc=-17180
  p=7213: card=7162, a_p=+52, disc=-26148
  p=7219: card=7123, a_p=+97, disc=-19467
  p=7229: card=7332, a_p=-102, disc=-18512
  p=7237: card=7198, a_p=+40, disc=-27348
  p=7243: card=7287, a_p=-43, disc=-27123
  p=7247: card=7211, a_p=+37, disc=-27619
  p=7253: card=7351, a_p=-97, disc=-19603

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_858 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i858_p7193 : Fact (7193 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7207 : Fact (7207 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7211 : Fact (7211 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7213 : Fact (7213 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7219 : Fact (7219 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7229 : Fact (7229 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7237 : Fact (7237 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7243 : Fact (7243 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7247 : Fact (7247 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7253 : Fact (7253 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p7193 : (E143_Finset 7193).card = 7236 := by native_decide
theorem BSD_E143_card_p7207 : (E143_Finset 7207).card = 7108 := by native_decide
theorem BSD_E143_card_p7211 : (E143_Finset 7211).card = 7104 := by native_decide
theorem BSD_E143_card_p7213 : (E143_Finset 7213).card = 7162 := by native_decide
theorem BSD_E143_card_p7219 : (E143_Finset 7219).card = 7123 := by native_decide
theorem BSD_E143_card_p7229 : (E143_Finset 7229).card = 7332 := by native_decide
theorem BSD_E143_card_p7237 : (E143_Finset 7237).card = 7198 := by native_decide
theorem BSD_E143_card_p7243 : (E143_Finset 7243).card = 7287 := by native_decide
theorem BSD_E143_card_p7247 : (E143_Finset 7247).card = 7211 := by native_decide
theorem BSD_E143_card_p7253 : (E143_Finset 7253).card = 7351 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p7193 : a_p 7193 = (-42 : ℤ) := by
  have h := BSD_E143_card_p7193; unfold a_p; omega
theorem BSD_ap_p7207 : a_p 7207 = (100 : ℤ) := by
  have h := BSD_E143_card_p7207; unfold a_p; omega
theorem BSD_ap_p7211 : a_p 7211 = (108 : ℤ) := by
  have h := BSD_E143_card_p7211; unfold a_p; omega
theorem BSD_ap_p7213 : a_p 7213 = (52 : ℤ) := by
  have h := BSD_E143_card_p7213; unfold a_p; omega
theorem BSD_ap_p7219 : a_p 7219 = (97 : ℤ) := by
  have h := BSD_E143_card_p7219; unfold a_p; omega
theorem BSD_ap_p7229 : a_p 7229 = (-102 : ℤ) := by
  have h := BSD_E143_card_p7229; unfold a_p; omega
theorem BSD_ap_p7237 : a_p 7237 = (40 : ℤ) := by
  have h := BSD_E143_card_p7237; unfold a_p; omega
theorem BSD_ap_p7243 : a_p 7243 = (-43 : ℤ) := by
  have h := BSD_E143_card_p7243; unfold a_p; omega
theorem BSD_ap_p7247 : a_p 7247 = (37 : ℤ) := by
  have h := BSD_E143_card_p7247; unfold a_p; omega
theorem BSD_ap_p7253 : a_p 7253 = (-97 : ℤ) := by
  have h := BSD_E143_card_p7253; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=7193: a_p=-42, 4p-a_p²=27008
theorem BSD_DegreeNonneg_p7193 : BSD_FrobeniusDegreeNonneg_OPEN 7193 := fun r => by
  have hap : (a_p 7193 : ℝ) = -42 := by exact_mod_cast BSD_ap_p7193
  have key : r ^ 2 - (a_p 7193 : ℝ) * r + ((7193 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 27008/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

-- p=7207: a_p=+100, 4p-a_p²=18828
theorem BSD_DegreeNonneg_p7207 : BSD_FrobeniusDegreeNonneg_OPEN 7207 := fun r => by
  have hap : (a_p 7207 : ℝ) = 100 := by exact_mod_cast BSD_ap_p7207
  have key : r ^ 2 - (a_p 7207 : ℝ) * r + ((7207 : ℕ) : ℝ) =
      (r - 100/2) ^ 2 + 18828/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (100 : ℝ)/2)]

-- p=7211: a_p=+108, 4p-a_p²=17180
theorem BSD_DegreeNonneg_p7211 : BSD_FrobeniusDegreeNonneg_OPEN 7211 := fun r => by
  have hap : (a_p 7211 : ℝ) = 108 := by exact_mod_cast BSD_ap_p7211
  have key : r ^ 2 - (a_p 7211 : ℝ) * r + ((7211 : ℕ) : ℝ) =
      (r - 108/2) ^ 2 + 17180/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (108 : ℝ)/2)]

-- p=7213: a_p=+52, 4p-a_p²=26148
theorem BSD_DegreeNonneg_p7213 : BSD_FrobeniusDegreeNonneg_OPEN 7213 := fun r => by
  have hap : (a_p 7213 : ℝ) = 52 := by exact_mod_cast BSD_ap_p7213
  have key : r ^ 2 - (a_p 7213 : ℝ) * r + ((7213 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 26148/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

-- p=7219: a_p=+97, 4p-a_p²=19467
theorem BSD_DegreeNonneg_p7219 : BSD_FrobeniusDegreeNonneg_OPEN 7219 := fun r => by
  have hap : (a_p 7219 : ℝ) = 97 := by exact_mod_cast BSD_ap_p7219
  have key : r ^ 2 - (a_p 7219 : ℝ) * r + ((7219 : ℕ) : ℝ) =
      (r - 97/2) ^ 2 + 19467/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (97 : ℝ)/2)]

-- p=7229: a_p=-102, 4p-a_p²=18512
theorem BSD_DegreeNonneg_p7229 : BSD_FrobeniusDegreeNonneg_OPEN 7229 := fun r => by
  have hap : (a_p 7229 : ℝ) = -102 := by exact_mod_cast BSD_ap_p7229
  have key : r ^ 2 - (a_p 7229 : ℝ) * r + ((7229 : ℕ) : ℝ) =
      (r + 102/2) ^ 2 + 18512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (102 : ℝ)/2)]

-- p=7237: a_p=+40, 4p-a_p²=27348
theorem BSD_DegreeNonneg_p7237 : BSD_FrobeniusDegreeNonneg_OPEN 7237 := fun r => by
  have hap : (a_p 7237 : ℝ) = 40 := by exact_mod_cast BSD_ap_p7237
  have key : r ^ 2 - (a_p 7237 : ℝ) * r + ((7237 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 27348/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

-- p=7243: a_p=-43, 4p-a_p²=27123
theorem BSD_DegreeNonneg_p7243 : BSD_FrobeniusDegreeNonneg_OPEN 7243 := fun r => by
  have hap : (a_p 7243 : ℝ) = -43 := by exact_mod_cast BSD_ap_p7243
  have key : r ^ 2 - (a_p 7243 : ℝ) * r + ((7243 : ℕ) : ℝ) =
      (r + 43/2) ^ 2 + 27123/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (43 : ℝ)/2)]

-- p=7247: a_p=+37, 4p-a_p²=27619
theorem BSD_DegreeNonneg_p7247 : BSD_FrobeniusDegreeNonneg_OPEN 7247 := fun r => by
  have hap : (a_p 7247 : ℝ) = 37 := by exact_mod_cast BSD_ap_p7247
  have key : r ^ 2 - (a_p 7247 : ℝ) * r + ((7247 : ℕ) : ℝ) =
      (r - 37/2) ^ 2 + 27619/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (37 : ℝ)/2)]

-- p=7253: a_p=-97, 4p-a_p²=19603
theorem BSD_DegreeNonneg_p7253 : BSD_FrobeniusDegreeNonneg_OPEN 7253 := fun r => by
  have hap : (a_p 7253 : ℝ) = -97 := by exact_mod_cast BSD_ap_p7253
  have key : r ^ 2 - (a_p 7253 : ℝ) * r + ((7253 : ℕ) : ℝ) =
      (r + 97/2) ^ 2 + 19603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (97 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p7193 : BSD_Hasse_OPEN 7193 :=
  BSD_hasse_of_degree_nonneg 7193 BSD_DegreeNonneg_p7193
theorem BSD_Hasse_OPEN_p7207 : BSD_Hasse_OPEN 7207 :=
  BSD_hasse_of_degree_nonneg 7207 BSD_DegreeNonneg_p7207
theorem BSD_Hasse_OPEN_p7211 : BSD_Hasse_OPEN 7211 :=
  BSD_hasse_of_degree_nonneg 7211 BSD_DegreeNonneg_p7211
theorem BSD_Hasse_OPEN_p7213 : BSD_Hasse_OPEN 7213 :=
  BSD_hasse_of_degree_nonneg 7213 BSD_DegreeNonneg_p7213
theorem BSD_Hasse_OPEN_p7219 : BSD_Hasse_OPEN 7219 :=
  BSD_hasse_of_degree_nonneg 7219 BSD_DegreeNonneg_p7219
theorem BSD_Hasse_OPEN_p7229 : BSD_Hasse_OPEN 7229 :=
  BSD_hasse_of_degree_nonneg 7229 BSD_DegreeNonneg_p7229
theorem BSD_Hasse_OPEN_p7237 : BSD_Hasse_OPEN 7237 :=
  BSD_hasse_of_degree_nonneg 7237 BSD_DegreeNonneg_p7237
theorem BSD_Hasse_OPEN_p7243 : BSD_Hasse_OPEN 7243 :=
  BSD_hasse_of_degree_nonneg 7243 BSD_DegreeNonneg_p7243
theorem BSD_Hasse_OPEN_p7247 : BSD_Hasse_OPEN 7247 :=
  BSD_hasse_of_degree_nonneg 7247 BSD_DegreeNonneg_p7247
theorem BSD_Hasse_OPEN_p7253 : BSD_Hasse_OPEN 7253 :=
  BSD_hasse_of_degree_nonneg 7253 BSD_DegreeNonneg_p7253

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p7193 : (a_p 7193 : ℝ) ^ 2 ≤ 4 * (7193 : ℝ) :=
  BSD_disc_from_deg_858 BSD_DegreeNonneg_p7193
theorem BSD_HasseBound_Disc_p7207 : (a_p 7207 : ℝ) ^ 2 ≤ 4 * (7207 : ℝ) :=
  BSD_disc_from_deg_858 BSD_DegreeNonneg_p7207
theorem BSD_HasseBound_Disc_p7211 : (a_p 7211 : ℝ) ^ 2 ≤ 4 * (7211 : ℝ) :=
  BSD_disc_from_deg_858 BSD_DegreeNonneg_p7211
theorem BSD_HasseBound_Disc_p7213 : (a_p 7213 : ℝ) ^ 2 ≤ 4 * (7213 : ℝ) :=
  BSD_disc_from_deg_858 BSD_DegreeNonneg_p7213
theorem BSD_HasseBound_Disc_p7219 : (a_p 7219 : ℝ) ^ 2 ≤ 4 * (7219 : ℝ) :=
  BSD_disc_from_deg_858 BSD_DegreeNonneg_p7219
theorem BSD_HasseBound_Disc_p7229 : (a_p 7229 : ℝ) ^ 2 ≤ 4 * (7229 : ℝ) :=
  BSD_disc_from_deg_858 BSD_DegreeNonneg_p7229
theorem BSD_HasseBound_Disc_p7237 : (a_p 7237 : ℝ) ^ 2 ≤ 4 * (7237 : ℝ) :=
  BSD_disc_from_deg_858 BSD_DegreeNonneg_p7237
theorem BSD_HasseBound_Disc_p7243 : (a_p 7243 : ℝ) ^ 2 ≤ 4 * (7243 : ℝ) :=
  BSD_disc_from_deg_858 BSD_DegreeNonneg_p7243
theorem BSD_HasseBound_Disc_p7247 : (a_p 7247 : ℝ) ^ 2 ≤ 4 * (7247 : ℝ) :=
  BSD_disc_from_deg_858 BSD_DegreeNonneg_p7247
theorem BSD_HasseBound_Disc_p7253 : (a_p 7253 : ℝ) ^ 2 ≤ 4 * (7253 : ℝ) :=
  BSD_disc_from_deg_858 BSD_DegreeNonneg_p7253

end Towers.BSD
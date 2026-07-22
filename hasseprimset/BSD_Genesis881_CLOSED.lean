/-
================================================================
Towers / BSD / BSD_Genesis881_CLOSED  (genesis-881)

HasseBridge Tier C: Hasse bounds for primes
9281..9349 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=9281: card=9438, a_p=-156, disc=-12788
  p=9283: card=9378, a_p=-94, disc=-28296
  p=9293: card=9280, a_p=+14, disc=-36976
  p=9311: card=9181, a_p=+131, disc=-20083
  p=9319: card=9418, a_p=-98, disc=-27672
  p=9323: card=9190, a_p=+134, disc=-19336
  p=9337: card=9225, a_p=+113, disc=-24579
  p=9341: card=9236, a_p=+106, disc=-26128
  p=9343: card=9527, a_p=-183, disc=-3883
  p=9349: card=9486, a_p=-136, disc=-18900

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_881 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i881_p9281 : Fact (9281 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9283 : Fact (9283 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9293 : Fact (9293 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9311 : Fact (9311 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9319 : Fact (9319 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9323 : Fact (9323 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9337 : Fact (9337 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9341 : Fact (9341 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9343 : Fact (9343 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9349 : Fact (9349 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p9281 : (E143_Finset 9281).card = 9438 := by native_decide
theorem BSD_E143_card_p9283 : (E143_Finset 9283).card = 9378 := by native_decide
theorem BSD_E143_card_p9293 : (E143_Finset 9293).card = 9280 := by native_decide
theorem BSD_E143_card_p9311 : (E143_Finset 9311).card = 9181 := by native_decide
theorem BSD_E143_card_p9319 : (E143_Finset 9319).card = 9418 := by native_decide
theorem BSD_E143_card_p9323 : (E143_Finset 9323).card = 9190 := by native_decide
theorem BSD_E143_card_p9337 : (E143_Finset 9337).card = 9225 := by native_decide
theorem BSD_E143_card_p9341 : (E143_Finset 9341).card = 9236 := by native_decide
theorem BSD_E143_card_p9343 : (E143_Finset 9343).card = 9527 := by native_decide
theorem BSD_E143_card_p9349 : (E143_Finset 9349).card = 9486 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p9281 : a_p 9281 = (-156 : ℤ) := by
  have h := BSD_E143_card_p9281; unfold a_p; omega
theorem BSD_ap_p9283 : a_p 9283 = (-94 : ℤ) := by
  have h := BSD_E143_card_p9283; unfold a_p; omega
theorem BSD_ap_p9293 : a_p 9293 = (14 : ℤ) := by
  have h := BSD_E143_card_p9293; unfold a_p; omega
theorem BSD_ap_p9311 : a_p 9311 = (131 : ℤ) := by
  have h := BSD_E143_card_p9311; unfold a_p; omega
theorem BSD_ap_p9319 : a_p 9319 = (-98 : ℤ) := by
  have h := BSD_E143_card_p9319; unfold a_p; omega
theorem BSD_ap_p9323 : a_p 9323 = (134 : ℤ) := by
  have h := BSD_E143_card_p9323; unfold a_p; omega
theorem BSD_ap_p9337 : a_p 9337 = (113 : ℤ) := by
  have h := BSD_E143_card_p9337; unfold a_p; omega
theorem BSD_ap_p9341 : a_p 9341 = (106 : ℤ) := by
  have h := BSD_E143_card_p9341; unfold a_p; omega
theorem BSD_ap_p9343 : a_p 9343 = (-183 : ℤ) := by
  have h := BSD_E143_card_p9343; unfold a_p; omega
theorem BSD_ap_p9349 : a_p 9349 = (-136 : ℤ) := by
  have h := BSD_E143_card_p9349; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=9281: a_p=-156, 4p-a_p²=12788
theorem BSD_DegreeNonneg_p9281 : BSD_FrobeniusDegreeNonneg_OPEN 9281 := fun r => by
  have hap : (a_p 9281 : ℝ) = -156 := by exact_mod_cast BSD_ap_p9281
  have key : r ^ 2 - (a_p 9281 : ℝ) * r + ((9281 : ℕ) : ℝ) =
      (r + 156/2) ^ 2 + 12788/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (156 : ℝ)/2)]

-- p=9283: a_p=-94, 4p-a_p²=28296
theorem BSD_DegreeNonneg_p9283 : BSD_FrobeniusDegreeNonneg_OPEN 9283 := fun r => by
  have hap : (a_p 9283 : ℝ) = -94 := by exact_mod_cast BSD_ap_p9283
  have key : r ^ 2 - (a_p 9283 : ℝ) * r + ((9283 : ℕ) : ℝ) =
      (r + 94/2) ^ 2 + 28296/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (94 : ℝ)/2)]

-- p=9293: a_p=+14, 4p-a_p²=36976
theorem BSD_DegreeNonneg_p9293 : BSD_FrobeniusDegreeNonneg_OPEN 9293 := fun r => by
  have hap : (a_p 9293 : ℝ) = 14 := by exact_mod_cast BSD_ap_p9293
  have key : r ^ 2 - (a_p 9293 : ℝ) * r + ((9293 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 36976/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

-- p=9311: a_p=+131, 4p-a_p²=20083
theorem BSD_DegreeNonneg_p9311 : BSD_FrobeniusDegreeNonneg_OPEN 9311 := fun r => by
  have hap : (a_p 9311 : ℝ) = 131 := by exact_mod_cast BSD_ap_p9311
  have key : r ^ 2 - (a_p 9311 : ℝ) * r + ((9311 : ℕ) : ℝ) =
      (r - 131/2) ^ 2 + 20083/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (131 : ℝ)/2)]

-- p=9319: a_p=-98, 4p-a_p²=27672
theorem BSD_DegreeNonneg_p9319 : BSD_FrobeniusDegreeNonneg_OPEN 9319 := fun r => by
  have hap : (a_p 9319 : ℝ) = -98 := by exact_mod_cast BSD_ap_p9319
  have key : r ^ 2 - (a_p 9319 : ℝ) * r + ((9319 : ℕ) : ℝ) =
      (r + 98/2) ^ 2 + 27672/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (98 : ℝ)/2)]

-- p=9323: a_p=+134, 4p-a_p²=19336
theorem BSD_DegreeNonneg_p9323 : BSD_FrobeniusDegreeNonneg_OPEN 9323 := fun r => by
  have hap : (a_p 9323 : ℝ) = 134 := by exact_mod_cast BSD_ap_p9323
  have key : r ^ 2 - (a_p 9323 : ℝ) * r + ((9323 : ℕ) : ℝ) =
      (r - 134/2) ^ 2 + 19336/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (134 : ℝ)/2)]

-- p=9337: a_p=+113, 4p-a_p²=24579
theorem BSD_DegreeNonneg_p9337 : BSD_FrobeniusDegreeNonneg_OPEN 9337 := fun r => by
  have hap : (a_p 9337 : ℝ) = 113 := by exact_mod_cast BSD_ap_p9337
  have key : r ^ 2 - (a_p 9337 : ℝ) * r + ((9337 : ℕ) : ℝ) =
      (r - 113/2) ^ 2 + 24579/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (113 : ℝ)/2)]

-- p=9341: a_p=+106, 4p-a_p²=26128
theorem BSD_DegreeNonneg_p9341 : BSD_FrobeniusDegreeNonneg_OPEN 9341 := fun r => by
  have hap : (a_p 9341 : ℝ) = 106 := by exact_mod_cast BSD_ap_p9341
  have key : r ^ 2 - (a_p 9341 : ℝ) * r + ((9341 : ℕ) : ℝ) =
      (r - 106/2) ^ 2 + 26128/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (106 : ℝ)/2)]

-- p=9343: a_p=-183, 4p-a_p²=3883
theorem BSD_DegreeNonneg_p9343 : BSD_FrobeniusDegreeNonneg_OPEN 9343 := fun r => by
  have hap : (a_p 9343 : ℝ) = -183 := by exact_mod_cast BSD_ap_p9343
  have key : r ^ 2 - (a_p 9343 : ℝ) * r + ((9343 : ℕ) : ℝ) =
      (r + 183/2) ^ 2 + 3883/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (183 : ℝ)/2)]

-- p=9349: a_p=-136, 4p-a_p²=18900
theorem BSD_DegreeNonneg_p9349 : BSD_FrobeniusDegreeNonneg_OPEN 9349 := fun r => by
  have hap : (a_p 9349 : ℝ) = -136 := by exact_mod_cast BSD_ap_p9349
  have key : r ^ 2 - (a_p 9349 : ℝ) * r + ((9349 : ℕ) : ℝ) =
      (r + 136/2) ^ 2 + 18900/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (136 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p9281 : BSD_Hasse_OPEN 9281 :=
  BSD_hasse_of_degree_nonneg 9281 BSD_DegreeNonneg_p9281
theorem BSD_Hasse_OPEN_p9283 : BSD_Hasse_OPEN 9283 :=
  BSD_hasse_of_degree_nonneg 9283 BSD_DegreeNonneg_p9283
theorem BSD_Hasse_OPEN_p9293 : BSD_Hasse_OPEN 9293 :=
  BSD_hasse_of_degree_nonneg 9293 BSD_DegreeNonneg_p9293
theorem BSD_Hasse_OPEN_p9311 : BSD_Hasse_OPEN 9311 :=
  BSD_hasse_of_degree_nonneg 9311 BSD_DegreeNonneg_p9311
theorem BSD_Hasse_OPEN_p9319 : BSD_Hasse_OPEN 9319 :=
  BSD_hasse_of_degree_nonneg 9319 BSD_DegreeNonneg_p9319
theorem BSD_Hasse_OPEN_p9323 : BSD_Hasse_OPEN 9323 :=
  BSD_hasse_of_degree_nonneg 9323 BSD_DegreeNonneg_p9323
theorem BSD_Hasse_OPEN_p9337 : BSD_Hasse_OPEN 9337 :=
  BSD_hasse_of_degree_nonneg 9337 BSD_DegreeNonneg_p9337
theorem BSD_Hasse_OPEN_p9341 : BSD_Hasse_OPEN 9341 :=
  BSD_hasse_of_degree_nonneg 9341 BSD_DegreeNonneg_p9341
theorem BSD_Hasse_OPEN_p9343 : BSD_Hasse_OPEN 9343 :=
  BSD_hasse_of_degree_nonneg 9343 BSD_DegreeNonneg_p9343
theorem BSD_Hasse_OPEN_p9349 : BSD_Hasse_OPEN 9349 :=
  BSD_hasse_of_degree_nonneg 9349 BSD_DegreeNonneg_p9349

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p9281 : (a_p 9281 : ℝ) ^ 2 ≤ 4 * (9281 : ℝ) :=
  BSD_disc_from_deg_881 BSD_DegreeNonneg_p9281
theorem BSD_HasseBound_Disc_p9283 : (a_p 9283 : ℝ) ^ 2 ≤ 4 * (9283 : ℝ) :=
  BSD_disc_from_deg_881 BSD_DegreeNonneg_p9283
theorem BSD_HasseBound_Disc_p9293 : (a_p 9293 : ℝ) ^ 2 ≤ 4 * (9293 : ℝ) :=
  BSD_disc_from_deg_881 BSD_DegreeNonneg_p9293
theorem BSD_HasseBound_Disc_p9311 : (a_p 9311 : ℝ) ^ 2 ≤ 4 * (9311 : ℝ) :=
  BSD_disc_from_deg_881 BSD_DegreeNonneg_p9311
theorem BSD_HasseBound_Disc_p9319 : (a_p 9319 : ℝ) ^ 2 ≤ 4 * (9319 : ℝ) :=
  BSD_disc_from_deg_881 BSD_DegreeNonneg_p9319
theorem BSD_HasseBound_Disc_p9323 : (a_p 9323 : ℝ) ^ 2 ≤ 4 * (9323 : ℝ) :=
  BSD_disc_from_deg_881 BSD_DegreeNonneg_p9323
theorem BSD_HasseBound_Disc_p9337 : (a_p 9337 : ℝ) ^ 2 ≤ 4 * (9337 : ℝ) :=
  BSD_disc_from_deg_881 BSD_DegreeNonneg_p9337
theorem BSD_HasseBound_Disc_p9341 : (a_p 9341 : ℝ) ^ 2 ≤ 4 * (9341 : ℝ) :=
  BSD_disc_from_deg_881 BSD_DegreeNonneg_p9341
theorem BSD_HasseBound_Disc_p9343 : (a_p 9343 : ℝ) ^ 2 ≤ 4 * (9343 : ℝ) :=
  BSD_disc_from_deg_881 BSD_DegreeNonneg_p9343
theorem BSD_HasseBound_Disc_p9349 : (a_p 9349 : ℝ) ^ 2 ≤ 4 * (9349 : ℝ) :=
  BSD_disc_from_deg_881 BSD_DegreeNonneg_p9349

end Towers.BSD
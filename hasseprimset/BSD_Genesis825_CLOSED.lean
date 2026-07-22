/-
================================================================
Towers / BSD / BSD_Genesis825_CLOSED  (genesis-825)

HasseBridge Tier C: Hasse bounds for primes
4289..4391 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=4289: card=4340, a_p=-50, disc=-14656
  p=4297: card=4290, a_p=+8, disc=-17124
  p=4327: card=4221, a_p=+107, disc=-5859
  p=4337: card=4320, a_p=+18, disc=-17024
  p=4339: card=4417, a_p=-77, disc=-11427
  p=4349: card=4368, a_p=-18, disc=-17072
  p=4357: card=4241, a_p=+117, disc=-3739
  p=4363: card=4246, a_p=+118, disc=-3528
  p=4373: card=4278, a_p=+96, disc=-8276
  p=4391: card=4500, a_p=-108, disc=-5900

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_825 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i825_p4289 : Fact (4289 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4297 : Fact (4297 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4327 : Fact (4327 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4337 : Fact (4337 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4339 : Fact (4339 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4349 : Fact (4349 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4357 : Fact (4357 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4363 : Fact (4363 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4373 : Fact (4373 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4391 : Fact (4391 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p4289 : (E143_Finset 4289).card = 4340 := by native_decide
theorem BSD_E143_card_p4297 : (E143_Finset 4297).card = 4290 := by native_decide
theorem BSD_E143_card_p4327 : (E143_Finset 4327).card = 4221 := by native_decide
theorem BSD_E143_card_p4337 : (E143_Finset 4337).card = 4320 := by native_decide
theorem BSD_E143_card_p4339 : (E143_Finset 4339).card = 4417 := by native_decide
theorem BSD_E143_card_p4349 : (E143_Finset 4349).card = 4368 := by native_decide
theorem BSD_E143_card_p4357 : (E143_Finset 4357).card = 4241 := by native_decide
theorem BSD_E143_card_p4363 : (E143_Finset 4363).card = 4246 := by native_decide
theorem BSD_E143_card_p4373 : (E143_Finset 4373).card = 4278 := by native_decide
theorem BSD_E143_card_p4391 : (E143_Finset 4391).card = 4500 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p4289 : a_p 4289 = (-50 : ℤ) := by
  have h := BSD_E143_card_p4289; unfold a_p; omega
theorem BSD_ap_p4297 : a_p 4297 = (8 : ℤ) := by
  have h := BSD_E143_card_p4297; unfold a_p; omega
theorem BSD_ap_p4327 : a_p 4327 = (107 : ℤ) := by
  have h := BSD_E143_card_p4327; unfold a_p; omega
theorem BSD_ap_p4337 : a_p 4337 = (18 : ℤ) := by
  have h := BSD_E143_card_p4337; unfold a_p; omega
theorem BSD_ap_p4339 : a_p 4339 = (-77 : ℤ) := by
  have h := BSD_E143_card_p4339; unfold a_p; omega
theorem BSD_ap_p4349 : a_p 4349 = (-18 : ℤ) := by
  have h := BSD_E143_card_p4349; unfold a_p; omega
theorem BSD_ap_p4357 : a_p 4357 = (117 : ℤ) := by
  have h := BSD_E143_card_p4357; unfold a_p; omega
theorem BSD_ap_p4363 : a_p 4363 = (118 : ℤ) := by
  have h := BSD_E143_card_p4363; unfold a_p; omega
theorem BSD_ap_p4373 : a_p 4373 = (96 : ℤ) := by
  have h := BSD_E143_card_p4373; unfold a_p; omega
theorem BSD_ap_p4391 : a_p 4391 = (-108 : ℤ) := by
  have h := BSD_E143_card_p4391; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=4289: a_p=-50, 4p-a_p²=14656
theorem BSD_DegreeNonneg_p4289 : BSD_FrobeniusDegreeNonneg_OPEN 4289 := fun r => by
  have hap : (a_p 4289 : ℝ) = -50 := by exact_mod_cast BSD_ap_p4289
  have key : r ^ 2 - (a_p 4289 : ℝ) * r + ((4289 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 14656/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

-- p=4297: a_p=+8, 4p-a_p²=17124
theorem BSD_DegreeNonneg_p4297 : BSD_FrobeniusDegreeNonneg_OPEN 4297 := fun r => by
  have hap : (a_p 4297 : ℝ) = 8 := by exact_mod_cast BSD_ap_p4297
  have key : r ^ 2 - (a_p 4297 : ℝ) * r + ((4297 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 17124/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

-- p=4327: a_p=+107, 4p-a_p²=5859
theorem BSD_DegreeNonneg_p4327 : BSD_FrobeniusDegreeNonneg_OPEN 4327 := fun r => by
  have hap : (a_p 4327 : ℝ) = 107 := by exact_mod_cast BSD_ap_p4327
  have key : r ^ 2 - (a_p 4327 : ℝ) * r + ((4327 : ℕ) : ℝ) =
      (r - 107/2) ^ 2 + 5859/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (107 : ℝ)/2)]

-- p=4337: a_p=+18, 4p-a_p²=17024
theorem BSD_DegreeNonneg_p4337 : BSD_FrobeniusDegreeNonneg_OPEN 4337 := fun r => by
  have hap : (a_p 4337 : ℝ) = 18 := by exact_mod_cast BSD_ap_p4337
  have key : r ^ 2 - (a_p 4337 : ℝ) * r + ((4337 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 17024/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

-- p=4339: a_p=-77, 4p-a_p²=11427
theorem BSD_DegreeNonneg_p4339 : BSD_FrobeniusDegreeNonneg_OPEN 4339 := fun r => by
  have hap : (a_p 4339 : ℝ) = -77 := by exact_mod_cast BSD_ap_p4339
  have key : r ^ 2 - (a_p 4339 : ℝ) * r + ((4339 : ℕ) : ℝ) =
      (r + 77/2) ^ 2 + 11427/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (77 : ℝ)/2)]

-- p=4349: a_p=-18, 4p-a_p²=17072
theorem BSD_DegreeNonneg_p4349 : BSD_FrobeniusDegreeNonneg_OPEN 4349 := fun r => by
  have hap : (a_p 4349 : ℝ) = -18 := by exact_mod_cast BSD_ap_p4349
  have key : r ^ 2 - (a_p 4349 : ℝ) * r + ((4349 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 17072/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

-- p=4357: a_p=+117, 4p-a_p²=3739
theorem BSD_DegreeNonneg_p4357 : BSD_FrobeniusDegreeNonneg_OPEN 4357 := fun r => by
  have hap : (a_p 4357 : ℝ) = 117 := by exact_mod_cast BSD_ap_p4357
  have key : r ^ 2 - (a_p 4357 : ℝ) * r + ((4357 : ℕ) : ℝ) =
      (r - 117/2) ^ 2 + 3739/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (117 : ℝ)/2)]

-- p=4363: a_p=+118, 4p-a_p²=3528
theorem BSD_DegreeNonneg_p4363 : BSD_FrobeniusDegreeNonneg_OPEN 4363 := fun r => by
  have hap : (a_p 4363 : ℝ) = 118 := by exact_mod_cast BSD_ap_p4363
  have key : r ^ 2 - (a_p 4363 : ℝ) * r + ((4363 : ℕ) : ℝ) =
      (r - 118/2) ^ 2 + 3528/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (118 : ℝ)/2)]

-- p=4373: a_p=+96, 4p-a_p²=8276
theorem BSD_DegreeNonneg_p4373 : BSD_FrobeniusDegreeNonneg_OPEN 4373 := fun r => by
  have hap : (a_p 4373 : ℝ) = 96 := by exact_mod_cast BSD_ap_p4373
  have key : r ^ 2 - (a_p 4373 : ℝ) * r + ((4373 : ℕ) : ℝ) =
      (r - 96/2) ^ 2 + 8276/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (96 : ℝ)/2)]

-- p=4391: a_p=-108, 4p-a_p²=5900
theorem BSD_DegreeNonneg_p4391 : BSD_FrobeniusDegreeNonneg_OPEN 4391 := fun r => by
  have hap : (a_p 4391 : ℝ) = -108 := by exact_mod_cast BSD_ap_p4391
  have key : r ^ 2 - (a_p 4391 : ℝ) * r + ((4391 : ℕ) : ℝ) =
      (r + 108/2) ^ 2 + 5900/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (108 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p4289 : BSD_Hasse_OPEN 4289 :=
  BSD_hasse_of_degree_nonneg 4289 BSD_DegreeNonneg_p4289
theorem BSD_Hasse_OPEN_p4297 : BSD_Hasse_OPEN 4297 :=
  BSD_hasse_of_degree_nonneg 4297 BSD_DegreeNonneg_p4297
theorem BSD_Hasse_OPEN_p4327 : BSD_Hasse_OPEN 4327 :=
  BSD_hasse_of_degree_nonneg 4327 BSD_DegreeNonneg_p4327
theorem BSD_Hasse_OPEN_p4337 : BSD_Hasse_OPEN 4337 :=
  BSD_hasse_of_degree_nonneg 4337 BSD_DegreeNonneg_p4337
theorem BSD_Hasse_OPEN_p4339 : BSD_Hasse_OPEN 4339 :=
  BSD_hasse_of_degree_nonneg 4339 BSD_DegreeNonneg_p4339
theorem BSD_Hasse_OPEN_p4349 : BSD_Hasse_OPEN 4349 :=
  BSD_hasse_of_degree_nonneg 4349 BSD_DegreeNonneg_p4349
theorem BSD_Hasse_OPEN_p4357 : BSD_Hasse_OPEN 4357 :=
  BSD_hasse_of_degree_nonneg 4357 BSD_DegreeNonneg_p4357
theorem BSD_Hasse_OPEN_p4363 : BSD_Hasse_OPEN 4363 :=
  BSD_hasse_of_degree_nonneg 4363 BSD_DegreeNonneg_p4363
theorem BSD_Hasse_OPEN_p4373 : BSD_Hasse_OPEN 4373 :=
  BSD_hasse_of_degree_nonneg 4373 BSD_DegreeNonneg_p4373
theorem BSD_Hasse_OPEN_p4391 : BSD_Hasse_OPEN 4391 :=
  BSD_hasse_of_degree_nonneg 4391 BSD_DegreeNonneg_p4391

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p4289 : (a_p 4289 : ℝ) ^ 2 ≤ 4 * (4289 : ℝ) :=
  BSD_disc_from_deg_825 BSD_DegreeNonneg_p4289
theorem BSD_HasseBound_Disc_p4297 : (a_p 4297 : ℝ) ^ 2 ≤ 4 * (4297 : ℝ) :=
  BSD_disc_from_deg_825 BSD_DegreeNonneg_p4297
theorem BSD_HasseBound_Disc_p4327 : (a_p 4327 : ℝ) ^ 2 ≤ 4 * (4327 : ℝ) :=
  BSD_disc_from_deg_825 BSD_DegreeNonneg_p4327
theorem BSD_HasseBound_Disc_p4337 : (a_p 4337 : ℝ) ^ 2 ≤ 4 * (4337 : ℝ) :=
  BSD_disc_from_deg_825 BSD_DegreeNonneg_p4337
theorem BSD_HasseBound_Disc_p4339 : (a_p 4339 : ℝ) ^ 2 ≤ 4 * (4339 : ℝ) :=
  BSD_disc_from_deg_825 BSD_DegreeNonneg_p4339
theorem BSD_HasseBound_Disc_p4349 : (a_p 4349 : ℝ) ^ 2 ≤ 4 * (4349 : ℝ) :=
  BSD_disc_from_deg_825 BSD_DegreeNonneg_p4349
theorem BSD_HasseBound_Disc_p4357 : (a_p 4357 : ℝ) ^ 2 ≤ 4 * (4357 : ℝ) :=
  BSD_disc_from_deg_825 BSD_DegreeNonneg_p4357
theorem BSD_HasseBound_Disc_p4363 : (a_p 4363 : ℝ) ^ 2 ≤ 4 * (4363 : ℝ) :=
  BSD_disc_from_deg_825 BSD_DegreeNonneg_p4363
theorem BSD_HasseBound_Disc_p4373 : (a_p 4373 : ℝ) ^ 2 ≤ 4 * (4373 : ℝ) :=
  BSD_disc_from_deg_825 BSD_DegreeNonneg_p4373
theorem BSD_HasseBound_Disc_p4391 : (a_p 4391 : ℝ) ^ 2 ≤ 4 * (4391 : ℝ) :=
  BSD_disc_from_deg_825 BSD_DegreeNonneg_p4391

end Towers.BSD
/-
================================================================
Towers / BSD / BSD_Genesis813_CLOSED  (genesis-813)

HasseBridge Tier C: Hasse bounds for primes
3329..3391 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=3329: card=3272, a_p=+58, disc=-9952
  p=3331: card=3219, a_p=+113, disc=-555
  p=3343: card=3302, a_p=+42, disc=-11608
  p=3347: card=3291, a_p=+57, disc=-10139
  p=3359: card=3343, a_p=+17, disc=-13147
  p=3361: card=3452, a_p=-90, disc=-5344
  p=3371: card=3387, a_p=-15, disc=-13259
  p=3373: card=3438, a_p=-64, disc=-9396
  p=3389: card=3451, a_p=-61, disc=-9835
  p=3391: card=3344, a_p=+48, disc=-11260

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_813 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i813_p3329 : Fact (3329 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3331 : Fact (3331 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3343 : Fact (3343 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3347 : Fact (3347 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3359 : Fact (3359 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3361 : Fact (3361 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3371 : Fact (3371 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3373 : Fact (3373 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3389 : Fact (3389 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3391 : Fact (3391 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p3329 : (E143_Finset 3329).card = 3272 := by native_decide
theorem BSD_E143_card_p3331 : (E143_Finset 3331).card = 3219 := by native_decide
theorem BSD_E143_card_p3343 : (E143_Finset 3343).card = 3302 := by native_decide
theorem BSD_E143_card_p3347 : (E143_Finset 3347).card = 3291 := by native_decide
theorem BSD_E143_card_p3359 : (E143_Finset 3359).card = 3343 := by native_decide
theorem BSD_E143_card_p3361 : (E143_Finset 3361).card = 3452 := by native_decide
theorem BSD_E143_card_p3371 : (E143_Finset 3371).card = 3387 := by native_decide
theorem BSD_E143_card_p3373 : (E143_Finset 3373).card = 3438 := by native_decide
theorem BSD_E143_card_p3389 : (E143_Finset 3389).card = 3451 := by native_decide
theorem BSD_E143_card_p3391 : (E143_Finset 3391).card = 3344 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p3329 : a_p 3329 = (58 : ℤ) := by
  have h := BSD_E143_card_p3329; unfold a_p; omega
theorem BSD_ap_p3331 : a_p 3331 = (113 : ℤ) := by
  have h := BSD_E143_card_p3331; unfold a_p; omega
theorem BSD_ap_p3343 : a_p 3343 = (42 : ℤ) := by
  have h := BSD_E143_card_p3343; unfold a_p; omega
theorem BSD_ap_p3347 : a_p 3347 = (57 : ℤ) := by
  have h := BSD_E143_card_p3347; unfold a_p; omega
theorem BSD_ap_p3359 : a_p 3359 = (17 : ℤ) := by
  have h := BSD_E143_card_p3359; unfold a_p; omega
theorem BSD_ap_p3361 : a_p 3361 = (-90 : ℤ) := by
  have h := BSD_E143_card_p3361; unfold a_p; omega
theorem BSD_ap_p3371 : a_p 3371 = (-15 : ℤ) := by
  have h := BSD_E143_card_p3371; unfold a_p; omega
theorem BSD_ap_p3373 : a_p 3373 = (-64 : ℤ) := by
  have h := BSD_E143_card_p3373; unfold a_p; omega
theorem BSD_ap_p3389 : a_p 3389 = (-61 : ℤ) := by
  have h := BSD_E143_card_p3389; unfold a_p; omega
theorem BSD_ap_p3391 : a_p 3391 = (48 : ℤ) := by
  have h := BSD_E143_card_p3391; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=3329: a_p=+58, 4p-a_p²=9952
theorem BSD_DegreeNonneg_p3329 : BSD_FrobeniusDegreeNonneg_OPEN 3329 := fun r => by
  have hap : (a_p 3329 : ℝ) = 58 := by exact_mod_cast BSD_ap_p3329
  have key : r ^ 2 - (a_p 3329 : ℝ) * r + ((3329 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 9952/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

-- p=3331: a_p=+113, 4p-a_p²=555
theorem BSD_DegreeNonneg_p3331 : BSD_FrobeniusDegreeNonneg_OPEN 3331 := fun r => by
  have hap : (a_p 3331 : ℝ) = 113 := by exact_mod_cast BSD_ap_p3331
  have key : r ^ 2 - (a_p 3331 : ℝ) * r + ((3331 : ℕ) : ℝ) =
      (r - 113/2) ^ 2 + 555/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (113 : ℝ)/2)]

-- p=3343: a_p=+42, 4p-a_p²=11608
theorem BSD_DegreeNonneg_p3343 : BSD_FrobeniusDegreeNonneg_OPEN 3343 := fun r => by
  have hap : (a_p 3343 : ℝ) = 42 := by exact_mod_cast BSD_ap_p3343
  have key : r ^ 2 - (a_p 3343 : ℝ) * r + ((3343 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 11608/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

-- p=3347: a_p=+57, 4p-a_p²=10139
theorem BSD_DegreeNonneg_p3347 : BSD_FrobeniusDegreeNonneg_OPEN 3347 := fun r => by
  have hap : (a_p 3347 : ℝ) = 57 := by exact_mod_cast BSD_ap_p3347
  have key : r ^ 2 - (a_p 3347 : ℝ) * r + ((3347 : ℕ) : ℝ) =
      (r - 57/2) ^ 2 + 10139/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (57 : ℝ)/2)]

-- p=3359: a_p=+17, 4p-a_p²=13147
theorem BSD_DegreeNonneg_p3359 : BSD_FrobeniusDegreeNonneg_OPEN 3359 := fun r => by
  have hap : (a_p 3359 : ℝ) = 17 := by exact_mod_cast BSD_ap_p3359
  have key : r ^ 2 - (a_p 3359 : ℝ) * r + ((3359 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 13147/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

-- p=3361: a_p=-90, 4p-a_p²=5344
theorem BSD_DegreeNonneg_p3361 : BSD_FrobeniusDegreeNonneg_OPEN 3361 := fun r => by
  have hap : (a_p 3361 : ℝ) = -90 := by exact_mod_cast BSD_ap_p3361
  have key : r ^ 2 - (a_p 3361 : ℝ) * r + ((3361 : ℕ) : ℝ) =
      (r + 90/2) ^ 2 + 5344/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (90 : ℝ)/2)]

-- p=3371: a_p=-15, 4p-a_p²=13259
theorem BSD_DegreeNonneg_p3371 : BSD_FrobeniusDegreeNonneg_OPEN 3371 := fun r => by
  have hap : (a_p 3371 : ℝ) = -15 := by exact_mod_cast BSD_ap_p3371
  have key : r ^ 2 - (a_p 3371 : ℝ) * r + ((3371 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 13259/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

-- p=3373: a_p=-64, 4p-a_p²=9396
theorem BSD_DegreeNonneg_p3373 : BSD_FrobeniusDegreeNonneg_OPEN 3373 := fun r => by
  have hap : (a_p 3373 : ℝ) = -64 := by exact_mod_cast BSD_ap_p3373
  have key : r ^ 2 - (a_p 3373 : ℝ) * r + ((3373 : ℕ) : ℝ) =
      (r + 64/2) ^ 2 + 9396/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (64 : ℝ)/2)]

-- p=3389: a_p=-61, 4p-a_p²=9835
theorem BSD_DegreeNonneg_p3389 : BSD_FrobeniusDegreeNonneg_OPEN 3389 := fun r => by
  have hap : (a_p 3389 : ℝ) = -61 := by exact_mod_cast BSD_ap_p3389
  have key : r ^ 2 - (a_p 3389 : ℝ) * r + ((3389 : ℕ) : ℝ) =
      (r + 61/2) ^ 2 + 9835/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (61 : ℝ)/2)]

-- p=3391: a_p=+48, 4p-a_p²=11260
theorem BSD_DegreeNonneg_p3391 : BSD_FrobeniusDegreeNonneg_OPEN 3391 := fun r => by
  have hap : (a_p 3391 : ℝ) = 48 := by exact_mod_cast BSD_ap_p3391
  have key : r ^ 2 - (a_p 3391 : ℝ) * r + ((3391 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 11260/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p3329 : BSD_Hasse_OPEN 3329 :=
  BSD_hasse_of_degree_nonneg 3329 BSD_DegreeNonneg_p3329
theorem BSD_Hasse_OPEN_p3331 : BSD_Hasse_OPEN 3331 :=
  BSD_hasse_of_degree_nonneg 3331 BSD_DegreeNonneg_p3331
theorem BSD_Hasse_OPEN_p3343 : BSD_Hasse_OPEN 3343 :=
  BSD_hasse_of_degree_nonneg 3343 BSD_DegreeNonneg_p3343
theorem BSD_Hasse_OPEN_p3347 : BSD_Hasse_OPEN 3347 :=
  BSD_hasse_of_degree_nonneg 3347 BSD_DegreeNonneg_p3347
theorem BSD_Hasse_OPEN_p3359 : BSD_Hasse_OPEN 3359 :=
  BSD_hasse_of_degree_nonneg 3359 BSD_DegreeNonneg_p3359
theorem BSD_Hasse_OPEN_p3361 : BSD_Hasse_OPEN 3361 :=
  BSD_hasse_of_degree_nonneg 3361 BSD_DegreeNonneg_p3361
theorem BSD_Hasse_OPEN_p3371 : BSD_Hasse_OPEN 3371 :=
  BSD_hasse_of_degree_nonneg 3371 BSD_DegreeNonneg_p3371
theorem BSD_Hasse_OPEN_p3373 : BSD_Hasse_OPEN 3373 :=
  BSD_hasse_of_degree_nonneg 3373 BSD_DegreeNonneg_p3373
theorem BSD_Hasse_OPEN_p3389 : BSD_Hasse_OPEN 3389 :=
  BSD_hasse_of_degree_nonneg 3389 BSD_DegreeNonneg_p3389
theorem BSD_Hasse_OPEN_p3391 : BSD_Hasse_OPEN 3391 :=
  BSD_hasse_of_degree_nonneg 3391 BSD_DegreeNonneg_p3391

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p3329 : (a_p 3329 : ℝ) ^ 2 ≤ 4 * (3329 : ℝ) :=
  BSD_disc_from_deg_813 BSD_DegreeNonneg_p3329
theorem BSD_HasseBound_Disc_p3331 : (a_p 3331 : ℝ) ^ 2 ≤ 4 * (3331 : ℝ) :=
  BSD_disc_from_deg_813 BSD_DegreeNonneg_p3331
theorem BSD_HasseBound_Disc_p3343 : (a_p 3343 : ℝ) ^ 2 ≤ 4 * (3343 : ℝ) :=
  BSD_disc_from_deg_813 BSD_DegreeNonneg_p3343
theorem BSD_HasseBound_Disc_p3347 : (a_p 3347 : ℝ) ^ 2 ≤ 4 * (3347 : ℝ) :=
  BSD_disc_from_deg_813 BSD_DegreeNonneg_p3347
theorem BSD_HasseBound_Disc_p3359 : (a_p 3359 : ℝ) ^ 2 ≤ 4 * (3359 : ℝ) :=
  BSD_disc_from_deg_813 BSD_DegreeNonneg_p3359
theorem BSD_HasseBound_Disc_p3361 : (a_p 3361 : ℝ) ^ 2 ≤ 4 * (3361 : ℝ) :=
  BSD_disc_from_deg_813 BSD_DegreeNonneg_p3361
theorem BSD_HasseBound_Disc_p3371 : (a_p 3371 : ℝ) ^ 2 ≤ 4 * (3371 : ℝ) :=
  BSD_disc_from_deg_813 BSD_DegreeNonneg_p3371
theorem BSD_HasseBound_Disc_p3373 : (a_p 3373 : ℝ) ^ 2 ≤ 4 * (3373 : ℝ) :=
  BSD_disc_from_deg_813 BSD_DegreeNonneg_p3373
theorem BSD_HasseBound_Disc_p3389 : (a_p 3389 : ℝ) ^ 2 ≤ 4 * (3389 : ℝ) :=
  BSD_disc_from_deg_813 BSD_DegreeNonneg_p3389
theorem BSD_HasseBound_Disc_p3391 : (a_p 3391 : ℝ) ^ 2 ≤ 4 * (3391 : ℝ) :=
  BSD_disc_from_deg_813 BSD_DegreeNonneg_p3391

end Towers.BSD
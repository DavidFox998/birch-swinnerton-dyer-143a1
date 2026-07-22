/-
================================================================
Towers / BSD / BSD_Genesis824_CLOSED  (genesis-824)

HasseBridge Tier C: Hasse bounds for primes
4229..4283 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=4229: card=4245, a_p=-15, disc=-16691
  p=4231: card=4334, a_p=-102, disc=-6520
  p=4241: card=4300, a_p=-58, disc=-13600
  p=4243: card=4218, a_p=+26, disc=-16296
  p=4253: card=4308, a_p=-54, disc=-14096
  p=4259: card=4188, a_p=+72, disc=-11852
  p=4261: card=4231, a_p=+31, disc=-16083
  p=4271: card=4347, a_p=-75, disc=-11459
  p=4273: card=4223, a_p=+51, disc=-14491
  p=4283: card=4271, a_p=+13, disc=-16963

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_824 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i824_p4229 : Fact (4229 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4231 : Fact (4231 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4241 : Fact (4241 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4243 : Fact (4243 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4253 : Fact (4253 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4259 : Fact (4259 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4261 : Fact (4261 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4271 : Fact (4271 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4273 : Fact (4273 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4283 : Fact (4283 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p4229 : (E143_Finset 4229).card = 4245 := by native_decide
theorem BSD_E143_card_p4231 : (E143_Finset 4231).card = 4334 := by native_decide
theorem BSD_E143_card_p4241 : (E143_Finset 4241).card = 4300 := by native_decide
theorem BSD_E143_card_p4243 : (E143_Finset 4243).card = 4218 := by native_decide
theorem BSD_E143_card_p4253 : (E143_Finset 4253).card = 4308 := by native_decide
theorem BSD_E143_card_p4259 : (E143_Finset 4259).card = 4188 := by native_decide
theorem BSD_E143_card_p4261 : (E143_Finset 4261).card = 4231 := by native_decide
theorem BSD_E143_card_p4271 : (E143_Finset 4271).card = 4347 := by native_decide
theorem BSD_E143_card_p4273 : (E143_Finset 4273).card = 4223 := by native_decide
theorem BSD_E143_card_p4283 : (E143_Finset 4283).card = 4271 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p4229 : a_p 4229 = (-15 : ℤ) := by
  have h := BSD_E143_card_p4229; unfold a_p; omega
theorem BSD_ap_p4231 : a_p 4231 = (-102 : ℤ) := by
  have h := BSD_E143_card_p4231; unfold a_p; omega
theorem BSD_ap_p4241 : a_p 4241 = (-58 : ℤ) := by
  have h := BSD_E143_card_p4241; unfold a_p; omega
theorem BSD_ap_p4243 : a_p 4243 = (26 : ℤ) := by
  have h := BSD_E143_card_p4243; unfold a_p; omega
theorem BSD_ap_p4253 : a_p 4253 = (-54 : ℤ) := by
  have h := BSD_E143_card_p4253; unfold a_p; omega
theorem BSD_ap_p4259 : a_p 4259 = (72 : ℤ) := by
  have h := BSD_E143_card_p4259; unfold a_p; omega
theorem BSD_ap_p4261 : a_p 4261 = (31 : ℤ) := by
  have h := BSD_E143_card_p4261; unfold a_p; omega
theorem BSD_ap_p4271 : a_p 4271 = (-75 : ℤ) := by
  have h := BSD_E143_card_p4271; unfold a_p; omega
theorem BSD_ap_p4273 : a_p 4273 = (51 : ℤ) := by
  have h := BSD_E143_card_p4273; unfold a_p; omega
theorem BSD_ap_p4283 : a_p 4283 = (13 : ℤ) := by
  have h := BSD_E143_card_p4283; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=4229: a_p=-15, 4p-a_p²=16691
theorem BSD_DegreeNonneg_p4229 : BSD_FrobeniusDegreeNonneg_OPEN 4229 := fun r => by
  have hap : (a_p 4229 : ℝ) = -15 := by exact_mod_cast BSD_ap_p4229
  have key : r ^ 2 - (a_p 4229 : ℝ) * r + ((4229 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 16691/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

-- p=4231: a_p=-102, 4p-a_p²=6520
theorem BSD_DegreeNonneg_p4231 : BSD_FrobeniusDegreeNonneg_OPEN 4231 := fun r => by
  have hap : (a_p 4231 : ℝ) = -102 := by exact_mod_cast BSD_ap_p4231
  have key : r ^ 2 - (a_p 4231 : ℝ) * r + ((4231 : ℕ) : ℝ) =
      (r + 102/2) ^ 2 + 6520/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (102 : ℝ)/2)]

-- p=4241: a_p=-58, 4p-a_p²=13600
theorem BSD_DegreeNonneg_p4241 : BSD_FrobeniusDegreeNonneg_OPEN 4241 := fun r => by
  have hap : (a_p 4241 : ℝ) = -58 := by exact_mod_cast BSD_ap_p4241
  have key : r ^ 2 - (a_p 4241 : ℝ) * r + ((4241 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 13600/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

-- p=4243: a_p=+26, 4p-a_p²=16296
theorem BSD_DegreeNonneg_p4243 : BSD_FrobeniusDegreeNonneg_OPEN 4243 := fun r => by
  have hap : (a_p 4243 : ℝ) = 26 := by exact_mod_cast BSD_ap_p4243
  have key : r ^ 2 - (a_p 4243 : ℝ) * r + ((4243 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 16296/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

-- p=4253: a_p=-54, 4p-a_p²=14096
theorem BSD_DegreeNonneg_p4253 : BSD_FrobeniusDegreeNonneg_OPEN 4253 := fun r => by
  have hap : (a_p 4253 : ℝ) = -54 := by exact_mod_cast BSD_ap_p4253
  have key : r ^ 2 - (a_p 4253 : ℝ) * r + ((4253 : ℕ) : ℝ) =
      (r + 54/2) ^ 2 + 14096/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (54 : ℝ)/2)]

-- p=4259: a_p=+72, 4p-a_p²=11852
theorem BSD_DegreeNonneg_p4259 : BSD_FrobeniusDegreeNonneg_OPEN 4259 := fun r => by
  have hap : (a_p 4259 : ℝ) = 72 := by exact_mod_cast BSD_ap_p4259
  have key : r ^ 2 - (a_p 4259 : ℝ) * r + ((4259 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 11852/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

-- p=4261: a_p=+31, 4p-a_p²=16083
theorem BSD_DegreeNonneg_p4261 : BSD_FrobeniusDegreeNonneg_OPEN 4261 := fun r => by
  have hap : (a_p 4261 : ℝ) = 31 := by exact_mod_cast BSD_ap_p4261
  have key : r ^ 2 - (a_p 4261 : ℝ) * r + ((4261 : ℕ) : ℝ) =
      (r - 31/2) ^ 2 + 16083/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (31 : ℝ)/2)]

-- p=4271: a_p=-75, 4p-a_p²=11459
theorem BSD_DegreeNonneg_p4271 : BSD_FrobeniusDegreeNonneg_OPEN 4271 := fun r => by
  have hap : (a_p 4271 : ℝ) = -75 := by exact_mod_cast BSD_ap_p4271
  have key : r ^ 2 - (a_p 4271 : ℝ) * r + ((4271 : ℕ) : ℝ) =
      (r + 75/2) ^ 2 + 11459/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (75 : ℝ)/2)]

-- p=4273: a_p=+51, 4p-a_p²=14491
theorem BSD_DegreeNonneg_p4273 : BSD_FrobeniusDegreeNonneg_OPEN 4273 := fun r => by
  have hap : (a_p 4273 : ℝ) = 51 := by exact_mod_cast BSD_ap_p4273
  have key : r ^ 2 - (a_p 4273 : ℝ) * r + ((4273 : ℕ) : ℝ) =
      (r - 51/2) ^ 2 + 14491/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (51 : ℝ)/2)]

-- p=4283: a_p=+13, 4p-a_p²=16963
theorem BSD_DegreeNonneg_p4283 : BSD_FrobeniusDegreeNonneg_OPEN 4283 := fun r => by
  have hap : (a_p 4283 : ℝ) = 13 := by exact_mod_cast BSD_ap_p4283
  have key : r ^ 2 - (a_p 4283 : ℝ) * r + ((4283 : ℕ) : ℝ) =
      (r - 13/2) ^ 2 + 16963/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (13 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p4229 : BSD_Hasse_OPEN 4229 :=
  BSD_hasse_of_degree_nonneg 4229 BSD_DegreeNonneg_p4229
theorem BSD_Hasse_OPEN_p4231 : BSD_Hasse_OPEN 4231 :=
  BSD_hasse_of_degree_nonneg 4231 BSD_DegreeNonneg_p4231
theorem BSD_Hasse_OPEN_p4241 : BSD_Hasse_OPEN 4241 :=
  BSD_hasse_of_degree_nonneg 4241 BSD_DegreeNonneg_p4241
theorem BSD_Hasse_OPEN_p4243 : BSD_Hasse_OPEN 4243 :=
  BSD_hasse_of_degree_nonneg 4243 BSD_DegreeNonneg_p4243
theorem BSD_Hasse_OPEN_p4253 : BSD_Hasse_OPEN 4253 :=
  BSD_hasse_of_degree_nonneg 4253 BSD_DegreeNonneg_p4253
theorem BSD_Hasse_OPEN_p4259 : BSD_Hasse_OPEN 4259 :=
  BSD_hasse_of_degree_nonneg 4259 BSD_DegreeNonneg_p4259
theorem BSD_Hasse_OPEN_p4261 : BSD_Hasse_OPEN 4261 :=
  BSD_hasse_of_degree_nonneg 4261 BSD_DegreeNonneg_p4261
theorem BSD_Hasse_OPEN_p4271 : BSD_Hasse_OPEN 4271 :=
  BSD_hasse_of_degree_nonneg 4271 BSD_DegreeNonneg_p4271
theorem BSD_Hasse_OPEN_p4273 : BSD_Hasse_OPEN 4273 :=
  BSD_hasse_of_degree_nonneg 4273 BSD_DegreeNonneg_p4273
theorem BSD_Hasse_OPEN_p4283 : BSD_Hasse_OPEN 4283 :=
  BSD_hasse_of_degree_nonneg 4283 BSD_DegreeNonneg_p4283

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p4229 : (a_p 4229 : ℝ) ^ 2 ≤ 4 * (4229 : ℝ) :=
  BSD_disc_from_deg_824 BSD_DegreeNonneg_p4229
theorem BSD_HasseBound_Disc_p4231 : (a_p 4231 : ℝ) ^ 2 ≤ 4 * (4231 : ℝ) :=
  BSD_disc_from_deg_824 BSD_DegreeNonneg_p4231
theorem BSD_HasseBound_Disc_p4241 : (a_p 4241 : ℝ) ^ 2 ≤ 4 * (4241 : ℝ) :=
  BSD_disc_from_deg_824 BSD_DegreeNonneg_p4241
theorem BSD_HasseBound_Disc_p4243 : (a_p 4243 : ℝ) ^ 2 ≤ 4 * (4243 : ℝ) :=
  BSD_disc_from_deg_824 BSD_DegreeNonneg_p4243
theorem BSD_HasseBound_Disc_p4253 : (a_p 4253 : ℝ) ^ 2 ≤ 4 * (4253 : ℝ) :=
  BSD_disc_from_deg_824 BSD_DegreeNonneg_p4253
theorem BSD_HasseBound_Disc_p4259 : (a_p 4259 : ℝ) ^ 2 ≤ 4 * (4259 : ℝ) :=
  BSD_disc_from_deg_824 BSD_DegreeNonneg_p4259
theorem BSD_HasseBound_Disc_p4261 : (a_p 4261 : ℝ) ^ 2 ≤ 4 * (4261 : ℝ) :=
  BSD_disc_from_deg_824 BSD_DegreeNonneg_p4261
theorem BSD_HasseBound_Disc_p4271 : (a_p 4271 : ℝ) ^ 2 ≤ 4 * (4271 : ℝ) :=
  BSD_disc_from_deg_824 BSD_DegreeNonneg_p4271
theorem BSD_HasseBound_Disc_p4273 : (a_p 4273 : ℝ) ^ 2 ≤ 4 * (4273 : ℝ) :=
  BSD_disc_from_deg_824 BSD_DegreeNonneg_p4273
theorem BSD_HasseBound_Disc_p4283 : (a_p 4283 : ℝ) ^ 2 ≤ 4 * (4283 : ℝ) :=
  BSD_disc_from_deg_824 BSD_DegreeNonneg_p4283

end Towers.BSD
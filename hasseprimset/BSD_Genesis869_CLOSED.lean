/-
================================================================
Towers / BSD / BSD_Genesis869_CLOSED  (genesis-869)

HasseBridge Tier C: Hasse bounds for primes
8209..8273 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=8209: card=8151, a_p=+59, disc=-29355
  p=8219: card=8198, a_p=+22, disc=-32392
  p=8221: card=8207, a_p=+15, disc=-32659
  p=8231: card=8139, a_p=+93, disc=-24275
  p=8233: card=8245, a_p=-11, disc=-32811
  p=8237: card=8109, a_p=+129, disc=-16307
  p=8243: card=8265, a_p=-21, disc=-32531
  p=8263: card=8148, a_p=+116, disc=-19596
  p=8269: card=8272, a_p=-2, disc=-33072
  p=8273: card=8416, a_p=-142, disc=-12928

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_869 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i869_p8209 : Fact (8209 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8219 : Fact (8219 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8221 : Fact (8221 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8231 : Fact (8231 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8233 : Fact (8233 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8237 : Fact (8237 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8243 : Fact (8243 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8263 : Fact (8263 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8269 : Fact (8269 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8273 : Fact (8273 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p8209 : (E143_Finset 8209).card = 8151 := by native_decide
theorem BSD_E143_card_p8219 : (E143_Finset 8219).card = 8198 := by native_decide
theorem BSD_E143_card_p8221 : (E143_Finset 8221).card = 8207 := by native_decide
theorem BSD_E143_card_p8231 : (E143_Finset 8231).card = 8139 := by native_decide
theorem BSD_E143_card_p8233 : (E143_Finset 8233).card = 8245 := by native_decide
theorem BSD_E143_card_p8237 : (E143_Finset 8237).card = 8109 := by native_decide
theorem BSD_E143_card_p8243 : (E143_Finset 8243).card = 8265 := by native_decide
theorem BSD_E143_card_p8263 : (E143_Finset 8263).card = 8148 := by native_decide
theorem BSD_E143_card_p8269 : (E143_Finset 8269).card = 8272 := by native_decide
theorem BSD_E143_card_p8273 : (E143_Finset 8273).card = 8416 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p8209 : a_p 8209 = (59 : ℤ) := by
  have h := BSD_E143_card_p8209; unfold a_p; omega
theorem BSD_ap_p8219 : a_p 8219 = (22 : ℤ) := by
  have h := BSD_E143_card_p8219; unfold a_p; omega
theorem BSD_ap_p8221 : a_p 8221 = (15 : ℤ) := by
  have h := BSD_E143_card_p8221; unfold a_p; omega
theorem BSD_ap_p8231 : a_p 8231 = (93 : ℤ) := by
  have h := BSD_E143_card_p8231; unfold a_p; omega
theorem BSD_ap_p8233 : a_p 8233 = (-11 : ℤ) := by
  have h := BSD_E143_card_p8233; unfold a_p; omega
theorem BSD_ap_p8237 : a_p 8237 = (129 : ℤ) := by
  have h := BSD_E143_card_p8237; unfold a_p; omega
theorem BSD_ap_p8243 : a_p 8243 = (-21 : ℤ) := by
  have h := BSD_E143_card_p8243; unfold a_p; omega
theorem BSD_ap_p8263 : a_p 8263 = (116 : ℤ) := by
  have h := BSD_E143_card_p8263; unfold a_p; omega
theorem BSD_ap_p8269 : a_p 8269 = (-2 : ℤ) := by
  have h := BSD_E143_card_p8269; unfold a_p; omega
theorem BSD_ap_p8273 : a_p 8273 = (-142 : ℤ) := by
  have h := BSD_E143_card_p8273; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=8209: a_p=+59, 4p-a_p²=29355
theorem BSD_DegreeNonneg_p8209 : BSD_FrobeniusDegreeNonneg_OPEN 8209 := fun r => by
  have hap : (a_p 8209 : ℝ) = 59 := by exact_mod_cast BSD_ap_p8209
  have key : r ^ 2 - (a_p 8209 : ℝ) * r + ((8209 : ℕ) : ℝ) =
      (r - 59/2) ^ 2 + 29355/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (59 : ℝ)/2)]

-- p=8219: a_p=+22, 4p-a_p²=32392
theorem BSD_DegreeNonneg_p8219 : BSD_FrobeniusDegreeNonneg_OPEN 8219 := fun r => by
  have hap : (a_p 8219 : ℝ) = 22 := by exact_mod_cast BSD_ap_p8219
  have key : r ^ 2 - (a_p 8219 : ℝ) * r + ((8219 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 32392/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

-- p=8221: a_p=+15, 4p-a_p²=32659
theorem BSD_DegreeNonneg_p8221 : BSD_FrobeniusDegreeNonneg_OPEN 8221 := fun r => by
  have hap : (a_p 8221 : ℝ) = 15 := by exact_mod_cast BSD_ap_p8221
  have key : r ^ 2 - (a_p 8221 : ℝ) * r + ((8221 : ℕ) : ℝ) =
      (r - 15/2) ^ 2 + 32659/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (15 : ℝ)/2)]

-- p=8231: a_p=+93, 4p-a_p²=24275
theorem BSD_DegreeNonneg_p8231 : BSD_FrobeniusDegreeNonneg_OPEN 8231 := fun r => by
  have hap : (a_p 8231 : ℝ) = 93 := by exact_mod_cast BSD_ap_p8231
  have key : r ^ 2 - (a_p 8231 : ℝ) * r + ((8231 : ℕ) : ℝ) =
      (r - 93/2) ^ 2 + 24275/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (93 : ℝ)/2)]

-- p=8233: a_p=-11, 4p-a_p²=32811
theorem BSD_DegreeNonneg_p8233 : BSD_FrobeniusDegreeNonneg_OPEN 8233 := fun r => by
  have hap : (a_p 8233 : ℝ) = -11 := by exact_mod_cast BSD_ap_p8233
  have key : r ^ 2 - (a_p 8233 : ℝ) * r + ((8233 : ℕ) : ℝ) =
      (r + 11/2) ^ 2 + 32811/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (11 : ℝ)/2)]

-- p=8237: a_p=+129, 4p-a_p²=16307
theorem BSD_DegreeNonneg_p8237 : BSD_FrobeniusDegreeNonneg_OPEN 8237 := fun r => by
  have hap : (a_p 8237 : ℝ) = 129 := by exact_mod_cast BSD_ap_p8237
  have key : r ^ 2 - (a_p 8237 : ℝ) * r + ((8237 : ℕ) : ℝ) =
      (r - 129/2) ^ 2 + 16307/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (129 : ℝ)/2)]

-- p=8243: a_p=-21, 4p-a_p²=32531
theorem BSD_DegreeNonneg_p8243 : BSD_FrobeniusDegreeNonneg_OPEN 8243 := fun r => by
  have hap : (a_p 8243 : ℝ) = -21 := by exact_mod_cast BSD_ap_p8243
  have key : r ^ 2 - (a_p 8243 : ℝ) * r + ((8243 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 32531/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

-- p=8263: a_p=+116, 4p-a_p²=19596
theorem BSD_DegreeNonneg_p8263 : BSD_FrobeniusDegreeNonneg_OPEN 8263 := fun r => by
  have hap : (a_p 8263 : ℝ) = 116 := by exact_mod_cast BSD_ap_p8263
  have key : r ^ 2 - (a_p 8263 : ℝ) * r + ((8263 : ℕ) : ℝ) =
      (r - 116/2) ^ 2 + 19596/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (116 : ℝ)/2)]

-- p=8269: a_p=-2, 4p-a_p²=33072
theorem BSD_DegreeNonneg_p8269 : BSD_FrobeniusDegreeNonneg_OPEN 8269 := fun r => by
  have hap : (a_p 8269 : ℝ) = -2 := by exact_mod_cast BSD_ap_p8269
  have key : r ^ 2 - (a_p 8269 : ℝ) * r + ((8269 : ℕ) : ℝ) =
      (r + 2/2) ^ 2 + 33072/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (2 : ℝ)/2)]

-- p=8273: a_p=-142, 4p-a_p²=12928
theorem BSD_DegreeNonneg_p8273 : BSD_FrobeniusDegreeNonneg_OPEN 8273 := fun r => by
  have hap : (a_p 8273 : ℝ) = -142 := by exact_mod_cast BSD_ap_p8273
  have key : r ^ 2 - (a_p 8273 : ℝ) * r + ((8273 : ℕ) : ℝ) =
      (r + 142/2) ^ 2 + 12928/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (142 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p8209 : BSD_Hasse_OPEN 8209 :=
  BSD_hasse_of_degree_nonneg 8209 BSD_DegreeNonneg_p8209
theorem BSD_Hasse_OPEN_p8219 : BSD_Hasse_OPEN 8219 :=
  BSD_hasse_of_degree_nonneg 8219 BSD_DegreeNonneg_p8219
theorem BSD_Hasse_OPEN_p8221 : BSD_Hasse_OPEN 8221 :=
  BSD_hasse_of_degree_nonneg 8221 BSD_DegreeNonneg_p8221
theorem BSD_Hasse_OPEN_p8231 : BSD_Hasse_OPEN 8231 :=
  BSD_hasse_of_degree_nonneg 8231 BSD_DegreeNonneg_p8231
theorem BSD_Hasse_OPEN_p8233 : BSD_Hasse_OPEN 8233 :=
  BSD_hasse_of_degree_nonneg 8233 BSD_DegreeNonneg_p8233
theorem BSD_Hasse_OPEN_p8237 : BSD_Hasse_OPEN 8237 :=
  BSD_hasse_of_degree_nonneg 8237 BSD_DegreeNonneg_p8237
theorem BSD_Hasse_OPEN_p8243 : BSD_Hasse_OPEN 8243 :=
  BSD_hasse_of_degree_nonneg 8243 BSD_DegreeNonneg_p8243
theorem BSD_Hasse_OPEN_p8263 : BSD_Hasse_OPEN 8263 :=
  BSD_hasse_of_degree_nonneg 8263 BSD_DegreeNonneg_p8263
theorem BSD_Hasse_OPEN_p8269 : BSD_Hasse_OPEN 8269 :=
  BSD_hasse_of_degree_nonneg 8269 BSD_DegreeNonneg_p8269
theorem BSD_Hasse_OPEN_p8273 : BSD_Hasse_OPEN 8273 :=
  BSD_hasse_of_degree_nonneg 8273 BSD_DegreeNonneg_p8273

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p8209 : (a_p 8209 : ℝ) ^ 2 ≤ 4 * (8209 : ℝ) :=
  BSD_disc_from_deg_869 BSD_DegreeNonneg_p8209
theorem BSD_HasseBound_Disc_p8219 : (a_p 8219 : ℝ) ^ 2 ≤ 4 * (8219 : ℝ) :=
  BSD_disc_from_deg_869 BSD_DegreeNonneg_p8219
theorem BSD_HasseBound_Disc_p8221 : (a_p 8221 : ℝ) ^ 2 ≤ 4 * (8221 : ℝ) :=
  BSD_disc_from_deg_869 BSD_DegreeNonneg_p8221
theorem BSD_HasseBound_Disc_p8231 : (a_p 8231 : ℝ) ^ 2 ≤ 4 * (8231 : ℝ) :=
  BSD_disc_from_deg_869 BSD_DegreeNonneg_p8231
theorem BSD_HasseBound_Disc_p8233 : (a_p 8233 : ℝ) ^ 2 ≤ 4 * (8233 : ℝ) :=
  BSD_disc_from_deg_869 BSD_DegreeNonneg_p8233
theorem BSD_HasseBound_Disc_p8237 : (a_p 8237 : ℝ) ^ 2 ≤ 4 * (8237 : ℝ) :=
  BSD_disc_from_deg_869 BSD_DegreeNonneg_p8237
theorem BSD_HasseBound_Disc_p8243 : (a_p 8243 : ℝ) ^ 2 ≤ 4 * (8243 : ℝ) :=
  BSD_disc_from_deg_869 BSD_DegreeNonneg_p8243
theorem BSD_HasseBound_Disc_p8263 : (a_p 8263 : ℝ) ^ 2 ≤ 4 * (8263 : ℝ) :=
  BSD_disc_from_deg_869 BSD_DegreeNonneg_p8263
theorem BSD_HasseBound_Disc_p8269 : (a_p 8269 : ℝ) ^ 2 ≤ 4 * (8269 : ℝ) :=
  BSD_disc_from_deg_869 BSD_DegreeNonneg_p8269
theorem BSD_HasseBound_Disc_p8273 : (a_p 8273 : ℝ) ^ 2 ≤ 4 * (8273 : ℝ) :=
  BSD_disc_from_deg_869 BSD_DegreeNonneg_p8273

end Towers.BSD
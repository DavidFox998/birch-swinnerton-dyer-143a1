/-
================================================================
Towers / BSD / BSD_Genesis880_CLOSED  (genesis-880)

HasseBridge Tier C: Hasse bounds for primes
9187..9277 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=9187: card=9330, a_p=-142, disc=-16584
  p=9199: card=9184, a_p=+16, disc=-36540
  p=9203: card=9160, a_p=+44, disc=-34876
  p=9209: card=9222, a_p=-12, disc=-36692
  p=9221: card=9301, a_p=-79, disc=-30643
  p=9227: card=9228, a_p=+0, disc=-36908
  p=9239: card=9228, a_p=+12, disc=-36812
  p=9241: card=9281, a_p=-39, disc=-35443
  p=9257: card=9140, a_p=+118, disc=-23104
  p=9277: card=9261, a_p=+17, disc=-36819

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_880 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i880_p9187 : Fact (9187 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9199 : Fact (9199 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9203 : Fact (9203 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9209 : Fact (9209 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9221 : Fact (9221 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9227 : Fact (9227 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9239 : Fact (9239 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9241 : Fact (9241 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9257 : Fact (9257 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9277 : Fact (9277 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p9187 : (E143_Finset 9187).card = 9330 := by native_decide
theorem BSD_E143_card_p9199 : (E143_Finset 9199).card = 9184 := by native_decide
theorem BSD_E143_card_p9203 : (E143_Finset 9203).card = 9160 := by native_decide
theorem BSD_E143_card_p9209 : (E143_Finset 9209).card = 9222 := by native_decide
theorem BSD_E143_card_p9221 : (E143_Finset 9221).card = 9301 := by native_decide
theorem BSD_E143_card_p9227 : (E143_Finset 9227).card = 9228 := by native_decide
theorem BSD_E143_card_p9239 : (E143_Finset 9239).card = 9228 := by native_decide
theorem BSD_E143_card_p9241 : (E143_Finset 9241).card = 9281 := by native_decide
theorem BSD_E143_card_p9257 : (E143_Finset 9257).card = 9140 := by native_decide
theorem BSD_E143_card_p9277 : (E143_Finset 9277).card = 9261 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p9187 : a_p 9187 = (-142 : ℤ) := by
  have h := BSD_E143_card_p9187; unfold a_p; omega
theorem BSD_ap_p9199 : a_p 9199 = (16 : ℤ) := by
  have h := BSD_E143_card_p9199; unfold a_p; omega
theorem BSD_ap_p9203 : a_p 9203 = (44 : ℤ) := by
  have h := BSD_E143_card_p9203; unfold a_p; omega
theorem BSD_ap_p9209 : a_p 9209 = (-12 : ℤ) := by
  have h := BSD_E143_card_p9209; unfold a_p; omega
theorem BSD_ap_p9221 : a_p 9221 = (-79 : ℤ) := by
  have h := BSD_E143_card_p9221; unfold a_p; omega
theorem BSD_ap_p9227 : a_p 9227 = (0 : ℤ) := by
  have h := BSD_E143_card_p9227; unfold a_p; omega
theorem BSD_ap_p9239 : a_p 9239 = (12 : ℤ) := by
  have h := BSD_E143_card_p9239; unfold a_p; omega
theorem BSD_ap_p9241 : a_p 9241 = (-39 : ℤ) := by
  have h := BSD_E143_card_p9241; unfold a_p; omega
theorem BSD_ap_p9257 : a_p 9257 = (118 : ℤ) := by
  have h := BSD_E143_card_p9257; unfold a_p; omega
theorem BSD_ap_p9277 : a_p 9277 = (17 : ℤ) := by
  have h := BSD_E143_card_p9277; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=9187: a_p=-142, 4p-a_p²=16584
theorem BSD_DegreeNonneg_p9187 : BSD_FrobeniusDegreeNonneg_OPEN 9187 := fun r => by
  have hap : (a_p 9187 : ℝ) = -142 := by exact_mod_cast BSD_ap_p9187
  have key : r ^ 2 - (a_p 9187 : ℝ) * r + ((9187 : ℕ) : ℝ) =
      (r + 142/2) ^ 2 + 16584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (142 : ℝ)/2)]

-- p=9199: a_p=+16, 4p-a_p²=36540
theorem BSD_DegreeNonneg_p9199 : BSD_FrobeniusDegreeNonneg_OPEN 9199 := fun r => by
  have hap : (a_p 9199 : ℝ) = 16 := by exact_mod_cast BSD_ap_p9199
  have key : r ^ 2 - (a_p 9199 : ℝ) * r + ((9199 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 36540/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

-- p=9203: a_p=+44, 4p-a_p²=34876
theorem BSD_DegreeNonneg_p9203 : BSD_FrobeniusDegreeNonneg_OPEN 9203 := fun r => by
  have hap : (a_p 9203 : ℝ) = 44 := by exact_mod_cast BSD_ap_p9203
  have key : r ^ 2 - (a_p 9203 : ℝ) * r + ((9203 : ℕ) : ℝ) =
      (r - 44/2) ^ 2 + 34876/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (44 : ℝ)/2)]

-- p=9209: a_p=-12, 4p-a_p²=36692
theorem BSD_DegreeNonneg_p9209 : BSD_FrobeniusDegreeNonneg_OPEN 9209 := fun r => by
  have hap : (a_p 9209 : ℝ) = -12 := by exact_mod_cast BSD_ap_p9209
  have key : r ^ 2 - (a_p 9209 : ℝ) * r + ((9209 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 36692/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

-- p=9221: a_p=-79, 4p-a_p²=30643
theorem BSD_DegreeNonneg_p9221 : BSD_FrobeniusDegreeNonneg_OPEN 9221 := fun r => by
  have hap : (a_p 9221 : ℝ) = -79 := by exact_mod_cast BSD_ap_p9221
  have key : r ^ 2 - (a_p 9221 : ℝ) * r + ((9221 : ℕ) : ℝ) =
      (r + 79/2) ^ 2 + 30643/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (79 : ℝ)/2)]

-- p=9227: a_p=+0, 4p-a_p²=36908
theorem BSD_DegreeNonneg_p9227 : BSD_FrobeniusDegreeNonneg_OPEN 9227 := fun r => by
  have hap : (a_p 9227 : ℝ) = 0 := by exact_mod_cast BSD_ap_p9227
  have key : r ^ 2 - (a_p 9227 : ℝ) * r + ((9227 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 36908/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

-- p=9239: a_p=+12, 4p-a_p²=36812
theorem BSD_DegreeNonneg_p9239 : BSD_FrobeniusDegreeNonneg_OPEN 9239 := fun r => by
  have hap : (a_p 9239 : ℝ) = 12 := by exact_mod_cast BSD_ap_p9239
  have key : r ^ 2 - (a_p 9239 : ℝ) * r + ((9239 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 36812/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

-- p=9241: a_p=-39, 4p-a_p²=35443
theorem BSD_DegreeNonneg_p9241 : BSD_FrobeniusDegreeNonneg_OPEN 9241 := fun r => by
  have hap : (a_p 9241 : ℝ) = -39 := by exact_mod_cast BSD_ap_p9241
  have key : r ^ 2 - (a_p 9241 : ℝ) * r + ((9241 : ℕ) : ℝ) =
      (r + 39/2) ^ 2 + 35443/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (39 : ℝ)/2)]

-- p=9257: a_p=+118, 4p-a_p²=23104
theorem BSD_DegreeNonneg_p9257 : BSD_FrobeniusDegreeNonneg_OPEN 9257 := fun r => by
  have hap : (a_p 9257 : ℝ) = 118 := by exact_mod_cast BSD_ap_p9257
  have key : r ^ 2 - (a_p 9257 : ℝ) * r + ((9257 : ℕ) : ℝ) =
      (r - 118/2) ^ 2 + 23104/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (118 : ℝ)/2)]

-- p=9277: a_p=+17, 4p-a_p²=36819
theorem BSD_DegreeNonneg_p9277 : BSD_FrobeniusDegreeNonneg_OPEN 9277 := fun r => by
  have hap : (a_p 9277 : ℝ) = 17 := by exact_mod_cast BSD_ap_p9277
  have key : r ^ 2 - (a_p 9277 : ℝ) * r + ((9277 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 36819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p9187 : BSD_Hasse_OPEN 9187 :=
  BSD_hasse_of_degree_nonneg 9187 BSD_DegreeNonneg_p9187
theorem BSD_Hasse_OPEN_p9199 : BSD_Hasse_OPEN 9199 :=
  BSD_hasse_of_degree_nonneg 9199 BSD_DegreeNonneg_p9199
theorem BSD_Hasse_OPEN_p9203 : BSD_Hasse_OPEN 9203 :=
  BSD_hasse_of_degree_nonneg 9203 BSD_DegreeNonneg_p9203
theorem BSD_Hasse_OPEN_p9209 : BSD_Hasse_OPEN 9209 :=
  BSD_hasse_of_degree_nonneg 9209 BSD_DegreeNonneg_p9209
theorem BSD_Hasse_OPEN_p9221 : BSD_Hasse_OPEN 9221 :=
  BSD_hasse_of_degree_nonneg 9221 BSD_DegreeNonneg_p9221
theorem BSD_Hasse_OPEN_p9227 : BSD_Hasse_OPEN 9227 :=
  BSD_hasse_of_degree_nonneg 9227 BSD_DegreeNonneg_p9227
theorem BSD_Hasse_OPEN_p9239 : BSD_Hasse_OPEN 9239 :=
  BSD_hasse_of_degree_nonneg 9239 BSD_DegreeNonneg_p9239
theorem BSD_Hasse_OPEN_p9241 : BSD_Hasse_OPEN 9241 :=
  BSD_hasse_of_degree_nonneg 9241 BSD_DegreeNonneg_p9241
theorem BSD_Hasse_OPEN_p9257 : BSD_Hasse_OPEN 9257 :=
  BSD_hasse_of_degree_nonneg 9257 BSD_DegreeNonneg_p9257
theorem BSD_Hasse_OPEN_p9277 : BSD_Hasse_OPEN 9277 :=
  BSD_hasse_of_degree_nonneg 9277 BSD_DegreeNonneg_p9277

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p9187 : (a_p 9187 : ℝ) ^ 2 ≤ 4 * (9187 : ℝ) :=
  BSD_disc_from_deg_880 BSD_DegreeNonneg_p9187
theorem BSD_HasseBound_Disc_p9199 : (a_p 9199 : ℝ) ^ 2 ≤ 4 * (9199 : ℝ) :=
  BSD_disc_from_deg_880 BSD_DegreeNonneg_p9199
theorem BSD_HasseBound_Disc_p9203 : (a_p 9203 : ℝ) ^ 2 ≤ 4 * (9203 : ℝ) :=
  BSD_disc_from_deg_880 BSD_DegreeNonneg_p9203
theorem BSD_HasseBound_Disc_p9209 : (a_p 9209 : ℝ) ^ 2 ≤ 4 * (9209 : ℝ) :=
  BSD_disc_from_deg_880 BSD_DegreeNonneg_p9209
theorem BSD_HasseBound_Disc_p9221 : (a_p 9221 : ℝ) ^ 2 ≤ 4 * (9221 : ℝ) :=
  BSD_disc_from_deg_880 BSD_DegreeNonneg_p9221
theorem BSD_HasseBound_Disc_p9227 : (a_p 9227 : ℝ) ^ 2 ≤ 4 * (9227 : ℝ) :=
  BSD_disc_from_deg_880 BSD_DegreeNonneg_p9227
theorem BSD_HasseBound_Disc_p9239 : (a_p 9239 : ℝ) ^ 2 ≤ 4 * (9239 : ℝ) :=
  BSD_disc_from_deg_880 BSD_DegreeNonneg_p9239
theorem BSD_HasseBound_Disc_p9241 : (a_p 9241 : ℝ) ^ 2 ≤ 4 * (9241 : ℝ) :=
  BSD_disc_from_deg_880 BSD_DegreeNonneg_p9241
theorem BSD_HasseBound_Disc_p9257 : (a_p 9257 : ℝ) ^ 2 ≤ 4 * (9257 : ℝ) :=
  BSD_disc_from_deg_880 BSD_DegreeNonneg_p9257
theorem BSD_HasseBound_Disc_p9277 : (a_p 9277 : ℝ) ^ 2 ≤ 4 * (9277 : ℝ) :=
  BSD_disc_from_deg_880 BSD_DegreeNonneg_p9277

end Towers.BSD
/-
================================================================
Towers / BSD / BSD_Genesis787_CLOSED  (genesis-787)

HasseBridge Tier C: Hasse bounds for primes
1289..1361 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1289: card=1260, a_p=+30, disc=-4256
  p=1291: card=1256, a_p=+36, disc=-3868
  p=1297: card=1346, a_p=-48, disc=-2884
  p=1301: card=1311, a_p=-9, disc=-5123
  p=1303: card=1293, a_p=+11, disc=-5091
  p=1307: card=1260, a_p=+48, disc=-2924
  p=1319: card=1322, a_p=-2, disc=-5272
  p=1321: card=1281, a_p=+41, disc=-3603
  p=1327: card=1332, a_p=-4, disc=-5292
  p=1361: card=1334, a_p=+28, disc=-4660

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_787 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i787_p1289 : Fact (1289 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1291 : Fact (1291 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1297 : Fact (1297 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1301 : Fact (1301 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1303 : Fact (1303 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1307 : Fact (1307 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1319 : Fact (1319 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1321 : Fact (1321 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1327 : Fact (1327 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1361 : Fact (1361 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1289 : (E143_Finset 1289).card = 1260 := by native_decide
theorem BSD_E143_card_p1291 : (E143_Finset 1291).card = 1256 := by native_decide
theorem BSD_E143_card_p1297 : (E143_Finset 1297).card = 1346 := by native_decide
theorem BSD_E143_card_p1301 : (E143_Finset 1301).card = 1311 := by native_decide
theorem BSD_E143_card_p1303 : (E143_Finset 1303).card = 1293 := by native_decide
theorem BSD_E143_card_p1307 : (E143_Finset 1307).card = 1260 := by native_decide
theorem BSD_E143_card_p1319 : (E143_Finset 1319).card = 1322 := by native_decide
theorem BSD_E143_card_p1321 : (E143_Finset 1321).card = 1281 := by native_decide
theorem BSD_E143_card_p1327 : (E143_Finset 1327).card = 1332 := by native_decide
theorem BSD_E143_card_p1361 : (E143_Finset 1361).card = 1334 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1289 : a_p 1289 = (30 : ℤ) := by
  have h := BSD_E143_card_p1289; unfold a_p; omega
theorem BSD_ap_p1291 : a_p 1291 = (36 : ℤ) := by
  have h := BSD_E143_card_p1291; unfold a_p; omega
theorem BSD_ap_p1297 : a_p 1297 = (-48 : ℤ) := by
  have h := BSD_E143_card_p1297; unfold a_p; omega
theorem BSD_ap_p1301 : a_p 1301 = (-9 : ℤ) := by
  have h := BSD_E143_card_p1301; unfold a_p; omega
theorem BSD_ap_p1303 : a_p 1303 = (11 : ℤ) := by
  have h := BSD_E143_card_p1303; unfold a_p; omega
theorem BSD_ap_p1307 : a_p 1307 = (48 : ℤ) := by
  have h := BSD_E143_card_p1307; unfold a_p; omega
theorem BSD_ap_p1319 : a_p 1319 = (-2 : ℤ) := by
  have h := BSD_E143_card_p1319; unfold a_p; omega
theorem BSD_ap_p1321 : a_p 1321 = (41 : ℤ) := by
  have h := BSD_E143_card_p1321; unfold a_p; omega
theorem BSD_ap_p1327 : a_p 1327 = (-4 : ℤ) := by
  have h := BSD_E143_card_p1327; unfold a_p; omega
theorem BSD_ap_p1361 : a_p 1361 = (28 : ℤ) := by
  have h := BSD_E143_card_p1361; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1289: a_p=+30, 4p-a_p²=4256
theorem BSD_DegreeNonneg_p1289 : BSD_FrobeniusDegreeNonneg_OPEN 1289 := fun r => by
  have hap : (a_p 1289 : ℝ) = 30 := by exact_mod_cast BSD_ap_p1289
  have key : r ^ 2 - (a_p 1289 : ℝ) * r + ((1289 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 4256/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

-- p=1291: a_p=+36, 4p-a_p²=3868
theorem BSD_DegreeNonneg_p1291 : BSD_FrobeniusDegreeNonneg_OPEN 1291 := fun r => by
  have hap : (a_p 1291 : ℝ) = 36 := by exact_mod_cast BSD_ap_p1291
  have key : r ^ 2 - (a_p 1291 : ℝ) * r + ((1291 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 3868/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

-- p=1297: a_p=-48, 4p-a_p²=2884
theorem BSD_DegreeNonneg_p1297 : BSD_FrobeniusDegreeNonneg_OPEN 1297 := fun r => by
  have hap : (a_p 1297 : ℝ) = -48 := by exact_mod_cast BSD_ap_p1297
  have key : r ^ 2 - (a_p 1297 : ℝ) * r + ((1297 : ℕ) : ℝ) =
      (r + 48/2) ^ 2 + 2884/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (48 : ℝ)/2)]

-- p=1301: a_p=-9, 4p-a_p²=5123
theorem BSD_DegreeNonneg_p1301 : BSD_FrobeniusDegreeNonneg_OPEN 1301 := fun r => by
  have hap : (a_p 1301 : ℝ) = -9 := by exact_mod_cast BSD_ap_p1301
  have key : r ^ 2 - (a_p 1301 : ℝ) * r + ((1301 : ℕ) : ℝ) =
      (r + 9/2) ^ 2 + 5123/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (9 : ℝ)/2)]

-- p=1303: a_p=+11, 4p-a_p²=5091
theorem BSD_DegreeNonneg_p1303 : BSD_FrobeniusDegreeNonneg_OPEN 1303 := fun r => by
  have hap : (a_p 1303 : ℝ) = 11 := by exact_mod_cast BSD_ap_p1303
  have key : r ^ 2 - (a_p 1303 : ℝ) * r + ((1303 : ℕ) : ℝ) =
      (r - 11/2) ^ 2 + 5091/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (11 : ℝ)/2)]

-- p=1307: a_p=+48, 4p-a_p²=2924
theorem BSD_DegreeNonneg_p1307 : BSD_FrobeniusDegreeNonneg_OPEN 1307 := fun r => by
  have hap : (a_p 1307 : ℝ) = 48 := by exact_mod_cast BSD_ap_p1307
  have key : r ^ 2 - (a_p 1307 : ℝ) * r + ((1307 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 2924/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

-- p=1319: a_p=-2, 4p-a_p²=5272
theorem BSD_DegreeNonneg_p1319 : BSD_FrobeniusDegreeNonneg_OPEN 1319 := fun r => by
  have hap : (a_p 1319 : ℝ) = -2 := by exact_mod_cast BSD_ap_p1319
  have key : r ^ 2 - (a_p 1319 : ℝ) * r + ((1319 : ℕ) : ℝ) =
      (r + 2/2) ^ 2 + 5272/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (2 : ℝ)/2)]

-- p=1321: a_p=+41, 4p-a_p²=3603
theorem BSD_DegreeNonneg_p1321 : BSD_FrobeniusDegreeNonneg_OPEN 1321 := fun r => by
  have hap : (a_p 1321 : ℝ) = 41 := by exact_mod_cast BSD_ap_p1321
  have key : r ^ 2 - (a_p 1321 : ℝ) * r + ((1321 : ℕ) : ℝ) =
      (r - 41/2) ^ 2 + 3603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (41 : ℝ)/2)]

-- p=1327: a_p=-4, 4p-a_p²=5292
theorem BSD_DegreeNonneg_p1327 : BSD_FrobeniusDegreeNonneg_OPEN 1327 := fun r => by
  have hap : (a_p 1327 : ℝ) = -4 := by exact_mod_cast BSD_ap_p1327
  have key : r ^ 2 - (a_p 1327 : ℝ) * r + ((1327 : ℕ) : ℝ) =
      (r + 4/2) ^ 2 + 5292/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (4 : ℝ)/2)]

-- p=1361: a_p=+28, 4p-a_p²=4660
theorem BSD_DegreeNonneg_p1361 : BSD_FrobeniusDegreeNonneg_OPEN 1361 := fun r => by
  have hap : (a_p 1361 : ℝ) = 28 := by exact_mod_cast BSD_ap_p1361
  have key : r ^ 2 - (a_p 1361 : ℝ) * r + ((1361 : ℕ) : ℝ) =
      (r - 28/2) ^ 2 + 4660/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (28 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1289 : BSD_Hasse_OPEN 1289 :=
  BSD_hasse_of_degree_nonneg 1289 BSD_DegreeNonneg_p1289
theorem BSD_Hasse_OPEN_p1291 : BSD_Hasse_OPEN 1291 :=
  BSD_hasse_of_degree_nonneg 1291 BSD_DegreeNonneg_p1291
theorem BSD_Hasse_OPEN_p1297 : BSD_Hasse_OPEN 1297 :=
  BSD_hasse_of_degree_nonneg 1297 BSD_DegreeNonneg_p1297
theorem BSD_Hasse_OPEN_p1301 : BSD_Hasse_OPEN 1301 :=
  BSD_hasse_of_degree_nonneg 1301 BSD_DegreeNonneg_p1301
theorem BSD_Hasse_OPEN_p1303 : BSD_Hasse_OPEN 1303 :=
  BSD_hasse_of_degree_nonneg 1303 BSD_DegreeNonneg_p1303
theorem BSD_Hasse_OPEN_p1307 : BSD_Hasse_OPEN 1307 :=
  BSD_hasse_of_degree_nonneg 1307 BSD_DegreeNonneg_p1307
theorem BSD_Hasse_OPEN_p1319 : BSD_Hasse_OPEN 1319 :=
  BSD_hasse_of_degree_nonneg 1319 BSD_DegreeNonneg_p1319
theorem BSD_Hasse_OPEN_p1321 : BSD_Hasse_OPEN 1321 :=
  BSD_hasse_of_degree_nonneg 1321 BSD_DegreeNonneg_p1321
theorem BSD_Hasse_OPEN_p1327 : BSD_Hasse_OPEN 1327 :=
  BSD_hasse_of_degree_nonneg 1327 BSD_DegreeNonneg_p1327
theorem BSD_Hasse_OPEN_p1361 : BSD_Hasse_OPEN 1361 :=
  BSD_hasse_of_degree_nonneg 1361 BSD_DegreeNonneg_p1361

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1289 : (a_p 1289 : ℝ) ^ 2 ≤ 4 * (1289 : ℝ) :=
  BSD_disc_from_deg_787 BSD_DegreeNonneg_p1289
theorem BSD_HasseBound_Disc_p1291 : (a_p 1291 : ℝ) ^ 2 ≤ 4 * (1291 : ℝ) :=
  BSD_disc_from_deg_787 BSD_DegreeNonneg_p1291
theorem BSD_HasseBound_Disc_p1297 : (a_p 1297 : ℝ) ^ 2 ≤ 4 * (1297 : ℝ) :=
  BSD_disc_from_deg_787 BSD_DegreeNonneg_p1297
theorem BSD_HasseBound_Disc_p1301 : (a_p 1301 : ℝ) ^ 2 ≤ 4 * (1301 : ℝ) :=
  BSD_disc_from_deg_787 BSD_DegreeNonneg_p1301
theorem BSD_HasseBound_Disc_p1303 : (a_p 1303 : ℝ) ^ 2 ≤ 4 * (1303 : ℝ) :=
  BSD_disc_from_deg_787 BSD_DegreeNonneg_p1303
theorem BSD_HasseBound_Disc_p1307 : (a_p 1307 : ℝ) ^ 2 ≤ 4 * (1307 : ℝ) :=
  BSD_disc_from_deg_787 BSD_DegreeNonneg_p1307
theorem BSD_HasseBound_Disc_p1319 : (a_p 1319 : ℝ) ^ 2 ≤ 4 * (1319 : ℝ) :=
  BSD_disc_from_deg_787 BSD_DegreeNonneg_p1319
theorem BSD_HasseBound_Disc_p1321 : (a_p 1321 : ℝ) ^ 2 ≤ 4 * (1321 : ℝ) :=
  BSD_disc_from_deg_787 BSD_DegreeNonneg_p1321
theorem BSD_HasseBound_Disc_p1327 : (a_p 1327 : ℝ) ^ 2 ≤ 4 * (1327 : ℝ) :=
  BSD_disc_from_deg_787 BSD_DegreeNonneg_p1327
theorem BSD_HasseBound_Disc_p1361 : (a_p 1361 : ℝ) ^ 2 ≤ 4 * (1361 : ℝ) :=
  BSD_disc_from_deg_787 BSD_DegreeNonneg_p1361

end Towers.BSD
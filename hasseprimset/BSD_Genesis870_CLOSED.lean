/-
================================================================
Towers / BSD / BSD_Genesis870_CLOSED  (genesis-870)

HasseBridge Tier C: Hasse bounds for primes
8287..8369 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=8287: card=8240, a_p=+48, disc=-30844
  p=8291: card=8350, a_p=-58, disc=-29800
  p=8293: card=8160, a_p=+134, disc=-15216
  p=8297: card=8367, a_p=-69, disc=-28427
  p=8311: card=8332, a_p=-20, disc=-32844
  p=8317: card=8284, a_p=+34, disc=-32112
  p=8329: card=8244, a_p=+86, disc=-25920
  p=8353: card=8297, a_p=+57, disc=-30163
  p=8363: card=8500, a_p=-136, disc=-14956
  p=8369: card=8304, a_p=+66, disc=-29120

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_870 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i870_p8287 : Fact (8287 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8291 : Fact (8291 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8293 : Fact (8293 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8297 : Fact (8297 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8311 : Fact (8311 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8317 : Fact (8317 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8329 : Fact (8329 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8353 : Fact (8353 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8363 : Fact (8363 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8369 : Fact (8369 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p8287 : (E143_Finset 8287).card = 8240 := by native_decide
theorem BSD_E143_card_p8291 : (E143_Finset 8291).card = 8350 := by native_decide
theorem BSD_E143_card_p8293 : (E143_Finset 8293).card = 8160 := by native_decide
theorem BSD_E143_card_p8297 : (E143_Finset 8297).card = 8367 := by native_decide
theorem BSD_E143_card_p8311 : (E143_Finset 8311).card = 8332 := by native_decide
theorem BSD_E143_card_p8317 : (E143_Finset 8317).card = 8284 := by native_decide
theorem BSD_E143_card_p8329 : (E143_Finset 8329).card = 8244 := by native_decide
theorem BSD_E143_card_p8353 : (E143_Finset 8353).card = 8297 := by native_decide
theorem BSD_E143_card_p8363 : (E143_Finset 8363).card = 8500 := by native_decide
theorem BSD_E143_card_p8369 : (E143_Finset 8369).card = 8304 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p8287 : a_p 8287 = (48 : ℤ) := by
  have h := BSD_E143_card_p8287; unfold a_p; omega
theorem BSD_ap_p8291 : a_p 8291 = (-58 : ℤ) := by
  have h := BSD_E143_card_p8291; unfold a_p; omega
theorem BSD_ap_p8293 : a_p 8293 = (134 : ℤ) := by
  have h := BSD_E143_card_p8293; unfold a_p; omega
theorem BSD_ap_p8297 : a_p 8297 = (-69 : ℤ) := by
  have h := BSD_E143_card_p8297; unfold a_p; omega
theorem BSD_ap_p8311 : a_p 8311 = (-20 : ℤ) := by
  have h := BSD_E143_card_p8311; unfold a_p; omega
theorem BSD_ap_p8317 : a_p 8317 = (34 : ℤ) := by
  have h := BSD_E143_card_p8317; unfold a_p; omega
theorem BSD_ap_p8329 : a_p 8329 = (86 : ℤ) := by
  have h := BSD_E143_card_p8329; unfold a_p; omega
theorem BSD_ap_p8353 : a_p 8353 = (57 : ℤ) := by
  have h := BSD_E143_card_p8353; unfold a_p; omega
theorem BSD_ap_p8363 : a_p 8363 = (-136 : ℤ) := by
  have h := BSD_E143_card_p8363; unfold a_p; omega
theorem BSD_ap_p8369 : a_p 8369 = (66 : ℤ) := by
  have h := BSD_E143_card_p8369; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=8287: a_p=+48, 4p-a_p²=30844
theorem BSD_DegreeNonneg_p8287 : BSD_FrobeniusDegreeNonneg_OPEN 8287 := fun r => by
  have hap : (a_p 8287 : ℝ) = 48 := by exact_mod_cast BSD_ap_p8287
  have key : r ^ 2 - (a_p 8287 : ℝ) * r + ((8287 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 30844/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

-- p=8291: a_p=-58, 4p-a_p²=29800
theorem BSD_DegreeNonneg_p8291 : BSD_FrobeniusDegreeNonneg_OPEN 8291 := fun r => by
  have hap : (a_p 8291 : ℝ) = -58 := by exact_mod_cast BSD_ap_p8291
  have key : r ^ 2 - (a_p 8291 : ℝ) * r + ((8291 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 29800/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

-- p=8293: a_p=+134, 4p-a_p²=15216
theorem BSD_DegreeNonneg_p8293 : BSD_FrobeniusDegreeNonneg_OPEN 8293 := fun r => by
  have hap : (a_p 8293 : ℝ) = 134 := by exact_mod_cast BSD_ap_p8293
  have key : r ^ 2 - (a_p 8293 : ℝ) * r + ((8293 : ℕ) : ℝ) =
      (r - 134/2) ^ 2 + 15216/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (134 : ℝ)/2)]

-- p=8297: a_p=-69, 4p-a_p²=28427
theorem BSD_DegreeNonneg_p8297 : BSD_FrobeniusDegreeNonneg_OPEN 8297 := fun r => by
  have hap : (a_p 8297 : ℝ) = -69 := by exact_mod_cast BSD_ap_p8297
  have key : r ^ 2 - (a_p 8297 : ℝ) * r + ((8297 : ℕ) : ℝ) =
      (r + 69/2) ^ 2 + 28427/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (69 : ℝ)/2)]

-- p=8311: a_p=-20, 4p-a_p²=32844
theorem BSD_DegreeNonneg_p8311 : BSD_FrobeniusDegreeNonneg_OPEN 8311 := fun r => by
  have hap : (a_p 8311 : ℝ) = -20 := by exact_mod_cast BSD_ap_p8311
  have key : r ^ 2 - (a_p 8311 : ℝ) * r + ((8311 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 32844/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=8317: a_p=+34, 4p-a_p²=32112
theorem BSD_DegreeNonneg_p8317 : BSD_FrobeniusDegreeNonneg_OPEN 8317 := fun r => by
  have hap : (a_p 8317 : ℝ) = 34 := by exact_mod_cast BSD_ap_p8317
  have key : r ^ 2 - (a_p 8317 : ℝ) * r + ((8317 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 32112/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

-- p=8329: a_p=+86, 4p-a_p²=25920
theorem BSD_DegreeNonneg_p8329 : BSD_FrobeniusDegreeNonneg_OPEN 8329 := fun r => by
  have hap : (a_p 8329 : ℝ) = 86 := by exact_mod_cast BSD_ap_p8329
  have key : r ^ 2 - (a_p 8329 : ℝ) * r + ((8329 : ℕ) : ℝ) =
      (r - 86/2) ^ 2 + 25920/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (86 : ℝ)/2)]

-- p=8353: a_p=+57, 4p-a_p²=30163
theorem BSD_DegreeNonneg_p8353 : BSD_FrobeniusDegreeNonneg_OPEN 8353 := fun r => by
  have hap : (a_p 8353 : ℝ) = 57 := by exact_mod_cast BSD_ap_p8353
  have key : r ^ 2 - (a_p 8353 : ℝ) * r + ((8353 : ℕ) : ℝ) =
      (r - 57/2) ^ 2 + 30163/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (57 : ℝ)/2)]

-- p=8363: a_p=-136, 4p-a_p²=14956
theorem BSD_DegreeNonneg_p8363 : BSD_FrobeniusDegreeNonneg_OPEN 8363 := fun r => by
  have hap : (a_p 8363 : ℝ) = -136 := by exact_mod_cast BSD_ap_p8363
  have key : r ^ 2 - (a_p 8363 : ℝ) * r + ((8363 : ℕ) : ℝ) =
      (r + 136/2) ^ 2 + 14956/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (136 : ℝ)/2)]

-- p=8369: a_p=+66, 4p-a_p²=29120
theorem BSD_DegreeNonneg_p8369 : BSD_FrobeniusDegreeNonneg_OPEN 8369 := fun r => by
  have hap : (a_p 8369 : ℝ) = 66 := by exact_mod_cast BSD_ap_p8369
  have key : r ^ 2 - (a_p 8369 : ℝ) * r + ((8369 : ℕ) : ℝ) =
      (r - 66/2) ^ 2 + 29120/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (66 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p8287 : BSD_Hasse_OPEN 8287 :=
  BSD_hasse_of_degree_nonneg 8287 BSD_DegreeNonneg_p8287
theorem BSD_Hasse_OPEN_p8291 : BSD_Hasse_OPEN 8291 :=
  BSD_hasse_of_degree_nonneg 8291 BSD_DegreeNonneg_p8291
theorem BSD_Hasse_OPEN_p8293 : BSD_Hasse_OPEN 8293 :=
  BSD_hasse_of_degree_nonneg 8293 BSD_DegreeNonneg_p8293
theorem BSD_Hasse_OPEN_p8297 : BSD_Hasse_OPEN 8297 :=
  BSD_hasse_of_degree_nonneg 8297 BSD_DegreeNonneg_p8297
theorem BSD_Hasse_OPEN_p8311 : BSD_Hasse_OPEN 8311 :=
  BSD_hasse_of_degree_nonneg 8311 BSD_DegreeNonneg_p8311
theorem BSD_Hasse_OPEN_p8317 : BSD_Hasse_OPEN 8317 :=
  BSD_hasse_of_degree_nonneg 8317 BSD_DegreeNonneg_p8317
theorem BSD_Hasse_OPEN_p8329 : BSD_Hasse_OPEN 8329 :=
  BSD_hasse_of_degree_nonneg 8329 BSD_DegreeNonneg_p8329
theorem BSD_Hasse_OPEN_p8353 : BSD_Hasse_OPEN 8353 :=
  BSD_hasse_of_degree_nonneg 8353 BSD_DegreeNonneg_p8353
theorem BSD_Hasse_OPEN_p8363 : BSD_Hasse_OPEN 8363 :=
  BSD_hasse_of_degree_nonneg 8363 BSD_DegreeNonneg_p8363
theorem BSD_Hasse_OPEN_p8369 : BSD_Hasse_OPEN 8369 :=
  BSD_hasse_of_degree_nonneg 8369 BSD_DegreeNonneg_p8369

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p8287 : (a_p 8287 : ℝ) ^ 2 ≤ 4 * (8287 : ℝ) :=
  BSD_disc_from_deg_870 BSD_DegreeNonneg_p8287
theorem BSD_HasseBound_Disc_p8291 : (a_p 8291 : ℝ) ^ 2 ≤ 4 * (8291 : ℝ) :=
  BSD_disc_from_deg_870 BSD_DegreeNonneg_p8291
theorem BSD_HasseBound_Disc_p8293 : (a_p 8293 : ℝ) ^ 2 ≤ 4 * (8293 : ℝ) :=
  BSD_disc_from_deg_870 BSD_DegreeNonneg_p8293
theorem BSD_HasseBound_Disc_p8297 : (a_p 8297 : ℝ) ^ 2 ≤ 4 * (8297 : ℝ) :=
  BSD_disc_from_deg_870 BSD_DegreeNonneg_p8297
theorem BSD_HasseBound_Disc_p8311 : (a_p 8311 : ℝ) ^ 2 ≤ 4 * (8311 : ℝ) :=
  BSD_disc_from_deg_870 BSD_DegreeNonneg_p8311
theorem BSD_HasseBound_Disc_p8317 : (a_p 8317 : ℝ) ^ 2 ≤ 4 * (8317 : ℝ) :=
  BSD_disc_from_deg_870 BSD_DegreeNonneg_p8317
theorem BSD_HasseBound_Disc_p8329 : (a_p 8329 : ℝ) ^ 2 ≤ 4 * (8329 : ℝ) :=
  BSD_disc_from_deg_870 BSD_DegreeNonneg_p8329
theorem BSD_HasseBound_Disc_p8353 : (a_p 8353 : ℝ) ^ 2 ≤ 4 * (8353 : ℝ) :=
  BSD_disc_from_deg_870 BSD_DegreeNonneg_p8353
theorem BSD_HasseBound_Disc_p8363 : (a_p 8363 : ℝ) ^ 2 ≤ 4 * (8363 : ℝ) :=
  BSD_disc_from_deg_870 BSD_DegreeNonneg_p8363
theorem BSD_HasseBound_Disc_p8369 : (a_p 8369 : ℝ) ^ 2 ≤ 4 * (8369 : ℝ) :=
  BSD_disc_from_deg_870 BSD_DegreeNonneg_p8369

end Towers.BSD
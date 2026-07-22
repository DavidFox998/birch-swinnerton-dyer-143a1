/-
================================================================
Towers / BSD / BSD_Genesis799_CLOSED  (genesis-799)

HasseBridge Tier C: Hasse bounds for primes
2207..2273 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2207: card=2130, a_p=+78, disc=-2744
  p=2213: card=2162, a_p=+52, disc=-6148
  p=2221: card=2160, a_p=+62, disc=-5040
  p=2237: card=2280, a_p=-42, disc=-7184
  p=2239: card=2290, a_p=-50, disc=-6456
  p=2243: card=2280, a_p=-36, disc=-7676
  p=2251: card=2244, a_p=+8, disc=-8940
  p=2267: card=2257, a_p=+11, disc=-8947
  p=2269: card=2271, a_p=-1, disc=-9075
  p=2273: card=2320, a_p=-46, disc=-6976

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_799 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i799_p2207 : Fact (2207 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2213 : Fact (2213 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2221 : Fact (2221 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2237 : Fact (2237 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2239 : Fact (2239 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2243 : Fact (2243 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2251 : Fact (2251 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2267 : Fact (2267 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2269 : Fact (2269 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2273 : Fact (2273 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2207 : (E143_Finset 2207).card = 2130 := by native_decide
theorem BSD_E143_card_p2213 : (E143_Finset 2213).card = 2162 := by native_decide
theorem BSD_E143_card_p2221 : (E143_Finset 2221).card = 2160 := by native_decide
theorem BSD_E143_card_p2237 : (E143_Finset 2237).card = 2280 := by native_decide
theorem BSD_E143_card_p2239 : (E143_Finset 2239).card = 2290 := by native_decide
theorem BSD_E143_card_p2243 : (E143_Finset 2243).card = 2280 := by native_decide
theorem BSD_E143_card_p2251 : (E143_Finset 2251).card = 2244 := by native_decide
theorem BSD_E143_card_p2267 : (E143_Finset 2267).card = 2257 := by native_decide
theorem BSD_E143_card_p2269 : (E143_Finset 2269).card = 2271 := by native_decide
theorem BSD_E143_card_p2273 : (E143_Finset 2273).card = 2320 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2207 : a_p 2207 = (78 : ℤ) := by
  have h := BSD_E143_card_p2207; unfold a_p; omega
theorem BSD_ap_p2213 : a_p 2213 = (52 : ℤ) := by
  have h := BSD_E143_card_p2213; unfold a_p; omega
theorem BSD_ap_p2221 : a_p 2221 = (62 : ℤ) := by
  have h := BSD_E143_card_p2221; unfold a_p; omega
theorem BSD_ap_p2237 : a_p 2237 = (-42 : ℤ) := by
  have h := BSD_E143_card_p2237; unfold a_p; omega
theorem BSD_ap_p2239 : a_p 2239 = (-50 : ℤ) := by
  have h := BSD_E143_card_p2239; unfold a_p; omega
theorem BSD_ap_p2243 : a_p 2243 = (-36 : ℤ) := by
  have h := BSD_E143_card_p2243; unfold a_p; omega
theorem BSD_ap_p2251 : a_p 2251 = (8 : ℤ) := by
  have h := BSD_E143_card_p2251; unfold a_p; omega
theorem BSD_ap_p2267 : a_p 2267 = (11 : ℤ) := by
  have h := BSD_E143_card_p2267; unfold a_p; omega
theorem BSD_ap_p2269 : a_p 2269 = (-1 : ℤ) := by
  have h := BSD_E143_card_p2269; unfold a_p; omega
theorem BSD_ap_p2273 : a_p 2273 = (-46 : ℤ) := by
  have h := BSD_E143_card_p2273; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2207: a_p=+78, 4p-a_p²=2744
theorem BSD_DegreeNonneg_p2207 : BSD_FrobeniusDegreeNonneg_OPEN 2207 := fun r => by
  have hap : (a_p 2207 : ℝ) = 78 := by exact_mod_cast BSD_ap_p2207
  have key : r ^ 2 - (a_p 2207 : ℝ) * r + ((2207 : ℕ) : ℝ) =
      (r - 78/2) ^ 2 + 2744/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (78 : ℝ)/2)]

-- p=2213: a_p=+52, 4p-a_p²=6148
theorem BSD_DegreeNonneg_p2213 : BSD_FrobeniusDegreeNonneg_OPEN 2213 := fun r => by
  have hap : (a_p 2213 : ℝ) = 52 := by exact_mod_cast BSD_ap_p2213
  have key : r ^ 2 - (a_p 2213 : ℝ) * r + ((2213 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 6148/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

-- p=2221: a_p=+62, 4p-a_p²=5040
theorem BSD_DegreeNonneg_p2221 : BSD_FrobeniusDegreeNonneg_OPEN 2221 := fun r => by
  have hap : (a_p 2221 : ℝ) = 62 := by exact_mod_cast BSD_ap_p2221
  have key : r ^ 2 - (a_p 2221 : ℝ) * r + ((2221 : ℕ) : ℝ) =
      (r - 62/2) ^ 2 + 5040/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (62 : ℝ)/2)]

-- p=2237: a_p=-42, 4p-a_p²=7184
theorem BSD_DegreeNonneg_p2237 : BSD_FrobeniusDegreeNonneg_OPEN 2237 := fun r => by
  have hap : (a_p 2237 : ℝ) = -42 := by exact_mod_cast BSD_ap_p2237
  have key : r ^ 2 - (a_p 2237 : ℝ) * r + ((2237 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 7184/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

-- p=2239: a_p=-50, 4p-a_p²=6456
theorem BSD_DegreeNonneg_p2239 : BSD_FrobeniusDegreeNonneg_OPEN 2239 := fun r => by
  have hap : (a_p 2239 : ℝ) = -50 := by exact_mod_cast BSD_ap_p2239
  have key : r ^ 2 - (a_p 2239 : ℝ) * r + ((2239 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 6456/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

-- p=2243: a_p=-36, 4p-a_p²=7676
theorem BSD_DegreeNonneg_p2243 : BSD_FrobeniusDegreeNonneg_OPEN 2243 := fun r => by
  have hap : (a_p 2243 : ℝ) = -36 := by exact_mod_cast BSD_ap_p2243
  have key : r ^ 2 - (a_p 2243 : ℝ) * r + ((2243 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 7676/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

-- p=2251: a_p=+8, 4p-a_p²=8940
theorem BSD_DegreeNonneg_p2251 : BSD_FrobeniusDegreeNonneg_OPEN 2251 := fun r => by
  have hap : (a_p 2251 : ℝ) = 8 := by exact_mod_cast BSD_ap_p2251
  have key : r ^ 2 - (a_p 2251 : ℝ) * r + ((2251 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 8940/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

-- p=2267: a_p=+11, 4p-a_p²=8947
theorem BSD_DegreeNonneg_p2267 : BSD_FrobeniusDegreeNonneg_OPEN 2267 := fun r => by
  have hap : (a_p 2267 : ℝ) = 11 := by exact_mod_cast BSD_ap_p2267
  have key : r ^ 2 - (a_p 2267 : ℝ) * r + ((2267 : ℕ) : ℝ) =
      (r - 11/2) ^ 2 + 8947/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (11 : ℝ)/2)]

-- p=2269: a_p=-1, 4p-a_p²=9075
theorem BSD_DegreeNonneg_p2269 : BSD_FrobeniusDegreeNonneg_OPEN 2269 := fun r => by
  have hap : (a_p 2269 : ℝ) = -1 := by exact_mod_cast BSD_ap_p2269
  have key : r ^ 2 - (a_p 2269 : ℝ) * r + ((2269 : ℕ) : ℝ) =
      (r + 1/2) ^ 2 + 9075/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (1 : ℝ)/2)]

-- p=2273: a_p=-46, 4p-a_p²=6976
theorem BSD_DegreeNonneg_p2273 : BSD_FrobeniusDegreeNonneg_OPEN 2273 := fun r => by
  have hap : (a_p 2273 : ℝ) = -46 := by exact_mod_cast BSD_ap_p2273
  have key : r ^ 2 - (a_p 2273 : ℝ) * r + ((2273 : ℕ) : ℝ) =
      (r + 46/2) ^ 2 + 6976/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (46 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2207 : BSD_Hasse_OPEN 2207 :=
  BSD_hasse_of_degree_nonneg 2207 BSD_DegreeNonneg_p2207
theorem BSD_Hasse_OPEN_p2213 : BSD_Hasse_OPEN 2213 :=
  BSD_hasse_of_degree_nonneg 2213 BSD_DegreeNonneg_p2213
theorem BSD_Hasse_OPEN_p2221 : BSD_Hasse_OPEN 2221 :=
  BSD_hasse_of_degree_nonneg 2221 BSD_DegreeNonneg_p2221
theorem BSD_Hasse_OPEN_p2237 : BSD_Hasse_OPEN 2237 :=
  BSD_hasse_of_degree_nonneg 2237 BSD_DegreeNonneg_p2237
theorem BSD_Hasse_OPEN_p2239 : BSD_Hasse_OPEN 2239 :=
  BSD_hasse_of_degree_nonneg 2239 BSD_DegreeNonneg_p2239
theorem BSD_Hasse_OPEN_p2243 : BSD_Hasse_OPEN 2243 :=
  BSD_hasse_of_degree_nonneg 2243 BSD_DegreeNonneg_p2243
theorem BSD_Hasse_OPEN_p2251 : BSD_Hasse_OPEN 2251 :=
  BSD_hasse_of_degree_nonneg 2251 BSD_DegreeNonneg_p2251
theorem BSD_Hasse_OPEN_p2267 : BSD_Hasse_OPEN 2267 :=
  BSD_hasse_of_degree_nonneg 2267 BSD_DegreeNonneg_p2267
theorem BSD_Hasse_OPEN_p2269 : BSD_Hasse_OPEN 2269 :=
  BSD_hasse_of_degree_nonneg 2269 BSD_DegreeNonneg_p2269
theorem BSD_Hasse_OPEN_p2273 : BSD_Hasse_OPEN 2273 :=
  BSD_hasse_of_degree_nonneg 2273 BSD_DegreeNonneg_p2273

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2207 : (a_p 2207 : ℝ) ^ 2 ≤ 4 * (2207 : ℝ) :=
  BSD_disc_from_deg_799 BSD_DegreeNonneg_p2207
theorem BSD_HasseBound_Disc_p2213 : (a_p 2213 : ℝ) ^ 2 ≤ 4 * (2213 : ℝ) :=
  BSD_disc_from_deg_799 BSD_DegreeNonneg_p2213
theorem BSD_HasseBound_Disc_p2221 : (a_p 2221 : ℝ) ^ 2 ≤ 4 * (2221 : ℝ) :=
  BSD_disc_from_deg_799 BSD_DegreeNonneg_p2221
theorem BSD_HasseBound_Disc_p2237 : (a_p 2237 : ℝ) ^ 2 ≤ 4 * (2237 : ℝ) :=
  BSD_disc_from_deg_799 BSD_DegreeNonneg_p2237
theorem BSD_HasseBound_Disc_p2239 : (a_p 2239 : ℝ) ^ 2 ≤ 4 * (2239 : ℝ) :=
  BSD_disc_from_deg_799 BSD_DegreeNonneg_p2239
theorem BSD_HasseBound_Disc_p2243 : (a_p 2243 : ℝ) ^ 2 ≤ 4 * (2243 : ℝ) :=
  BSD_disc_from_deg_799 BSD_DegreeNonneg_p2243
theorem BSD_HasseBound_Disc_p2251 : (a_p 2251 : ℝ) ^ 2 ≤ 4 * (2251 : ℝ) :=
  BSD_disc_from_deg_799 BSD_DegreeNonneg_p2251
theorem BSD_HasseBound_Disc_p2267 : (a_p 2267 : ℝ) ^ 2 ≤ 4 * (2267 : ℝ) :=
  BSD_disc_from_deg_799 BSD_DegreeNonneg_p2267
theorem BSD_HasseBound_Disc_p2269 : (a_p 2269 : ℝ) ^ 2 ≤ 4 * (2269 : ℝ) :=
  BSD_disc_from_deg_799 BSD_DegreeNonneg_p2269
theorem BSD_HasseBound_Disc_p2273 : (a_p 2273 : ℝ) ^ 2 ≤ 4 * (2273 : ℝ) :=
  BSD_disc_from_deg_799 BSD_DegreeNonneg_p2273

end Towers.BSD
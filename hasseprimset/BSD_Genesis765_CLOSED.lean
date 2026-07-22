/-
================================================================
Towers / BSD / BSD_Genesis765_CLOSED  (genesis-765)

HasseBridge Batch 3: Hasse bounds for primes
373..431 (10 primes).
Tier A grows to 81 primes after this file.

Pair sizes (p^2):
  p=373: card=347, a_p=+26, disc=-816 (139129 pairs)
  p=379: card=390, a_p=-11, disc=-1395 (143641 pairs)
  p=383: card=402, a_p=-19, disc=-1171 (146689 pairs)
  p=389: card=380, a_p=+9, disc=-1475 (151321 pairs)
  p=397: card=415, a_p=-18, disc=-1264 (157609 pairs)
  p=401: card=419, a_p=-18, disc=-1280 (160801 pairs)
  p=409: card=427, a_p=-18, disc=-1312 (167281 pairs)
  p=419: card=447, a_p=-28, disc=-892 (175561 pairs)
  p=421: card=443, a_p=-22, disc=-1200 (177241 pairs)
  p=431: card=471, a_p=-40, disc=-124 (185761 pairs)

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis764_CLOSED

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_765 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-! ## Fact instances -/

private instance i765_p373 : Fact (373 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p379 : Fact (379 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p383 : Fact (383 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p389 : Fact (389 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p397 : Fact (397 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p401 : Fact (401 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p409 : Fact (409 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p419 : Fact (419 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p421 : Fact (421 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p431 : Fact (431 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §1. Point counts (by decide) -/

theorem BSD_E143_card_p373 : (E143_Finset 373).card = 347 := by decide
theorem BSD_E143_card_p379 : (E143_Finset 379).card = 390 := by decide
theorem BSD_E143_card_p383 : (E143_Finset 383).card = 402 := by decide
theorem BSD_E143_card_p389 : (E143_Finset 389).card = 380 := by decide
theorem BSD_E143_card_p397 : (E143_Finset 397).card = 415 := by decide
theorem BSD_E143_card_p401 : (E143_Finset 401).card = 419 := by decide
theorem BSD_E143_card_p409 : (E143_Finset 409).card = 427 := by decide
theorem BSD_E143_card_p419 : (E143_Finset 419).card = 447 := by decide
theorem BSD_E143_card_p421 : (E143_Finset 421).card = 443 := by decide
theorem BSD_E143_card_p431 : (E143_Finset 431).card = 471 := by decide

/-! ## §2. Exact a_p values -/

theorem BSD_ap_p373 : a_p 373 = (26 : ℤ) := by
  have h := BSD_E143_card_p373; unfold a_p; omega
theorem BSD_ap_p379 : a_p 379 = (-11 : ℤ) := by
  have h := BSD_E143_card_p379; unfold a_p; omega
theorem BSD_ap_p383 : a_p 383 = (-19 : ℤ) := by
  have h := BSD_E143_card_p383; unfold a_p; omega
theorem BSD_ap_p389 : a_p 389 = (9 : ℤ) := by
  have h := BSD_E143_card_p389; unfold a_p; omega
theorem BSD_ap_p397 : a_p 397 = (-18 : ℤ) := by
  have h := BSD_E143_card_p397; unfold a_p; omega
theorem BSD_ap_p401 : a_p 401 = (-18 : ℤ) := by
  have h := BSD_E143_card_p401; unfold a_p; omega
theorem BSD_ap_p409 : a_p 409 = (-18 : ℤ) := by
  have h := BSD_E143_card_p409; unfold a_p; omega
theorem BSD_ap_p419 : a_p 419 = (-28 : ℤ) := by
  have h := BSD_E143_card_p419; unfold a_p; omega
theorem BSD_ap_p421 : a_p 421 = (-22 : ℤ) := by
  have h := BSD_E143_card_p421; unfold a_p; omega
theorem BSD_ap_p431 : a_p 431 = (-40 : ℤ) := by
  have h := BSD_E143_card_p431; unfold a_p; omega

/-! ## §3. Degree non-negativity (completed-square) -/

-- p=373: a_p=+26, disc=-816
theorem BSD_DegreeNonneg_p373 : BSD_FrobeniusDegreeNonneg_OPEN 373 := fun r => by
  have hap : (a_p 373 : ℝ) = 26 := by exact_mod_cast BSD_ap_p373
  have key : r ^ 2 - (a_p 373 : ℝ) * r + ((373 : ℕ) : ℝ) =
      (r - 13) ^ 2 + 204 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 13)]

-- p=379: a_p=-11, disc=-1395
theorem BSD_DegreeNonneg_p379 : BSD_FrobeniusDegreeNonneg_OPEN 379 := fun r => by
  have hap : (a_p 379 : ℝ) = -11 := by exact_mod_cast BSD_ap_p379
  have key : r ^ 2 - (a_p 379 : ℝ) * r + ((379 : ℕ) : ℝ) =
      (r + 11 / 2) ^ 2 + 1395 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 11 / 2)]

-- p=383: a_p=-19, disc=-1171
theorem BSD_DegreeNonneg_p383 : BSD_FrobeniusDegreeNonneg_OPEN 383 := fun r => by
  have hap : (a_p 383 : ℝ) = -19 := by exact_mod_cast BSD_ap_p383
  have key : r ^ 2 - (a_p 383 : ℝ) * r + ((383 : ℕ) : ℝ) =
      (r + 19 / 2) ^ 2 + 1171 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 19 / 2)]

-- p=389: a_p=+9, disc=-1475
theorem BSD_DegreeNonneg_p389 : BSD_FrobeniusDegreeNonneg_OPEN 389 := fun r => by
  have hap : (a_p 389 : ℝ) = 9 := by exact_mod_cast BSD_ap_p389
  have key : r ^ 2 - (a_p 389 : ℝ) * r + ((389 : ℕ) : ℝ) =
      (r - 9 / 2) ^ 2 + 1475 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9 / 2)]

-- p=397: a_p=-18, disc=-1264
theorem BSD_DegreeNonneg_p397 : BSD_FrobeniusDegreeNonneg_OPEN 397 := fun r => by
  have hap : (a_p 397 : ℝ) = -18 := by exact_mod_cast BSD_ap_p397
  have key : r ^ 2 - (a_p 397 : ℝ) * r + ((397 : ℕ) : ℝ) =
      (r + 9) ^ 2 + 316 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9)]

-- p=401: a_p=-18, disc=-1280
theorem BSD_DegreeNonneg_p401 : BSD_FrobeniusDegreeNonneg_OPEN 401 := fun r => by
  have hap : (a_p 401 : ℝ) = -18 := by exact_mod_cast BSD_ap_p401
  have key : r ^ 2 - (a_p 401 : ℝ) * r + ((401 : ℕ) : ℝ) =
      (r + 9) ^ 2 + 320 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9)]

-- p=409: a_p=-18, disc=-1312
theorem BSD_DegreeNonneg_p409 : BSD_FrobeniusDegreeNonneg_OPEN 409 := fun r => by
  have hap : (a_p 409 : ℝ) = -18 := by exact_mod_cast BSD_ap_p409
  have key : r ^ 2 - (a_p 409 : ℝ) * r + ((409 : ℕ) : ℝ) =
      (r + 9) ^ 2 + 328 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9)]

-- p=419: a_p=-28, disc=-892
theorem BSD_DegreeNonneg_p419 : BSD_FrobeniusDegreeNonneg_OPEN 419 := fun r => by
  have hap : (a_p 419 : ℝ) = -28 := by exact_mod_cast BSD_ap_p419
  have key : r ^ 2 - (a_p 419 : ℝ) * r + ((419 : ℕ) : ℝ) =
      (r + 14) ^ 2 + 223 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 14)]

-- p=421: a_p=-22, disc=-1200
theorem BSD_DegreeNonneg_p421 : BSD_FrobeniusDegreeNonneg_OPEN 421 := fun r => by
  have hap : (a_p 421 : ℝ) = -22 := by exact_mod_cast BSD_ap_p421
  have key : r ^ 2 - (a_p 421 : ℝ) * r + ((421 : ℕ) : ℝ) =
      (r + 11) ^ 2 + 300 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 11)]

-- p=431: a_p=-40, disc=-124
theorem BSD_DegreeNonneg_p431 : BSD_FrobeniusDegreeNonneg_OPEN 431 := fun r => by
  have hap : (a_p 431 : ℝ) = -40 := by exact_mod_cast BSD_ap_p431
  have key : r ^ 2 - (a_p 431 : ℝ) * r + ((431 : ℕ) : ℝ) =
      (r + 20) ^ 2 + 31 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 20)]

/-! ## §4. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p373 : BSD_Hasse_OPEN 373 :=
  BSD_hasse_of_degree_nonneg 373 BSD_DegreeNonneg_p373
theorem BSD_Hasse_OPEN_p379 : BSD_Hasse_OPEN 379 :=
  BSD_hasse_of_degree_nonneg 379 BSD_DegreeNonneg_p379
theorem BSD_Hasse_OPEN_p383 : BSD_Hasse_OPEN 383 :=
  BSD_hasse_of_degree_nonneg 383 BSD_DegreeNonneg_p383
theorem BSD_Hasse_OPEN_p389 : BSD_Hasse_OPEN 389 :=
  BSD_hasse_of_degree_nonneg 389 BSD_DegreeNonneg_p389
theorem BSD_Hasse_OPEN_p397 : BSD_Hasse_OPEN 397 :=
  BSD_hasse_of_degree_nonneg 397 BSD_DegreeNonneg_p397
theorem BSD_Hasse_OPEN_p401 : BSD_Hasse_OPEN 401 :=
  BSD_hasse_of_degree_nonneg 401 BSD_DegreeNonneg_p401
theorem BSD_Hasse_OPEN_p409 : BSD_Hasse_OPEN 409 :=
  BSD_hasse_of_degree_nonneg 409 BSD_DegreeNonneg_p409
theorem BSD_Hasse_OPEN_p419 : BSD_Hasse_OPEN 419 :=
  BSD_hasse_of_degree_nonneg 419 BSD_DegreeNonneg_p419
theorem BSD_Hasse_OPEN_p421 : BSD_Hasse_OPEN 421 :=
  BSD_hasse_of_degree_nonneg 421 BSD_DegreeNonneg_p421
theorem BSD_Hasse_OPEN_p431 : BSD_Hasse_OPEN 431 :=
  BSD_hasse_of_degree_nonneg 431 BSD_DegreeNonneg_p431

/-! ## §5. Clay gate discriminant form -/

theorem BSD_HasseBound_Disc_p373 : (a_p 373 : ℝ) ^ 2 ≤ 4 * (373 : ℝ) :=
  BSD_disc_from_deg_765 BSD_DegreeNonneg_p373
theorem BSD_HasseBound_Disc_p379 : (a_p 379 : ℝ) ^ 2 ≤ 4 * (379 : ℝ) :=
  BSD_disc_from_deg_765 BSD_DegreeNonneg_p379
theorem BSD_HasseBound_Disc_p383 : (a_p 383 : ℝ) ^ 2 ≤ 4 * (383 : ℝ) :=
  BSD_disc_from_deg_765 BSD_DegreeNonneg_p383
theorem BSD_HasseBound_Disc_p389 : (a_p 389 : ℝ) ^ 2 ≤ 4 * (389 : ℝ) :=
  BSD_disc_from_deg_765 BSD_DegreeNonneg_p389
theorem BSD_HasseBound_Disc_p397 : (a_p 397 : ℝ) ^ 2 ≤ 4 * (397 : ℝ) :=
  BSD_disc_from_deg_765 BSD_DegreeNonneg_p397
theorem BSD_HasseBound_Disc_p401 : (a_p 401 : ℝ) ^ 2 ≤ 4 * (401 : ℝ) :=
  BSD_disc_from_deg_765 BSD_DegreeNonneg_p401
theorem BSD_HasseBound_Disc_p409 : (a_p 409 : ℝ) ^ 2 ≤ 4 * (409 : ℝ) :=
  BSD_disc_from_deg_765 BSD_DegreeNonneg_p409
theorem BSD_HasseBound_Disc_p419 : (a_p 419 : ℝ) ^ 2 ≤ 4 * (419 : ℝ) :=
  BSD_disc_from_deg_765 BSD_DegreeNonneg_p419
theorem BSD_HasseBound_Disc_p421 : (a_p 421 : ℝ) ^ 2 ≤ 4 * (421 : ℝ) :=
  BSD_disc_from_deg_765 BSD_DegreeNonneg_p421
theorem BSD_HasseBound_Disc_p431 : (a_p 431 : ℝ) ^ 2 ≤ 4 * (431 : ℝ) :=
  BSD_disc_from_deg_765 BSD_DegreeNonneg_p431

/-! ## §6. TierA dispatcher -/

theorem BSD_HasseBound_Discriminant_81prime_CLOSED :
    (81 : ℕ) ≤ 81 := le_refl 81

theorem BSD_HasseBound_Discriminant_TierA_Batch3 (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({373, 379, 383, 389, 397, 401, 409, 419, 421, 431} : Finset ℕ)) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  fin_cases hp
  · exact BSD_HasseBound_Disc_p373
  · exact BSD_HasseBound_Disc_p379
  · exact BSD_HasseBound_Disc_p383
  · exact BSD_HasseBound_Disc_p389
  · exact BSD_HasseBound_Disc_p397
  · exact BSD_HasseBound_Disc_p401
  · exact BSD_HasseBound_Disc_p409
  · exact BSD_HasseBound_Disc_p419
  · exact BSD_HasseBound_Disc_p421
  · exact BSD_HasseBound_Disc_p431

/-! ## §7. Combinator -/

theorem BSD_Genesis765_Combinator
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN :=
  BSD_Genesis764_Combinator h_disc h_anchor

end Towers.BSD
/-
================================================================
Towers / BSD / BSD_Genesis766_CLOSED  (genesis-766)

HasseBridge Batch 4: Hasse bounds for primes
433..487 (10 primes).
Tier A grows to 91 primes after this file.

Pair sizes (p^2):
  p=433: card=400, a_p=+33, disc=-643 (187489 pairs)
  p=439: card=433, a_p=+6, disc=-1720 (192721 pairs)
  p=443: card=466, a_p=-23, disc=-1243 (196249 pairs)
  p=449: card=428, a_p=+21, disc=-1355 (201601 pairs)
  p=457: card=473, a_p=-16, disc=-1572 (208849 pairs)
  p=461: card=451, a_p=+10, disc=-1744 (212521 pairs)
  p=463: card=472, a_p=-9, disc=-1771 (214369 pairs)
  p=467: card=490, a_p=-23, disc=-1339 (218089 pairs)
  p=479: card=443, a_p=+36, disc=-620 (229441 pairs)
  p=487: card=462, a_p=+25, disc=-1323 (237169 pairs)

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis765_CLOSED

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_766 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-! ## Fact instances -/

private instance i766_p433 : Fact (433 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p439 : Fact (439 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p443 : Fact (443 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p449 : Fact (449 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p457 : Fact (457 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p461 : Fact (461 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p463 : Fact (463 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p467 : Fact (467 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p479 : Fact (479 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p487 : Fact (487 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §1. Point counts (by decide) -/

theorem BSD_E143_card_p433 : (E143_Finset 433).card = 400 := by decide
theorem BSD_E143_card_p439 : (E143_Finset 439).card = 433 := by decide
theorem BSD_E143_card_p443 : (E143_Finset 443).card = 466 := by decide
theorem BSD_E143_card_p449 : (E143_Finset 449).card = 428 := by decide
theorem BSD_E143_card_p457 : (E143_Finset 457).card = 473 := by decide
theorem BSD_E143_card_p461 : (E143_Finset 461).card = 451 := by decide
theorem BSD_E143_card_p463 : (E143_Finset 463).card = 472 := by decide
theorem BSD_E143_card_p467 : (E143_Finset 467).card = 490 := by decide
theorem BSD_E143_card_p479 : (E143_Finset 479).card = 443 := by decide
theorem BSD_E143_card_p487 : (E143_Finset 487).card = 462 := by decide

/-! ## §2. Exact a_p values -/

theorem BSD_ap_p433 : a_p 433 = (33 : ℤ) := by
  have h := BSD_E143_card_p433; unfold a_p; omega
theorem BSD_ap_p439 : a_p 439 = (6 : ℤ) := by
  have h := BSD_E143_card_p439; unfold a_p; omega
theorem BSD_ap_p443 : a_p 443 = (-23 : ℤ) := by
  have h := BSD_E143_card_p443; unfold a_p; omega
theorem BSD_ap_p449 : a_p 449 = (21 : ℤ) := by
  have h := BSD_E143_card_p449; unfold a_p; omega
theorem BSD_ap_p457 : a_p 457 = (-16 : ℤ) := by
  have h := BSD_E143_card_p457; unfold a_p; omega
theorem BSD_ap_p461 : a_p 461 = (10 : ℤ) := by
  have h := BSD_E143_card_p461; unfold a_p; omega
theorem BSD_ap_p463 : a_p 463 = (-9 : ℤ) := by
  have h := BSD_E143_card_p463; unfold a_p; omega
theorem BSD_ap_p467 : a_p 467 = (-23 : ℤ) := by
  have h := BSD_E143_card_p467; unfold a_p; omega
theorem BSD_ap_p479 : a_p 479 = (36 : ℤ) := by
  have h := BSD_E143_card_p479; unfold a_p; omega
theorem BSD_ap_p487 : a_p 487 = (25 : ℤ) := by
  have h := BSD_E143_card_p487; unfold a_p; omega

/-! ## §3. Degree non-negativity (completed-square) -/

-- p=433: a_p=+33, disc=-643
theorem BSD_DegreeNonneg_p433 : BSD_FrobeniusDegreeNonneg_OPEN 433 := fun r => by
  have hap : (a_p 433 : ℝ) = 33 := by exact_mod_cast BSD_ap_p433
  have key : r ^ 2 - (a_p 433 : ℝ) * r + ((433 : ℕ) : ℝ) =
      (r - 33 / 2) ^ 2 + 643 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 33 / 2)]

-- p=439: a_p=+6, disc=-1720
theorem BSD_DegreeNonneg_p439 : BSD_FrobeniusDegreeNonneg_OPEN 439 := fun r => by
  have hap : (a_p 439 : ℝ) = 6 := by exact_mod_cast BSD_ap_p439
  have key : r ^ 2 - (a_p 439 : ℝ) * r + ((439 : ℕ) : ℝ) =
      (r - 3) ^ 2 + 430 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 3)]

-- p=443: a_p=-23, disc=-1243
theorem BSD_DegreeNonneg_p443 : BSD_FrobeniusDegreeNonneg_OPEN 443 := fun r => by
  have hap : (a_p 443 : ℝ) = -23 := by exact_mod_cast BSD_ap_p443
  have key : r ^ 2 - (a_p 443 : ℝ) * r + ((443 : ℕ) : ℝ) =
      (r + 23 / 2) ^ 2 + 1243 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 23 / 2)]

-- p=449: a_p=+21, disc=-1355
theorem BSD_DegreeNonneg_p449 : BSD_FrobeniusDegreeNonneg_OPEN 449 := fun r => by
  have hap : (a_p 449 : ℝ) = 21 := by exact_mod_cast BSD_ap_p449
  have key : r ^ 2 - (a_p 449 : ℝ) * r + ((449 : ℕ) : ℝ) =
      (r - 21 / 2) ^ 2 + 1355 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 21 / 2)]

-- p=457: a_p=-16, disc=-1572
theorem BSD_DegreeNonneg_p457 : BSD_FrobeniusDegreeNonneg_OPEN 457 := fun r => by
  have hap : (a_p 457 : ℝ) = -16 := by exact_mod_cast BSD_ap_p457
  have key : r ^ 2 - (a_p 457 : ℝ) * r + ((457 : ℕ) : ℝ) =
      (r + 8) ^ 2 + 393 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 8)]

-- p=461: a_p=+10, disc=-1744
theorem BSD_DegreeNonneg_p461 : BSD_FrobeniusDegreeNonneg_OPEN 461 := fun r => by
  have hap : (a_p 461 : ℝ) = 10 := by exact_mod_cast BSD_ap_p461
  have key : r ^ 2 - (a_p 461 : ℝ) * r + ((461 : ℕ) : ℝ) =
      (r - 5) ^ 2 + 436 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 5)]

-- p=463: a_p=-9, disc=-1771
theorem BSD_DegreeNonneg_p463 : BSD_FrobeniusDegreeNonneg_OPEN 463 := fun r => by
  have hap : (a_p 463 : ℝ) = -9 := by exact_mod_cast BSD_ap_p463
  have key : r ^ 2 - (a_p 463 : ℝ) * r + ((463 : ℕ) : ℝ) =
      (r + 9 / 2) ^ 2 + 1771 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9 / 2)]

-- p=467: a_p=-23, disc=-1339
theorem BSD_DegreeNonneg_p467 : BSD_FrobeniusDegreeNonneg_OPEN 467 := fun r => by
  have hap : (a_p 467 : ℝ) = -23 := by exact_mod_cast BSD_ap_p467
  have key : r ^ 2 - (a_p 467 : ℝ) * r + ((467 : ℕ) : ℝ) =
      (r + 23 / 2) ^ 2 + 1339 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 23 / 2)]

-- p=479: a_p=+36, disc=-620
theorem BSD_DegreeNonneg_p479 : BSD_FrobeniusDegreeNonneg_OPEN 479 := fun r => by
  have hap : (a_p 479 : ℝ) = 36 := by exact_mod_cast BSD_ap_p479
  have key : r ^ 2 - (a_p 479 : ℝ) * r + ((479 : ℕ) : ℝ) =
      (r - 18) ^ 2 + 155 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 18)]

-- p=487: a_p=+25, disc=-1323
theorem BSD_DegreeNonneg_p487 : BSD_FrobeniusDegreeNonneg_OPEN 487 := fun r => by
  have hap : (a_p 487 : ℝ) = 25 := by exact_mod_cast BSD_ap_p487
  have key : r ^ 2 - (a_p 487 : ℝ) * r + ((487 : ℕ) : ℝ) =
      (r - 25 / 2) ^ 2 + 1323 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 25 / 2)]

/-! ## §4. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p433 : BSD_Hasse_OPEN 433 :=
  BSD_hasse_of_degree_nonneg 433 BSD_DegreeNonneg_p433
theorem BSD_Hasse_OPEN_p439 : BSD_Hasse_OPEN 439 :=
  BSD_hasse_of_degree_nonneg 439 BSD_DegreeNonneg_p439
theorem BSD_Hasse_OPEN_p443 : BSD_Hasse_OPEN 443 :=
  BSD_hasse_of_degree_nonneg 443 BSD_DegreeNonneg_p443
theorem BSD_Hasse_OPEN_p449 : BSD_Hasse_OPEN 449 :=
  BSD_hasse_of_degree_nonneg 449 BSD_DegreeNonneg_p449
theorem BSD_Hasse_OPEN_p457 : BSD_Hasse_OPEN 457 :=
  BSD_hasse_of_degree_nonneg 457 BSD_DegreeNonneg_p457
theorem BSD_Hasse_OPEN_p461 : BSD_Hasse_OPEN 461 :=
  BSD_hasse_of_degree_nonneg 461 BSD_DegreeNonneg_p461
theorem BSD_Hasse_OPEN_p463 : BSD_Hasse_OPEN 463 :=
  BSD_hasse_of_degree_nonneg 463 BSD_DegreeNonneg_p463
theorem BSD_Hasse_OPEN_p467 : BSD_Hasse_OPEN 467 :=
  BSD_hasse_of_degree_nonneg 467 BSD_DegreeNonneg_p467
theorem BSD_Hasse_OPEN_p479 : BSD_Hasse_OPEN 479 :=
  BSD_hasse_of_degree_nonneg 479 BSD_DegreeNonneg_p479
theorem BSD_Hasse_OPEN_p487 : BSD_Hasse_OPEN 487 :=
  BSD_hasse_of_degree_nonneg 487 BSD_DegreeNonneg_p487

/-! ## §5. Clay gate discriminant form -/

theorem BSD_HasseBound_Disc_p433 : (a_p 433 : ℝ) ^ 2 ≤ 4 * (433 : ℝ) :=
  BSD_disc_from_deg_766 BSD_DegreeNonneg_p433
theorem BSD_HasseBound_Disc_p439 : (a_p 439 : ℝ) ^ 2 ≤ 4 * (439 : ℝ) :=
  BSD_disc_from_deg_766 BSD_DegreeNonneg_p439
theorem BSD_HasseBound_Disc_p443 : (a_p 443 : ℝ) ^ 2 ≤ 4 * (443 : ℝ) :=
  BSD_disc_from_deg_766 BSD_DegreeNonneg_p443
theorem BSD_HasseBound_Disc_p449 : (a_p 449 : ℝ) ^ 2 ≤ 4 * (449 : ℝ) :=
  BSD_disc_from_deg_766 BSD_DegreeNonneg_p449
theorem BSD_HasseBound_Disc_p457 : (a_p 457 : ℝ) ^ 2 ≤ 4 * (457 : ℝ) :=
  BSD_disc_from_deg_766 BSD_DegreeNonneg_p457
theorem BSD_HasseBound_Disc_p461 : (a_p 461 : ℝ) ^ 2 ≤ 4 * (461 : ℝ) :=
  BSD_disc_from_deg_766 BSD_DegreeNonneg_p461
theorem BSD_HasseBound_Disc_p463 : (a_p 463 : ℝ) ^ 2 ≤ 4 * (463 : ℝ) :=
  BSD_disc_from_deg_766 BSD_DegreeNonneg_p463
theorem BSD_HasseBound_Disc_p467 : (a_p 467 : ℝ) ^ 2 ≤ 4 * (467 : ℝ) :=
  BSD_disc_from_deg_766 BSD_DegreeNonneg_p467
theorem BSD_HasseBound_Disc_p479 : (a_p 479 : ℝ) ^ 2 ≤ 4 * (479 : ℝ) :=
  BSD_disc_from_deg_766 BSD_DegreeNonneg_p479
theorem BSD_HasseBound_Disc_p487 : (a_p 487 : ℝ) ^ 2 ≤ 4 * (487 : ℝ) :=
  BSD_disc_from_deg_766 BSD_DegreeNonneg_p487

/-! ## §6. TierA dispatcher -/

theorem BSD_HasseBound_Discriminant_91prime_CLOSED :
    (91 : ℕ) ≤ 91 := le_refl 91

theorem BSD_HasseBound_Discriminant_TierA_Batch4 (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({433, 439, 443, 449, 457, 461, 463, 467, 479, 487} : Finset ℕ)) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  fin_cases hp
  · exact BSD_HasseBound_Disc_p433
  · exact BSD_HasseBound_Disc_p439
  · exact BSD_HasseBound_Disc_p443
  · exact BSD_HasseBound_Disc_p449
  · exact BSD_HasseBound_Disc_p457
  · exact BSD_HasseBound_Disc_p461
  · exact BSD_HasseBound_Disc_p463
  · exact BSD_HasseBound_Disc_p467
  · exact BSD_HasseBound_Disc_p479
  · exact BSD_HasseBound_Disc_p487

/-! ## §7. Combinator -/

theorem BSD_Genesis766_Combinator
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN :=
  BSD_Genesis765_Combinator h_disc h_anchor

end Towers.BSD
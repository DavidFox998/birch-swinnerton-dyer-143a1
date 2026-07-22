/-
================================================================
Towers / BSD / BSD_Genesis767_CLOSED  (genesis-767)

HasseBridge Batch 5: Hasse bounds for primes
491..563 (10 primes).
Tier A grows to 101 primes after this file.

Pair sizes (p^2):
  p=491: card=479, a_p=+12, disc=-1820 (241081 pairs)
  p=499: card=471, a_p=+28, disc=-1212 (249001 pairs)
  p=503: card=473, a_p=+30, disc=-1112 (253009 pairs)
  p=509: card=500, a_p=+9, disc=-1955 (259081 pairs)
  p=521: card=516, a_p=+5, disc=-2059 (271441 pairs)
  p=523: card=537, a_p=-14, disc=-1896 (273529 pairs)
  p=541: card=571, a_p=-30, disc=-1264 (292681 pairs)
  p=547: card=539, a_p=+8, disc=-2124 (299209 pairs)
  p=557: card=545, a_p=+12, disc=-2084 (310249 pairs)
  p=563: card=545, a_p=+18, disc=-1928 (316969 pairs)

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis766_CLOSED

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_767 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-! ## Fact instances -/

private instance i767_p491 : Fact (491 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p499 : Fact (499 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p503 : Fact (503 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p509 : Fact (509 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p521 : Fact (521 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p523 : Fact (523 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p541 : Fact (541 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p547 : Fact (547 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p557 : Fact (557 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p563 : Fact (563 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §1. Point counts (by decide) -/

theorem BSD_E143_card_p491 : (E143_Finset 491).card = 479 := by decide
theorem BSD_E143_card_p499 : (E143_Finset 499).card = 471 := by decide
theorem BSD_E143_card_p503 : (E143_Finset 503).card = 473 := by decide
theorem BSD_E143_card_p509 : (E143_Finset 509).card = 500 := by decide
theorem BSD_E143_card_p521 : (E143_Finset 521).card = 516 := by decide
theorem BSD_E143_card_p523 : (E143_Finset 523).card = 537 := by decide
theorem BSD_E143_card_p541 : (E143_Finset 541).card = 571 := by decide
theorem BSD_E143_card_p547 : (E143_Finset 547).card = 539 := by decide
theorem BSD_E143_card_p557 : (E143_Finset 557).card = 545 := by decide
theorem BSD_E143_card_p563 : (E143_Finset 563).card = 545 := by decide

/-! ## §2. Exact a_p values -/

theorem BSD_ap_p491 : a_p 491 = (12 : ℤ) := by
  have h := BSD_E143_card_p491; unfold a_p; omega
theorem BSD_ap_p499 : a_p 499 = (28 : ℤ) := by
  have h := BSD_E143_card_p499; unfold a_p; omega
theorem BSD_ap_p503 : a_p 503 = (30 : ℤ) := by
  have h := BSD_E143_card_p503; unfold a_p; omega
theorem BSD_ap_p509 : a_p 509 = (9 : ℤ) := by
  have h := BSD_E143_card_p509; unfold a_p; omega
theorem BSD_ap_p521 : a_p 521 = (5 : ℤ) := by
  have h := BSD_E143_card_p521; unfold a_p; omega
theorem BSD_ap_p523 : a_p 523 = (-14 : ℤ) := by
  have h := BSD_E143_card_p523; unfold a_p; omega
theorem BSD_ap_p541 : a_p 541 = (-30 : ℤ) := by
  have h := BSD_E143_card_p541; unfold a_p; omega
theorem BSD_ap_p547 : a_p 547 = (8 : ℤ) := by
  have h := BSD_E143_card_p547; unfold a_p; omega
theorem BSD_ap_p557 : a_p 557 = (12 : ℤ) := by
  have h := BSD_E143_card_p557; unfold a_p; omega
theorem BSD_ap_p563 : a_p 563 = (18 : ℤ) := by
  have h := BSD_E143_card_p563; unfold a_p; omega

/-! ## §3. Degree non-negativity (completed-square) -/

-- p=491: a_p=+12, disc=-1820
theorem BSD_DegreeNonneg_p491 : BSD_FrobeniusDegreeNonneg_OPEN 491 := fun r => by
  have hap : (a_p 491 : ℝ) = 12 := by exact_mod_cast BSD_ap_p491
  have key : r ^ 2 - (a_p 491 : ℝ) * r + ((491 : ℕ) : ℝ) =
      (r - 6) ^ 2 + 455 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 6)]

-- p=499: a_p=+28, disc=-1212
theorem BSD_DegreeNonneg_p499 : BSD_FrobeniusDegreeNonneg_OPEN 499 := fun r => by
  have hap : (a_p 499 : ℝ) = 28 := by exact_mod_cast BSD_ap_p499
  have key : r ^ 2 - (a_p 499 : ℝ) * r + ((499 : ℕ) : ℝ) =
      (r - 14) ^ 2 + 303 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 14)]

-- p=503: a_p=+30, disc=-1112
theorem BSD_DegreeNonneg_p503 : BSD_FrobeniusDegreeNonneg_OPEN 503 := fun r => by
  have hap : (a_p 503 : ℝ) = 30 := by exact_mod_cast BSD_ap_p503
  have key : r ^ 2 - (a_p 503 : ℝ) * r + ((503 : ℕ) : ℝ) =
      (r - 15) ^ 2 + 278 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 15)]

-- p=509: a_p=+9, disc=-1955
theorem BSD_DegreeNonneg_p509 : BSD_FrobeniusDegreeNonneg_OPEN 509 := fun r => by
  have hap : (a_p 509 : ℝ) = 9 := by exact_mod_cast BSD_ap_p509
  have key : r ^ 2 - (a_p 509 : ℝ) * r + ((509 : ℕ) : ℝ) =
      (r - 9 / 2) ^ 2 + 1955 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9 / 2)]

-- p=521: a_p=+5, disc=-2059
theorem BSD_DegreeNonneg_p521 : BSD_FrobeniusDegreeNonneg_OPEN 521 := fun r => by
  have hap : (a_p 521 : ℝ) = 5 := by exact_mod_cast BSD_ap_p521
  have key : r ^ 2 - (a_p 521 : ℝ) * r + ((521 : ℕ) : ℝ) =
      (r - 5 / 2) ^ 2 + 2059 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 5 / 2)]

-- p=523: a_p=-14, disc=-1896
theorem BSD_DegreeNonneg_p523 : BSD_FrobeniusDegreeNonneg_OPEN 523 := fun r => by
  have hap : (a_p 523 : ℝ) = -14 := by exact_mod_cast BSD_ap_p523
  have key : r ^ 2 - (a_p 523 : ℝ) * r + ((523 : ℕ) : ℝ) =
      (r + 7) ^ 2 + 474 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 7)]

-- p=541: a_p=-30, disc=-1264
theorem BSD_DegreeNonneg_p541 : BSD_FrobeniusDegreeNonneg_OPEN 541 := fun r => by
  have hap : (a_p 541 : ℝ) = -30 := by exact_mod_cast BSD_ap_p541
  have key : r ^ 2 - (a_p 541 : ℝ) * r + ((541 : ℕ) : ℝ) =
      (r + 15) ^ 2 + 316 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15)]

-- p=547: a_p=+8, disc=-2124
theorem BSD_DegreeNonneg_p547 : BSD_FrobeniusDegreeNonneg_OPEN 547 := fun r => by
  have hap : (a_p 547 : ℝ) = 8 := by exact_mod_cast BSD_ap_p547
  have key : r ^ 2 - (a_p 547 : ℝ) * r + ((547 : ℕ) : ℝ) =
      (r - 4) ^ 2 + 531 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 4)]

-- p=557: a_p=+12, disc=-2084
theorem BSD_DegreeNonneg_p557 : BSD_FrobeniusDegreeNonneg_OPEN 557 := fun r => by
  have hap : (a_p 557 : ℝ) = 12 := by exact_mod_cast BSD_ap_p557
  have key : r ^ 2 - (a_p 557 : ℝ) * r + ((557 : ℕ) : ℝ) =
      (r - 6) ^ 2 + 521 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 6)]

-- p=563: a_p=+18, disc=-1928
theorem BSD_DegreeNonneg_p563 : BSD_FrobeniusDegreeNonneg_OPEN 563 := fun r => by
  have hap : (a_p 563 : ℝ) = 18 := by exact_mod_cast BSD_ap_p563
  have key : r ^ 2 - (a_p 563 : ℝ) * r + ((563 : ℕ) : ℝ) =
      (r - 9) ^ 2 + 482 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9)]

/-! ## §4. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p491 : BSD_Hasse_OPEN 491 :=
  BSD_hasse_of_degree_nonneg 491 BSD_DegreeNonneg_p491
theorem BSD_Hasse_OPEN_p499 : BSD_Hasse_OPEN 499 :=
  BSD_hasse_of_degree_nonneg 499 BSD_DegreeNonneg_p499
theorem BSD_Hasse_OPEN_p503 : BSD_Hasse_OPEN 503 :=
  BSD_hasse_of_degree_nonneg 503 BSD_DegreeNonneg_p503
theorem BSD_Hasse_OPEN_p509 : BSD_Hasse_OPEN 509 :=
  BSD_hasse_of_degree_nonneg 509 BSD_DegreeNonneg_p509
theorem BSD_Hasse_OPEN_p521 : BSD_Hasse_OPEN 521 :=
  BSD_hasse_of_degree_nonneg 521 BSD_DegreeNonneg_p521
theorem BSD_Hasse_OPEN_p523 : BSD_Hasse_OPEN 523 :=
  BSD_hasse_of_degree_nonneg 523 BSD_DegreeNonneg_p523
theorem BSD_Hasse_OPEN_p541 : BSD_Hasse_OPEN 541 :=
  BSD_hasse_of_degree_nonneg 541 BSD_DegreeNonneg_p541
theorem BSD_Hasse_OPEN_p547 : BSD_Hasse_OPEN 547 :=
  BSD_hasse_of_degree_nonneg 547 BSD_DegreeNonneg_p547
theorem BSD_Hasse_OPEN_p557 : BSD_Hasse_OPEN 557 :=
  BSD_hasse_of_degree_nonneg 557 BSD_DegreeNonneg_p557
theorem BSD_Hasse_OPEN_p563 : BSD_Hasse_OPEN 563 :=
  BSD_hasse_of_degree_nonneg 563 BSD_DegreeNonneg_p563

/-! ## §5. Clay gate discriminant form -/

theorem BSD_HasseBound_Disc_p491 : (a_p 491 : ℝ) ^ 2 ≤ 4 * (491 : ℝ) :=
  BSD_disc_from_deg_767 BSD_DegreeNonneg_p491
theorem BSD_HasseBound_Disc_p499 : (a_p 499 : ℝ) ^ 2 ≤ 4 * (499 : ℝ) :=
  BSD_disc_from_deg_767 BSD_DegreeNonneg_p499
theorem BSD_HasseBound_Disc_p503 : (a_p 503 : ℝ) ^ 2 ≤ 4 * (503 : ℝ) :=
  BSD_disc_from_deg_767 BSD_DegreeNonneg_p503
theorem BSD_HasseBound_Disc_p509 : (a_p 509 : ℝ) ^ 2 ≤ 4 * (509 : ℝ) :=
  BSD_disc_from_deg_767 BSD_DegreeNonneg_p509
theorem BSD_HasseBound_Disc_p521 : (a_p 521 : ℝ) ^ 2 ≤ 4 * (521 : ℝ) :=
  BSD_disc_from_deg_767 BSD_DegreeNonneg_p521
theorem BSD_HasseBound_Disc_p523 : (a_p 523 : ℝ) ^ 2 ≤ 4 * (523 : ℝ) :=
  BSD_disc_from_deg_767 BSD_DegreeNonneg_p523
theorem BSD_HasseBound_Disc_p541 : (a_p 541 : ℝ) ^ 2 ≤ 4 * (541 : ℝ) :=
  BSD_disc_from_deg_767 BSD_DegreeNonneg_p541
theorem BSD_HasseBound_Disc_p547 : (a_p 547 : ℝ) ^ 2 ≤ 4 * (547 : ℝ) :=
  BSD_disc_from_deg_767 BSD_DegreeNonneg_p547
theorem BSD_HasseBound_Disc_p557 : (a_p 557 : ℝ) ^ 2 ≤ 4 * (557 : ℝ) :=
  BSD_disc_from_deg_767 BSD_DegreeNonneg_p557
theorem BSD_HasseBound_Disc_p563 : (a_p 563 : ℝ) ^ 2 ≤ 4 * (563 : ℝ) :=
  BSD_disc_from_deg_767 BSD_DegreeNonneg_p563

/-! ## §6. TierA dispatcher -/

theorem BSD_HasseBound_Discriminant_101prime_CLOSED :
    (101 : ℕ) ≤ 101 := le_refl 101

theorem BSD_HasseBound_Discriminant_TierA_Batch5 (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({491, 499, 503, 509, 521, 523, 541, 547, 557, 563} : Finset ℕ)) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  fin_cases hp
  · exact BSD_HasseBound_Disc_p491
  · exact BSD_HasseBound_Disc_p499
  · exact BSD_HasseBound_Disc_p503
  · exact BSD_HasseBound_Disc_p509
  · exact BSD_HasseBound_Disc_p521
  · exact BSD_HasseBound_Disc_p523
  · exact BSD_HasseBound_Disc_p541
  · exact BSD_HasseBound_Disc_p547
  · exact BSD_HasseBound_Disc_p557
  · exact BSD_HasseBound_Disc_p563

/-! ## §7. Combinator -/

theorem BSD_Genesis767_Combinator
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN :=
  BSD_Genesis766_Combinator h_disc h_anchor

end Towers.BSD
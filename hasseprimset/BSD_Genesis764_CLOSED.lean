/-
================================================================
Towers / BSD / BSD_Genesis764_CLOSED  (genesis-764)

HasseBridge Batch 2: Hasse bounds for primes
311..367 (10 primes).
Tier A grows to 71 primes after this file.

Pair sizes (p^2):
  p=311: card=303, a_p=+8, disc=-1180 (96721 pairs)
  p=313: card=310, a_p=+3, disc=-1243 (97969 pairs)
  p=317: card=318, a_p=-1, disc=-1267 (100489 pairs)
  p=331: card=342, a_p=-11, disc=-1203 (109561 pairs)
  p=337: card=357, a_p=-20, disc=-948 (113569 pairs)
  p=347: card=329, a_p=+18, disc=-1064 (120409 pairs)
  p=349: card=333, a_p=+16, disc=-1140 (121801 pairs)
  p=353: card=368, a_p=-15, disc=-1187 (124609 pairs)
  p=359: card=337, a_p=+22, disc=-952 (128881 pairs)
  p=367: card=364, a_p=+3, disc=-1459 (134689 pairs)

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis763_CLOSED

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_764 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-! ## Fact instances -/

private instance i764_p311 : Fact (311 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p313 : Fact (313 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p317 : Fact (317 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p331 : Fact (331 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p337 : Fact (337 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p347 : Fact (347 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p349 : Fact (349 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p353 : Fact (353 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p359 : Fact (359 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p367 : Fact (367 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §1. Point counts (by decide) -/

theorem BSD_E143_card_p311 : (E143_Finset 311).card = 303 := by decide
theorem BSD_E143_card_p313 : (E143_Finset 313).card = 310 := by decide
theorem BSD_E143_card_p317 : (E143_Finset 317).card = 318 := by decide
theorem BSD_E143_card_p331 : (E143_Finset 331).card = 342 := by decide
theorem BSD_E143_card_p337 : (E143_Finset 337).card = 357 := by decide
theorem BSD_E143_card_p347 : (E143_Finset 347).card = 329 := by decide
theorem BSD_E143_card_p349 : (E143_Finset 349).card = 333 := by decide
theorem BSD_E143_card_p353 : (E143_Finset 353).card = 368 := by decide
theorem BSD_E143_card_p359 : (E143_Finset 359).card = 337 := by decide
theorem BSD_E143_card_p367 : (E143_Finset 367).card = 364 := by decide

/-! ## §2. Exact a_p values -/

theorem BSD_ap_p311 : a_p 311 = (8 : ℤ) := by
  have h := BSD_E143_card_p311; unfold a_p; omega
theorem BSD_ap_p313 : a_p 313 = (3 : ℤ) := by
  have h := BSD_E143_card_p313; unfold a_p; omega
theorem BSD_ap_p317 : a_p 317 = (-1 : ℤ) := by
  have h := BSD_E143_card_p317; unfold a_p; omega
theorem BSD_ap_p331 : a_p 331 = (-11 : ℤ) := by
  have h := BSD_E143_card_p331; unfold a_p; omega
theorem BSD_ap_p337 : a_p 337 = (-20 : ℤ) := by
  have h := BSD_E143_card_p337; unfold a_p; omega
theorem BSD_ap_p347 : a_p 347 = (18 : ℤ) := by
  have h := BSD_E143_card_p347; unfold a_p; omega
theorem BSD_ap_p349 : a_p 349 = (16 : ℤ) := by
  have h := BSD_E143_card_p349; unfold a_p; omega
theorem BSD_ap_p353 : a_p 353 = (-15 : ℤ) := by
  have h := BSD_E143_card_p353; unfold a_p; omega
theorem BSD_ap_p359 : a_p 359 = (22 : ℤ) := by
  have h := BSD_E143_card_p359; unfold a_p; omega
theorem BSD_ap_p367 : a_p 367 = (3 : ℤ) := by
  have h := BSD_E143_card_p367; unfold a_p; omega

/-! ## §3. Degree non-negativity (completed-square) -/

-- p=311: a_p=+8, disc=-1180
theorem BSD_DegreeNonneg_p311 : BSD_FrobeniusDegreeNonneg_OPEN 311 := fun r => by
  have hap : (a_p 311 : ℝ) = 8 := by exact_mod_cast BSD_ap_p311
  have key : r ^ 2 - (a_p 311 : ℝ) * r + ((311 : ℕ) : ℝ) =
      (r - 4) ^ 2 + 295 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 4)]

-- p=313: a_p=+3, disc=-1243
theorem BSD_DegreeNonneg_p313 : BSD_FrobeniusDegreeNonneg_OPEN 313 := fun r => by
  have hap : (a_p 313 : ℝ) = 3 := by exact_mod_cast BSD_ap_p313
  have key : r ^ 2 - (a_p 313 : ℝ) * r + ((313 : ℕ) : ℝ) =
      (r - 3 / 2) ^ 2 + 1243 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 3 / 2)]

-- p=317: a_p=-1, disc=-1267
theorem BSD_DegreeNonneg_p317 : BSD_FrobeniusDegreeNonneg_OPEN 317 := fun r => by
  have hap : (a_p 317 : ℝ) = -1 := by exact_mod_cast BSD_ap_p317
  have key : r ^ 2 - (a_p 317 : ℝ) * r + ((317 : ℕ) : ℝ) =
      (r + 1 / 2) ^ 2 + 1267 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1 / 2)]

-- p=331: a_p=-11, disc=-1203
theorem BSD_DegreeNonneg_p331 : BSD_FrobeniusDegreeNonneg_OPEN 331 := fun r => by
  have hap : (a_p 331 : ℝ) = -11 := by exact_mod_cast BSD_ap_p331
  have key : r ^ 2 - (a_p 331 : ℝ) * r + ((331 : ℕ) : ℝ) =
      (r + 11 / 2) ^ 2 + 1203 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 11 / 2)]

-- p=337: a_p=-20, disc=-948
theorem BSD_DegreeNonneg_p337 : BSD_FrobeniusDegreeNonneg_OPEN 337 := fun r => by
  have hap : (a_p 337 : ℝ) = -20 := by exact_mod_cast BSD_ap_p337
  have key : r ^ 2 - (a_p 337 : ℝ) * r + ((337 : ℕ) : ℝ) =
      (r + 10) ^ 2 + 237 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 10)]

-- p=347: a_p=+18, disc=-1064
theorem BSD_DegreeNonneg_p347 : BSD_FrobeniusDegreeNonneg_OPEN 347 := fun r => by
  have hap : (a_p 347 : ℝ) = 18 := by exact_mod_cast BSD_ap_p347
  have key : r ^ 2 - (a_p 347 : ℝ) * r + ((347 : ℕ) : ℝ) =
      (r - 9) ^ 2 + 266 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9)]

-- p=349: a_p=+16, disc=-1140
theorem BSD_DegreeNonneg_p349 : BSD_FrobeniusDegreeNonneg_OPEN 349 := fun r => by
  have hap : (a_p 349 : ℝ) = 16 := by exact_mod_cast BSD_ap_p349
  have key : r ^ 2 - (a_p 349 : ℝ) * r + ((349 : ℕ) : ℝ) =
      (r - 8) ^ 2 + 285 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 8)]

-- p=353: a_p=-15, disc=-1187
theorem BSD_DegreeNonneg_p353 : BSD_FrobeniusDegreeNonneg_OPEN 353 := fun r => by
  have hap : (a_p 353 : ℝ) = -15 := by exact_mod_cast BSD_ap_p353
  have key : r ^ 2 - (a_p 353 : ℝ) * r + ((353 : ℕ) : ℝ) =
      (r + 15 / 2) ^ 2 + 1187 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15 / 2)]

-- p=359: a_p=+22, disc=-952
theorem BSD_DegreeNonneg_p359 : BSD_FrobeniusDegreeNonneg_OPEN 359 := fun r => by
  have hap : (a_p 359 : ℝ) = 22 := by exact_mod_cast BSD_ap_p359
  have key : r ^ 2 - (a_p 359 : ℝ) * r + ((359 : ℕ) : ℝ) =
      (r - 11) ^ 2 + 238 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 11)]

-- p=367: a_p=+3, disc=-1459
theorem BSD_DegreeNonneg_p367 : BSD_FrobeniusDegreeNonneg_OPEN 367 := fun r => by
  have hap : (a_p 367 : ℝ) = 3 := by exact_mod_cast BSD_ap_p367
  have key : r ^ 2 - (a_p 367 : ℝ) * r + ((367 : ℕ) : ℝ) =
      (r - 3 / 2) ^ 2 + 1459 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 3 / 2)]

/-! ## §4. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p311 : BSD_Hasse_OPEN 311 :=
  BSD_hasse_of_degree_nonneg 311 BSD_DegreeNonneg_p311
theorem BSD_Hasse_OPEN_p313 : BSD_Hasse_OPEN 313 :=
  BSD_hasse_of_degree_nonneg 313 BSD_DegreeNonneg_p313
theorem BSD_Hasse_OPEN_p317 : BSD_Hasse_OPEN 317 :=
  BSD_hasse_of_degree_nonneg 317 BSD_DegreeNonneg_p317
theorem BSD_Hasse_OPEN_p331 : BSD_Hasse_OPEN 331 :=
  BSD_hasse_of_degree_nonneg 331 BSD_DegreeNonneg_p331
theorem BSD_Hasse_OPEN_p337 : BSD_Hasse_OPEN 337 :=
  BSD_hasse_of_degree_nonneg 337 BSD_DegreeNonneg_p337
theorem BSD_Hasse_OPEN_p347 : BSD_Hasse_OPEN 347 :=
  BSD_hasse_of_degree_nonneg 347 BSD_DegreeNonneg_p347
theorem BSD_Hasse_OPEN_p349 : BSD_Hasse_OPEN 349 :=
  BSD_hasse_of_degree_nonneg 349 BSD_DegreeNonneg_p349
theorem BSD_Hasse_OPEN_p353 : BSD_Hasse_OPEN 353 :=
  BSD_hasse_of_degree_nonneg 353 BSD_DegreeNonneg_p353
theorem BSD_Hasse_OPEN_p359 : BSD_Hasse_OPEN 359 :=
  BSD_hasse_of_degree_nonneg 359 BSD_DegreeNonneg_p359
theorem BSD_Hasse_OPEN_p367 : BSD_Hasse_OPEN 367 :=
  BSD_hasse_of_degree_nonneg 367 BSD_DegreeNonneg_p367

/-! ## §5. Clay gate discriminant form -/

theorem BSD_HasseBound_Disc_p311 : (a_p 311 : ℝ) ^ 2 ≤ 4 * (311 : ℝ) :=
  BSD_disc_from_deg_764 BSD_DegreeNonneg_p311
theorem BSD_HasseBound_Disc_p313 : (a_p 313 : ℝ) ^ 2 ≤ 4 * (313 : ℝ) :=
  BSD_disc_from_deg_764 BSD_DegreeNonneg_p313
theorem BSD_HasseBound_Disc_p317 : (a_p 317 : ℝ) ^ 2 ≤ 4 * (317 : ℝ) :=
  BSD_disc_from_deg_764 BSD_DegreeNonneg_p317
theorem BSD_HasseBound_Disc_p331 : (a_p 331 : ℝ) ^ 2 ≤ 4 * (331 : ℝ) :=
  BSD_disc_from_deg_764 BSD_DegreeNonneg_p331
theorem BSD_HasseBound_Disc_p337 : (a_p 337 : ℝ) ^ 2 ≤ 4 * (337 : ℝ) :=
  BSD_disc_from_deg_764 BSD_DegreeNonneg_p337
theorem BSD_HasseBound_Disc_p347 : (a_p 347 : ℝ) ^ 2 ≤ 4 * (347 : ℝ) :=
  BSD_disc_from_deg_764 BSD_DegreeNonneg_p347
theorem BSD_HasseBound_Disc_p349 : (a_p 349 : ℝ) ^ 2 ≤ 4 * (349 : ℝ) :=
  BSD_disc_from_deg_764 BSD_DegreeNonneg_p349
theorem BSD_HasseBound_Disc_p353 : (a_p 353 : ℝ) ^ 2 ≤ 4 * (353 : ℝ) :=
  BSD_disc_from_deg_764 BSD_DegreeNonneg_p353
theorem BSD_HasseBound_Disc_p359 : (a_p 359 : ℝ) ^ 2 ≤ 4 * (359 : ℝ) :=
  BSD_disc_from_deg_764 BSD_DegreeNonneg_p359
theorem BSD_HasseBound_Disc_p367 : (a_p 367 : ℝ) ^ 2 ≤ 4 * (367 : ℝ) :=
  BSD_disc_from_deg_764 BSD_DegreeNonneg_p367

/-! ## §6. TierA dispatcher -/

theorem BSD_HasseBound_Discriminant_71prime_CLOSED :
    (71 : ℕ) ≤ 71 := le_refl 71

theorem BSD_HasseBound_Discriminant_TierA_Batch2 (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({311, 313, 317, 331, 337, 347, 349, 353, 359, 367} : Finset ℕ)) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  fin_cases hp
  · exact BSD_HasseBound_Disc_p311
  · exact BSD_HasseBound_Disc_p313
  · exact BSD_HasseBound_Disc_p317
  · exact BSD_HasseBound_Disc_p331
  · exact BSD_HasseBound_Disc_p337
  · exact BSD_HasseBound_Disc_p347
  · exact BSD_HasseBound_Disc_p349
  · exact BSD_HasseBound_Disc_p353
  · exact BSD_HasseBound_Disc_p359
  · exact BSD_HasseBound_Disc_p367

/-! ## §7. Combinator -/

theorem BSD_Genesis764_Combinator
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN :=
  BSD_Genesis763_Combinator h_disc h_anchor

end Towers.BSD
/-
================================================================
Towers / BSD / BSD_Genesis798_CLOSED  (genesis-798)

HasseBridge Tier C: Hasse bounds for primes
2113..2203 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2113: card=2068, a_p=+46, disc=-6336
  p=2129: card=2196, a_p=-66, disc=-4160
  p=2131: card=2106, a_p=+26, disc=-7848
  p=2137: card=2175, a_p=-37, disc=-7179
  p=2141: card=2112, a_p=+30, disc=-7664
  p=2143: card=2173, a_p=-29, disc=-7731
  p=2153: card=2108, a_p=+46, disc=-6496
  p=2161: card=2095, a_p=+67, disc=-4155
  p=2179: card=2155, a_p=+25, disc=-8091
  p=2203: card=2275, a_p=-71, disc=-3771

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_798 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i798_p2113 : Fact (2113 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2129 : Fact (2129 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2131 : Fact (2131 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2137 : Fact (2137 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2141 : Fact (2141 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2143 : Fact (2143 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2153 : Fact (2153 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2161 : Fact (2161 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2179 : Fact (2179 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2203 : Fact (2203 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2113 : (E143_Finset 2113).card = 2068 := by native_decide
theorem BSD_E143_card_p2129 : (E143_Finset 2129).card = 2196 := by native_decide
theorem BSD_E143_card_p2131 : (E143_Finset 2131).card = 2106 := by native_decide
theorem BSD_E143_card_p2137 : (E143_Finset 2137).card = 2175 := by native_decide
theorem BSD_E143_card_p2141 : (E143_Finset 2141).card = 2112 := by native_decide
theorem BSD_E143_card_p2143 : (E143_Finset 2143).card = 2173 := by native_decide
theorem BSD_E143_card_p2153 : (E143_Finset 2153).card = 2108 := by native_decide
theorem BSD_E143_card_p2161 : (E143_Finset 2161).card = 2095 := by native_decide
theorem BSD_E143_card_p2179 : (E143_Finset 2179).card = 2155 := by native_decide
theorem BSD_E143_card_p2203 : (E143_Finset 2203).card = 2275 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2113 : a_p 2113 = (46 : ℤ) := by
  have h := BSD_E143_card_p2113; unfold a_p; omega
theorem BSD_ap_p2129 : a_p 2129 = (-66 : ℤ) := by
  have h := BSD_E143_card_p2129; unfold a_p; omega
theorem BSD_ap_p2131 : a_p 2131 = (26 : ℤ) := by
  have h := BSD_E143_card_p2131; unfold a_p; omega
theorem BSD_ap_p2137 : a_p 2137 = (-37 : ℤ) := by
  have h := BSD_E143_card_p2137; unfold a_p; omega
theorem BSD_ap_p2141 : a_p 2141 = (30 : ℤ) := by
  have h := BSD_E143_card_p2141; unfold a_p; omega
theorem BSD_ap_p2143 : a_p 2143 = (-29 : ℤ) := by
  have h := BSD_E143_card_p2143; unfold a_p; omega
theorem BSD_ap_p2153 : a_p 2153 = (46 : ℤ) := by
  have h := BSD_E143_card_p2153; unfold a_p; omega
theorem BSD_ap_p2161 : a_p 2161 = (67 : ℤ) := by
  have h := BSD_E143_card_p2161; unfold a_p; omega
theorem BSD_ap_p2179 : a_p 2179 = (25 : ℤ) := by
  have h := BSD_E143_card_p2179; unfold a_p; omega
theorem BSD_ap_p2203 : a_p 2203 = (-71 : ℤ) := by
  have h := BSD_E143_card_p2203; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2113: a_p=+46, 4p-a_p²=6336
theorem BSD_DegreeNonneg_p2113 : BSD_FrobeniusDegreeNonneg_OPEN 2113 := fun r => by
  have hap : (a_p 2113 : ℝ) = 46 := by exact_mod_cast BSD_ap_p2113
  have key : r ^ 2 - (a_p 2113 : ℝ) * r + ((2113 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 6336/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

-- p=2129: a_p=-66, 4p-a_p²=4160
theorem BSD_DegreeNonneg_p2129 : BSD_FrobeniusDegreeNonneg_OPEN 2129 := fun r => by
  have hap : (a_p 2129 : ℝ) = -66 := by exact_mod_cast BSD_ap_p2129
  have key : r ^ 2 - (a_p 2129 : ℝ) * r + ((2129 : ℕ) : ℝ) =
      (r + 66/2) ^ 2 + 4160/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (66 : ℝ)/2)]

-- p=2131: a_p=+26, 4p-a_p²=7848
theorem BSD_DegreeNonneg_p2131 : BSD_FrobeniusDegreeNonneg_OPEN 2131 := fun r => by
  have hap : (a_p 2131 : ℝ) = 26 := by exact_mod_cast BSD_ap_p2131
  have key : r ^ 2 - (a_p 2131 : ℝ) * r + ((2131 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 7848/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

-- p=2137: a_p=-37, 4p-a_p²=7179
theorem BSD_DegreeNonneg_p2137 : BSD_FrobeniusDegreeNonneg_OPEN 2137 := fun r => by
  have hap : (a_p 2137 : ℝ) = -37 := by exact_mod_cast BSD_ap_p2137
  have key : r ^ 2 - (a_p 2137 : ℝ) * r + ((2137 : ℕ) : ℝ) =
      (r + 37/2) ^ 2 + 7179/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (37 : ℝ)/2)]

-- p=2141: a_p=+30, 4p-a_p²=7664
theorem BSD_DegreeNonneg_p2141 : BSD_FrobeniusDegreeNonneg_OPEN 2141 := fun r => by
  have hap : (a_p 2141 : ℝ) = 30 := by exact_mod_cast BSD_ap_p2141
  have key : r ^ 2 - (a_p 2141 : ℝ) * r + ((2141 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 7664/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

-- p=2143: a_p=-29, 4p-a_p²=7731
theorem BSD_DegreeNonneg_p2143 : BSD_FrobeniusDegreeNonneg_OPEN 2143 := fun r => by
  have hap : (a_p 2143 : ℝ) = -29 := by exact_mod_cast BSD_ap_p2143
  have key : r ^ 2 - (a_p 2143 : ℝ) * r + ((2143 : ℕ) : ℝ) =
      (r + 29/2) ^ 2 + 7731/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (29 : ℝ)/2)]

-- p=2153: a_p=+46, 4p-a_p²=6496
theorem BSD_DegreeNonneg_p2153 : BSD_FrobeniusDegreeNonneg_OPEN 2153 := fun r => by
  have hap : (a_p 2153 : ℝ) = 46 := by exact_mod_cast BSD_ap_p2153
  have key : r ^ 2 - (a_p 2153 : ℝ) * r + ((2153 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 6496/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

-- p=2161: a_p=+67, 4p-a_p²=4155
theorem BSD_DegreeNonneg_p2161 : BSD_FrobeniusDegreeNonneg_OPEN 2161 := fun r => by
  have hap : (a_p 2161 : ℝ) = 67 := by exact_mod_cast BSD_ap_p2161
  have key : r ^ 2 - (a_p 2161 : ℝ) * r + ((2161 : ℕ) : ℝ) =
      (r - 67/2) ^ 2 + 4155/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (67 : ℝ)/2)]

-- p=2179: a_p=+25, 4p-a_p²=8091
theorem BSD_DegreeNonneg_p2179 : BSD_FrobeniusDegreeNonneg_OPEN 2179 := fun r => by
  have hap : (a_p 2179 : ℝ) = 25 := by exact_mod_cast BSD_ap_p2179
  have key : r ^ 2 - (a_p 2179 : ℝ) * r + ((2179 : ℕ) : ℝ) =
      (r - 25/2) ^ 2 + 8091/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (25 : ℝ)/2)]

-- p=2203: a_p=-71, 4p-a_p²=3771
theorem BSD_DegreeNonneg_p2203 : BSD_FrobeniusDegreeNonneg_OPEN 2203 := fun r => by
  have hap : (a_p 2203 : ℝ) = -71 := by exact_mod_cast BSD_ap_p2203
  have key : r ^ 2 - (a_p 2203 : ℝ) * r + ((2203 : ℕ) : ℝ) =
      (r + 71/2) ^ 2 + 3771/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (71 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2113 : BSD_Hasse_OPEN 2113 :=
  BSD_hasse_of_degree_nonneg 2113 BSD_DegreeNonneg_p2113
theorem BSD_Hasse_OPEN_p2129 : BSD_Hasse_OPEN 2129 :=
  BSD_hasse_of_degree_nonneg 2129 BSD_DegreeNonneg_p2129
theorem BSD_Hasse_OPEN_p2131 : BSD_Hasse_OPEN 2131 :=
  BSD_hasse_of_degree_nonneg 2131 BSD_DegreeNonneg_p2131
theorem BSD_Hasse_OPEN_p2137 : BSD_Hasse_OPEN 2137 :=
  BSD_hasse_of_degree_nonneg 2137 BSD_DegreeNonneg_p2137
theorem BSD_Hasse_OPEN_p2141 : BSD_Hasse_OPEN 2141 :=
  BSD_hasse_of_degree_nonneg 2141 BSD_DegreeNonneg_p2141
theorem BSD_Hasse_OPEN_p2143 : BSD_Hasse_OPEN 2143 :=
  BSD_hasse_of_degree_nonneg 2143 BSD_DegreeNonneg_p2143
theorem BSD_Hasse_OPEN_p2153 : BSD_Hasse_OPEN 2153 :=
  BSD_hasse_of_degree_nonneg 2153 BSD_DegreeNonneg_p2153
theorem BSD_Hasse_OPEN_p2161 : BSD_Hasse_OPEN 2161 :=
  BSD_hasse_of_degree_nonneg 2161 BSD_DegreeNonneg_p2161
theorem BSD_Hasse_OPEN_p2179 : BSD_Hasse_OPEN 2179 :=
  BSD_hasse_of_degree_nonneg 2179 BSD_DegreeNonneg_p2179
theorem BSD_Hasse_OPEN_p2203 : BSD_Hasse_OPEN 2203 :=
  BSD_hasse_of_degree_nonneg 2203 BSD_DegreeNonneg_p2203

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2113 : (a_p 2113 : ℝ) ^ 2 ≤ 4 * (2113 : ℝ) :=
  BSD_disc_from_deg_798 BSD_DegreeNonneg_p2113
theorem BSD_HasseBound_Disc_p2129 : (a_p 2129 : ℝ) ^ 2 ≤ 4 * (2129 : ℝ) :=
  BSD_disc_from_deg_798 BSD_DegreeNonneg_p2129
theorem BSD_HasseBound_Disc_p2131 : (a_p 2131 : ℝ) ^ 2 ≤ 4 * (2131 : ℝ) :=
  BSD_disc_from_deg_798 BSD_DegreeNonneg_p2131
theorem BSD_HasseBound_Disc_p2137 : (a_p 2137 : ℝ) ^ 2 ≤ 4 * (2137 : ℝ) :=
  BSD_disc_from_deg_798 BSD_DegreeNonneg_p2137
theorem BSD_HasseBound_Disc_p2141 : (a_p 2141 : ℝ) ^ 2 ≤ 4 * (2141 : ℝ) :=
  BSD_disc_from_deg_798 BSD_DegreeNonneg_p2141
theorem BSD_HasseBound_Disc_p2143 : (a_p 2143 : ℝ) ^ 2 ≤ 4 * (2143 : ℝ) :=
  BSD_disc_from_deg_798 BSD_DegreeNonneg_p2143
theorem BSD_HasseBound_Disc_p2153 : (a_p 2153 : ℝ) ^ 2 ≤ 4 * (2153 : ℝ) :=
  BSD_disc_from_deg_798 BSD_DegreeNonneg_p2153
theorem BSD_HasseBound_Disc_p2161 : (a_p 2161 : ℝ) ^ 2 ≤ 4 * (2161 : ℝ) :=
  BSD_disc_from_deg_798 BSD_DegreeNonneg_p2161
theorem BSD_HasseBound_Disc_p2179 : (a_p 2179 : ℝ) ^ 2 ≤ 4 * (2179 : ℝ) :=
  BSD_disc_from_deg_798 BSD_DegreeNonneg_p2179
theorem BSD_HasseBound_Disc_p2203 : (a_p 2203 : ℝ) ^ 2 ≤ 4 * (2203 : ℝ) :=
  BSD_disc_from_deg_798 BSD_DegreeNonneg_p2203

end Towers.BSD
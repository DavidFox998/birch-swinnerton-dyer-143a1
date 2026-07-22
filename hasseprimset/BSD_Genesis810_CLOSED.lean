/-
================================================================
Towers / BSD / BSD_Genesis810_CLOSED  (genesis-810)

HasseBridge Tier C: Hasse bounds for primes
3067..3167 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=3067: card=3075, a_p=-7, disc=-12219
  p=3079: card=3118, a_p=-38, disc=-10872
  p=3083: card=3081, a_p=+3, disc=-12323
  p=3089: card=3079, a_p=+11, disc=-12235
  p=3109: card=3056, a_p=+54, disc=-9520
  p=3119: card=3134, a_p=-14, disc=-12280
  p=3121: card=3154, a_p=-32, disc=-11460
  p=3137: card=3210, a_p=-72, disc=-7364
  p=3163: card=3078, a_p=+86, disc=-5256
  p=3167: card=3174, a_p=-6, disc=-12632

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_810 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i810_p3067 : Fact (3067 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3079 : Fact (3079 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3083 : Fact (3083 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3089 : Fact (3089 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3109 : Fact (3109 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3119 : Fact (3119 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3121 : Fact (3121 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3137 : Fact (3137 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3163 : Fact (3163 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3167 : Fact (3167 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p3067 : (E143_Finset 3067).card = 3075 := by native_decide
theorem BSD_E143_card_p3079 : (E143_Finset 3079).card = 3118 := by native_decide
theorem BSD_E143_card_p3083 : (E143_Finset 3083).card = 3081 := by native_decide
theorem BSD_E143_card_p3089 : (E143_Finset 3089).card = 3079 := by native_decide
theorem BSD_E143_card_p3109 : (E143_Finset 3109).card = 3056 := by native_decide
theorem BSD_E143_card_p3119 : (E143_Finset 3119).card = 3134 := by native_decide
theorem BSD_E143_card_p3121 : (E143_Finset 3121).card = 3154 := by native_decide
theorem BSD_E143_card_p3137 : (E143_Finset 3137).card = 3210 := by native_decide
theorem BSD_E143_card_p3163 : (E143_Finset 3163).card = 3078 := by native_decide
theorem BSD_E143_card_p3167 : (E143_Finset 3167).card = 3174 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p3067 : a_p 3067 = (-7 : ℤ) := by
  have h := BSD_E143_card_p3067; unfold a_p; omega
theorem BSD_ap_p3079 : a_p 3079 = (-38 : ℤ) := by
  have h := BSD_E143_card_p3079; unfold a_p; omega
theorem BSD_ap_p3083 : a_p 3083 = (3 : ℤ) := by
  have h := BSD_E143_card_p3083; unfold a_p; omega
theorem BSD_ap_p3089 : a_p 3089 = (11 : ℤ) := by
  have h := BSD_E143_card_p3089; unfold a_p; omega
theorem BSD_ap_p3109 : a_p 3109 = (54 : ℤ) := by
  have h := BSD_E143_card_p3109; unfold a_p; omega
theorem BSD_ap_p3119 : a_p 3119 = (-14 : ℤ) := by
  have h := BSD_E143_card_p3119; unfold a_p; omega
theorem BSD_ap_p3121 : a_p 3121 = (-32 : ℤ) := by
  have h := BSD_E143_card_p3121; unfold a_p; omega
theorem BSD_ap_p3137 : a_p 3137 = (-72 : ℤ) := by
  have h := BSD_E143_card_p3137; unfold a_p; omega
theorem BSD_ap_p3163 : a_p 3163 = (86 : ℤ) := by
  have h := BSD_E143_card_p3163; unfold a_p; omega
theorem BSD_ap_p3167 : a_p 3167 = (-6 : ℤ) := by
  have h := BSD_E143_card_p3167; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=3067: a_p=-7, 4p-a_p²=12219
theorem BSD_DegreeNonneg_p3067 : BSD_FrobeniusDegreeNonneg_OPEN 3067 := fun r => by
  have hap : (a_p 3067 : ℝ) = -7 := by exact_mod_cast BSD_ap_p3067
  have key : r ^ 2 - (a_p 3067 : ℝ) * r + ((3067 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 12219/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

-- p=3079: a_p=-38, 4p-a_p²=10872
theorem BSD_DegreeNonneg_p3079 : BSD_FrobeniusDegreeNonneg_OPEN 3079 := fun r => by
  have hap : (a_p 3079 : ℝ) = -38 := by exact_mod_cast BSD_ap_p3079
  have key : r ^ 2 - (a_p 3079 : ℝ) * r + ((3079 : ℕ) : ℝ) =
      (r + 38/2) ^ 2 + 10872/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (38 : ℝ)/2)]

-- p=3083: a_p=+3, 4p-a_p²=12323
theorem BSD_DegreeNonneg_p3083 : BSD_FrobeniusDegreeNonneg_OPEN 3083 := fun r => by
  have hap : (a_p 3083 : ℝ) = 3 := by exact_mod_cast BSD_ap_p3083
  have key : r ^ 2 - (a_p 3083 : ℝ) * r + ((3083 : ℕ) : ℝ) =
      (r - 3/2) ^ 2 + 12323/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (3 : ℝ)/2)]

-- p=3089: a_p=+11, 4p-a_p²=12235
theorem BSD_DegreeNonneg_p3089 : BSD_FrobeniusDegreeNonneg_OPEN 3089 := fun r => by
  have hap : (a_p 3089 : ℝ) = 11 := by exact_mod_cast BSD_ap_p3089
  have key : r ^ 2 - (a_p 3089 : ℝ) * r + ((3089 : ℕ) : ℝ) =
      (r - 11/2) ^ 2 + 12235/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (11 : ℝ)/2)]

-- p=3109: a_p=+54, 4p-a_p²=9520
theorem BSD_DegreeNonneg_p3109 : BSD_FrobeniusDegreeNonneg_OPEN 3109 := fun r => by
  have hap : (a_p 3109 : ℝ) = 54 := by exact_mod_cast BSD_ap_p3109
  have key : r ^ 2 - (a_p 3109 : ℝ) * r + ((3109 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 9520/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

-- p=3119: a_p=-14, 4p-a_p²=12280
theorem BSD_DegreeNonneg_p3119 : BSD_FrobeniusDegreeNonneg_OPEN 3119 := fun r => by
  have hap : (a_p 3119 : ℝ) = -14 := by exact_mod_cast BSD_ap_p3119
  have key : r ^ 2 - (a_p 3119 : ℝ) * r + ((3119 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 12280/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

-- p=3121: a_p=-32, 4p-a_p²=11460
theorem BSD_DegreeNonneg_p3121 : BSD_FrobeniusDegreeNonneg_OPEN 3121 := fun r => by
  have hap : (a_p 3121 : ℝ) = -32 := by exact_mod_cast BSD_ap_p3121
  have key : r ^ 2 - (a_p 3121 : ℝ) * r + ((3121 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 11460/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

-- p=3137: a_p=-72, 4p-a_p²=7364
theorem BSD_DegreeNonneg_p3137 : BSD_FrobeniusDegreeNonneg_OPEN 3137 := fun r => by
  have hap : (a_p 3137 : ℝ) = -72 := by exact_mod_cast BSD_ap_p3137
  have key : r ^ 2 - (a_p 3137 : ℝ) * r + ((3137 : ℕ) : ℝ) =
      (r + 72/2) ^ 2 + 7364/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (72 : ℝ)/2)]

-- p=3163: a_p=+86, 4p-a_p²=5256
theorem BSD_DegreeNonneg_p3163 : BSD_FrobeniusDegreeNonneg_OPEN 3163 := fun r => by
  have hap : (a_p 3163 : ℝ) = 86 := by exact_mod_cast BSD_ap_p3163
  have key : r ^ 2 - (a_p 3163 : ℝ) * r + ((3163 : ℕ) : ℝ) =
      (r - 86/2) ^ 2 + 5256/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (86 : ℝ)/2)]

-- p=3167: a_p=-6, 4p-a_p²=12632
theorem BSD_DegreeNonneg_p3167 : BSD_FrobeniusDegreeNonneg_OPEN 3167 := fun r => by
  have hap : (a_p 3167 : ℝ) = -6 := by exact_mod_cast BSD_ap_p3167
  have key : r ^ 2 - (a_p 3167 : ℝ) * r + ((3167 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 12632/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p3067 : BSD_Hasse_OPEN 3067 :=
  BSD_hasse_of_degree_nonneg 3067 BSD_DegreeNonneg_p3067
theorem BSD_Hasse_OPEN_p3079 : BSD_Hasse_OPEN 3079 :=
  BSD_hasse_of_degree_nonneg 3079 BSD_DegreeNonneg_p3079
theorem BSD_Hasse_OPEN_p3083 : BSD_Hasse_OPEN 3083 :=
  BSD_hasse_of_degree_nonneg 3083 BSD_DegreeNonneg_p3083
theorem BSD_Hasse_OPEN_p3089 : BSD_Hasse_OPEN 3089 :=
  BSD_hasse_of_degree_nonneg 3089 BSD_DegreeNonneg_p3089
theorem BSD_Hasse_OPEN_p3109 : BSD_Hasse_OPEN 3109 :=
  BSD_hasse_of_degree_nonneg 3109 BSD_DegreeNonneg_p3109
theorem BSD_Hasse_OPEN_p3119 : BSD_Hasse_OPEN 3119 :=
  BSD_hasse_of_degree_nonneg 3119 BSD_DegreeNonneg_p3119
theorem BSD_Hasse_OPEN_p3121 : BSD_Hasse_OPEN 3121 :=
  BSD_hasse_of_degree_nonneg 3121 BSD_DegreeNonneg_p3121
theorem BSD_Hasse_OPEN_p3137 : BSD_Hasse_OPEN 3137 :=
  BSD_hasse_of_degree_nonneg 3137 BSD_DegreeNonneg_p3137
theorem BSD_Hasse_OPEN_p3163 : BSD_Hasse_OPEN 3163 :=
  BSD_hasse_of_degree_nonneg 3163 BSD_DegreeNonneg_p3163
theorem BSD_Hasse_OPEN_p3167 : BSD_Hasse_OPEN 3167 :=
  BSD_hasse_of_degree_nonneg 3167 BSD_DegreeNonneg_p3167

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p3067 : (a_p 3067 : ℝ) ^ 2 ≤ 4 * (3067 : ℝ) :=
  BSD_disc_from_deg_810 BSD_DegreeNonneg_p3067
theorem BSD_HasseBound_Disc_p3079 : (a_p 3079 : ℝ) ^ 2 ≤ 4 * (3079 : ℝ) :=
  BSD_disc_from_deg_810 BSD_DegreeNonneg_p3079
theorem BSD_HasseBound_Disc_p3083 : (a_p 3083 : ℝ) ^ 2 ≤ 4 * (3083 : ℝ) :=
  BSD_disc_from_deg_810 BSD_DegreeNonneg_p3083
theorem BSD_HasseBound_Disc_p3089 : (a_p 3089 : ℝ) ^ 2 ≤ 4 * (3089 : ℝ) :=
  BSD_disc_from_deg_810 BSD_DegreeNonneg_p3089
theorem BSD_HasseBound_Disc_p3109 : (a_p 3109 : ℝ) ^ 2 ≤ 4 * (3109 : ℝ) :=
  BSD_disc_from_deg_810 BSD_DegreeNonneg_p3109
theorem BSD_HasseBound_Disc_p3119 : (a_p 3119 : ℝ) ^ 2 ≤ 4 * (3119 : ℝ) :=
  BSD_disc_from_deg_810 BSD_DegreeNonneg_p3119
theorem BSD_HasseBound_Disc_p3121 : (a_p 3121 : ℝ) ^ 2 ≤ 4 * (3121 : ℝ) :=
  BSD_disc_from_deg_810 BSD_DegreeNonneg_p3121
theorem BSD_HasseBound_Disc_p3137 : (a_p 3137 : ℝ) ^ 2 ≤ 4 * (3137 : ℝ) :=
  BSD_disc_from_deg_810 BSD_DegreeNonneg_p3137
theorem BSD_HasseBound_Disc_p3163 : (a_p 3163 : ℝ) ^ 2 ≤ 4 * (3163 : ℝ) :=
  BSD_disc_from_deg_810 BSD_DegreeNonneg_p3163
theorem BSD_HasseBound_Disc_p3167 : (a_p 3167 : ℝ) ^ 2 ≤ 4 * (3167 : ℝ) :=
  BSD_disc_from_deg_810 BSD_DegreeNonneg_p3167

end Towers.BSD
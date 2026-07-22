/-
================================================================
Towers / BSD / BSD_Genesis867_CLOSED  (genesis-867)

HasseBridge Tier C: Hasse bounds for primes
8011..8093 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=8011: card=8035, a_p=-23, disc=-31515
  p=8017: card=8024, a_p=-6, disc=-32032
  p=8039: card=8093, a_p=-53, disc=-29347
  p=8053: card=7960, a_p=+94, disc=-23376
  p=8059: card=8060, a_p=+0, disc=-32236
  p=8069: card=8162, a_p=-92, disc=-23812
  p=8081: card=8192, a_p=-110, disc=-20224
  p=8087: card=8198, a_p=-110, disc=-20248
  p=8089: card=7991, a_p=+99, disc=-22555
  p=8093: card=8006, a_p=+88, disc=-24628

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_867 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i867_p8011 : Fact (8011 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8017 : Fact (8017 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8039 : Fact (8039 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8053 : Fact (8053 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8059 : Fact (8059 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8069 : Fact (8069 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8081 : Fact (8081 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8087 : Fact (8087 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8089 : Fact (8089 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8093 : Fact (8093 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p8011 : (E143_Finset 8011).card = 8035 := by native_decide
theorem BSD_E143_card_p8017 : (E143_Finset 8017).card = 8024 := by native_decide
theorem BSD_E143_card_p8039 : (E143_Finset 8039).card = 8093 := by native_decide
theorem BSD_E143_card_p8053 : (E143_Finset 8053).card = 7960 := by native_decide
theorem BSD_E143_card_p8059 : (E143_Finset 8059).card = 8060 := by native_decide
theorem BSD_E143_card_p8069 : (E143_Finset 8069).card = 8162 := by native_decide
theorem BSD_E143_card_p8081 : (E143_Finset 8081).card = 8192 := by native_decide
theorem BSD_E143_card_p8087 : (E143_Finset 8087).card = 8198 := by native_decide
theorem BSD_E143_card_p8089 : (E143_Finset 8089).card = 7991 := by native_decide
theorem BSD_E143_card_p8093 : (E143_Finset 8093).card = 8006 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p8011 : a_p 8011 = (-23 : ℤ) := by
  have h := BSD_E143_card_p8011; unfold a_p; omega
theorem BSD_ap_p8017 : a_p 8017 = (-6 : ℤ) := by
  have h := BSD_E143_card_p8017; unfold a_p; omega
theorem BSD_ap_p8039 : a_p 8039 = (-53 : ℤ) := by
  have h := BSD_E143_card_p8039; unfold a_p; omega
theorem BSD_ap_p8053 : a_p 8053 = (94 : ℤ) := by
  have h := BSD_E143_card_p8053; unfold a_p; omega
theorem BSD_ap_p8059 : a_p 8059 = (0 : ℤ) := by
  have h := BSD_E143_card_p8059; unfold a_p; omega
theorem BSD_ap_p8069 : a_p 8069 = (-92 : ℤ) := by
  have h := BSD_E143_card_p8069; unfold a_p; omega
theorem BSD_ap_p8081 : a_p 8081 = (-110 : ℤ) := by
  have h := BSD_E143_card_p8081; unfold a_p; omega
theorem BSD_ap_p8087 : a_p 8087 = (-110 : ℤ) := by
  have h := BSD_E143_card_p8087; unfold a_p; omega
theorem BSD_ap_p8089 : a_p 8089 = (99 : ℤ) := by
  have h := BSD_E143_card_p8089; unfold a_p; omega
theorem BSD_ap_p8093 : a_p 8093 = (88 : ℤ) := by
  have h := BSD_E143_card_p8093; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=8011: a_p=-23, 4p-a_p²=31515
theorem BSD_DegreeNonneg_p8011 : BSD_FrobeniusDegreeNonneg_OPEN 8011 := fun r => by
  have hap : (a_p 8011 : ℝ) = -23 := by exact_mod_cast BSD_ap_p8011
  have key : r ^ 2 - (a_p 8011 : ℝ) * r + ((8011 : ℕ) : ℝ) =
      (r + 23/2) ^ 2 + 31515/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (23 : ℝ)/2)]

-- p=8017: a_p=-6, 4p-a_p²=32032
theorem BSD_DegreeNonneg_p8017 : BSD_FrobeniusDegreeNonneg_OPEN 8017 := fun r => by
  have hap : (a_p 8017 : ℝ) = -6 := by exact_mod_cast BSD_ap_p8017
  have key : r ^ 2 - (a_p 8017 : ℝ) * r + ((8017 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 32032/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

-- p=8039: a_p=-53, 4p-a_p²=29347
theorem BSD_DegreeNonneg_p8039 : BSD_FrobeniusDegreeNonneg_OPEN 8039 := fun r => by
  have hap : (a_p 8039 : ℝ) = -53 := by exact_mod_cast BSD_ap_p8039
  have key : r ^ 2 - (a_p 8039 : ℝ) * r + ((8039 : ℕ) : ℝ) =
      (r + 53/2) ^ 2 + 29347/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (53 : ℝ)/2)]

-- p=8053: a_p=+94, 4p-a_p²=23376
theorem BSD_DegreeNonneg_p8053 : BSD_FrobeniusDegreeNonneg_OPEN 8053 := fun r => by
  have hap : (a_p 8053 : ℝ) = 94 := by exact_mod_cast BSD_ap_p8053
  have key : r ^ 2 - (a_p 8053 : ℝ) * r + ((8053 : ℕ) : ℝ) =
      (r - 94/2) ^ 2 + 23376/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (94 : ℝ)/2)]

-- p=8059: a_p=+0, 4p-a_p²=32236
theorem BSD_DegreeNonneg_p8059 : BSD_FrobeniusDegreeNonneg_OPEN 8059 := fun r => by
  have hap : (a_p 8059 : ℝ) = 0 := by exact_mod_cast BSD_ap_p8059
  have key : r ^ 2 - (a_p 8059 : ℝ) * r + ((8059 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 32236/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

-- p=8069: a_p=-92, 4p-a_p²=23812
theorem BSD_DegreeNonneg_p8069 : BSD_FrobeniusDegreeNonneg_OPEN 8069 := fun r => by
  have hap : (a_p 8069 : ℝ) = -92 := by exact_mod_cast BSD_ap_p8069
  have key : r ^ 2 - (a_p 8069 : ℝ) * r + ((8069 : ℕ) : ℝ) =
      (r + 92/2) ^ 2 + 23812/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (92 : ℝ)/2)]

-- p=8081: a_p=-110, 4p-a_p²=20224
theorem BSD_DegreeNonneg_p8081 : BSD_FrobeniusDegreeNonneg_OPEN 8081 := fun r => by
  have hap : (a_p 8081 : ℝ) = -110 := by exact_mod_cast BSD_ap_p8081
  have key : r ^ 2 - (a_p 8081 : ℝ) * r + ((8081 : ℕ) : ℝ) =
      (r + 110/2) ^ 2 + 20224/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (110 : ℝ)/2)]

-- p=8087: a_p=-110, 4p-a_p²=20248
theorem BSD_DegreeNonneg_p8087 : BSD_FrobeniusDegreeNonneg_OPEN 8087 := fun r => by
  have hap : (a_p 8087 : ℝ) = -110 := by exact_mod_cast BSD_ap_p8087
  have key : r ^ 2 - (a_p 8087 : ℝ) * r + ((8087 : ℕ) : ℝ) =
      (r + 110/2) ^ 2 + 20248/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (110 : ℝ)/2)]

-- p=8089: a_p=+99, 4p-a_p²=22555
theorem BSD_DegreeNonneg_p8089 : BSD_FrobeniusDegreeNonneg_OPEN 8089 := fun r => by
  have hap : (a_p 8089 : ℝ) = 99 := by exact_mod_cast BSD_ap_p8089
  have key : r ^ 2 - (a_p 8089 : ℝ) * r + ((8089 : ℕ) : ℝ) =
      (r - 99/2) ^ 2 + 22555/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (99 : ℝ)/2)]

-- p=8093: a_p=+88, 4p-a_p²=24628
theorem BSD_DegreeNonneg_p8093 : BSD_FrobeniusDegreeNonneg_OPEN 8093 := fun r => by
  have hap : (a_p 8093 : ℝ) = 88 := by exact_mod_cast BSD_ap_p8093
  have key : r ^ 2 - (a_p 8093 : ℝ) * r + ((8093 : ℕ) : ℝ) =
      (r - 88/2) ^ 2 + 24628/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (88 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p8011 : BSD_Hasse_OPEN 8011 :=
  BSD_hasse_of_degree_nonneg 8011 BSD_DegreeNonneg_p8011
theorem BSD_Hasse_OPEN_p8017 : BSD_Hasse_OPEN 8017 :=
  BSD_hasse_of_degree_nonneg 8017 BSD_DegreeNonneg_p8017
theorem BSD_Hasse_OPEN_p8039 : BSD_Hasse_OPEN 8039 :=
  BSD_hasse_of_degree_nonneg 8039 BSD_DegreeNonneg_p8039
theorem BSD_Hasse_OPEN_p8053 : BSD_Hasse_OPEN 8053 :=
  BSD_hasse_of_degree_nonneg 8053 BSD_DegreeNonneg_p8053
theorem BSD_Hasse_OPEN_p8059 : BSD_Hasse_OPEN 8059 :=
  BSD_hasse_of_degree_nonneg 8059 BSD_DegreeNonneg_p8059
theorem BSD_Hasse_OPEN_p8069 : BSD_Hasse_OPEN 8069 :=
  BSD_hasse_of_degree_nonneg 8069 BSD_DegreeNonneg_p8069
theorem BSD_Hasse_OPEN_p8081 : BSD_Hasse_OPEN 8081 :=
  BSD_hasse_of_degree_nonneg 8081 BSD_DegreeNonneg_p8081
theorem BSD_Hasse_OPEN_p8087 : BSD_Hasse_OPEN 8087 :=
  BSD_hasse_of_degree_nonneg 8087 BSD_DegreeNonneg_p8087
theorem BSD_Hasse_OPEN_p8089 : BSD_Hasse_OPEN 8089 :=
  BSD_hasse_of_degree_nonneg 8089 BSD_DegreeNonneg_p8089
theorem BSD_Hasse_OPEN_p8093 : BSD_Hasse_OPEN 8093 :=
  BSD_hasse_of_degree_nonneg 8093 BSD_DegreeNonneg_p8093

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p8011 : (a_p 8011 : ℝ) ^ 2 ≤ 4 * (8011 : ℝ) :=
  BSD_disc_from_deg_867 BSD_DegreeNonneg_p8011
theorem BSD_HasseBound_Disc_p8017 : (a_p 8017 : ℝ) ^ 2 ≤ 4 * (8017 : ℝ) :=
  BSD_disc_from_deg_867 BSD_DegreeNonneg_p8017
theorem BSD_HasseBound_Disc_p8039 : (a_p 8039 : ℝ) ^ 2 ≤ 4 * (8039 : ℝ) :=
  BSD_disc_from_deg_867 BSD_DegreeNonneg_p8039
theorem BSD_HasseBound_Disc_p8053 : (a_p 8053 : ℝ) ^ 2 ≤ 4 * (8053 : ℝ) :=
  BSD_disc_from_deg_867 BSD_DegreeNonneg_p8053
theorem BSD_HasseBound_Disc_p8059 : (a_p 8059 : ℝ) ^ 2 ≤ 4 * (8059 : ℝ) :=
  BSD_disc_from_deg_867 BSD_DegreeNonneg_p8059
theorem BSD_HasseBound_Disc_p8069 : (a_p 8069 : ℝ) ^ 2 ≤ 4 * (8069 : ℝ) :=
  BSD_disc_from_deg_867 BSD_DegreeNonneg_p8069
theorem BSD_HasseBound_Disc_p8081 : (a_p 8081 : ℝ) ^ 2 ≤ 4 * (8081 : ℝ) :=
  BSD_disc_from_deg_867 BSD_DegreeNonneg_p8081
theorem BSD_HasseBound_Disc_p8087 : (a_p 8087 : ℝ) ^ 2 ≤ 4 * (8087 : ℝ) :=
  BSD_disc_from_deg_867 BSD_DegreeNonneg_p8087
theorem BSD_HasseBound_Disc_p8089 : (a_p 8089 : ℝ) ^ 2 ≤ 4 * (8089 : ℝ) :=
  BSD_disc_from_deg_867 BSD_DegreeNonneg_p8089
theorem BSD_HasseBound_Disc_p8093 : (a_p 8093 : ℝ) ^ 2 ≤ 4 * (8093 : ℝ) :=
  BSD_disc_from_deg_867 BSD_DegreeNonneg_p8093

end Towers.BSD
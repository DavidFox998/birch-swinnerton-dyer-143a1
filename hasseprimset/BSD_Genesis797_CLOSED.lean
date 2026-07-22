/-
================================================================
Towers / BSD / BSD_Genesis797_CLOSED  (genesis-797)

HasseBridge Tier C: Hasse bounds for primes
2039..2111 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=2039: card=2032, a_p=+8, disc=-8092
  p=2053: card=2106, a_p=-52, disc=-5508
  p=2063: card=2128, a_p=-64, disc=-4156
  p=2069: card=2156, a_p=-86, disc=-880
  p=2081: card=2052, a_p=+30, disc=-7424
  p=2083: card=2147, a_p=-63, disc=-4363
  p=2087: card=2020, a_p=+68, disc=-3724
  p=2089: card=2056, a_p=+34, disc=-7200
  p=2099: card=2119, a_p=-19, disc=-8035
  p=2111: card=2136, a_p=-24, disc=-7868

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_797 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i797_p2039 : Fact (2039 : ℕ).Prime := ⟨by norm_num⟩
private instance i797_p2053 : Fact (2053 : ℕ).Prime := ⟨by norm_num⟩
private instance i797_p2063 : Fact (2063 : ℕ).Prime := ⟨by norm_num⟩
private instance i797_p2069 : Fact (2069 : ℕ).Prime := ⟨by norm_num⟩
private instance i797_p2081 : Fact (2081 : ℕ).Prime := ⟨by norm_num⟩
private instance i797_p2083 : Fact (2083 : ℕ).Prime := ⟨by norm_num⟩
private instance i797_p2087 : Fact (2087 : ℕ).Prime := ⟨by norm_num⟩
private instance i797_p2089 : Fact (2089 : ℕ).Prime := ⟨by norm_num⟩
private instance i797_p2099 : Fact (2099 : ℕ).Prime := ⟨by norm_num⟩
private instance i797_p2111 : Fact (2111 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p2039 : (E143_Finset 2039).card = 2032 := by native_decide
theorem BSD_E143_card_p2053 : (E143_Finset 2053).card = 2106 := by native_decide
theorem BSD_E143_card_p2063 : (E143_Finset 2063).card = 2128 := by native_decide
theorem BSD_E143_card_p2069 : (E143_Finset 2069).card = 2156 := by native_decide
theorem BSD_E143_card_p2081 : (E143_Finset 2081).card = 2052 := by native_decide
theorem BSD_E143_card_p2083 : (E143_Finset 2083).card = 2147 := by native_decide
theorem BSD_E143_card_p2087 : (E143_Finset 2087).card = 2020 := by native_decide
theorem BSD_E143_card_p2089 : (E143_Finset 2089).card = 2056 := by native_decide
theorem BSD_E143_card_p2099 : (E143_Finset 2099).card = 2119 := by native_decide
theorem BSD_E143_card_p2111 : (E143_Finset 2111).card = 2136 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p2039 : a_p 2039 = (8 : ℤ) := by
  have h := BSD_E143_card_p2039; unfold a_p; omega
theorem BSD_ap_p2053 : a_p 2053 = (-52 : ℤ) := by
  have h := BSD_E143_card_p2053; unfold a_p; omega
theorem BSD_ap_p2063 : a_p 2063 = (-64 : ℤ) := by
  have h := BSD_E143_card_p2063; unfold a_p; omega
theorem BSD_ap_p2069 : a_p 2069 = (-86 : ℤ) := by
  have h := BSD_E143_card_p2069; unfold a_p; omega
theorem BSD_ap_p2081 : a_p 2081 = (30 : ℤ) := by
  have h := BSD_E143_card_p2081; unfold a_p; omega
theorem BSD_ap_p2083 : a_p 2083 = (-63 : ℤ) := by
  have h := BSD_E143_card_p2083; unfold a_p; omega
theorem BSD_ap_p2087 : a_p 2087 = (68 : ℤ) := by
  have h := BSD_E143_card_p2087; unfold a_p; omega
theorem BSD_ap_p2089 : a_p 2089 = (34 : ℤ) := by
  have h := BSD_E143_card_p2089; unfold a_p; omega
theorem BSD_ap_p2099 : a_p 2099 = (-19 : ℤ) := by
  have h := BSD_E143_card_p2099; unfold a_p; omega
theorem BSD_ap_p2111 : a_p 2111 = (-24 : ℤ) := by
  have h := BSD_E143_card_p2111; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=2039: a_p=+8, 4p-a_p²=8092
theorem BSD_DegreeNonneg_p2039 : BSD_FrobeniusDegreeNonneg_OPEN 2039 := fun r => by
  have hap : (a_p 2039 : ℝ) = 8 := by exact_mod_cast BSD_ap_p2039
  have key : r ^ 2 - (a_p 2039 : ℝ) * r + ((2039 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 8092/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

-- p=2053: a_p=-52, 4p-a_p²=5508
theorem BSD_DegreeNonneg_p2053 : BSD_FrobeniusDegreeNonneg_OPEN 2053 := fun r => by
  have hap : (a_p 2053 : ℝ) = -52 := by exact_mod_cast BSD_ap_p2053
  have key : r ^ 2 - (a_p 2053 : ℝ) * r + ((2053 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 5508/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

-- p=2063: a_p=-64, 4p-a_p²=4156
theorem BSD_DegreeNonneg_p2063 : BSD_FrobeniusDegreeNonneg_OPEN 2063 := fun r => by
  have hap : (a_p 2063 : ℝ) = -64 := by exact_mod_cast BSD_ap_p2063
  have key : r ^ 2 - (a_p 2063 : ℝ) * r + ((2063 : ℕ) : ℝ) =
      (r + 64/2) ^ 2 + 4156/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (64 : ℝ)/2)]

-- p=2069: a_p=-86, 4p-a_p²=880
theorem BSD_DegreeNonneg_p2069 : BSD_FrobeniusDegreeNonneg_OPEN 2069 := fun r => by
  have hap : (a_p 2069 : ℝ) = -86 := by exact_mod_cast BSD_ap_p2069
  have key : r ^ 2 - (a_p 2069 : ℝ) * r + ((2069 : ℕ) : ℝ) =
      (r + 86/2) ^ 2 + 880/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (86 : ℝ)/2)]

-- p=2081: a_p=+30, 4p-a_p²=7424
theorem BSD_DegreeNonneg_p2081 : BSD_FrobeniusDegreeNonneg_OPEN 2081 := fun r => by
  have hap : (a_p 2081 : ℝ) = 30 := by exact_mod_cast BSD_ap_p2081
  have key : r ^ 2 - (a_p 2081 : ℝ) * r + ((2081 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 7424/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

-- p=2083: a_p=-63, 4p-a_p²=4363
theorem BSD_DegreeNonneg_p2083 : BSD_FrobeniusDegreeNonneg_OPEN 2083 := fun r => by
  have hap : (a_p 2083 : ℝ) = -63 := by exact_mod_cast BSD_ap_p2083
  have key : r ^ 2 - (a_p 2083 : ℝ) * r + ((2083 : ℕ) : ℝ) =
      (r + 63/2) ^ 2 + 4363/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (63 : ℝ)/2)]

-- p=2087: a_p=+68, 4p-a_p²=3724
theorem BSD_DegreeNonneg_p2087 : BSD_FrobeniusDegreeNonneg_OPEN 2087 := fun r => by
  have hap : (a_p 2087 : ℝ) = 68 := by exact_mod_cast BSD_ap_p2087
  have key : r ^ 2 - (a_p 2087 : ℝ) * r + ((2087 : ℕ) : ℝ) =
      (r - 68/2) ^ 2 + 3724/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (68 : ℝ)/2)]

-- p=2089: a_p=+34, 4p-a_p²=7200
theorem BSD_DegreeNonneg_p2089 : BSD_FrobeniusDegreeNonneg_OPEN 2089 := fun r => by
  have hap : (a_p 2089 : ℝ) = 34 := by exact_mod_cast BSD_ap_p2089
  have key : r ^ 2 - (a_p 2089 : ℝ) * r + ((2089 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 7200/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

-- p=2099: a_p=-19, 4p-a_p²=8035
theorem BSD_DegreeNonneg_p2099 : BSD_FrobeniusDegreeNonneg_OPEN 2099 := fun r => by
  have hap : (a_p 2099 : ℝ) = -19 := by exact_mod_cast BSD_ap_p2099
  have key : r ^ 2 - (a_p 2099 : ℝ) * r + ((2099 : ℕ) : ℝ) =
      (r + 19/2) ^ 2 + 8035/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (19 : ℝ)/2)]

-- p=2111: a_p=-24, 4p-a_p²=7868
theorem BSD_DegreeNonneg_p2111 : BSD_FrobeniusDegreeNonneg_OPEN 2111 := fun r => by
  have hap : (a_p 2111 : ℝ) = -24 := by exact_mod_cast BSD_ap_p2111
  have key : r ^ 2 - (a_p 2111 : ℝ) * r + ((2111 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 7868/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p2039 : BSD_Hasse_OPEN 2039 :=
  BSD_hasse_of_degree_nonneg 2039 BSD_DegreeNonneg_p2039
theorem BSD_Hasse_OPEN_p2053 : BSD_Hasse_OPEN 2053 :=
  BSD_hasse_of_degree_nonneg 2053 BSD_DegreeNonneg_p2053
theorem BSD_Hasse_OPEN_p2063 : BSD_Hasse_OPEN 2063 :=
  BSD_hasse_of_degree_nonneg 2063 BSD_DegreeNonneg_p2063
theorem BSD_Hasse_OPEN_p2069 : BSD_Hasse_OPEN 2069 :=
  BSD_hasse_of_degree_nonneg 2069 BSD_DegreeNonneg_p2069
theorem BSD_Hasse_OPEN_p2081 : BSD_Hasse_OPEN 2081 :=
  BSD_hasse_of_degree_nonneg 2081 BSD_DegreeNonneg_p2081
theorem BSD_Hasse_OPEN_p2083 : BSD_Hasse_OPEN 2083 :=
  BSD_hasse_of_degree_nonneg 2083 BSD_DegreeNonneg_p2083
theorem BSD_Hasse_OPEN_p2087 : BSD_Hasse_OPEN 2087 :=
  BSD_hasse_of_degree_nonneg 2087 BSD_DegreeNonneg_p2087
theorem BSD_Hasse_OPEN_p2089 : BSD_Hasse_OPEN 2089 :=
  BSD_hasse_of_degree_nonneg 2089 BSD_DegreeNonneg_p2089
theorem BSD_Hasse_OPEN_p2099 : BSD_Hasse_OPEN 2099 :=
  BSD_hasse_of_degree_nonneg 2099 BSD_DegreeNonneg_p2099
theorem BSD_Hasse_OPEN_p2111 : BSD_Hasse_OPEN 2111 :=
  BSD_hasse_of_degree_nonneg 2111 BSD_DegreeNonneg_p2111

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p2039 : (a_p 2039 : ℝ) ^ 2 ≤ 4 * (2039 : ℝ) :=
  BSD_disc_from_deg_797 BSD_DegreeNonneg_p2039
theorem BSD_HasseBound_Disc_p2053 : (a_p 2053 : ℝ) ^ 2 ≤ 4 * (2053 : ℝ) :=
  BSD_disc_from_deg_797 BSD_DegreeNonneg_p2053
theorem BSD_HasseBound_Disc_p2063 : (a_p 2063 : ℝ) ^ 2 ≤ 4 * (2063 : ℝ) :=
  BSD_disc_from_deg_797 BSD_DegreeNonneg_p2063
theorem BSD_HasseBound_Disc_p2069 : (a_p 2069 : ℝ) ^ 2 ≤ 4 * (2069 : ℝ) :=
  BSD_disc_from_deg_797 BSD_DegreeNonneg_p2069
theorem BSD_HasseBound_Disc_p2081 : (a_p 2081 : ℝ) ^ 2 ≤ 4 * (2081 : ℝ) :=
  BSD_disc_from_deg_797 BSD_DegreeNonneg_p2081
theorem BSD_HasseBound_Disc_p2083 : (a_p 2083 : ℝ) ^ 2 ≤ 4 * (2083 : ℝ) :=
  BSD_disc_from_deg_797 BSD_DegreeNonneg_p2083
theorem BSD_HasseBound_Disc_p2087 : (a_p 2087 : ℝ) ^ 2 ≤ 4 * (2087 : ℝ) :=
  BSD_disc_from_deg_797 BSD_DegreeNonneg_p2087
theorem BSD_HasseBound_Disc_p2089 : (a_p 2089 : ℝ) ^ 2 ≤ 4 * (2089 : ℝ) :=
  BSD_disc_from_deg_797 BSD_DegreeNonneg_p2089
theorem BSD_HasseBound_Disc_p2099 : (a_p 2099 : ℝ) ^ 2 ≤ 4 * (2099 : ℝ) :=
  BSD_disc_from_deg_797 BSD_DegreeNonneg_p2099
theorem BSD_HasseBound_Disc_p2111 : (a_p 2111 : ℝ) ^ 2 ≤ 4 * (2111 : ℝ) :=
  BSD_disc_from_deg_797 BSD_DegreeNonneg_p2111

end Towers.BSD
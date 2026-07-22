/-
================================================================
Towers / BSD / BSD_Genesis822_CLOSED  (genesis-822)

HasseBridge Tier C: Hasse bounds for primes
4051..4129 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=4051: card=4073, a_p=-21, disc=-15763
  p=4057: card=4143, a_p=-85, disc=-9003
  p=4073: card=4033, a_p=+41, disc=-14611
  p=4079: card=4176, a_p=-96, disc=-7100
  p=4091: card=4092, a_p=+0, disc=-16364
  p=4093: card=4000, a_p=+94, disc=-7536
  p=4099: card=4000, a_p=+100, disc=-6396
  p=4111: card=4132, a_p=-20, disc=-16044
  p=4127: card=4030, a_p=+98, disc=-6904
  p=4129: card=4173, a_p=-43, disc=-14667

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_822 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i822_p4051 : Fact (4051 : ℕ).Prime := ⟨by norm_num⟩
private instance i822_p4057 : Fact (4057 : ℕ).Prime := ⟨by norm_num⟩
private instance i822_p4073 : Fact (4073 : ℕ).Prime := ⟨by norm_num⟩
private instance i822_p4079 : Fact (4079 : ℕ).Prime := ⟨by norm_num⟩
private instance i822_p4091 : Fact (4091 : ℕ).Prime := ⟨by norm_num⟩
private instance i822_p4093 : Fact (4093 : ℕ).Prime := ⟨by norm_num⟩
private instance i822_p4099 : Fact (4099 : ℕ).Prime := ⟨by norm_num⟩
private instance i822_p4111 : Fact (4111 : ℕ).Prime := ⟨by norm_num⟩
private instance i822_p4127 : Fact (4127 : ℕ).Prime := ⟨by norm_num⟩
private instance i822_p4129 : Fact (4129 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p4051 : (E143_Finset 4051).card = 4073 := by native_decide
theorem BSD_E143_card_p4057 : (E143_Finset 4057).card = 4143 := by native_decide
theorem BSD_E143_card_p4073 : (E143_Finset 4073).card = 4033 := by native_decide
theorem BSD_E143_card_p4079 : (E143_Finset 4079).card = 4176 := by native_decide
theorem BSD_E143_card_p4091 : (E143_Finset 4091).card = 4092 := by native_decide
theorem BSD_E143_card_p4093 : (E143_Finset 4093).card = 4000 := by native_decide
theorem BSD_E143_card_p4099 : (E143_Finset 4099).card = 4000 := by native_decide
theorem BSD_E143_card_p4111 : (E143_Finset 4111).card = 4132 := by native_decide
theorem BSD_E143_card_p4127 : (E143_Finset 4127).card = 4030 := by native_decide
theorem BSD_E143_card_p4129 : (E143_Finset 4129).card = 4173 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p4051 : a_p 4051 = (-21 : ℤ) := by
  have h := BSD_E143_card_p4051; unfold a_p; omega
theorem BSD_ap_p4057 : a_p 4057 = (-85 : ℤ) := by
  have h := BSD_E143_card_p4057; unfold a_p; omega
theorem BSD_ap_p4073 : a_p 4073 = (41 : ℤ) := by
  have h := BSD_E143_card_p4073; unfold a_p; omega
theorem BSD_ap_p4079 : a_p 4079 = (-96 : ℤ) := by
  have h := BSD_E143_card_p4079; unfold a_p; omega
theorem BSD_ap_p4091 : a_p 4091 = (0 : ℤ) := by
  have h := BSD_E143_card_p4091; unfold a_p; omega
theorem BSD_ap_p4093 : a_p 4093 = (94 : ℤ) := by
  have h := BSD_E143_card_p4093; unfold a_p; omega
theorem BSD_ap_p4099 : a_p 4099 = (100 : ℤ) := by
  have h := BSD_E143_card_p4099; unfold a_p; omega
theorem BSD_ap_p4111 : a_p 4111 = (-20 : ℤ) := by
  have h := BSD_E143_card_p4111; unfold a_p; omega
theorem BSD_ap_p4127 : a_p 4127 = (98 : ℤ) := by
  have h := BSD_E143_card_p4127; unfold a_p; omega
theorem BSD_ap_p4129 : a_p 4129 = (-43 : ℤ) := by
  have h := BSD_E143_card_p4129; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=4051: a_p=-21, 4p-a_p²=15763
theorem BSD_DegreeNonneg_p4051 : BSD_FrobeniusDegreeNonneg_OPEN 4051 := fun r => by
  have hap : (a_p 4051 : ℝ) = -21 := by exact_mod_cast BSD_ap_p4051
  have key : r ^ 2 - (a_p 4051 : ℝ) * r + ((4051 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 15763/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

-- p=4057: a_p=-85, 4p-a_p²=9003
theorem BSD_DegreeNonneg_p4057 : BSD_FrobeniusDegreeNonneg_OPEN 4057 := fun r => by
  have hap : (a_p 4057 : ℝ) = -85 := by exact_mod_cast BSD_ap_p4057
  have key : r ^ 2 - (a_p 4057 : ℝ) * r + ((4057 : ℕ) : ℝ) =
      (r + 85/2) ^ 2 + 9003/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (85 : ℝ)/2)]

-- p=4073: a_p=+41, 4p-a_p²=14611
theorem BSD_DegreeNonneg_p4073 : BSD_FrobeniusDegreeNonneg_OPEN 4073 := fun r => by
  have hap : (a_p 4073 : ℝ) = 41 := by exact_mod_cast BSD_ap_p4073
  have key : r ^ 2 - (a_p 4073 : ℝ) * r + ((4073 : ℕ) : ℝ) =
      (r - 41/2) ^ 2 + 14611/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (41 : ℝ)/2)]

-- p=4079: a_p=-96, 4p-a_p²=7100
theorem BSD_DegreeNonneg_p4079 : BSD_FrobeniusDegreeNonneg_OPEN 4079 := fun r => by
  have hap : (a_p 4079 : ℝ) = -96 := by exact_mod_cast BSD_ap_p4079
  have key : r ^ 2 - (a_p 4079 : ℝ) * r + ((4079 : ℕ) : ℝ) =
      (r + 96/2) ^ 2 + 7100/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (96 : ℝ)/2)]

-- p=4091: a_p=+0, 4p-a_p²=16364
theorem BSD_DegreeNonneg_p4091 : BSD_FrobeniusDegreeNonneg_OPEN 4091 := fun r => by
  have hap : (a_p 4091 : ℝ) = 0 := by exact_mod_cast BSD_ap_p4091
  have key : r ^ 2 - (a_p 4091 : ℝ) * r + ((4091 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 16364/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

-- p=4093: a_p=+94, 4p-a_p²=7536
theorem BSD_DegreeNonneg_p4093 : BSD_FrobeniusDegreeNonneg_OPEN 4093 := fun r => by
  have hap : (a_p 4093 : ℝ) = 94 := by exact_mod_cast BSD_ap_p4093
  have key : r ^ 2 - (a_p 4093 : ℝ) * r + ((4093 : ℕ) : ℝ) =
      (r - 94/2) ^ 2 + 7536/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (94 : ℝ)/2)]

-- p=4099: a_p=+100, 4p-a_p²=6396
theorem BSD_DegreeNonneg_p4099 : BSD_FrobeniusDegreeNonneg_OPEN 4099 := fun r => by
  have hap : (a_p 4099 : ℝ) = 100 := by exact_mod_cast BSD_ap_p4099
  have key : r ^ 2 - (a_p 4099 : ℝ) * r + ((4099 : ℕ) : ℝ) =
      (r - 100/2) ^ 2 + 6396/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (100 : ℝ)/2)]

-- p=4111: a_p=-20, 4p-a_p²=16044
theorem BSD_DegreeNonneg_p4111 : BSD_FrobeniusDegreeNonneg_OPEN 4111 := fun r => by
  have hap : (a_p 4111 : ℝ) = -20 := by exact_mod_cast BSD_ap_p4111
  have key : r ^ 2 - (a_p 4111 : ℝ) * r + ((4111 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 16044/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=4127: a_p=+98, 4p-a_p²=6904
theorem BSD_DegreeNonneg_p4127 : BSD_FrobeniusDegreeNonneg_OPEN 4127 := fun r => by
  have hap : (a_p 4127 : ℝ) = 98 := by exact_mod_cast BSD_ap_p4127
  have key : r ^ 2 - (a_p 4127 : ℝ) * r + ((4127 : ℕ) : ℝ) =
      (r - 98/2) ^ 2 + 6904/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (98 : ℝ)/2)]

-- p=4129: a_p=-43, 4p-a_p²=14667
theorem BSD_DegreeNonneg_p4129 : BSD_FrobeniusDegreeNonneg_OPEN 4129 := fun r => by
  have hap : (a_p 4129 : ℝ) = -43 := by exact_mod_cast BSD_ap_p4129
  have key : r ^ 2 - (a_p 4129 : ℝ) * r + ((4129 : ℕ) : ℝ) =
      (r + 43/2) ^ 2 + 14667/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (43 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p4051 : BSD_Hasse_OPEN 4051 :=
  BSD_hasse_of_degree_nonneg 4051 BSD_DegreeNonneg_p4051
theorem BSD_Hasse_OPEN_p4057 : BSD_Hasse_OPEN 4057 :=
  BSD_hasse_of_degree_nonneg 4057 BSD_DegreeNonneg_p4057
theorem BSD_Hasse_OPEN_p4073 : BSD_Hasse_OPEN 4073 :=
  BSD_hasse_of_degree_nonneg 4073 BSD_DegreeNonneg_p4073
theorem BSD_Hasse_OPEN_p4079 : BSD_Hasse_OPEN 4079 :=
  BSD_hasse_of_degree_nonneg 4079 BSD_DegreeNonneg_p4079
theorem BSD_Hasse_OPEN_p4091 : BSD_Hasse_OPEN 4091 :=
  BSD_hasse_of_degree_nonneg 4091 BSD_DegreeNonneg_p4091
theorem BSD_Hasse_OPEN_p4093 : BSD_Hasse_OPEN 4093 :=
  BSD_hasse_of_degree_nonneg 4093 BSD_DegreeNonneg_p4093
theorem BSD_Hasse_OPEN_p4099 : BSD_Hasse_OPEN 4099 :=
  BSD_hasse_of_degree_nonneg 4099 BSD_DegreeNonneg_p4099
theorem BSD_Hasse_OPEN_p4111 : BSD_Hasse_OPEN 4111 :=
  BSD_hasse_of_degree_nonneg 4111 BSD_DegreeNonneg_p4111
theorem BSD_Hasse_OPEN_p4127 : BSD_Hasse_OPEN 4127 :=
  BSD_hasse_of_degree_nonneg 4127 BSD_DegreeNonneg_p4127
theorem BSD_Hasse_OPEN_p4129 : BSD_Hasse_OPEN 4129 :=
  BSD_hasse_of_degree_nonneg 4129 BSD_DegreeNonneg_p4129

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p4051 : (a_p 4051 : ℝ) ^ 2 ≤ 4 * (4051 : ℝ) :=
  BSD_disc_from_deg_822 BSD_DegreeNonneg_p4051
theorem BSD_HasseBound_Disc_p4057 : (a_p 4057 : ℝ) ^ 2 ≤ 4 * (4057 : ℝ) :=
  BSD_disc_from_deg_822 BSD_DegreeNonneg_p4057
theorem BSD_HasseBound_Disc_p4073 : (a_p 4073 : ℝ) ^ 2 ≤ 4 * (4073 : ℝ) :=
  BSD_disc_from_deg_822 BSD_DegreeNonneg_p4073
theorem BSD_HasseBound_Disc_p4079 : (a_p 4079 : ℝ) ^ 2 ≤ 4 * (4079 : ℝ) :=
  BSD_disc_from_deg_822 BSD_DegreeNonneg_p4079
theorem BSD_HasseBound_Disc_p4091 : (a_p 4091 : ℝ) ^ 2 ≤ 4 * (4091 : ℝ) :=
  BSD_disc_from_deg_822 BSD_DegreeNonneg_p4091
theorem BSD_HasseBound_Disc_p4093 : (a_p 4093 : ℝ) ^ 2 ≤ 4 * (4093 : ℝ) :=
  BSD_disc_from_deg_822 BSD_DegreeNonneg_p4093
theorem BSD_HasseBound_Disc_p4099 : (a_p 4099 : ℝ) ^ 2 ≤ 4 * (4099 : ℝ) :=
  BSD_disc_from_deg_822 BSD_DegreeNonneg_p4099
theorem BSD_HasseBound_Disc_p4111 : (a_p 4111 : ℝ) ^ 2 ≤ 4 * (4111 : ℝ) :=
  BSD_disc_from_deg_822 BSD_DegreeNonneg_p4111
theorem BSD_HasseBound_Disc_p4127 : (a_p 4127 : ℝ) ^ 2 ≤ 4 * (4127 : ℝ) :=
  BSD_disc_from_deg_822 BSD_DegreeNonneg_p4127
theorem BSD_HasseBound_Disc_p4129 : (a_p 4129 : ℝ) ^ 2 ≤ 4 * (4129 : ℝ) :=
  BSD_disc_from_deg_822 BSD_DegreeNonneg_p4129

end Towers.BSD
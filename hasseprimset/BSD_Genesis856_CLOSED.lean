/-
================================================================
Towers / BSD / BSD_Genesis856_CLOSED  (genesis-856)

HasseBridge Tier C: Hasse bounds for primes
6991..7069 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=6991: card=7098, a_p=-106, disc=-16728
  p=6997: card=6863, a_p=+135, disc=-9763
  p=7001: card=7024, a_p=-22, disc=-27520
  p=7013: card=7032, a_p=-18, disc=-27728
  p=7019: card=7040, a_p=-20, disc=-27676
  p=7027: card=6995, a_p=+33, disc=-27019
  p=7039: card=6974, a_p=+66, disc=-23800
  p=7043: card=7144, a_p=-100, disc=-18172
  p=7057: card=7090, a_p=-32, disc=-27204
  p=7069: card=7194, a_p=-124, disc=-12900

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_856 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i856_p6991 : Fact (6991 : ℕ).Prime := ⟨by norm_num⟩
private instance i856_p6997 : Fact (6997 : ℕ).Prime := ⟨by norm_num⟩
private instance i856_p7001 : Fact (7001 : ℕ).Prime := ⟨by norm_num⟩
private instance i856_p7013 : Fact (7013 : ℕ).Prime := ⟨by norm_num⟩
private instance i856_p7019 : Fact (7019 : ℕ).Prime := ⟨by norm_num⟩
private instance i856_p7027 : Fact (7027 : ℕ).Prime := ⟨by norm_num⟩
private instance i856_p7039 : Fact (7039 : ℕ).Prime := ⟨by norm_num⟩
private instance i856_p7043 : Fact (7043 : ℕ).Prime := ⟨by norm_num⟩
private instance i856_p7057 : Fact (7057 : ℕ).Prime := ⟨by norm_num⟩
private instance i856_p7069 : Fact (7069 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p6991 : (E143_Finset 6991).card = 7098 := by native_decide
theorem BSD_E143_card_p6997 : (E143_Finset 6997).card = 6863 := by native_decide
theorem BSD_E143_card_p7001 : (E143_Finset 7001).card = 7024 := by native_decide
theorem BSD_E143_card_p7013 : (E143_Finset 7013).card = 7032 := by native_decide
theorem BSD_E143_card_p7019 : (E143_Finset 7019).card = 7040 := by native_decide
theorem BSD_E143_card_p7027 : (E143_Finset 7027).card = 6995 := by native_decide
theorem BSD_E143_card_p7039 : (E143_Finset 7039).card = 6974 := by native_decide
theorem BSD_E143_card_p7043 : (E143_Finset 7043).card = 7144 := by native_decide
theorem BSD_E143_card_p7057 : (E143_Finset 7057).card = 7090 := by native_decide
theorem BSD_E143_card_p7069 : (E143_Finset 7069).card = 7194 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p6991 : a_p 6991 = (-106 : ℤ) := by
  have h := BSD_E143_card_p6991; unfold a_p; omega
theorem BSD_ap_p6997 : a_p 6997 = (135 : ℤ) := by
  have h := BSD_E143_card_p6997; unfold a_p; omega
theorem BSD_ap_p7001 : a_p 7001 = (-22 : ℤ) := by
  have h := BSD_E143_card_p7001; unfold a_p; omega
theorem BSD_ap_p7013 : a_p 7013 = (-18 : ℤ) := by
  have h := BSD_E143_card_p7013; unfold a_p; omega
theorem BSD_ap_p7019 : a_p 7019 = (-20 : ℤ) := by
  have h := BSD_E143_card_p7019; unfold a_p; omega
theorem BSD_ap_p7027 : a_p 7027 = (33 : ℤ) := by
  have h := BSD_E143_card_p7027; unfold a_p; omega
theorem BSD_ap_p7039 : a_p 7039 = (66 : ℤ) := by
  have h := BSD_E143_card_p7039; unfold a_p; omega
theorem BSD_ap_p7043 : a_p 7043 = (-100 : ℤ) := by
  have h := BSD_E143_card_p7043; unfold a_p; omega
theorem BSD_ap_p7057 : a_p 7057 = (-32 : ℤ) := by
  have h := BSD_E143_card_p7057; unfold a_p; omega
theorem BSD_ap_p7069 : a_p 7069 = (-124 : ℤ) := by
  have h := BSD_E143_card_p7069; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=6991: a_p=-106, 4p-a_p²=16728
theorem BSD_DegreeNonneg_p6991 : BSD_FrobeniusDegreeNonneg_OPEN 6991 := fun r => by
  have hap : (a_p 6991 : ℝ) = -106 := by exact_mod_cast BSD_ap_p6991
  have key : r ^ 2 - (a_p 6991 : ℝ) * r + ((6991 : ℕ) : ℝ) =
      (r + 106/2) ^ 2 + 16728/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (106 : ℝ)/2)]

-- p=6997: a_p=+135, 4p-a_p²=9763
theorem BSD_DegreeNonneg_p6997 : BSD_FrobeniusDegreeNonneg_OPEN 6997 := fun r => by
  have hap : (a_p 6997 : ℝ) = 135 := by exact_mod_cast BSD_ap_p6997
  have key : r ^ 2 - (a_p 6997 : ℝ) * r + ((6997 : ℕ) : ℝ) =
      (r - 135/2) ^ 2 + 9763/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (135 : ℝ)/2)]

-- p=7001: a_p=-22, 4p-a_p²=27520
theorem BSD_DegreeNonneg_p7001 : BSD_FrobeniusDegreeNonneg_OPEN 7001 := fun r => by
  have hap : (a_p 7001 : ℝ) = -22 := by exact_mod_cast BSD_ap_p7001
  have key : r ^ 2 - (a_p 7001 : ℝ) * r + ((7001 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 27520/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

-- p=7013: a_p=-18, 4p-a_p²=27728
theorem BSD_DegreeNonneg_p7013 : BSD_FrobeniusDegreeNonneg_OPEN 7013 := fun r => by
  have hap : (a_p 7013 : ℝ) = -18 := by exact_mod_cast BSD_ap_p7013
  have key : r ^ 2 - (a_p 7013 : ℝ) * r + ((7013 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 27728/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

-- p=7019: a_p=-20, 4p-a_p²=27676
theorem BSD_DegreeNonneg_p7019 : BSD_FrobeniusDegreeNonneg_OPEN 7019 := fun r => by
  have hap : (a_p 7019 : ℝ) = -20 := by exact_mod_cast BSD_ap_p7019
  have key : r ^ 2 - (a_p 7019 : ℝ) * r + ((7019 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 27676/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=7027: a_p=+33, 4p-a_p²=27019
theorem BSD_DegreeNonneg_p7027 : BSD_FrobeniusDegreeNonneg_OPEN 7027 := fun r => by
  have hap : (a_p 7027 : ℝ) = 33 := by exact_mod_cast BSD_ap_p7027
  have key : r ^ 2 - (a_p 7027 : ℝ) * r + ((7027 : ℕ) : ℝ) =
      (r - 33/2) ^ 2 + 27019/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (33 : ℝ)/2)]

-- p=7039: a_p=+66, 4p-a_p²=23800
theorem BSD_DegreeNonneg_p7039 : BSD_FrobeniusDegreeNonneg_OPEN 7039 := fun r => by
  have hap : (a_p 7039 : ℝ) = 66 := by exact_mod_cast BSD_ap_p7039
  have key : r ^ 2 - (a_p 7039 : ℝ) * r + ((7039 : ℕ) : ℝ) =
      (r - 66/2) ^ 2 + 23800/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (66 : ℝ)/2)]

-- p=7043: a_p=-100, 4p-a_p²=18172
theorem BSD_DegreeNonneg_p7043 : BSD_FrobeniusDegreeNonneg_OPEN 7043 := fun r => by
  have hap : (a_p 7043 : ℝ) = -100 := by exact_mod_cast BSD_ap_p7043
  have key : r ^ 2 - (a_p 7043 : ℝ) * r + ((7043 : ℕ) : ℝ) =
      (r + 100/2) ^ 2 + 18172/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (100 : ℝ)/2)]

-- p=7057: a_p=-32, 4p-a_p²=27204
theorem BSD_DegreeNonneg_p7057 : BSD_FrobeniusDegreeNonneg_OPEN 7057 := fun r => by
  have hap : (a_p 7057 : ℝ) = -32 := by exact_mod_cast BSD_ap_p7057
  have key : r ^ 2 - (a_p 7057 : ℝ) * r + ((7057 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 27204/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

-- p=7069: a_p=-124, 4p-a_p²=12900
theorem BSD_DegreeNonneg_p7069 : BSD_FrobeniusDegreeNonneg_OPEN 7069 := fun r => by
  have hap : (a_p 7069 : ℝ) = -124 := by exact_mod_cast BSD_ap_p7069
  have key : r ^ 2 - (a_p 7069 : ℝ) * r + ((7069 : ℕ) : ℝ) =
      (r + 124/2) ^ 2 + 12900/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (124 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p6991 : BSD_Hasse_OPEN 6991 :=
  BSD_hasse_of_degree_nonneg 6991 BSD_DegreeNonneg_p6991
theorem BSD_Hasse_OPEN_p6997 : BSD_Hasse_OPEN 6997 :=
  BSD_hasse_of_degree_nonneg 6997 BSD_DegreeNonneg_p6997
theorem BSD_Hasse_OPEN_p7001 : BSD_Hasse_OPEN 7001 :=
  BSD_hasse_of_degree_nonneg 7001 BSD_DegreeNonneg_p7001
theorem BSD_Hasse_OPEN_p7013 : BSD_Hasse_OPEN 7013 :=
  BSD_hasse_of_degree_nonneg 7013 BSD_DegreeNonneg_p7013
theorem BSD_Hasse_OPEN_p7019 : BSD_Hasse_OPEN 7019 :=
  BSD_hasse_of_degree_nonneg 7019 BSD_DegreeNonneg_p7019
theorem BSD_Hasse_OPEN_p7027 : BSD_Hasse_OPEN 7027 :=
  BSD_hasse_of_degree_nonneg 7027 BSD_DegreeNonneg_p7027
theorem BSD_Hasse_OPEN_p7039 : BSD_Hasse_OPEN 7039 :=
  BSD_hasse_of_degree_nonneg 7039 BSD_DegreeNonneg_p7039
theorem BSD_Hasse_OPEN_p7043 : BSD_Hasse_OPEN 7043 :=
  BSD_hasse_of_degree_nonneg 7043 BSD_DegreeNonneg_p7043
theorem BSD_Hasse_OPEN_p7057 : BSD_Hasse_OPEN 7057 :=
  BSD_hasse_of_degree_nonneg 7057 BSD_DegreeNonneg_p7057
theorem BSD_Hasse_OPEN_p7069 : BSD_Hasse_OPEN 7069 :=
  BSD_hasse_of_degree_nonneg 7069 BSD_DegreeNonneg_p7069

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p6991 : (a_p 6991 : ℝ) ^ 2 ≤ 4 * (6991 : ℝ) :=
  BSD_disc_from_deg_856 BSD_DegreeNonneg_p6991
theorem BSD_HasseBound_Disc_p6997 : (a_p 6997 : ℝ) ^ 2 ≤ 4 * (6997 : ℝ) :=
  BSD_disc_from_deg_856 BSD_DegreeNonneg_p6997
theorem BSD_HasseBound_Disc_p7001 : (a_p 7001 : ℝ) ^ 2 ≤ 4 * (7001 : ℝ) :=
  BSD_disc_from_deg_856 BSD_DegreeNonneg_p7001
theorem BSD_HasseBound_Disc_p7013 : (a_p 7013 : ℝ) ^ 2 ≤ 4 * (7013 : ℝ) :=
  BSD_disc_from_deg_856 BSD_DegreeNonneg_p7013
theorem BSD_HasseBound_Disc_p7019 : (a_p 7019 : ℝ) ^ 2 ≤ 4 * (7019 : ℝ) :=
  BSD_disc_from_deg_856 BSD_DegreeNonneg_p7019
theorem BSD_HasseBound_Disc_p7027 : (a_p 7027 : ℝ) ^ 2 ≤ 4 * (7027 : ℝ) :=
  BSD_disc_from_deg_856 BSD_DegreeNonneg_p7027
theorem BSD_HasseBound_Disc_p7039 : (a_p 7039 : ℝ) ^ 2 ≤ 4 * (7039 : ℝ) :=
  BSD_disc_from_deg_856 BSD_DegreeNonneg_p7039
theorem BSD_HasseBound_Disc_p7043 : (a_p 7043 : ℝ) ^ 2 ≤ 4 * (7043 : ℝ) :=
  BSD_disc_from_deg_856 BSD_DegreeNonneg_p7043
theorem BSD_HasseBound_Disc_p7057 : (a_p 7057 : ℝ) ^ 2 ≤ 4 * (7057 : ℝ) :=
  BSD_disc_from_deg_856 BSD_DegreeNonneg_p7057
theorem BSD_HasseBound_Disc_p7069 : (a_p 7069 : ℝ) ^ 2 ≤ 4 * (7069 : ℝ) :=
  BSD_disc_from_deg_856 BSD_DegreeNonneg_p7069

end Towers.BSD
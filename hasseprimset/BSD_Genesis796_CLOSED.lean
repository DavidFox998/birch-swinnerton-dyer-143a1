/-
================================================================
Towers / BSD / BSD_Genesis796_CLOSED  (genesis-796)

HasseBridge Tier C: Hasse bounds for primes
1979..2029 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1979: card=1944, a_p=+36, disc=-6620
  p=1987: card=1986, a_p=+2, disc=-7944
  p=1993: card=2054, a_p=-60, disc=-4372
  p=1997: card=1962, a_p=+36, disc=-6692
  p=1999: card=2022, a_p=-22, disc=-7512
  p=2003: card=2000, a_p=+4, disc=-7996
  p=2011: card=2017, a_p=-5, disc=-8019
  p=2017: card=2033, a_p=-15, disc=-7843
  p=2027: card=1961, a_p=+67, disc=-3619
  p=2029: card=2085, a_p=-55, disc=-5091

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_796 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i796_p1979 : Fact (1979 : ℕ).Prime := ⟨by norm_num⟩
private instance i796_p1987 : Fact (1987 : ℕ).Prime := ⟨by norm_num⟩
private instance i796_p1993 : Fact (1993 : ℕ).Prime := ⟨by norm_num⟩
private instance i796_p1997 : Fact (1997 : ℕ).Prime := ⟨by norm_num⟩
private instance i796_p1999 : Fact (1999 : ℕ).Prime := ⟨by norm_num⟩
private instance i796_p2003 : Fact (2003 : ℕ).Prime := ⟨by norm_num⟩
private instance i796_p2011 : Fact (2011 : ℕ).Prime := ⟨by norm_num⟩
private instance i796_p2017 : Fact (2017 : ℕ).Prime := ⟨by norm_num⟩
private instance i796_p2027 : Fact (2027 : ℕ).Prime := ⟨by norm_num⟩
private instance i796_p2029 : Fact (2029 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1979 : (E143_Finset 1979).card = 1944 := by native_decide
theorem BSD_E143_card_p1987 : (E143_Finset 1987).card = 1986 := by native_decide
theorem BSD_E143_card_p1993 : (E143_Finset 1993).card = 2054 := by native_decide
theorem BSD_E143_card_p1997 : (E143_Finset 1997).card = 1962 := by native_decide
theorem BSD_E143_card_p1999 : (E143_Finset 1999).card = 2022 := by native_decide
theorem BSD_E143_card_p2003 : (E143_Finset 2003).card = 2000 := by native_decide
theorem BSD_E143_card_p2011 : (E143_Finset 2011).card = 2017 := by native_decide
theorem BSD_E143_card_p2017 : (E143_Finset 2017).card = 2033 := by native_decide
theorem BSD_E143_card_p2027 : (E143_Finset 2027).card = 1961 := by native_decide
theorem BSD_E143_card_p2029 : (E143_Finset 2029).card = 2085 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1979 : a_p 1979 = (36 : ℤ) := by
  have h := BSD_E143_card_p1979; unfold a_p; omega
theorem BSD_ap_p1987 : a_p 1987 = (2 : ℤ) := by
  have h := BSD_E143_card_p1987; unfold a_p; omega
theorem BSD_ap_p1993 : a_p 1993 = (-60 : ℤ) := by
  have h := BSD_E143_card_p1993; unfold a_p; omega
theorem BSD_ap_p1997 : a_p 1997 = (36 : ℤ) := by
  have h := BSD_E143_card_p1997; unfold a_p; omega
theorem BSD_ap_p1999 : a_p 1999 = (-22 : ℤ) := by
  have h := BSD_E143_card_p1999; unfold a_p; omega
theorem BSD_ap_p2003 : a_p 2003 = (4 : ℤ) := by
  have h := BSD_E143_card_p2003; unfold a_p; omega
theorem BSD_ap_p2011 : a_p 2011 = (-5 : ℤ) := by
  have h := BSD_E143_card_p2011; unfold a_p; omega
theorem BSD_ap_p2017 : a_p 2017 = (-15 : ℤ) := by
  have h := BSD_E143_card_p2017; unfold a_p; omega
theorem BSD_ap_p2027 : a_p 2027 = (67 : ℤ) := by
  have h := BSD_E143_card_p2027; unfold a_p; omega
theorem BSD_ap_p2029 : a_p 2029 = (-55 : ℤ) := by
  have h := BSD_E143_card_p2029; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1979: a_p=+36, 4p-a_p²=6620
theorem BSD_DegreeNonneg_p1979 : BSD_FrobeniusDegreeNonneg_OPEN 1979 := fun r => by
  have hap : (a_p 1979 : ℝ) = 36 := by exact_mod_cast BSD_ap_p1979
  have key : r ^ 2 - (a_p 1979 : ℝ) * r + ((1979 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 6620/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

-- p=1987: a_p=+2, 4p-a_p²=7944
theorem BSD_DegreeNonneg_p1987 : BSD_FrobeniusDegreeNonneg_OPEN 1987 := fun r => by
  have hap : (a_p 1987 : ℝ) = 2 := by exact_mod_cast BSD_ap_p1987
  have key : r ^ 2 - (a_p 1987 : ℝ) * r + ((1987 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 7944/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

-- p=1993: a_p=-60, 4p-a_p²=4372
theorem BSD_DegreeNonneg_p1993 : BSD_FrobeniusDegreeNonneg_OPEN 1993 := fun r => by
  have hap : (a_p 1993 : ℝ) = -60 := by exact_mod_cast BSD_ap_p1993
  have key : r ^ 2 - (a_p 1993 : ℝ) * r + ((1993 : ℕ) : ℝ) =
      (r + 60/2) ^ 2 + 4372/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (60 : ℝ)/2)]

-- p=1997: a_p=+36, 4p-a_p²=6692
theorem BSD_DegreeNonneg_p1997 : BSD_FrobeniusDegreeNonneg_OPEN 1997 := fun r => by
  have hap : (a_p 1997 : ℝ) = 36 := by exact_mod_cast BSD_ap_p1997
  have key : r ^ 2 - (a_p 1997 : ℝ) * r + ((1997 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 6692/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

-- p=1999: a_p=-22, 4p-a_p²=7512
theorem BSD_DegreeNonneg_p1999 : BSD_FrobeniusDegreeNonneg_OPEN 1999 := fun r => by
  have hap : (a_p 1999 : ℝ) = -22 := by exact_mod_cast BSD_ap_p1999
  have key : r ^ 2 - (a_p 1999 : ℝ) * r + ((1999 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 7512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

-- p=2003: a_p=+4, 4p-a_p²=7996
theorem BSD_DegreeNonneg_p2003 : BSD_FrobeniusDegreeNonneg_OPEN 2003 := fun r => by
  have hap : (a_p 2003 : ℝ) = 4 := by exact_mod_cast BSD_ap_p2003
  have key : r ^ 2 - (a_p 2003 : ℝ) * r + ((2003 : ℕ) : ℝ) =
      (r - 4/2) ^ 2 + 7996/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (4 : ℝ)/2)]

-- p=2011: a_p=-5, 4p-a_p²=8019
theorem BSD_DegreeNonneg_p2011 : BSD_FrobeniusDegreeNonneg_OPEN 2011 := fun r => by
  have hap : (a_p 2011 : ℝ) = -5 := by exact_mod_cast BSD_ap_p2011
  have key : r ^ 2 - (a_p 2011 : ℝ) * r + ((2011 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 8019/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

-- p=2017: a_p=-15, 4p-a_p²=7843
theorem BSD_DegreeNonneg_p2017 : BSD_FrobeniusDegreeNonneg_OPEN 2017 := fun r => by
  have hap : (a_p 2017 : ℝ) = -15 := by exact_mod_cast BSD_ap_p2017
  have key : r ^ 2 - (a_p 2017 : ℝ) * r + ((2017 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 7843/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

-- p=2027: a_p=+67, 4p-a_p²=3619
theorem BSD_DegreeNonneg_p2027 : BSD_FrobeniusDegreeNonneg_OPEN 2027 := fun r => by
  have hap : (a_p 2027 : ℝ) = 67 := by exact_mod_cast BSD_ap_p2027
  have key : r ^ 2 - (a_p 2027 : ℝ) * r + ((2027 : ℕ) : ℝ) =
      (r - 67/2) ^ 2 + 3619/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (67 : ℝ)/2)]

-- p=2029: a_p=-55, 4p-a_p²=5091
theorem BSD_DegreeNonneg_p2029 : BSD_FrobeniusDegreeNonneg_OPEN 2029 := fun r => by
  have hap : (a_p 2029 : ℝ) = -55 := by exact_mod_cast BSD_ap_p2029
  have key : r ^ 2 - (a_p 2029 : ℝ) * r + ((2029 : ℕ) : ℝ) =
      (r + 55/2) ^ 2 + 5091/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (55 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1979 : BSD_Hasse_OPEN 1979 :=
  BSD_hasse_of_degree_nonneg 1979 BSD_DegreeNonneg_p1979
theorem BSD_Hasse_OPEN_p1987 : BSD_Hasse_OPEN 1987 :=
  BSD_hasse_of_degree_nonneg 1987 BSD_DegreeNonneg_p1987
theorem BSD_Hasse_OPEN_p1993 : BSD_Hasse_OPEN 1993 :=
  BSD_hasse_of_degree_nonneg 1993 BSD_DegreeNonneg_p1993
theorem BSD_Hasse_OPEN_p1997 : BSD_Hasse_OPEN 1997 :=
  BSD_hasse_of_degree_nonneg 1997 BSD_DegreeNonneg_p1997
theorem BSD_Hasse_OPEN_p1999 : BSD_Hasse_OPEN 1999 :=
  BSD_hasse_of_degree_nonneg 1999 BSD_DegreeNonneg_p1999
theorem BSD_Hasse_OPEN_p2003 : BSD_Hasse_OPEN 2003 :=
  BSD_hasse_of_degree_nonneg 2003 BSD_DegreeNonneg_p2003
theorem BSD_Hasse_OPEN_p2011 : BSD_Hasse_OPEN 2011 :=
  BSD_hasse_of_degree_nonneg 2011 BSD_DegreeNonneg_p2011
theorem BSD_Hasse_OPEN_p2017 : BSD_Hasse_OPEN 2017 :=
  BSD_hasse_of_degree_nonneg 2017 BSD_DegreeNonneg_p2017
theorem BSD_Hasse_OPEN_p2027 : BSD_Hasse_OPEN 2027 :=
  BSD_hasse_of_degree_nonneg 2027 BSD_DegreeNonneg_p2027
theorem BSD_Hasse_OPEN_p2029 : BSD_Hasse_OPEN 2029 :=
  BSD_hasse_of_degree_nonneg 2029 BSD_DegreeNonneg_p2029

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1979 : (a_p 1979 : ℝ) ^ 2 ≤ 4 * (1979 : ℝ) :=
  BSD_disc_from_deg_796 BSD_DegreeNonneg_p1979
theorem BSD_HasseBound_Disc_p1987 : (a_p 1987 : ℝ) ^ 2 ≤ 4 * (1987 : ℝ) :=
  BSD_disc_from_deg_796 BSD_DegreeNonneg_p1987
theorem BSD_HasseBound_Disc_p1993 : (a_p 1993 : ℝ) ^ 2 ≤ 4 * (1993 : ℝ) :=
  BSD_disc_from_deg_796 BSD_DegreeNonneg_p1993
theorem BSD_HasseBound_Disc_p1997 : (a_p 1997 : ℝ) ^ 2 ≤ 4 * (1997 : ℝ) :=
  BSD_disc_from_deg_796 BSD_DegreeNonneg_p1997
theorem BSD_HasseBound_Disc_p1999 : (a_p 1999 : ℝ) ^ 2 ≤ 4 * (1999 : ℝ) :=
  BSD_disc_from_deg_796 BSD_DegreeNonneg_p1999
theorem BSD_HasseBound_Disc_p2003 : (a_p 2003 : ℝ) ^ 2 ≤ 4 * (2003 : ℝ) :=
  BSD_disc_from_deg_796 BSD_DegreeNonneg_p2003
theorem BSD_HasseBound_Disc_p2011 : (a_p 2011 : ℝ) ^ 2 ≤ 4 * (2011 : ℝ) :=
  BSD_disc_from_deg_796 BSD_DegreeNonneg_p2011
theorem BSD_HasseBound_Disc_p2017 : (a_p 2017 : ℝ) ^ 2 ≤ 4 * (2017 : ℝ) :=
  BSD_disc_from_deg_796 BSD_DegreeNonneg_p2017
theorem BSD_HasseBound_Disc_p2027 : (a_p 2027 : ℝ) ^ 2 ≤ 4 * (2027 : ℝ) :=
  BSD_disc_from_deg_796 BSD_DegreeNonneg_p2027
theorem BSD_HasseBound_Disc_p2029 : (a_p 2029 : ℝ) ^ 2 ≤ 4 * (2029 : ℝ) :=
  BSD_disc_from_deg_796 BSD_DegreeNonneg_p2029

end Towers.BSD
/-
================================================================
Towers / BSD / BSD_Genesis795_CLOSED  (genesis-795)

HasseBridge Tier C: Hasse bounds for primes
1879..1973 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1879: card=1873, a_p=+7, disc=-7467
  p=1889: card=1836, a_p=+54, disc=-4640
  p=1901: card=1877, a_p=+25, disc=-6979
  p=1907: card=1928, a_p=-20, disc=-7228
  p=1913: card=1856, a_p=+58, disc=-4288
  p=1931: card=1954, a_p=-22, disc=-7240
  p=1933: card=1930, a_p=+4, disc=-7716
  p=1949: card=1972, a_p=-22, disc=-7312
  p=1951: card=2015, a_p=-63, disc=-3835
  p=1973: card=1975, a_p=-1, disc=-7891

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_795 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i795_p1879 : Fact (1879 : ℕ).Prime := ⟨by norm_num⟩
private instance i795_p1889 : Fact (1889 : ℕ).Prime := ⟨by norm_num⟩
private instance i795_p1901 : Fact (1901 : ℕ).Prime := ⟨by norm_num⟩
private instance i795_p1907 : Fact (1907 : ℕ).Prime := ⟨by norm_num⟩
private instance i795_p1913 : Fact (1913 : ℕ).Prime := ⟨by norm_num⟩
private instance i795_p1931 : Fact (1931 : ℕ).Prime := ⟨by norm_num⟩
private instance i795_p1933 : Fact (1933 : ℕ).Prime := ⟨by norm_num⟩
private instance i795_p1949 : Fact (1949 : ℕ).Prime := ⟨by norm_num⟩
private instance i795_p1951 : Fact (1951 : ℕ).Prime := ⟨by norm_num⟩
private instance i795_p1973 : Fact (1973 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1879 : (E143_Finset 1879).card = 1873 := by native_decide
theorem BSD_E143_card_p1889 : (E143_Finset 1889).card = 1836 := by native_decide
theorem BSD_E143_card_p1901 : (E143_Finset 1901).card = 1877 := by native_decide
theorem BSD_E143_card_p1907 : (E143_Finset 1907).card = 1928 := by native_decide
theorem BSD_E143_card_p1913 : (E143_Finset 1913).card = 1856 := by native_decide
theorem BSD_E143_card_p1931 : (E143_Finset 1931).card = 1954 := by native_decide
theorem BSD_E143_card_p1933 : (E143_Finset 1933).card = 1930 := by native_decide
theorem BSD_E143_card_p1949 : (E143_Finset 1949).card = 1972 := by native_decide
theorem BSD_E143_card_p1951 : (E143_Finset 1951).card = 2015 := by native_decide
theorem BSD_E143_card_p1973 : (E143_Finset 1973).card = 1975 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1879 : a_p 1879 = (7 : ℤ) := by
  have h := BSD_E143_card_p1879; unfold a_p; omega
theorem BSD_ap_p1889 : a_p 1889 = (54 : ℤ) := by
  have h := BSD_E143_card_p1889; unfold a_p; omega
theorem BSD_ap_p1901 : a_p 1901 = (25 : ℤ) := by
  have h := BSD_E143_card_p1901; unfold a_p; omega
theorem BSD_ap_p1907 : a_p 1907 = (-20 : ℤ) := by
  have h := BSD_E143_card_p1907; unfold a_p; omega
theorem BSD_ap_p1913 : a_p 1913 = (58 : ℤ) := by
  have h := BSD_E143_card_p1913; unfold a_p; omega
theorem BSD_ap_p1931 : a_p 1931 = (-22 : ℤ) := by
  have h := BSD_E143_card_p1931; unfold a_p; omega
theorem BSD_ap_p1933 : a_p 1933 = (4 : ℤ) := by
  have h := BSD_E143_card_p1933; unfold a_p; omega
theorem BSD_ap_p1949 : a_p 1949 = (-22 : ℤ) := by
  have h := BSD_E143_card_p1949; unfold a_p; omega
theorem BSD_ap_p1951 : a_p 1951 = (-63 : ℤ) := by
  have h := BSD_E143_card_p1951; unfold a_p; omega
theorem BSD_ap_p1973 : a_p 1973 = (-1 : ℤ) := by
  have h := BSD_E143_card_p1973; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1879: a_p=+7, 4p-a_p²=7467
theorem BSD_DegreeNonneg_p1879 : BSD_FrobeniusDegreeNonneg_OPEN 1879 := fun r => by
  have hap : (a_p 1879 : ℝ) = 7 := by exact_mod_cast BSD_ap_p1879
  have key : r ^ 2 - (a_p 1879 : ℝ) * r + ((1879 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 7467/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

-- p=1889: a_p=+54, 4p-a_p²=4640
theorem BSD_DegreeNonneg_p1889 : BSD_FrobeniusDegreeNonneg_OPEN 1889 := fun r => by
  have hap : (a_p 1889 : ℝ) = 54 := by exact_mod_cast BSD_ap_p1889
  have key : r ^ 2 - (a_p 1889 : ℝ) * r + ((1889 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 4640/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

-- p=1901: a_p=+25, 4p-a_p²=6979
theorem BSD_DegreeNonneg_p1901 : BSD_FrobeniusDegreeNonneg_OPEN 1901 := fun r => by
  have hap : (a_p 1901 : ℝ) = 25 := by exact_mod_cast BSD_ap_p1901
  have key : r ^ 2 - (a_p 1901 : ℝ) * r + ((1901 : ℕ) : ℝ) =
      (r - 25/2) ^ 2 + 6979/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (25 : ℝ)/2)]

-- p=1907: a_p=-20, 4p-a_p²=7228
theorem BSD_DegreeNonneg_p1907 : BSD_FrobeniusDegreeNonneg_OPEN 1907 := fun r => by
  have hap : (a_p 1907 : ℝ) = -20 := by exact_mod_cast BSD_ap_p1907
  have key : r ^ 2 - (a_p 1907 : ℝ) * r + ((1907 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 7228/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=1913: a_p=+58, 4p-a_p²=4288
theorem BSD_DegreeNonneg_p1913 : BSD_FrobeniusDegreeNonneg_OPEN 1913 := fun r => by
  have hap : (a_p 1913 : ℝ) = 58 := by exact_mod_cast BSD_ap_p1913
  have key : r ^ 2 - (a_p 1913 : ℝ) * r + ((1913 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 4288/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

-- p=1931: a_p=-22, 4p-a_p²=7240
theorem BSD_DegreeNonneg_p1931 : BSD_FrobeniusDegreeNonneg_OPEN 1931 := fun r => by
  have hap : (a_p 1931 : ℝ) = -22 := by exact_mod_cast BSD_ap_p1931
  have key : r ^ 2 - (a_p 1931 : ℝ) * r + ((1931 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 7240/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

-- p=1933: a_p=+4, 4p-a_p²=7716
theorem BSD_DegreeNonneg_p1933 : BSD_FrobeniusDegreeNonneg_OPEN 1933 := fun r => by
  have hap : (a_p 1933 : ℝ) = 4 := by exact_mod_cast BSD_ap_p1933
  have key : r ^ 2 - (a_p 1933 : ℝ) * r + ((1933 : ℕ) : ℝ) =
      (r - 4/2) ^ 2 + 7716/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (4 : ℝ)/2)]

-- p=1949: a_p=-22, 4p-a_p²=7312
theorem BSD_DegreeNonneg_p1949 : BSD_FrobeniusDegreeNonneg_OPEN 1949 := fun r => by
  have hap : (a_p 1949 : ℝ) = -22 := by exact_mod_cast BSD_ap_p1949
  have key : r ^ 2 - (a_p 1949 : ℝ) * r + ((1949 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 7312/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

-- p=1951: a_p=-63, 4p-a_p²=3835
theorem BSD_DegreeNonneg_p1951 : BSD_FrobeniusDegreeNonneg_OPEN 1951 := fun r => by
  have hap : (a_p 1951 : ℝ) = -63 := by exact_mod_cast BSD_ap_p1951
  have key : r ^ 2 - (a_p 1951 : ℝ) * r + ((1951 : ℕ) : ℝ) =
      (r + 63/2) ^ 2 + 3835/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (63 : ℝ)/2)]

-- p=1973: a_p=-1, 4p-a_p²=7891
theorem BSD_DegreeNonneg_p1973 : BSD_FrobeniusDegreeNonneg_OPEN 1973 := fun r => by
  have hap : (a_p 1973 : ℝ) = -1 := by exact_mod_cast BSD_ap_p1973
  have key : r ^ 2 - (a_p 1973 : ℝ) * r + ((1973 : ℕ) : ℝ) =
      (r + 1/2) ^ 2 + 7891/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (1 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1879 : BSD_Hasse_OPEN 1879 :=
  BSD_hasse_of_degree_nonneg 1879 BSD_DegreeNonneg_p1879
theorem BSD_Hasse_OPEN_p1889 : BSD_Hasse_OPEN 1889 :=
  BSD_hasse_of_degree_nonneg 1889 BSD_DegreeNonneg_p1889
theorem BSD_Hasse_OPEN_p1901 : BSD_Hasse_OPEN 1901 :=
  BSD_hasse_of_degree_nonneg 1901 BSD_DegreeNonneg_p1901
theorem BSD_Hasse_OPEN_p1907 : BSD_Hasse_OPEN 1907 :=
  BSD_hasse_of_degree_nonneg 1907 BSD_DegreeNonneg_p1907
theorem BSD_Hasse_OPEN_p1913 : BSD_Hasse_OPEN 1913 :=
  BSD_hasse_of_degree_nonneg 1913 BSD_DegreeNonneg_p1913
theorem BSD_Hasse_OPEN_p1931 : BSD_Hasse_OPEN 1931 :=
  BSD_hasse_of_degree_nonneg 1931 BSD_DegreeNonneg_p1931
theorem BSD_Hasse_OPEN_p1933 : BSD_Hasse_OPEN 1933 :=
  BSD_hasse_of_degree_nonneg 1933 BSD_DegreeNonneg_p1933
theorem BSD_Hasse_OPEN_p1949 : BSD_Hasse_OPEN 1949 :=
  BSD_hasse_of_degree_nonneg 1949 BSD_DegreeNonneg_p1949
theorem BSD_Hasse_OPEN_p1951 : BSD_Hasse_OPEN 1951 :=
  BSD_hasse_of_degree_nonneg 1951 BSD_DegreeNonneg_p1951
theorem BSD_Hasse_OPEN_p1973 : BSD_Hasse_OPEN 1973 :=
  BSD_hasse_of_degree_nonneg 1973 BSD_DegreeNonneg_p1973

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1879 : (a_p 1879 : ℝ) ^ 2 ≤ 4 * (1879 : ℝ) :=
  BSD_disc_from_deg_795 BSD_DegreeNonneg_p1879
theorem BSD_HasseBound_Disc_p1889 : (a_p 1889 : ℝ) ^ 2 ≤ 4 * (1889 : ℝ) :=
  BSD_disc_from_deg_795 BSD_DegreeNonneg_p1889
theorem BSD_HasseBound_Disc_p1901 : (a_p 1901 : ℝ) ^ 2 ≤ 4 * (1901 : ℝ) :=
  BSD_disc_from_deg_795 BSD_DegreeNonneg_p1901
theorem BSD_HasseBound_Disc_p1907 : (a_p 1907 : ℝ) ^ 2 ≤ 4 * (1907 : ℝ) :=
  BSD_disc_from_deg_795 BSD_DegreeNonneg_p1907
theorem BSD_HasseBound_Disc_p1913 : (a_p 1913 : ℝ) ^ 2 ≤ 4 * (1913 : ℝ) :=
  BSD_disc_from_deg_795 BSD_DegreeNonneg_p1913
theorem BSD_HasseBound_Disc_p1931 : (a_p 1931 : ℝ) ^ 2 ≤ 4 * (1931 : ℝ) :=
  BSD_disc_from_deg_795 BSD_DegreeNonneg_p1931
theorem BSD_HasseBound_Disc_p1933 : (a_p 1933 : ℝ) ^ 2 ≤ 4 * (1933 : ℝ) :=
  BSD_disc_from_deg_795 BSD_DegreeNonneg_p1933
theorem BSD_HasseBound_Disc_p1949 : (a_p 1949 : ℝ) ^ 2 ≤ 4 * (1949 : ℝ) :=
  BSD_disc_from_deg_795 BSD_DegreeNonneg_p1949
theorem BSD_HasseBound_Disc_p1951 : (a_p 1951 : ℝ) ^ 2 ≤ 4 * (1951 : ℝ) :=
  BSD_disc_from_deg_795 BSD_DegreeNonneg_p1951
theorem BSD_HasseBound_Disc_p1973 : (a_p 1973 : ℝ) ^ 2 ≤ 4 * (1973 : ℝ) :=
  BSD_disc_from_deg_795 BSD_DegreeNonneg_p1973

end Towers.BSD
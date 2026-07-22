/-
================================================================
Towers / BSD / BSD_Genesis794_CLOSED  (genesis-794)

HasseBridge Tier C: Hasse bounds for primes
1801..1877 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=1801: card=1802, a_p=+0, disc=-7204
  p=1811: card=1852, a_p=-40, disc=-5644
  p=1823: card=1786, a_p=+38, disc=-5848
  p=1831: card=1785, a_p=+47, disc=-5115
  p=1847: card=1910, a_p=-62, disc=-3544
  p=1861: card=1882, a_p=-20, disc=-7044
  p=1867: card=1890, a_p=-22, disc=-6984
  p=1871: card=1851, a_p=+21, disc=-7043
  p=1873: card=1928, a_p=-54, disc=-4576
  p=1877: card=1954, a_p=-76, disc=-1732

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_794 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i794_p1801 : Fact (1801 : ℕ).Prime := ⟨by norm_num⟩
private instance i794_p1811 : Fact (1811 : ℕ).Prime := ⟨by norm_num⟩
private instance i794_p1823 : Fact (1823 : ℕ).Prime := ⟨by norm_num⟩
private instance i794_p1831 : Fact (1831 : ℕ).Prime := ⟨by norm_num⟩
private instance i794_p1847 : Fact (1847 : ℕ).Prime := ⟨by norm_num⟩
private instance i794_p1861 : Fact (1861 : ℕ).Prime := ⟨by norm_num⟩
private instance i794_p1867 : Fact (1867 : ℕ).Prime := ⟨by norm_num⟩
private instance i794_p1871 : Fact (1871 : ℕ).Prime := ⟨by norm_num⟩
private instance i794_p1873 : Fact (1873 : ℕ).Prime := ⟨by norm_num⟩
private instance i794_p1877 : Fact (1877 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p1801 : (E143_Finset 1801).card = 1802 := by native_decide
theorem BSD_E143_card_p1811 : (E143_Finset 1811).card = 1852 := by native_decide
theorem BSD_E143_card_p1823 : (E143_Finset 1823).card = 1786 := by native_decide
theorem BSD_E143_card_p1831 : (E143_Finset 1831).card = 1785 := by native_decide
theorem BSD_E143_card_p1847 : (E143_Finset 1847).card = 1910 := by native_decide
theorem BSD_E143_card_p1861 : (E143_Finset 1861).card = 1882 := by native_decide
theorem BSD_E143_card_p1867 : (E143_Finset 1867).card = 1890 := by native_decide
theorem BSD_E143_card_p1871 : (E143_Finset 1871).card = 1851 := by native_decide
theorem BSD_E143_card_p1873 : (E143_Finset 1873).card = 1928 := by native_decide
theorem BSD_E143_card_p1877 : (E143_Finset 1877).card = 1954 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p1801 : a_p 1801 = (0 : ℤ) := by
  have h := BSD_E143_card_p1801; unfold a_p; omega
theorem BSD_ap_p1811 : a_p 1811 = (-40 : ℤ) := by
  have h := BSD_E143_card_p1811; unfold a_p; omega
theorem BSD_ap_p1823 : a_p 1823 = (38 : ℤ) := by
  have h := BSD_E143_card_p1823; unfold a_p; omega
theorem BSD_ap_p1831 : a_p 1831 = (47 : ℤ) := by
  have h := BSD_E143_card_p1831; unfold a_p; omega
theorem BSD_ap_p1847 : a_p 1847 = (-62 : ℤ) := by
  have h := BSD_E143_card_p1847; unfold a_p; omega
theorem BSD_ap_p1861 : a_p 1861 = (-20 : ℤ) := by
  have h := BSD_E143_card_p1861; unfold a_p; omega
theorem BSD_ap_p1867 : a_p 1867 = (-22 : ℤ) := by
  have h := BSD_E143_card_p1867; unfold a_p; omega
theorem BSD_ap_p1871 : a_p 1871 = (21 : ℤ) := by
  have h := BSD_E143_card_p1871; unfold a_p; omega
theorem BSD_ap_p1873 : a_p 1873 = (-54 : ℤ) := by
  have h := BSD_E143_card_p1873; unfold a_p; omega
theorem BSD_ap_p1877 : a_p 1877 = (-76 : ℤ) := by
  have h := BSD_E143_card_p1877; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=1801: a_p=+0, 4p-a_p²=7204
theorem BSD_DegreeNonneg_p1801 : BSD_FrobeniusDegreeNonneg_OPEN 1801 := fun r => by
  have hap : (a_p 1801 : ℝ) = 0 := by exact_mod_cast BSD_ap_p1801
  have key : r ^ 2 - (a_p 1801 : ℝ) * r + ((1801 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 7204/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

-- p=1811: a_p=-40, 4p-a_p²=5644
theorem BSD_DegreeNonneg_p1811 : BSD_FrobeniusDegreeNonneg_OPEN 1811 := fun r => by
  have hap : (a_p 1811 : ℝ) = -40 := by exact_mod_cast BSD_ap_p1811
  have key : r ^ 2 - (a_p 1811 : ℝ) * r + ((1811 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 5644/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

-- p=1823: a_p=+38, 4p-a_p²=5848
theorem BSD_DegreeNonneg_p1823 : BSD_FrobeniusDegreeNonneg_OPEN 1823 := fun r => by
  have hap : (a_p 1823 : ℝ) = 38 := by exact_mod_cast BSD_ap_p1823
  have key : r ^ 2 - (a_p 1823 : ℝ) * r + ((1823 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 5848/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

-- p=1831: a_p=+47, 4p-a_p²=5115
theorem BSD_DegreeNonneg_p1831 : BSD_FrobeniusDegreeNonneg_OPEN 1831 := fun r => by
  have hap : (a_p 1831 : ℝ) = 47 := by exact_mod_cast BSD_ap_p1831
  have key : r ^ 2 - (a_p 1831 : ℝ) * r + ((1831 : ℕ) : ℝ) =
      (r - 47/2) ^ 2 + 5115/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (47 : ℝ)/2)]

-- p=1847: a_p=-62, 4p-a_p²=3544
theorem BSD_DegreeNonneg_p1847 : BSD_FrobeniusDegreeNonneg_OPEN 1847 := fun r => by
  have hap : (a_p 1847 : ℝ) = -62 := by exact_mod_cast BSD_ap_p1847
  have key : r ^ 2 - (a_p 1847 : ℝ) * r + ((1847 : ℕ) : ℝ) =
      (r + 62/2) ^ 2 + 3544/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (62 : ℝ)/2)]

-- p=1861: a_p=-20, 4p-a_p²=7044
theorem BSD_DegreeNonneg_p1861 : BSD_FrobeniusDegreeNonneg_OPEN 1861 := fun r => by
  have hap : (a_p 1861 : ℝ) = -20 := by exact_mod_cast BSD_ap_p1861
  have key : r ^ 2 - (a_p 1861 : ℝ) * r + ((1861 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 7044/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

-- p=1867: a_p=-22, 4p-a_p²=6984
theorem BSD_DegreeNonneg_p1867 : BSD_FrobeniusDegreeNonneg_OPEN 1867 := fun r => by
  have hap : (a_p 1867 : ℝ) = -22 := by exact_mod_cast BSD_ap_p1867
  have key : r ^ 2 - (a_p 1867 : ℝ) * r + ((1867 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 6984/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

-- p=1871: a_p=+21, 4p-a_p²=7043
theorem BSD_DegreeNonneg_p1871 : BSD_FrobeniusDegreeNonneg_OPEN 1871 := fun r => by
  have hap : (a_p 1871 : ℝ) = 21 := by exact_mod_cast BSD_ap_p1871
  have key : r ^ 2 - (a_p 1871 : ℝ) * r + ((1871 : ℕ) : ℝ) =
      (r - 21/2) ^ 2 + 7043/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (21 : ℝ)/2)]

-- p=1873: a_p=-54, 4p-a_p²=4576
theorem BSD_DegreeNonneg_p1873 : BSD_FrobeniusDegreeNonneg_OPEN 1873 := fun r => by
  have hap : (a_p 1873 : ℝ) = -54 := by exact_mod_cast BSD_ap_p1873
  have key : r ^ 2 - (a_p 1873 : ℝ) * r + ((1873 : ℕ) : ℝ) =
      (r + 54/2) ^ 2 + 4576/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (54 : ℝ)/2)]

-- p=1877: a_p=-76, 4p-a_p²=1732
theorem BSD_DegreeNonneg_p1877 : BSD_FrobeniusDegreeNonneg_OPEN 1877 := fun r => by
  have hap : (a_p 1877 : ℝ) = -76 := by exact_mod_cast BSD_ap_p1877
  have key : r ^ 2 - (a_p 1877 : ℝ) * r + ((1877 : ℕ) : ℝ) =
      (r + 76/2) ^ 2 + 1732/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (76 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p1801 : BSD_Hasse_OPEN 1801 :=
  BSD_hasse_of_degree_nonneg 1801 BSD_DegreeNonneg_p1801
theorem BSD_Hasse_OPEN_p1811 : BSD_Hasse_OPEN 1811 :=
  BSD_hasse_of_degree_nonneg 1811 BSD_DegreeNonneg_p1811
theorem BSD_Hasse_OPEN_p1823 : BSD_Hasse_OPEN 1823 :=
  BSD_hasse_of_degree_nonneg 1823 BSD_DegreeNonneg_p1823
theorem BSD_Hasse_OPEN_p1831 : BSD_Hasse_OPEN 1831 :=
  BSD_hasse_of_degree_nonneg 1831 BSD_DegreeNonneg_p1831
theorem BSD_Hasse_OPEN_p1847 : BSD_Hasse_OPEN 1847 :=
  BSD_hasse_of_degree_nonneg 1847 BSD_DegreeNonneg_p1847
theorem BSD_Hasse_OPEN_p1861 : BSD_Hasse_OPEN 1861 :=
  BSD_hasse_of_degree_nonneg 1861 BSD_DegreeNonneg_p1861
theorem BSD_Hasse_OPEN_p1867 : BSD_Hasse_OPEN 1867 :=
  BSD_hasse_of_degree_nonneg 1867 BSD_DegreeNonneg_p1867
theorem BSD_Hasse_OPEN_p1871 : BSD_Hasse_OPEN 1871 :=
  BSD_hasse_of_degree_nonneg 1871 BSD_DegreeNonneg_p1871
theorem BSD_Hasse_OPEN_p1873 : BSD_Hasse_OPEN 1873 :=
  BSD_hasse_of_degree_nonneg 1873 BSD_DegreeNonneg_p1873
theorem BSD_Hasse_OPEN_p1877 : BSD_Hasse_OPEN 1877 :=
  BSD_hasse_of_degree_nonneg 1877 BSD_DegreeNonneg_p1877

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p1801 : (a_p 1801 : ℝ) ^ 2 ≤ 4 * (1801 : ℝ) :=
  BSD_disc_from_deg_794 BSD_DegreeNonneg_p1801
theorem BSD_HasseBound_Disc_p1811 : (a_p 1811 : ℝ) ^ 2 ≤ 4 * (1811 : ℝ) :=
  BSD_disc_from_deg_794 BSD_DegreeNonneg_p1811
theorem BSD_HasseBound_Disc_p1823 : (a_p 1823 : ℝ) ^ 2 ≤ 4 * (1823 : ℝ) :=
  BSD_disc_from_deg_794 BSD_DegreeNonneg_p1823
theorem BSD_HasseBound_Disc_p1831 : (a_p 1831 : ℝ) ^ 2 ≤ 4 * (1831 : ℝ) :=
  BSD_disc_from_deg_794 BSD_DegreeNonneg_p1831
theorem BSD_HasseBound_Disc_p1847 : (a_p 1847 : ℝ) ^ 2 ≤ 4 * (1847 : ℝ) :=
  BSD_disc_from_deg_794 BSD_DegreeNonneg_p1847
theorem BSD_HasseBound_Disc_p1861 : (a_p 1861 : ℝ) ^ 2 ≤ 4 * (1861 : ℝ) :=
  BSD_disc_from_deg_794 BSD_DegreeNonneg_p1861
theorem BSD_HasseBound_Disc_p1867 : (a_p 1867 : ℝ) ^ 2 ≤ 4 * (1867 : ℝ) :=
  BSD_disc_from_deg_794 BSD_DegreeNonneg_p1867
theorem BSD_HasseBound_Disc_p1871 : (a_p 1871 : ℝ) ^ 2 ≤ 4 * (1871 : ℝ) :=
  BSD_disc_from_deg_794 BSD_DegreeNonneg_p1871
theorem BSD_HasseBound_Disc_p1873 : (a_p 1873 : ℝ) ^ 2 ≤ 4 * (1873 : ℝ) :=
  BSD_disc_from_deg_794 BSD_DegreeNonneg_p1873
theorem BSD_HasseBound_Disc_p1877 : (a_p 1877 : ℝ) ^ 2 ≤ 4 * (1877 : ℝ) :=
  BSD_disc_from_deg_794 BSD_DegreeNonneg_p1877

end Towers.BSD
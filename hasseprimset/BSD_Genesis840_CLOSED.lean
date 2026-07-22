/-
================================================================
Towers / BSD / BSD_Genesis840_CLOSED  (genesis-840)

HasseBridge Tier C: Hasse bounds for primes
5623..5683 (10 primes).

Affine point counts (native_decide on E143_Finset p):
  p=5623: card=5702, a_p=-78, disc=-16408
  p=5639: card=5564, a_p=+76, disc=-16780
  p=5641: card=5673, a_p=-31, disc=-21603
  p=5647: card=5533, a_p=+115, disc=-9363
  p=5651: card=5764, a_p=-112, disc=-10060
  p=5653: card=5706, a_p=-52, disc=-19908
  p=5657: card=5729, a_p=-71, disc=-17587
  p=5659: card=5753, a_p=-93, disc=-13987
  p=5669: card=5700, a_p=-30, disc=-21776
  p=5683: card=5820, a_p=-136, disc=-4236

0 sorry, classical trio.
NOT a brick. BSD: OPEN (Clay). No Clay claim.
================================================================
-/

import Towers.BSD.BSD_Genesis782_CLOSED
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Towers.BSD

private lemma BSD_disc_from_deg_840 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2); nlinarith [hspec]

/-! ## §1. Fact instances -/

private instance i840_p5623 : Fact (5623 : ℕ).Prime := ⟨by norm_num⟩
private instance i840_p5639 : Fact (5639 : ℕ).Prime := ⟨by norm_num⟩
private instance i840_p5641 : Fact (5641 : ℕ).Prime := ⟨by norm_num⟩
private instance i840_p5647 : Fact (5647 : ℕ).Prime := ⟨by norm_num⟩
private instance i840_p5651 : Fact (5651 : ℕ).Prime := ⟨by norm_num⟩
private instance i840_p5653 : Fact (5653 : ℕ).Prime := ⟨by norm_num⟩
private instance i840_p5657 : Fact (5657 : ℕ).Prime := ⟨by norm_num⟩
private instance i840_p5659 : Fact (5659 : ℕ).Prime := ⟨by norm_num⟩
private instance i840_p5669 : Fact (5669 : ℕ).Prime := ⟨by norm_num⟩
private instance i840_p5683 : Fact (5683 : ℕ).Prime := ⟨by norm_num⟩

/-! ## §2. Point counts (native_decide) -/

theorem BSD_E143_card_p5623 : (E143_Finset 5623).card = 5702 := by native_decide
theorem BSD_E143_card_p5639 : (E143_Finset 5639).card = 5564 := by native_decide
theorem BSD_E143_card_p5641 : (E143_Finset 5641).card = 5673 := by native_decide
theorem BSD_E143_card_p5647 : (E143_Finset 5647).card = 5533 := by native_decide
theorem BSD_E143_card_p5651 : (E143_Finset 5651).card = 5764 := by native_decide
theorem BSD_E143_card_p5653 : (E143_Finset 5653).card = 5706 := by native_decide
theorem BSD_E143_card_p5657 : (E143_Finset 5657).card = 5729 := by native_decide
theorem BSD_E143_card_p5659 : (E143_Finset 5659).card = 5753 := by native_decide
theorem BSD_E143_card_p5669 : (E143_Finset 5669).card = 5700 := by native_decide
theorem BSD_E143_card_p5683 : (E143_Finset 5683).card = 5820 := by native_decide

/-! ## §3. Exact a_p values -/

theorem BSD_ap_p5623 : a_p 5623 = (-78 : ℤ) := by
  have h := BSD_E143_card_p5623; unfold a_p; omega
theorem BSD_ap_p5639 : a_p 5639 = (76 : ℤ) := by
  have h := BSD_E143_card_p5639; unfold a_p; omega
theorem BSD_ap_p5641 : a_p 5641 = (-31 : ℤ) := by
  have h := BSD_E143_card_p5641; unfold a_p; omega
theorem BSD_ap_p5647 : a_p 5647 = (115 : ℤ) := by
  have h := BSD_E143_card_p5647; unfold a_p; omega
theorem BSD_ap_p5651 : a_p 5651 = (-112 : ℤ) := by
  have h := BSD_E143_card_p5651; unfold a_p; omega
theorem BSD_ap_p5653 : a_p 5653 = (-52 : ℤ) := by
  have h := BSD_E143_card_p5653; unfold a_p; omega
theorem BSD_ap_p5657 : a_p 5657 = (-71 : ℤ) := by
  have h := BSD_E143_card_p5657; unfold a_p; omega
theorem BSD_ap_p5659 : a_p 5659 = (-93 : ℤ) := by
  have h := BSD_E143_card_p5659; unfold a_p; omega
theorem BSD_ap_p5669 : a_p 5669 = (-30 : ℤ) := by
  have h := BSD_E143_card_p5669; unfold a_p; omega
theorem BSD_ap_p5683 : a_p 5683 = (-136 : ℤ) := by
  have h := BSD_E143_card_p5683; unfold a_p; omega

/-! ## §4. Degree non-negativity (completed-square, Hasse |a_p| ≤ 2√p) -/

-- p=5623: a_p=-78, 4p-a_p²=16408
theorem BSD_DegreeNonneg_p5623 : BSD_FrobeniusDegreeNonneg_OPEN 5623 := fun r => by
  have hap : (a_p 5623 : ℝ) = -78 := by exact_mod_cast BSD_ap_p5623
  have key : r ^ 2 - (a_p 5623 : ℝ) * r + ((5623 : ℕ) : ℝ) =
      (r + 78/2) ^ 2 + 16408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (78 : ℝ)/2)]

-- p=5639: a_p=+76, 4p-a_p²=16780
theorem BSD_DegreeNonneg_p5639 : BSD_FrobeniusDegreeNonneg_OPEN 5639 := fun r => by
  have hap : (a_p 5639 : ℝ) = 76 := by exact_mod_cast BSD_ap_p5639
  have key : r ^ 2 - (a_p 5639 : ℝ) * r + ((5639 : ℕ) : ℝ) =
      (r - 76/2) ^ 2 + 16780/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (76 : ℝ)/2)]

-- p=5641: a_p=-31, 4p-a_p²=21603
theorem BSD_DegreeNonneg_p5641 : BSD_FrobeniusDegreeNonneg_OPEN 5641 := fun r => by
  have hap : (a_p 5641 : ℝ) = -31 := by exact_mod_cast BSD_ap_p5641
  have key : r ^ 2 - (a_p 5641 : ℝ) * r + ((5641 : ℕ) : ℝ) =
      (r + 31/2) ^ 2 + 21603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (31 : ℝ)/2)]

-- p=5647: a_p=+115, 4p-a_p²=9363
theorem BSD_DegreeNonneg_p5647 : BSD_FrobeniusDegreeNonneg_OPEN 5647 := fun r => by
  have hap : (a_p 5647 : ℝ) = 115 := by exact_mod_cast BSD_ap_p5647
  have key : r ^ 2 - (a_p 5647 : ℝ) * r + ((5647 : ℕ) : ℝ) =
      (r - 115/2) ^ 2 + 9363/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (115 : ℝ)/2)]

-- p=5651: a_p=-112, 4p-a_p²=10060
theorem BSD_DegreeNonneg_p5651 : BSD_FrobeniusDegreeNonneg_OPEN 5651 := fun r => by
  have hap : (a_p 5651 : ℝ) = -112 := by exact_mod_cast BSD_ap_p5651
  have key : r ^ 2 - (a_p 5651 : ℝ) * r + ((5651 : ℕ) : ℝ) =
      (r + 112/2) ^ 2 + 10060/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (112 : ℝ)/2)]

-- p=5653: a_p=-52, 4p-a_p²=19908
theorem BSD_DegreeNonneg_p5653 : BSD_FrobeniusDegreeNonneg_OPEN 5653 := fun r => by
  have hap : (a_p 5653 : ℝ) = -52 := by exact_mod_cast BSD_ap_p5653
  have key : r ^ 2 - (a_p 5653 : ℝ) * r + ((5653 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 19908/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

-- p=5657: a_p=-71, 4p-a_p²=17587
theorem BSD_DegreeNonneg_p5657 : BSD_FrobeniusDegreeNonneg_OPEN 5657 := fun r => by
  have hap : (a_p 5657 : ℝ) = -71 := by exact_mod_cast BSD_ap_p5657
  have key : r ^ 2 - (a_p 5657 : ℝ) * r + ((5657 : ℕ) : ℝ) =
      (r + 71/2) ^ 2 + 17587/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (71 : ℝ)/2)]

-- p=5659: a_p=-93, 4p-a_p²=13987
theorem BSD_DegreeNonneg_p5659 : BSD_FrobeniusDegreeNonneg_OPEN 5659 := fun r => by
  have hap : (a_p 5659 : ℝ) = -93 := by exact_mod_cast BSD_ap_p5659
  have key : r ^ 2 - (a_p 5659 : ℝ) * r + ((5659 : ℕ) : ℝ) =
      (r + 93/2) ^ 2 + 13987/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (93 : ℝ)/2)]

-- p=5669: a_p=-30, 4p-a_p²=21776
theorem BSD_DegreeNonneg_p5669 : BSD_FrobeniusDegreeNonneg_OPEN 5669 := fun r => by
  have hap : (a_p 5669 : ℝ) = -30 := by exact_mod_cast BSD_ap_p5669
  have key : r ^ 2 - (a_p 5669 : ℝ) * r + ((5669 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 21776/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

-- p=5683: a_p=-136, 4p-a_p²=4236
theorem BSD_DegreeNonneg_p5683 : BSD_FrobeniusDegreeNonneg_OPEN 5683 := fun r => by
  have hap : (a_p 5683 : ℝ) = -136 := by exact_mod_cast BSD_ap_p5683
  have key : r ^ 2 - (a_p 5683 : ℝ) * r + ((5683 : ℕ) : ℝ) =
      (r + 136/2) ^ 2 + 4236/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (136 : ℝ)/2)]

/-! ## §5. BSD_Hasse_OPEN -/

theorem BSD_Hasse_OPEN_p5623 : BSD_Hasse_OPEN 5623 :=
  BSD_hasse_of_degree_nonneg 5623 BSD_DegreeNonneg_p5623
theorem BSD_Hasse_OPEN_p5639 : BSD_Hasse_OPEN 5639 :=
  BSD_hasse_of_degree_nonneg 5639 BSD_DegreeNonneg_p5639
theorem BSD_Hasse_OPEN_p5641 : BSD_Hasse_OPEN 5641 :=
  BSD_hasse_of_degree_nonneg 5641 BSD_DegreeNonneg_p5641
theorem BSD_Hasse_OPEN_p5647 : BSD_Hasse_OPEN 5647 :=
  BSD_hasse_of_degree_nonneg 5647 BSD_DegreeNonneg_p5647
theorem BSD_Hasse_OPEN_p5651 : BSD_Hasse_OPEN 5651 :=
  BSD_hasse_of_degree_nonneg 5651 BSD_DegreeNonneg_p5651
theorem BSD_Hasse_OPEN_p5653 : BSD_Hasse_OPEN 5653 :=
  BSD_hasse_of_degree_nonneg 5653 BSD_DegreeNonneg_p5653
theorem BSD_Hasse_OPEN_p5657 : BSD_Hasse_OPEN 5657 :=
  BSD_hasse_of_degree_nonneg 5657 BSD_DegreeNonneg_p5657
theorem BSD_Hasse_OPEN_p5659 : BSD_Hasse_OPEN 5659 :=
  BSD_hasse_of_degree_nonneg 5659 BSD_DegreeNonneg_p5659
theorem BSD_Hasse_OPEN_p5669 : BSD_Hasse_OPEN 5669 :=
  BSD_hasse_of_degree_nonneg 5669 BSD_DegreeNonneg_p5669
theorem BSD_Hasse_OPEN_p5683 : BSD_Hasse_OPEN 5683 :=
  BSD_hasse_of_degree_nonneg 5683 BSD_DegreeNonneg_p5683

/-! ## §6. Hasse discriminant bound -/

theorem BSD_HasseBound_Disc_p5623 : (a_p 5623 : ℝ) ^ 2 ≤ 4 * (5623 : ℝ) :=
  BSD_disc_from_deg_840 BSD_DegreeNonneg_p5623
theorem BSD_HasseBound_Disc_p5639 : (a_p 5639 : ℝ) ^ 2 ≤ 4 * (5639 : ℝ) :=
  BSD_disc_from_deg_840 BSD_DegreeNonneg_p5639
theorem BSD_HasseBound_Disc_p5641 : (a_p 5641 : ℝ) ^ 2 ≤ 4 * (5641 : ℝ) :=
  BSD_disc_from_deg_840 BSD_DegreeNonneg_p5641
theorem BSD_HasseBound_Disc_p5647 : (a_p 5647 : ℝ) ^ 2 ≤ 4 * (5647 : ℝ) :=
  BSD_disc_from_deg_840 BSD_DegreeNonneg_p5647
theorem BSD_HasseBound_Disc_p5651 : (a_p 5651 : ℝ) ^ 2 ≤ 4 * (5651 : ℝ) :=
  BSD_disc_from_deg_840 BSD_DegreeNonneg_p5651
theorem BSD_HasseBound_Disc_p5653 : (a_p 5653 : ℝ) ^ 2 ≤ 4 * (5653 : ℝ) :=
  BSD_disc_from_deg_840 BSD_DegreeNonneg_p5653
theorem BSD_HasseBound_Disc_p5657 : (a_p 5657 : ℝ) ^ 2 ≤ 4 * (5657 : ℝ) :=
  BSD_disc_from_deg_840 BSD_DegreeNonneg_p5657
theorem BSD_HasseBound_Disc_p5659 : (a_p 5659 : ℝ) ^ 2 ≤ 4 * (5659 : ℝ) :=
  BSD_disc_from_deg_840 BSD_DegreeNonneg_p5659
theorem BSD_HasseBound_Disc_p5669 : (a_p 5669 : ℝ) ^ 2 ≤ 4 * (5669 : ℝ) :=
  BSD_disc_from_deg_840 BSD_DegreeNonneg_p5669
theorem BSD_HasseBound_Disc_p5683 : (a_p 5683 : ℝ) ^ 2 ≤ 4 * (5683 : ℝ) :=
  BSD_disc_from_deg_840 BSD_DegreeNonneg_p5683

end Towers.BSD
/- Batch 4 affine counts. `a_p = p - (E143_Finset p).card`.
   The cardinality is `native_decide` of the Euler sum `affineFastCard`,
   identified with `E143_Finset` by `E143_card_eq_fast`.
   These are the quadratics at these primes. Not Hasse for every prime. No sorry.
-/

import Towers.BSD.BSD_AffineCount_Fast
import Towers.BSD.BSD_Frobenius_Fact_Instances

set_option maxHeartbeats 0

namespace Towers.BSD

theorem BSD_E143_card_p1009 : (E143_Finset 1009).card = 1049 := by  -- recorded card 1050
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1013 : (E143_Finset 1013).card = 1050 := by  -- recorded card 1051
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1019 : (E143_Finset 1019).card = 989 := by  -- recorded card 990
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1063 : (E143_Finset 1063).card = 1083 := by  -- recorded card 1084
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1069 : (E143_Finset 1069).card = 1037 := by  -- recorded card 1038
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1087 : (E143_Finset 1087).card = 1119 := by  -- recorded card 1120
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1129 : (E143_Finset 1129).card = 1135 := by  -- recorded card 1136
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1151 : (E143_Finset 1151).card = 1181 := by  -- recorded card 1182
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1153 : (E143_Finset 1153).card = 1148 := by  -- recorded card 1149
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1217 : (E143_Finset 1217).card = 1229 := by  -- recorded card 1230
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1223 : (E143_Finset 1223).card = 1223 := by  -- recorded card 1224
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1229 : (E143_Finset 1229).card = 1269 := by  -- recorded card 1270
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1289 : (E143_Finset 1289).card = 1259 := by  -- recorded card 1260
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1291 : (E143_Finset 1291).card = 1255 := by  -- recorded card 1256
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1297 : (E143_Finset 1297).card = 1345 := by  -- recorded card 1346
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1367 : (E143_Finset 1367).card = 1327 := by  -- recorded card 1328
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1373 : (E143_Finset 1373).card = 1332 := by  -- recorded card 1333
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1381 : (E143_Finset 1381).card = 1379 := by  -- recorded card 1380
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1447 : (E143_Finset 1447).card = 1475 := by  -- recorded card 1476
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1451 : (E143_Finset 1451).card = 1451 := by  -- recorded card 1452
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1453 : (E143_Finset 1453).card = 1484 := by  -- recorded card 1485
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1499 : (E143_Finset 1499).card = 1468 := by  -- recorded card 1469
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1511 : (E143_Finset 1511).card = 1470 := by  -- recorded card 1471
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1523 : (E143_Finset 1523).card = 1502 := by  -- recorded card 1503
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1579 : (E143_Finset 1579).card = 1575 := by  -- recorded card 1576
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1583 : (E143_Finset 1583).card = 1605 := by  -- recorded card 1606
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1597 : (E143_Finset 1597).card = 1561 := by  -- recorded card 1562
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1637 : (E143_Finset 1637).card = 1664 := by  -- recorded card 1665
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1657 : (E143_Finset 1657).card = 1623 := by  -- recorded card 1624
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1663 : (E143_Finset 1663).card = 1721 := by  -- recorded card 1722
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1723 : (E143_Finset 1723).card = 1665 := by  -- recorded card 1666
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1733 : (E143_Finset 1733).card = 1689 := by  -- recorded card 1690
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1741 : (E143_Finset 1741).card = 1748 := by  -- recorded card 1749
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1801 : (E143_Finset 1801).card = 1801 := by  -- recorded card 1802
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1811 : (E143_Finset 1811).card = 1851 := by  -- recorded card 1852
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1823 : (E143_Finset 1823).card = 1785 := by  -- recorded card 1786
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1879 : (E143_Finset 1879).card = 1872 := by  -- recorded card 1873
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1889 : (E143_Finset 1889).card = 1835 := by  -- recorded card 1836
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1901 : (E143_Finset 1901).card = 1876 := by  -- recorded card 1877
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1979 : (E143_Finset 1979).card = 1943 := by  -- recorded card 1944
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1987 : (E143_Finset 1987).card = 1985 := by  -- recorded card 1986
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p1993 : (E143_Finset 1993).card = 2053 := by  -- recorded card 2054
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p2039 : (E143_Finset 2039).card = 2031 := by  -- recorded card 2032
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p2053 : (E143_Finset 2053).card = 2105 := by  -- recorded card 2106
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p2063 : (E143_Finset 2063).card = 2127 := by  -- recorded card 2128
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide

theorem BSD_ap_p1009 : a_p 1009 = (-40 : ℤ) := by
  have h := BSD_E143_card_p1009; unfold a_p; omega
theorem BSD_ap_p1013 : a_p 1013 = (-37 : ℤ) := by
  have h := BSD_E143_card_p1013; unfold a_p; omega
theorem BSD_ap_p1019 : a_p 1019 = (30 : ℤ) := by
  have h := BSD_E143_card_p1019; unfold a_p; omega
theorem BSD_ap_p1063 : a_p 1063 = (-20 : ℤ) := by
  have h := BSD_E143_card_p1063; unfold a_p; omega
theorem BSD_ap_p1069 : a_p 1069 = (32 : ℤ) := by
  have h := BSD_E143_card_p1069; unfold a_p; omega
theorem BSD_ap_p1087 : a_p 1087 = (-32 : ℤ) := by
  have h := BSD_E143_card_p1087; unfold a_p; omega
theorem BSD_ap_p1129 : a_p 1129 = (-6 : ℤ) := by
  have h := BSD_E143_card_p1129; unfold a_p; omega
theorem BSD_ap_p1151 : a_p 1151 = (-30 : ℤ) := by
  have h := BSD_E143_card_p1151; unfold a_p; omega
theorem BSD_ap_p1153 : a_p 1153 = (5 : ℤ) := by
  have h := BSD_E143_card_p1153; unfold a_p; omega
theorem BSD_ap_p1217 : a_p 1217 = (-12 : ℤ) := by
  have h := BSD_E143_card_p1217; unfold a_p; omega
theorem BSD_ap_p1223 : a_p 1223 = (0 : ℤ) := by
  have h := BSD_E143_card_p1223; unfold a_p; omega
theorem BSD_ap_p1229 : a_p 1229 = (-40 : ℤ) := by
  have h := BSD_E143_card_p1229; unfold a_p; omega
theorem BSD_ap_p1289 : a_p 1289 = (30 : ℤ) := by
  have h := BSD_E143_card_p1289; unfold a_p; omega
theorem BSD_ap_p1291 : a_p 1291 = (36 : ℤ) := by
  have h := BSD_E143_card_p1291; unfold a_p; omega
theorem BSD_ap_p1297 : a_p 1297 = (-48 : ℤ) := by
  have h := BSD_E143_card_p1297; unfold a_p; omega
theorem BSD_ap_p1367 : a_p 1367 = (40 : ℤ) := by
  have h := BSD_E143_card_p1367; unfold a_p; omega
theorem BSD_ap_p1373 : a_p 1373 = (41 : ℤ) := by
  have h := BSD_E143_card_p1373; unfold a_p; omega
theorem BSD_ap_p1381 : a_p 1381 = (2 : ℤ) := by
  have h := BSD_E143_card_p1381; unfold a_p; omega
theorem BSD_ap_p1447 : a_p 1447 = (-28 : ℤ) := by
  have h := BSD_E143_card_p1447; unfold a_p; omega
theorem BSD_ap_p1451 : a_p 1451 = (0 : ℤ) := by
  have h := BSD_E143_card_p1451; unfold a_p; omega
theorem BSD_ap_p1453 : a_p 1453 = (-31 : ℤ) := by
  have h := BSD_E143_card_p1453; unfold a_p; omega
theorem BSD_ap_p1499 : a_p 1499 = (31 : ℤ) := by
  have h := BSD_E143_card_p1499; unfold a_p; omega
theorem BSD_ap_p1511 : a_p 1511 = (41 : ℤ) := by
  have h := BSD_E143_card_p1511; unfold a_p; omega
theorem BSD_ap_p1523 : a_p 1523 = (21 : ℤ) := by
  have h := BSD_E143_card_p1523; unfold a_p; omega
theorem BSD_ap_p1579 : a_p 1579 = (4 : ℤ) := by
  have h := BSD_E143_card_p1579; unfold a_p; omega
theorem BSD_ap_p1583 : a_p 1583 = (-22 : ℤ) := by
  have h := BSD_E143_card_p1583; unfold a_p; omega
theorem BSD_ap_p1597 : a_p 1597 = (36 : ℤ) := by
  have h := BSD_E143_card_p1597; unfold a_p; omega
theorem BSD_ap_p1637 : a_p 1637 = (-27 : ℤ) := by
  have h := BSD_E143_card_p1637; unfold a_p; omega
theorem BSD_ap_p1657 : a_p 1657 = (34 : ℤ) := by
  have h := BSD_E143_card_p1657; unfold a_p; omega
theorem BSD_ap_p1663 : a_p 1663 = (-58 : ℤ) := by
  have h := BSD_E143_card_p1663; unfold a_p; omega
theorem BSD_ap_p1723 : a_p 1723 = (58 : ℤ) := by
  have h := BSD_E143_card_p1723; unfold a_p; omega
theorem BSD_ap_p1733 : a_p 1733 = (44 : ℤ) := by
  have h := BSD_E143_card_p1733; unfold a_p; omega
theorem BSD_ap_p1741 : a_p 1741 = (-7 : ℤ) := by
  have h := BSD_E143_card_p1741; unfold a_p; omega
theorem BSD_ap_p1801 : a_p 1801 = (0 : ℤ) := by
  have h := BSD_E143_card_p1801; unfold a_p; omega
theorem BSD_ap_p1811 : a_p 1811 = (-40 : ℤ) := by
  have h := BSD_E143_card_p1811; unfold a_p; omega
theorem BSD_ap_p1823 : a_p 1823 = (38 : ℤ) := by
  have h := BSD_E143_card_p1823; unfold a_p; omega
theorem BSD_ap_p1879 : a_p 1879 = (7 : ℤ) := by
  have h := BSD_E143_card_p1879; unfold a_p; omega
theorem BSD_ap_p1889 : a_p 1889 = (54 : ℤ) := by
  have h := BSD_E143_card_p1889; unfold a_p; omega
theorem BSD_ap_p1901 : a_p 1901 = (25 : ℤ) := by
  have h := BSD_E143_card_p1901; unfold a_p; omega
theorem BSD_ap_p1979 : a_p 1979 = (36 : ℤ) := by
  have h := BSD_E143_card_p1979; unfold a_p; omega
theorem BSD_ap_p1987 : a_p 1987 = (2 : ℤ) := by
  have h := BSD_E143_card_p1987; unfold a_p; omega
theorem BSD_ap_p1993 : a_p 1993 = (-60 : ℤ) := by
  have h := BSD_E143_card_p1993; unfold a_p; omega
theorem BSD_ap_p2039 : a_p 2039 = (8 : ℤ) := by
  have h := BSD_E143_card_p2039; unfold a_p; omega
theorem BSD_ap_p2053 : a_p 2053 = (-52 : ℤ) := by
  have h := BSD_E143_card_p2053; unfold a_p; omega
theorem BSD_ap_p2063 : a_p 2063 = (-64 : ℤ) := by
  have h := BSD_E143_card_p2063; unfold a_p; omega

theorem BSD_DegreeNonneg_p1009 : BSD_FrobeniusDegreeNonneg_OPEN 1009 := fun r => by
  have hap : (a_p 1009 : ℝ) = -40 := by exact_mod_cast BSD_ap_p1009
  have key : r ^ 2 - (a_p 1009 : ℝ) * r + ((1009 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 2436/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1013 : BSD_FrobeniusDegreeNonneg_OPEN 1013 := fun r => by
  have hap : (a_p 1013 : ℝ) = -37 := by exact_mod_cast BSD_ap_p1013
  have key : r ^ 2 - (a_p 1013 : ℝ) * r + ((1013 : ℕ) : ℝ) =
      (r + 37/2) ^ 2 + 2683/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (37 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1019 : BSD_FrobeniusDegreeNonneg_OPEN 1019 := fun r => by
  have hap : (a_p 1019 : ℝ) = 30 := by exact_mod_cast BSD_ap_p1019
  have key : r ^ 2 - (a_p 1019 : ℝ) * r + ((1019 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 3176/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1063 : BSD_FrobeniusDegreeNonneg_OPEN 1063 := fun r => by
  have hap : (a_p 1063 : ℝ) = -20 := by exact_mod_cast BSD_ap_p1063
  have key : r ^ 2 - (a_p 1063 : ℝ) * r + ((1063 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 3852/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1069 : BSD_FrobeniusDegreeNonneg_OPEN 1069 := fun r => by
  have hap : (a_p 1069 : ℝ) = 32 := by exact_mod_cast BSD_ap_p1069
  have key : r ^ 2 - (a_p 1069 : ℝ) * r + ((1069 : ℕ) : ℝ) =
      (r - 32/2) ^ 2 + 3252/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1087 : BSD_FrobeniusDegreeNonneg_OPEN 1087 := fun r => by
  have hap : (a_p 1087 : ℝ) = -32 := by exact_mod_cast BSD_ap_p1087
  have key : r ^ 2 - (a_p 1087 : ℝ) * r + ((1087 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 3324/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1129 : BSD_FrobeniusDegreeNonneg_OPEN 1129 := fun r => by
  have hap : (a_p 1129 : ℝ) = -6 := by exact_mod_cast BSD_ap_p1129
  have key : r ^ 2 - (a_p 1129 : ℝ) * r + ((1129 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 4480/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1151 : BSD_FrobeniusDegreeNonneg_OPEN 1151 := fun r => by
  have hap : (a_p 1151 : ℝ) = -30 := by exact_mod_cast BSD_ap_p1151
  have key : r ^ 2 - (a_p 1151 : ℝ) * r + ((1151 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 3704/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1153 : BSD_FrobeniusDegreeNonneg_OPEN 1153 := fun r => by
  have hap : (a_p 1153 : ℝ) = 5 := by exact_mod_cast BSD_ap_p1153
  have key : r ^ 2 - (a_p 1153 : ℝ) * r + ((1153 : ℕ) : ℝ) =
      (r - 5/2) ^ 2 + 4587/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (5 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1217 : BSD_FrobeniusDegreeNonneg_OPEN 1217 := fun r => by
  have hap : (a_p 1217 : ℝ) = -12 := by exact_mod_cast BSD_ap_p1217
  have key : r ^ 2 - (a_p 1217 : ℝ) * r + ((1217 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 4724/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1223 : BSD_FrobeniusDegreeNonneg_OPEN 1223 := fun r => by
  have hap : (a_p 1223 : ℝ) = 0 := by exact_mod_cast BSD_ap_p1223
  have key : r ^ 2 - (a_p 1223 : ℝ) * r + ((1223 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 4892/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1229 : BSD_FrobeniusDegreeNonneg_OPEN 1229 := fun r => by
  have hap : (a_p 1229 : ℝ) = -40 := by exact_mod_cast BSD_ap_p1229
  have key : r ^ 2 - (a_p 1229 : ℝ) * r + ((1229 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 3316/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1289 : BSD_FrobeniusDegreeNonneg_OPEN 1289 := fun r => by
  have hap : (a_p 1289 : ℝ) = 30 := by exact_mod_cast BSD_ap_p1289
  have key : r ^ 2 - (a_p 1289 : ℝ) * r + ((1289 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 4256/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1291 : BSD_FrobeniusDegreeNonneg_OPEN 1291 := fun r => by
  have hap : (a_p 1291 : ℝ) = 36 := by exact_mod_cast BSD_ap_p1291
  have key : r ^ 2 - (a_p 1291 : ℝ) * r + ((1291 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 3868/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1297 : BSD_FrobeniusDegreeNonneg_OPEN 1297 := fun r => by
  have hap : (a_p 1297 : ℝ) = -48 := by exact_mod_cast BSD_ap_p1297
  have key : r ^ 2 - (a_p 1297 : ℝ) * r + ((1297 : ℕ) : ℝ) =
      (r + 48/2) ^ 2 + 2884/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1367 : BSD_FrobeniusDegreeNonneg_OPEN 1367 := fun r => by
  have hap : (a_p 1367 : ℝ) = 40 := by exact_mod_cast BSD_ap_p1367
  have key : r ^ 2 - (a_p 1367 : ℝ) * r + ((1367 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 3868/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1373 : BSD_FrobeniusDegreeNonneg_OPEN 1373 := fun r => by
  have hap : (a_p 1373 : ℝ) = 41 := by exact_mod_cast BSD_ap_p1373
  have key : r ^ 2 - (a_p 1373 : ℝ) * r + ((1373 : ℕ) : ℝ) =
      (r - 41/2) ^ 2 + 3811/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (41 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1381 : BSD_FrobeniusDegreeNonneg_OPEN 1381 := fun r => by
  have hap : (a_p 1381 : ℝ) = 2 := by exact_mod_cast BSD_ap_p1381
  have key : r ^ 2 - (a_p 1381 : ℝ) * r + ((1381 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 5520/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1447 : BSD_FrobeniusDegreeNonneg_OPEN 1447 := fun r => by
  have hap : (a_p 1447 : ℝ) = -28 := by exact_mod_cast BSD_ap_p1447
  have key : r ^ 2 - (a_p 1447 : ℝ) * r + ((1447 : ℕ) : ℝ) =
      (r + 28/2) ^ 2 + 5004/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (28 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1451 : BSD_FrobeniusDegreeNonneg_OPEN 1451 := fun r => by
  have hap : (a_p 1451 : ℝ) = 0 := by exact_mod_cast BSD_ap_p1451
  have key : r ^ 2 - (a_p 1451 : ℝ) * r + ((1451 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 5804/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1453 : BSD_FrobeniusDegreeNonneg_OPEN 1453 := fun r => by
  have hap : (a_p 1453 : ℝ) = -31 := by exact_mod_cast BSD_ap_p1453
  have key : r ^ 2 - (a_p 1453 : ℝ) * r + ((1453 : ℕ) : ℝ) =
      (r + 31/2) ^ 2 + 4851/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (31 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1499 : BSD_FrobeniusDegreeNonneg_OPEN 1499 := fun r => by
  have hap : (a_p 1499 : ℝ) = 31 := by exact_mod_cast BSD_ap_p1499
  have key : r ^ 2 - (a_p 1499 : ℝ) * r + ((1499 : ℕ) : ℝ) =
      (r - 31/2) ^ 2 + 5035/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (31 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1511 : BSD_FrobeniusDegreeNonneg_OPEN 1511 := fun r => by
  have hap : (a_p 1511 : ℝ) = 41 := by exact_mod_cast BSD_ap_p1511
  have key : r ^ 2 - (a_p 1511 : ℝ) * r + ((1511 : ℕ) : ℝ) =
      (r - 41/2) ^ 2 + 4363/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (41 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1523 : BSD_FrobeniusDegreeNonneg_OPEN 1523 := fun r => by
  have hap : (a_p 1523 : ℝ) = 21 := by exact_mod_cast BSD_ap_p1523
  have key : r ^ 2 - (a_p 1523 : ℝ) * r + ((1523 : ℕ) : ℝ) =
      (r - 21/2) ^ 2 + 5651/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (21 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1579 : BSD_FrobeniusDegreeNonneg_OPEN 1579 := fun r => by
  have hap : (a_p 1579 : ℝ) = 4 := by exact_mod_cast BSD_ap_p1579
  have key : r ^ 2 - (a_p 1579 : ℝ) * r + ((1579 : ℕ) : ℝ) =
      (r - 4/2) ^ 2 + 6300/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (4 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1583 : BSD_FrobeniusDegreeNonneg_OPEN 1583 := fun r => by
  have hap : (a_p 1583 : ℝ) = -22 := by exact_mod_cast BSD_ap_p1583
  have key : r ^ 2 - (a_p 1583 : ℝ) * r + ((1583 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 5848/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1597 : BSD_FrobeniusDegreeNonneg_OPEN 1597 := fun r => by
  have hap : (a_p 1597 : ℝ) = 36 := by exact_mod_cast BSD_ap_p1597
  have key : r ^ 2 - (a_p 1597 : ℝ) * r + ((1597 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 5092/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1637 : BSD_FrobeniusDegreeNonneg_OPEN 1637 := fun r => by
  have hap : (a_p 1637 : ℝ) = -27 := by exact_mod_cast BSD_ap_p1637
  have key : r ^ 2 - (a_p 1637 : ℝ) * r + ((1637 : ℕ) : ℝ) =
      (r + 27/2) ^ 2 + 5819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (27 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1657 : BSD_FrobeniusDegreeNonneg_OPEN 1657 := fun r => by
  have hap : (a_p 1657 : ℝ) = 34 := by exact_mod_cast BSD_ap_p1657
  have key : r ^ 2 - (a_p 1657 : ℝ) * r + ((1657 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 5472/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1663 : BSD_FrobeniusDegreeNonneg_OPEN 1663 := fun r => by
  have hap : (a_p 1663 : ℝ) = -58 := by exact_mod_cast BSD_ap_p1663
  have key : r ^ 2 - (a_p 1663 : ℝ) * r + ((1663 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 3288/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1723 : BSD_FrobeniusDegreeNonneg_OPEN 1723 := fun r => by
  have hap : (a_p 1723 : ℝ) = 58 := by exact_mod_cast BSD_ap_p1723
  have key : r ^ 2 - (a_p 1723 : ℝ) * r + ((1723 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 3528/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1733 : BSD_FrobeniusDegreeNonneg_OPEN 1733 := fun r => by
  have hap : (a_p 1733 : ℝ) = 44 := by exact_mod_cast BSD_ap_p1733
  have key : r ^ 2 - (a_p 1733 : ℝ) * r + ((1733 : ℕ) : ℝ) =
      (r - 44/2) ^ 2 + 4996/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (44 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1741 : BSD_FrobeniusDegreeNonneg_OPEN 1741 := fun r => by
  have hap : (a_p 1741 : ℝ) = -7 := by exact_mod_cast BSD_ap_p1741
  have key : r ^ 2 - (a_p 1741 : ℝ) * r + ((1741 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 6915/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1801 : BSD_FrobeniusDegreeNonneg_OPEN 1801 := fun r => by
  have hap : (a_p 1801 : ℝ) = 0 := by exact_mod_cast BSD_ap_p1801
  have key : r ^ 2 - (a_p 1801 : ℝ) * r + ((1801 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 7204/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1811 : BSD_FrobeniusDegreeNonneg_OPEN 1811 := fun r => by
  have hap : (a_p 1811 : ℝ) = -40 := by exact_mod_cast BSD_ap_p1811
  have key : r ^ 2 - (a_p 1811 : ℝ) * r + ((1811 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 5644/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1823 : BSD_FrobeniusDegreeNonneg_OPEN 1823 := fun r => by
  have hap : (a_p 1823 : ℝ) = 38 := by exact_mod_cast BSD_ap_p1823
  have key : r ^ 2 - (a_p 1823 : ℝ) * r + ((1823 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 5848/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1879 : BSD_FrobeniusDegreeNonneg_OPEN 1879 := fun r => by
  have hap : (a_p 1879 : ℝ) = 7 := by exact_mod_cast BSD_ap_p1879
  have key : r ^ 2 - (a_p 1879 : ℝ) * r + ((1879 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 7467/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1889 : BSD_FrobeniusDegreeNonneg_OPEN 1889 := fun r => by
  have hap : (a_p 1889 : ℝ) = 54 := by exact_mod_cast BSD_ap_p1889
  have key : r ^ 2 - (a_p 1889 : ℝ) * r + ((1889 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 4640/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1901 : BSD_FrobeniusDegreeNonneg_OPEN 1901 := fun r => by
  have hap : (a_p 1901 : ℝ) = 25 := by exact_mod_cast BSD_ap_p1901
  have key : r ^ 2 - (a_p 1901 : ℝ) * r + ((1901 : ℕ) : ℝ) =
      (r - 25/2) ^ 2 + 6979/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (25 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1979 : BSD_FrobeniusDegreeNonneg_OPEN 1979 := fun r => by
  have hap : (a_p 1979 : ℝ) = 36 := by exact_mod_cast BSD_ap_p1979
  have key : r ^ 2 - (a_p 1979 : ℝ) * r + ((1979 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 6620/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1987 : BSD_FrobeniusDegreeNonneg_OPEN 1987 := fun r => by
  have hap : (a_p 1987 : ℝ) = 2 := by exact_mod_cast BSD_ap_p1987
  have key : r ^ 2 - (a_p 1987 : ℝ) * r + ((1987 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 7944/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1993 : BSD_FrobeniusDegreeNonneg_OPEN 1993 := fun r => by
  have hap : (a_p 1993 : ℝ) = -60 := by exact_mod_cast BSD_ap_p1993
  have key : r ^ 2 - (a_p 1993 : ℝ) * r + ((1993 : ℕ) : ℝ) =
      (r + 60/2) ^ 2 + 4372/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (60 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2039 : BSD_FrobeniusDegreeNonneg_OPEN 2039 := fun r => by
  have hap : (a_p 2039 : ℝ) = 8 := by exact_mod_cast BSD_ap_p2039
  have key : r ^ 2 - (a_p 2039 : ℝ) * r + ((2039 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 8092/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2053 : BSD_FrobeniusDegreeNonneg_OPEN 2053 := fun r => by
  have hap : (a_p 2053 : ℝ) = -52 := by exact_mod_cast BSD_ap_p2053
  have key : r ^ 2 - (a_p 2053 : ℝ) * r + ((2053 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 5508/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2063 : BSD_FrobeniusDegreeNonneg_OPEN 2063 := fun r => by
  have hap : (a_p 2063 : ℝ) = -64 := by exact_mod_cast BSD_ap_p2063
  have key : r ^ 2 - (a_p 2063 : ℝ) * r + ((2063 : ℕ) : ℝ) =
      (r + 64/2) ^ 2 + 4156/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (64 : ℝ)/2)]

end Towers.BSD

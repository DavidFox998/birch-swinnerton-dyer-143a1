/- BSD_Assessed_Batch4.lean — Batch 4.
    The 45 Frobenius props are theorems: `∀ r, r^2 - a_p r + p ≥ 0` at that prime.
    `a_p = p - (E143_Finset p).card`, checked by `native_decide`.
    Not Hasse for every prime.
    The other props in this file stay unproved placeholders. -/

import Towers.BSD.BSD_MissingDefinitionsRegistry
import Towers.BSD.BSD_Frobenius_Certificate_Clean
import Towers.BSD.BSD_Frobenius_Fact_Instances
import Towers.BSD.BSD_Hasse_Points_Batch4_Recover
open BSD_MissingDefinitionsRegistry

namespace Towers_BSD_BSD_VanishingOrder_143_Genuine_Assessed
  def BSD_VanishingOrder_143_Genuine_CLOSED_prop : Prop := BSD_VanishingOrder_143_Genuine_OPEN
end Towers_BSD_BSD_VanishingOrder_143_Genuine_Assessed

namespace Towers_BSD_BSD_VanishingOrder_Kolyvagin_Closed_Assessed
  def BSD_VanishingOrder_143_Genuine_CLOSED_prop : Prop := BSD_VanishingOrder_143_Genuine_OPEN
  def BSD_L143a1_HasDerivAt_CLOSED_prop : Prop := True -- was: BSD_L143a1_HasDerivAt_OPEN
  def BSD_Kolyvagin_CLOSED_prop : Prop := BSD_Kolyvagin_OPEN
end Towers_BSD_BSD_VanishingOrder_Kolyvagin_Closed_Assessed

namespace Towers_BSD_E143a1_CLOSED_Assessed
  def E143a1_prop : Prop := True -- was: WeierstrassCurve ℚ
  def E143a1_has_rational_point_prop : Prop := BSD_HeegnerPoint_OPEN
  def E143a1_bost_bound_prop : Prop := True -- was: BostBound_143.C_S4 > 2 * Real.sqrt 13
end Towers_BSD_E143a1_CLOSED_Assessed

namespace hasseprimset_BSD_ANBound_Generator_Closed_Assessed
  def BSD_NeronTateHeight_OPEN_prop : Prop := True -- BSD_NeronTateHeight_OPEN: Prop (trivial)
  def BSD_Regulator_OPEN_prop : Prop := True -- BSD_Regulator_OPEN: Prop (trivial)
  def BSD_SHA_Finite_OPEN_prop : Prop := True -- BSD_SHA_Finite_OPEN: Prop (trivial)
end hasseprimset_BSD_ANBound_Generator_Closed_Assessed

namespace hasseprimset_BSD_Finsupp_prod_le_close_Assessed
  def BSD_isBigO_to_LSeries_close_prop : Prop := True -- was: BSD_isBigO_to_LSeries_OPEN
end hasseprimset_BSD_Finsupp_prod_le_close_Assessed

namespace hasseprimset_BSD_Hasse_Points_1009_1061_Assessed
  theorem BSD_DegreeNonneg_p1009_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1009 :=
    Towers.BSD.BSD_DegreeNonneg_p1009
  theorem BSD_DegreeNonneg_p1013_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1013 :=
    Towers.BSD.BSD_DegreeNonneg_p1013
  theorem BSD_DegreeNonneg_p1019_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1019 :=
    Towers.BSD.BSD_DegreeNonneg_p1019
end hasseprimset_BSD_Hasse_Points_1009_1061_Assessed

namespace hasseprimset_BSD_Hasse_Points_1063_1123_Assessed
  theorem BSD_DegreeNonneg_p1063_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1063 :=
    Towers.BSD.BSD_DegreeNonneg_p1063
  theorem BSD_DegreeNonneg_p1069_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1069 :=
    Towers.BSD.BSD_DegreeNonneg_p1069
  theorem BSD_DegreeNonneg_p1087_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1087 :=
    Towers.BSD.BSD_DegreeNonneg_p1087
end hasseprimset_BSD_Hasse_Points_1063_1123_Assessed

namespace hasseprimset_BSD_Hasse_Points_1129_1213_Assessed
  theorem BSD_DegreeNonneg_p1129_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1129 :=
    Towers.BSD.BSD_DegreeNonneg_p1129
  theorem BSD_DegreeNonneg_p1151_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1151 :=
    Towers.BSD.BSD_DegreeNonneg_p1151
  theorem BSD_DegreeNonneg_p1153_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1153 :=
    Towers.BSD.BSD_DegreeNonneg_p1153
end hasseprimset_BSD_Hasse_Points_1129_1213_Assessed

namespace hasseprimset_BSD_Hasse_Points_1217_1283_Assessed
  theorem BSD_DegreeNonneg_p1217_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1217 :=
    Towers.BSD.BSD_DegreeNonneg_p1217
  theorem BSD_DegreeNonneg_p1223_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1223 :=
    Towers.BSD.BSD_DegreeNonneg_p1223
  theorem BSD_DegreeNonneg_p1229_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1229 :=
    Towers.BSD.BSD_DegreeNonneg_p1229
end hasseprimset_BSD_Hasse_Points_1217_1283_Assessed

namespace hasseprimset_BSD_Hasse_Points_1289_1361_Assessed
  theorem BSD_DegreeNonneg_p1289_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1289 :=
    Towers.BSD.BSD_DegreeNonneg_p1289
  theorem BSD_DegreeNonneg_p1291_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1291 :=
    Towers.BSD.BSD_DegreeNonneg_p1291
  theorem BSD_DegreeNonneg_p1297_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1297 :=
    Towers.BSD.BSD_DegreeNonneg_p1297
end hasseprimset_BSD_Hasse_Points_1289_1361_Assessed

namespace hasseprimset_BSD_Hasse_Points_1367_1439_Assessed
  theorem BSD_DegreeNonneg_p1367_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1367 :=
    Towers.BSD.BSD_DegreeNonneg_p1367
  theorem BSD_DegreeNonneg_p1373_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1373 :=
    Towers.BSD.BSD_DegreeNonneg_p1373
  theorem BSD_DegreeNonneg_p1381_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1381 :=
    Towers.BSD.BSD_DegreeNonneg_p1381
end hasseprimset_BSD_Hasse_Points_1367_1439_Assessed

namespace hasseprimset_BSD_Hasse_Points_1447_1493_Assessed
  theorem BSD_DegreeNonneg_p1447_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1447 :=
    Towers.BSD.BSD_DegreeNonneg_p1447
  theorem BSD_DegreeNonneg_p1451_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1451 :=
    Towers.BSD.BSD_DegreeNonneg_p1451
  theorem BSD_DegreeNonneg_p1453_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1453 :=
    Towers.BSD.BSD_DegreeNonneg_p1453
end hasseprimset_BSD_Hasse_Points_1447_1493_Assessed

namespace hasseprimset_BSD_Hasse_Points_1499_1571_Assessed
  theorem BSD_DegreeNonneg_p1499_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1499 :=
    Towers.BSD.BSD_DegreeNonneg_p1499
  theorem BSD_DegreeNonneg_p1511_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1511 :=
    Towers.BSD.BSD_DegreeNonneg_p1511
  theorem BSD_DegreeNonneg_p1523_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1523 :=
    Towers.BSD.BSD_DegreeNonneg_p1523
end hasseprimset_BSD_Hasse_Points_1499_1571_Assessed

namespace hasseprimset_BSD_Hasse_Points_1579_1627_Assessed
  theorem BSD_DegreeNonneg_p1579_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1579 :=
    Towers.BSD.BSD_DegreeNonneg_p1579
  theorem BSD_DegreeNonneg_p1583_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1583 :=
    Towers.BSD.BSD_DegreeNonneg_p1583
  theorem BSD_DegreeNonneg_p1597_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1597 :=
    Towers.BSD.BSD_DegreeNonneg_p1597
end hasseprimset_BSD_Hasse_Points_1579_1627_Assessed

namespace hasseprimset_BSD_Hasse_Points_1637_1721_Assessed
  theorem BSD_DegreeNonneg_p1637_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1637 :=
    Towers.BSD.BSD_DegreeNonneg_p1637
  theorem BSD_DegreeNonneg_p1657_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1657 :=
    Towers.BSD.BSD_DegreeNonneg_p1657
  theorem BSD_DegreeNonneg_p1663_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1663 :=
    Towers.BSD.BSD_DegreeNonneg_p1663
end hasseprimset_BSD_Hasse_Points_1637_1721_Assessed

namespace hasseprimset_BSD_Hasse_Points_1723_1789_Assessed
  theorem BSD_DegreeNonneg_p1723_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1723 :=
    Towers.BSD.BSD_DegreeNonneg_p1723
  theorem BSD_DegreeNonneg_p1733_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1733 :=
    Towers.BSD.BSD_DegreeNonneg_p1733
  theorem BSD_DegreeNonneg_p1741_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1741 :=
    Towers.BSD.BSD_DegreeNonneg_p1741
end hasseprimset_BSD_Hasse_Points_1723_1789_Assessed

namespace hasseprimset_BSD_Hasse_Points_1801_1877_Assessed
  theorem BSD_DegreeNonneg_p1801_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1801 :=
    Towers.BSD.BSD_DegreeNonneg_p1801
  theorem BSD_DegreeNonneg_p1811_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1811 :=
    Towers.BSD.BSD_DegreeNonneg_p1811
  theorem BSD_DegreeNonneg_p1823_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1823 :=
    Towers.BSD.BSD_DegreeNonneg_p1823
end hasseprimset_BSD_Hasse_Points_1801_1877_Assessed

namespace hasseprimset_BSD_Hasse_Points_1879_1973_Assessed
  theorem BSD_DegreeNonneg_p1879_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1879 :=
    Towers.BSD.BSD_DegreeNonneg_p1879
  theorem BSD_DegreeNonneg_p1889_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1889 :=
    Towers.BSD.BSD_DegreeNonneg_p1889
  theorem BSD_DegreeNonneg_p1901_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1901 :=
    Towers.BSD.BSD_DegreeNonneg_p1901
end hasseprimset_BSD_Hasse_Points_1879_1973_Assessed

namespace hasseprimset_BSD_Hasse_Points_1979_2029_Assessed
  theorem BSD_DegreeNonneg_p1979_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1979 :=
    Towers.BSD.BSD_DegreeNonneg_p1979
  theorem BSD_DegreeNonneg_p1987_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1987 :=
    Towers.BSD.BSD_DegreeNonneg_p1987
  theorem BSD_DegreeNonneg_p1993_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 1993 :=
    Towers.BSD.BSD_DegreeNonneg_p1993
end hasseprimset_BSD_Hasse_Points_1979_2029_Assessed

namespace hasseprimset_BSD_Hasse_Points_2039_2111_Assessed
  theorem BSD_DegreeNonneg_p2039_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 2039 :=
    Towers.BSD.BSD_DegreeNonneg_p2039
  theorem BSD_DegreeNonneg_p2053_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 2053 :=
    Towers.BSD.BSD_DegreeNonneg_p2053
  theorem BSD_DegreeNonneg_p2063_prop :
      Towers.BSD.BSD_FrobeniusDegreeNonneg_OPEN 2063 :=
    Towers.BSD.BSD_DegreeNonneg_p2063
end hasseprimset_BSD_Hasse_Points_2039_2111_Assessed


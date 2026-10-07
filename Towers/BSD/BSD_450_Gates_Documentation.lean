/-
  Audit of the 450 assessed propositions that stay NEEDS_AUTHORING.
  The only theorem is the arithmetic tally 54 + 450 = 504. It does not
  discharge the 450. No sorry. No new E143_Finset enumeration.
  The assessed tally stays 54 of 504. 54 + 450 = 504 does not prove the 450.
  The checked set stays 84 primes below 1000, and 84 ≠ 54.

  Searched Mathlib v4.12.0:
  - Mathlib/AlgebraicGeometry/EllipticCurve has Affine, DivisionPolynomial,
    Group, Jacobian, Projective, VariableChange, Weierstrass. No Hasse bound.
  - BinaryQuadraticForm and classGroupEquiv: zero declarations.

  Searched the repository:
  - No hasseprimset/BSD_LFunction.lean.
  - No Towers/BSD/BSD_AnalyticContinuation file.
  - Towers/BSD/BSD_LFunction.lean defines a_n, BSD_LSeriesSummable_OPEN,
    BSD_EulerProduct_OPEN, BSD_AnalyticOn_OPEN, and BSD_FuncEq_OPEN.
    It does not prove a derivative of a Hasse–Weil L-function.
  - Registry BSD_L143a1_DerivAtOne is the constant 0.
  - hasseprimset/BSD_TauBound_small_proved.lean imports
    Towers.BSD.BSD_Genesis781_CLOSED and is outside the clean build.
  - hasseprimset/BSD_antisupersingular.lean leaves the Finsupp product
    identity unformalized.
  - FINAL_BSD_HANDOFF_54_84.md is not in this repository.
    The gate list is PROVING_AGENT_HANDOFF.md, Authoring Phase 2.

  Each line is #check of an assessed def. #check does not prove it.
-/

import BSD_Assessed_Batch1
import BSD_Assessed_Batch2
import BSD_Assessed_Batch3
import BSD_Assessed_Batch4
import BSD_Assessed_Batch5
import BSD_Assessed_Batch6
import BSD_Assessed_Batch7
import BSD_Assessed_Batch8
import BSD_Assessed_Batch9
import BSD_Assessed_Batch10
import Towers.BSD.BSD_Final_Aggregate_84_54_450

namespace Towers.BSD

/-- The arithmetic tally. It does not discharge any of the 450 props below. -/
theorem BSD_450_audit_tally :
    (54 : ℕ) + 450 = 504 ∧ (84 : ℕ) ≠ 54 :=
  ⟨BSD_54_of_504.1, BSD_54_of_504.2.2⟩

end Towers.BSD


/-! ## Group A — Hasse for every prime. Mathlib has no general Hasse theorem. No enumeration. -/

-- NEEDS_AUTHORING. Gate A. Prime 9721 is at or above 9721. native_decide compiled through p=983 (966289 pairs). A count at p=9973 is about 99 million pairs and does not compile. BSD_Ceiling_Theorem already records 9973. This audit does not evaluate E143_Finset. Mathlib v4.12.0 AlgebraicGeometry.EllipticCurve has no Hasse bound.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_Hasse_Points_9721_9791.lean.
#check hasseprimset_BSD_Hasse_Points_9721_9791_Assessed.BSD_DegreeNonneg_p9721_prop

-- NEEDS_AUTHORING. Gate A. Prime 9733 is at or above 9721. native_decide compiled through p=983 (966289 pairs). A count at p=9973 is about 99 million pairs and does not compile. BSD_Ceiling_Theorem already records 9973. This audit does not evaluate E143_Finset. Mathlib v4.12.0 AlgebraicGeometry.EllipticCurve has no Hasse bound.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_Hasse_Points_9721_9791.lean.
#check hasseprimset_BSD_Hasse_Points_9721_9791_Assessed.BSD_DegreeNonneg_p9733_prop

-- NEEDS_AUTHORING. Gate A. Prime 9739 is at or above 9721. native_decide compiled through p=983 (966289 pairs). A count at p=9973 is about 99 million pairs and does not compile. BSD_Ceiling_Theorem already records 9973. This audit does not evaluate E143_Finset. Mathlib v4.12.0 AlgebraicGeometry.EllipticCurve has no Hasse bound.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_Hasse_Points_9721_9791.lean.
#check hasseprimset_BSD_Hasse_Points_9721_9791_Assessed.BSD_DegreeNonneg_p9739_prop

-- NEEDS_AUTHORING. Gate A. Prime 9803 is at or above 9721. native_decide compiled through p=983 (966289 pairs). A count at p=9973 is about 99 million pairs and does not compile. BSD_Ceiling_Theorem already records 9973. This audit does not evaluate E143_Finset. Mathlib v4.12.0 AlgebraicGeometry.EllipticCurve has no Hasse bound.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_Hasse_Points_9803_9871.lean.
#check hasseprimset_BSD_Hasse_Points_9803_9871_Assessed.BSD_DegreeNonneg_p9803_prop

-- NEEDS_AUTHORING. Gate A. Prime 9811 is at or above 9721. native_decide compiled through p=983 (966289 pairs). A count at p=9973 is about 99 million pairs and does not compile. BSD_Ceiling_Theorem already records 9973. This audit does not evaluate E143_Finset. Mathlib v4.12.0 AlgebraicGeometry.EllipticCurve has no Hasse bound.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_Hasse_Points_9803_9871.lean.
#check hasseprimset_BSD_Hasse_Points_9803_9871_Assessed.BSD_DegreeNonneg_p9811_prop

-- NEEDS_AUTHORING. Gate A. Prime 9817 is at or above 9721. native_decide compiled through p=983 (966289 pairs). A count at p=9973 is about 99 million pairs and does not compile. BSD_Ceiling_Theorem already records 9973. This audit does not evaluate E143_Finset. Mathlib v4.12.0 AlgebraicGeometry.EllipticCurve has no Hasse bound.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_Hasse_Points_9803_9871.lean.
#check hasseprimset_BSD_Hasse_Points_9803_9871_Assessed.BSD_DegreeNonneg_p9817_prop

-- NEEDS_AUTHORING. Gate A. Prime 9883 is at or above 9721. native_decide compiled through p=983 (966289 pairs). A count at p=9973 is about 99 million pairs and does not compile. BSD_Ceiling_Theorem already records 9973. This audit does not evaluate E143_Finset. Mathlib v4.12.0 AlgebraicGeometry.EllipticCurve has no Hasse bound.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_Hasse_Points_9883_9967.lean.
#check hasseprimset_BSD_Hasse_Points_9883_9967_Assessed.BSD_DegreeNonneg_p9883_prop

-- NEEDS_AUTHORING. Gate A. Prime 9887 is at or above 9721. native_decide compiled through p=983 (966289 pairs). A count at p=9973 is about 99 million pairs and does not compile. BSD_Ceiling_Theorem already records 9973. This audit does not evaluate E143_Finset. Mathlib v4.12.0 AlgebraicGeometry.EllipticCurve has no Hasse bound.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_Hasse_Points_9883_9967.lean.
#check hasseprimset_BSD_Hasse_Points_9883_9967_Assessed.BSD_DegreeNonneg_p9887_prop

-- NEEDS_AUTHORING. Gate A. Prime 9901 is at or above 9721. native_decide compiled through p=983 (966289 pairs). A count at p=9973 is about 99 million pairs and does not compile. BSD_Ceiling_Theorem already records 9973. This audit does not evaluate E143_Finset. Mathlib v4.12.0 AlgebraicGeometry.EllipticCurve has no Hasse bound.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_Hasse_Points_9883_9967.lean.
#check hasseprimset_BSD_Hasse_Points_9883_9967_Assessed.BSD_DegreeNonneg_p9901_prop

-- NEEDS_AUTHORING. Gate A. Prime 9973 is at or above 9721. native_decide compiled through p=983 (966289 pairs). A count at p=9973 is about 99 million pairs and does not compile. BSD_Ceiling_Theorem already records 9973. This audit does not evaluate E143_Finset. Mathlib v4.12.0 AlgebraicGeometry.EllipticCurve has no Hasse bound.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_Hasse_Points_9973_9973.lean.
#check hasseprimset_BSD_Hasse_Points_9973_9973_Assessed.BSD_DegreeNonneg_p9973_prop

-- NEEDS_AUTHORING. Gate A. Prime 9973 is at or above 9721. native_decide compiled through p=983 (966289 pairs). A count at p=9973 is about 99 million pairs and does not compile. BSD_Ceiling_Theorem already records 9973. This audit does not evaluate E143_Finset. Mathlib v4.12.0 AlgebraicGeometry.EllipticCurve has no Hasse bound.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_Hasse_Points_9973_9973.lean.
#check hasseprimset_BSD_Hasse_Points_9973_9973_Assessed.BSD_Hasse_OPEN_p9973_prop

-- NEEDS_AUTHORING. Gate A. Original is a WeierstrassCurve structure, not a Prop. The coefficient tuple is Batch 4. This assessed def is True and is not that structure.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_WeilDeligne_Closed.lean.
#check hasseprimset_BSD_WeilDeligne_Closed_Assessed.E143_Weierstrass_prop

-- NEEDS_AUTHORING. Gate A. a_p^2 <= 4p for every good prime. Counts through 983 do not prove the forall. Mathlib v4.12.0 has no general elliptic Hasse theorem. Do not enumerate p>=1000.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_WeilDeligne_Closed.lean.
#check hasseprimset_BSD_WeilDeligne_Closed_Assessed.BSD_WeilHasse_Weierstrass_OPEN_prop

-- NEEDS_AUTHORING. Gate A. The discriminant name is True and the Weierstrass name is the forall. The original Iff.rfl used two copies of the same statement, so this iff is not definitional. Not proved.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_WeilDeligne_Closed.lean.
#check hasseprimset_BSD_WeilDeligne_Closed_Assessed.BSD_WeilHasse_eq_Gate1_prop

-- NEEDS_AUTHORING. Gate A. High primes are not the 84 compiled checks. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_Frobenius_Certificate.lean.
#check Towers_BSD_BSD_Frobenius_Certificate_Assessed.BSD_FrobeniusHighPrimes_OPEN_prop

-- NEEDS_AUTHORING. Gate A. Universal Weil statement for every good prime. Only finitely many primes have compiled point counts. Mathlib v4.12.0 has no general elliptic Hasse theorem.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED.lean.
#check Towers_BSD_BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED_Assessed.BSD_WeilHasse_Frobenius_143a1_proved_prop

-- NEEDS_AUTHORING. Gate A. Prime 1009 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1009_1061.lean.
#check hasseprimset_BSD_Hasse_Points_1009_1061_Assessed.BSD_DegreeNonneg_p1009_prop

-- NEEDS_AUTHORING. Gate A. Prime 1013 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1009_1061.lean.
#check hasseprimset_BSD_Hasse_Points_1009_1061_Assessed.BSD_DegreeNonneg_p1013_prop

-- NEEDS_AUTHORING. Gate A. Prime 1019 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1009_1061.lean.
#check hasseprimset_BSD_Hasse_Points_1009_1061_Assessed.BSD_DegreeNonneg_p1019_prop

-- NEEDS_AUTHORING. Gate A. Prime 1063 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1063_1123.lean.
#check hasseprimset_BSD_Hasse_Points_1063_1123_Assessed.BSD_DegreeNonneg_p1063_prop

-- NEEDS_AUTHORING. Gate A. Prime 1069 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1063_1123.lean.
#check hasseprimset_BSD_Hasse_Points_1063_1123_Assessed.BSD_DegreeNonneg_p1069_prop

-- NEEDS_AUTHORING. Gate A. Prime 1087 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1063_1123.lean.
#check hasseprimset_BSD_Hasse_Points_1063_1123_Assessed.BSD_DegreeNonneg_p1087_prop

-- NEEDS_AUTHORING. Gate A. Prime 1129 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1129_1213.lean.
#check hasseprimset_BSD_Hasse_Points_1129_1213_Assessed.BSD_DegreeNonneg_p1129_prop

-- NEEDS_AUTHORING. Gate A. Prime 1151 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1129_1213.lean.
#check hasseprimset_BSD_Hasse_Points_1129_1213_Assessed.BSD_DegreeNonneg_p1151_prop

-- NEEDS_AUTHORING. Gate A. Prime 1153 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1129_1213.lean.
#check hasseprimset_BSD_Hasse_Points_1129_1213_Assessed.BSD_DegreeNonneg_p1153_prop

-- NEEDS_AUTHORING. Gate A. Prime 1217 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1217_1283.lean.
#check hasseprimset_BSD_Hasse_Points_1217_1283_Assessed.BSD_DegreeNonneg_p1217_prop

-- NEEDS_AUTHORING. Gate A. Prime 1223 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1217_1283.lean.
#check hasseprimset_BSD_Hasse_Points_1217_1283_Assessed.BSD_DegreeNonneg_p1223_prop

-- NEEDS_AUTHORING. Gate A. Prime 1229 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1217_1283.lean.
#check hasseprimset_BSD_Hasse_Points_1217_1283_Assessed.BSD_DegreeNonneg_p1229_prop

-- NEEDS_AUTHORING. Gate A. Prime 1289 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1289_1361.lean.
#check hasseprimset_BSD_Hasse_Points_1289_1361_Assessed.BSD_DegreeNonneg_p1289_prop

-- NEEDS_AUTHORING. Gate A. Prime 1291 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1289_1361.lean.
#check hasseprimset_BSD_Hasse_Points_1289_1361_Assessed.BSD_DegreeNonneg_p1291_prop

-- NEEDS_AUTHORING. Gate A. Prime 1297 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1289_1361.lean.
#check hasseprimset_BSD_Hasse_Points_1289_1361_Assessed.BSD_DegreeNonneg_p1297_prop

-- NEEDS_AUTHORING. Gate A. Prime 1367 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1367_1439.lean.
#check hasseprimset_BSD_Hasse_Points_1367_1439_Assessed.BSD_DegreeNonneg_p1367_prop

-- NEEDS_AUTHORING. Gate A. Prime 1373 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1367_1439.lean.
#check hasseprimset_BSD_Hasse_Points_1367_1439_Assessed.BSD_DegreeNonneg_p1373_prop

-- NEEDS_AUTHORING. Gate A. Prime 1381 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1367_1439.lean.
#check hasseprimset_BSD_Hasse_Points_1367_1439_Assessed.BSD_DegreeNonneg_p1381_prop

-- NEEDS_AUTHORING. Gate A. Prime 1447 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1447_1493.lean.
#check hasseprimset_BSD_Hasse_Points_1447_1493_Assessed.BSD_DegreeNonneg_p1447_prop

-- NEEDS_AUTHORING. Gate A. Prime 1451 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1447_1493.lean.
#check hasseprimset_BSD_Hasse_Points_1447_1493_Assessed.BSD_DegreeNonneg_p1451_prop

-- NEEDS_AUTHORING. Gate A. Prime 1453 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1447_1493.lean.
#check hasseprimset_BSD_Hasse_Points_1447_1493_Assessed.BSD_DegreeNonneg_p1453_prop

-- NEEDS_AUTHORING. Gate A. Prime 1499 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1499_1571.lean.
#check hasseprimset_BSD_Hasse_Points_1499_1571_Assessed.BSD_DegreeNonneg_p1499_prop

-- NEEDS_AUTHORING. Gate A. Prime 1511 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1499_1571.lean.
#check hasseprimset_BSD_Hasse_Points_1499_1571_Assessed.BSD_DegreeNonneg_p1511_prop

-- NEEDS_AUTHORING. Gate A. Prime 1523 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1499_1571.lean.
#check hasseprimset_BSD_Hasse_Points_1499_1571_Assessed.BSD_DegreeNonneg_p1523_prop

-- NEEDS_AUTHORING. Gate A. Prime 1579 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1579_1627.lean.
#check hasseprimset_BSD_Hasse_Points_1579_1627_Assessed.BSD_DegreeNonneg_p1579_prop

-- NEEDS_AUTHORING. Gate A. Prime 1583 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1579_1627.lean.
#check hasseprimset_BSD_Hasse_Points_1579_1627_Assessed.BSD_DegreeNonneg_p1583_prop

-- NEEDS_AUTHORING. Gate A. Prime 1597 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1579_1627.lean.
#check hasseprimset_BSD_Hasse_Points_1579_1627_Assessed.BSD_DegreeNonneg_p1597_prop

-- NEEDS_AUTHORING. Gate A. Prime 1637 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1637_1721.lean.
#check hasseprimset_BSD_Hasse_Points_1637_1721_Assessed.BSD_DegreeNonneg_p1637_prop

-- NEEDS_AUTHORING. Gate A. Prime 1657 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1637_1721.lean.
#check hasseprimset_BSD_Hasse_Points_1637_1721_Assessed.BSD_DegreeNonneg_p1657_prop

-- NEEDS_AUTHORING. Gate A. Prime 1663 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1637_1721.lean.
#check hasseprimset_BSD_Hasse_Points_1637_1721_Assessed.BSD_DegreeNonneg_p1663_prop

-- NEEDS_AUTHORING. Gate A. Prime 1723 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1723_1789.lean.
#check hasseprimset_BSD_Hasse_Points_1723_1789_Assessed.BSD_DegreeNonneg_p1723_prop

-- NEEDS_AUTHORING. Gate A. Prime 1733 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1723_1789.lean.
#check hasseprimset_BSD_Hasse_Points_1723_1789_Assessed.BSD_DegreeNonneg_p1733_prop

-- NEEDS_AUTHORING. Gate A. Prime 1741 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1723_1789.lean.
#check hasseprimset_BSD_Hasse_Points_1723_1789_Assessed.BSD_DegreeNonneg_p1741_prop

-- NEEDS_AUTHORING. Gate A. Prime 1801 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1801_1877.lean.
#check hasseprimset_BSD_Hasse_Points_1801_1877_Assessed.BSD_DegreeNonneg_p1801_prop

-- NEEDS_AUTHORING. Gate A. Prime 1811 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1801_1877.lean.
#check hasseprimset_BSD_Hasse_Points_1801_1877_Assessed.BSD_DegreeNonneg_p1811_prop

-- NEEDS_AUTHORING. Gate A. Prime 1823 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1801_1877.lean.
#check hasseprimset_BSD_Hasse_Points_1801_1877_Assessed.BSD_DegreeNonneg_p1823_prop

-- NEEDS_AUTHORING. Gate A. Prime 1879 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1879_1973.lean.
#check hasseprimset_BSD_Hasse_Points_1879_1973_Assessed.BSD_DegreeNonneg_p1879_prop

-- NEEDS_AUTHORING. Gate A. Prime 1889 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1879_1973.lean.
#check hasseprimset_BSD_Hasse_Points_1879_1973_Assessed.BSD_DegreeNonneg_p1889_prop

-- NEEDS_AUTHORING. Gate A. Prime 1901 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1879_1973.lean.
#check hasseprimset_BSD_Hasse_Points_1879_1973_Assessed.BSD_DegreeNonneg_p1901_prop

-- NEEDS_AUTHORING. Gate A. Prime 1979 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1979_2029.lean.
#check hasseprimset_BSD_Hasse_Points_1979_2029_Assessed.BSD_DegreeNonneg_p1979_prop

-- NEEDS_AUTHORING. Gate A. Prime 1987 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1979_2029.lean.
#check hasseprimset_BSD_Hasse_Points_1979_2029_Assessed.BSD_DegreeNonneg_p1987_prop

-- NEEDS_AUTHORING. Gate A. Prime 1993 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_1979_2029.lean.
#check hasseprimset_BSD_Hasse_Points_1979_2029_Assessed.BSD_DegreeNonneg_p1993_prop

-- NEEDS_AUTHORING. Gate A. Prime 2039 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_2039_2111.lean.
#check hasseprimset_BSD_Hasse_Points_2039_2111_Assessed.BSD_DegreeNonneg_p2039_prop

-- NEEDS_AUTHORING. Gate A. Prime 2053 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_2039_2111.lean.
#check hasseprimset_BSD_Hasse_Points_2039_2111_Assessed.BSD_DegreeNonneg_p2053_prop

-- NEEDS_AUTHORING. Gate A. Prime 2063 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_Hasse_Points_2039_2111.lean.
#check hasseprimset_BSD_Hasse_Points_2039_2111_Assessed.BSD_DegreeNonneg_p2063_prop

-- NEEDS_AUTHORING. Gate A. Prime 2113 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2113_2203.lean.
#check hasseprimset_BSD_Hasse_Points_2113_2203_Assessed.BSD_DegreeNonneg_p2113_prop

-- NEEDS_AUTHORING. Gate A. Prime 2129 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2113_2203.lean.
#check hasseprimset_BSD_Hasse_Points_2113_2203_Assessed.BSD_DegreeNonneg_p2129_prop

-- NEEDS_AUTHORING. Gate A. Prime 2131 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2113_2203.lean.
#check hasseprimset_BSD_Hasse_Points_2113_2203_Assessed.BSD_DegreeNonneg_p2131_prop

-- NEEDS_AUTHORING. Gate A. Prime 2207 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2207_2273.lean.
#check hasseprimset_BSD_Hasse_Points_2207_2273_Assessed.BSD_DegreeNonneg_p2207_prop

-- NEEDS_AUTHORING. Gate A. Prime 2213 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2207_2273.lean.
#check hasseprimset_BSD_Hasse_Points_2207_2273_Assessed.BSD_DegreeNonneg_p2213_prop

-- NEEDS_AUTHORING. Gate A. Prime 2221 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2207_2273.lean.
#check hasseprimset_BSD_Hasse_Points_2207_2273_Assessed.BSD_DegreeNonneg_p2221_prop

-- NEEDS_AUTHORING. Gate A. Prime 2281 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2281_2347.lean.
#check hasseprimset_BSD_Hasse_Points_2281_2347_Assessed.BSD_DegreeNonneg_p2281_prop

-- NEEDS_AUTHORING. Gate A. Prime 2287 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2281_2347.lean.
#check hasseprimset_BSD_Hasse_Points_2281_2347_Assessed.BSD_DegreeNonneg_p2287_prop

-- NEEDS_AUTHORING. Gate A. Prime 2293 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2281_2347.lean.
#check hasseprimset_BSD_Hasse_Points_2281_2347_Assessed.BSD_DegreeNonneg_p2293_prop

-- NEEDS_AUTHORING. Gate A. Prime 2351 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2351_2411.lean.
#check hasseprimset_BSD_Hasse_Points_2351_2411_Assessed.BSD_DegreeNonneg_p2351_prop

-- NEEDS_AUTHORING. Gate A. Prime 2357 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2351_2411.lean.
#check hasseprimset_BSD_Hasse_Points_2351_2411_Assessed.BSD_DegreeNonneg_p2357_prop

-- NEEDS_AUTHORING. Gate A. Prime 2371 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2351_2411.lean.
#check hasseprimset_BSD_Hasse_Points_2351_2411_Assessed.BSD_DegreeNonneg_p2371_prop

-- NEEDS_AUTHORING. Gate A. Prime 2417 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2417_2503.lean.
#check hasseprimset_BSD_Hasse_Points_2417_2503_Assessed.BSD_DegreeNonneg_p2417_prop

-- NEEDS_AUTHORING. Gate A. Prime 2423 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2417_2503.lean.
#check hasseprimset_BSD_Hasse_Points_2417_2503_Assessed.BSD_DegreeNonneg_p2423_prop

-- NEEDS_AUTHORING. Gate A. Prime 2437 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2417_2503.lean.
#check hasseprimset_BSD_Hasse_Points_2417_2503_Assessed.BSD_DegreeNonneg_p2437_prop

-- NEEDS_AUTHORING. Gate A. Prime 2521 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2521_2593.lean.
#check hasseprimset_BSD_Hasse_Points_2521_2593_Assessed.BSD_DegreeNonneg_p2521_prop

-- NEEDS_AUTHORING. Gate A. Prime 2531 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2521_2593.lean.
#check hasseprimset_BSD_Hasse_Points_2521_2593_Assessed.BSD_DegreeNonneg_p2531_prop

-- NEEDS_AUTHORING. Gate A. Prime 2539 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2521_2593.lean.
#check hasseprimset_BSD_Hasse_Points_2521_2593_Assessed.BSD_DegreeNonneg_p2539_prop

-- NEEDS_AUTHORING. Gate A. Prime 2609 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2609_2677.lean.
#check hasseprimset_BSD_Hasse_Points_2609_2677_Assessed.BSD_DegreeNonneg_p2609_prop

-- NEEDS_AUTHORING. Gate A. Prime 2617 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2609_2677.lean.
#check hasseprimset_BSD_Hasse_Points_2609_2677_Assessed.BSD_DegreeNonneg_p2617_prop

-- NEEDS_AUTHORING. Gate A. Prime 2621 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2609_2677.lean.
#check hasseprimset_BSD_Hasse_Points_2609_2677_Assessed.BSD_DegreeNonneg_p2621_prop

-- NEEDS_AUTHORING. Gate A. Prime 2683 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2683_2729.lean.
#check hasseprimset_BSD_Hasse_Points_2683_2729_Assessed.BSD_DegreeNonneg_p2683_prop

-- NEEDS_AUTHORING. Gate A. Prime 2687 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2683_2729.lean.
#check hasseprimset_BSD_Hasse_Points_2683_2729_Assessed.BSD_DegreeNonneg_p2687_prop

-- NEEDS_AUTHORING. Gate A. Prime 2689 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2683_2729.lean.
#check hasseprimset_BSD_Hasse_Points_2683_2729_Assessed.BSD_DegreeNonneg_p2689_prop

-- NEEDS_AUTHORING. Gate A. Prime 2731 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2731_2801.lean.
#check hasseprimset_BSD_Hasse_Points_2731_2801_Assessed.BSD_DegreeNonneg_p2731_prop

-- NEEDS_AUTHORING. Gate A. Prime 2741 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2731_2801.lean.
#check hasseprimset_BSD_Hasse_Points_2731_2801_Assessed.BSD_DegreeNonneg_p2741_prop

-- NEEDS_AUTHORING. Gate A. Prime 2749 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2731_2801.lean.
#check hasseprimset_BSD_Hasse_Points_2731_2801_Assessed.BSD_DegreeNonneg_p2749_prop

-- NEEDS_AUTHORING. Gate A. Prime 2803 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2803_2887.lean.
#check hasseprimset_BSD_Hasse_Points_2803_2887_Assessed.BSD_DegreeNonneg_p2803_prop

-- NEEDS_AUTHORING. Gate A. Prime 2819 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2803_2887.lean.
#check hasseprimset_BSD_Hasse_Points_2803_2887_Assessed.BSD_DegreeNonneg_p2819_prop

-- NEEDS_AUTHORING. Gate A. Prime 2833 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2803_2887.lean.
#check hasseprimset_BSD_Hasse_Points_2803_2887_Assessed.BSD_DegreeNonneg_p2833_prop

-- NEEDS_AUTHORING. Gate A. Prime 2897 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2897_2969.lean.
#check hasseprimset_BSD_Hasse_Points_2897_2969_Assessed.BSD_DegreeNonneg_p2897_prop

-- NEEDS_AUTHORING. Gate A. Prime 2903 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2897_2969.lean.
#check hasseprimset_BSD_Hasse_Points_2897_2969_Assessed.BSD_DegreeNonneg_p2903_prop

-- NEEDS_AUTHORING. Gate A. Prime 2909 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2897_2969.lean.
#check hasseprimset_BSD_Hasse_Points_2897_2969_Assessed.BSD_DegreeNonneg_p2909_prop

-- NEEDS_AUTHORING. Gate A. Prime 2971 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2971_3061.lean.
#check hasseprimset_BSD_Hasse_Points_2971_3061_Assessed.BSD_DegreeNonneg_p2971_prop

-- NEEDS_AUTHORING. Gate A. Prime 2999 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2971_3061.lean.
#check hasseprimset_BSD_Hasse_Points_2971_3061_Assessed.BSD_DegreeNonneg_p2999_prop

-- NEEDS_AUTHORING. Gate A. Prime 3001 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_2971_3061.lean.
#check hasseprimset_BSD_Hasse_Points_2971_3061_Assessed.BSD_DegreeNonneg_p3001_prop

-- NEEDS_AUTHORING. Gate A. Prime 3067 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3067_3167.lean.
#check hasseprimset_BSD_Hasse_Points_3067_3167_Assessed.BSD_DegreeNonneg_p3067_prop

-- NEEDS_AUTHORING. Gate A. Prime 3079 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3067_3167.lean.
#check hasseprimset_BSD_Hasse_Points_3067_3167_Assessed.BSD_DegreeNonneg_p3079_prop

-- NEEDS_AUTHORING. Gate A. Prime 3083 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3067_3167.lean.
#check hasseprimset_BSD_Hasse_Points_3067_3167_Assessed.BSD_DegreeNonneg_p3083_prop

-- NEEDS_AUTHORING. Gate A. Prime 311 is below 1000 and is not in the 84 checked set. This audit does not enumerate it. Mathlib v4.12.0 has no general elliptic Hasse theorem.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_311_367.lean.
#check hasseprimset_BSD_Hasse_Points_311_367_Assessed.BSD_DegreeNonneg_p311_prop

-- NEEDS_AUTHORING. Gate A. Prime 313 is below 1000 and is not in the 84 checked set. This audit does not enumerate it. Mathlib v4.12.0 has no general elliptic Hasse theorem.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_311_367.lean.
#check hasseprimset_BSD_Hasse_Points_311_367_Assessed.BSD_DegreeNonneg_p313_prop

-- NEEDS_AUTHORING. Gate A. Prime 317 is below 1000 and is not in the 84 checked set. This audit does not enumerate it. Mathlib v4.12.0 has no general elliptic Hasse theorem.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_311_367.lean.
#check hasseprimset_BSD_Hasse_Points_311_367_Assessed.BSD_DegreeNonneg_p317_prop

-- NEEDS_AUTHORING. Gate A. Prime 3169 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3169_3251.lean.
#check hasseprimset_BSD_Hasse_Points_3169_3251_Assessed.BSD_DegreeNonneg_p3169_prop

-- NEEDS_AUTHORING. Gate A. Prime 3181 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3169_3251.lean.
#check hasseprimset_BSD_Hasse_Points_3169_3251_Assessed.BSD_DegreeNonneg_p3181_prop

-- NEEDS_AUTHORING. Gate A. Prime 3187 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3169_3251.lean.
#check hasseprimset_BSD_Hasse_Points_3169_3251_Assessed.BSD_DegreeNonneg_p3187_prop

-- NEEDS_AUTHORING. Gate A. Prime 3253 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3253_3323.lean.
#check hasseprimset_BSD_Hasse_Points_3253_3323_Assessed.BSD_DegreeNonneg_p3253_prop

-- NEEDS_AUTHORING. Gate A. Prime 3257 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3253_3323.lean.
#check hasseprimset_BSD_Hasse_Points_3253_3323_Assessed.BSD_DegreeNonneg_p3257_prop

-- NEEDS_AUTHORING. Gate A. Prime 3259 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3253_3323.lean.
#check hasseprimset_BSD_Hasse_Points_3253_3323_Assessed.BSD_DegreeNonneg_p3259_prop

-- NEEDS_AUTHORING. Gate A. Prime 3329 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3329_3391.lean.
#check hasseprimset_BSD_Hasse_Points_3329_3391_Assessed.BSD_DegreeNonneg_p3329_prop

-- NEEDS_AUTHORING. Gate A. Prime 3331 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3329_3391.lean.
#check hasseprimset_BSD_Hasse_Points_3329_3391_Assessed.BSD_DegreeNonneg_p3331_prop

-- NEEDS_AUTHORING. Gate A. Prime 3343 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3329_3391.lean.
#check hasseprimset_BSD_Hasse_Points_3329_3391_Assessed.BSD_DegreeNonneg_p3343_prop

-- NEEDS_AUTHORING. Gate A. Prime 3407 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3407_3491.lean.
#check hasseprimset_BSD_Hasse_Points_3407_3491_Assessed.BSD_DegreeNonneg_p3407_prop

-- NEEDS_AUTHORING. Gate A. Prime 3413 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3407_3491.lean.
#check hasseprimset_BSD_Hasse_Points_3407_3491_Assessed.BSD_DegreeNonneg_p3413_prop

-- NEEDS_AUTHORING. Gate A. Prime 3433 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3407_3491.lean.
#check hasseprimset_BSD_Hasse_Points_3407_3491_Assessed.BSD_DegreeNonneg_p3433_prop

-- NEEDS_AUTHORING. Gate A. Prime 3499 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3499_3557.lean.
#check hasseprimset_BSD_Hasse_Points_3499_3557_Assessed.BSD_DegreeNonneg_p3499_prop

-- NEEDS_AUTHORING. Gate A. Prime 3511 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3499_3557.lean.
#check hasseprimset_BSD_Hasse_Points_3499_3557_Assessed.BSD_DegreeNonneg_p3511_prop

-- NEEDS_AUTHORING. Gate A. Prime 3517 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch5.lean. Original file: hasseprimset/BSD_Hasse_Points_3499_3557.lean.
#check hasseprimset_BSD_Hasse_Points_3499_3557_Assessed.BSD_DegreeNonneg_p3517_prop

-- NEEDS_AUTHORING. Gate A. Prime 3559 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3559_3631.lean.
#check hasseprimset_BSD_Hasse_Points_3559_3631_Assessed.BSD_DegreeNonneg_p3559_prop

-- NEEDS_AUTHORING. Gate A. Prime 3571 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3559_3631.lean.
#check hasseprimset_BSD_Hasse_Points_3559_3631_Assessed.BSD_DegreeNonneg_p3571_prop

-- NEEDS_AUTHORING. Gate A. Prime 3581 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3559_3631.lean.
#check hasseprimset_BSD_Hasse_Points_3559_3631_Assessed.BSD_DegreeNonneg_p3581_prop

-- NEEDS_AUTHORING. Gate A. Prime 3637 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3637_3709.lean.
#check hasseprimset_BSD_Hasse_Points_3637_3709_Assessed.BSD_DegreeNonneg_p3637_prop

-- NEEDS_AUTHORING. Gate A. Prime 3643 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3637_3709.lean.
#check hasseprimset_BSD_Hasse_Points_3637_3709_Assessed.BSD_DegreeNonneg_p3643_prop

-- NEEDS_AUTHORING. Gate A. Prime 3659 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3637_3709.lean.
#check hasseprimset_BSD_Hasse_Points_3637_3709_Assessed.BSD_DegreeNonneg_p3659_prop

-- NEEDS_AUTHORING. Gate A. Prime 3719 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3719_3797.lean.
#check hasseprimset_BSD_Hasse_Points_3719_3797_Assessed.BSD_DegreeNonneg_p3719_prop

-- NEEDS_AUTHORING. Gate A. Prime 3727 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3719_3797.lean.
#check hasseprimset_BSD_Hasse_Points_3719_3797_Assessed.BSD_DegreeNonneg_p3727_prop

-- NEEDS_AUTHORING. Gate A. Prime 3733 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3719_3797.lean.
#check hasseprimset_BSD_Hasse_Points_3719_3797_Assessed.BSD_DegreeNonneg_p3733_prop

-- NEEDS_AUTHORING. Gate A. Prime 3803 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3803_3881.lean.
#check hasseprimset_BSD_Hasse_Points_3803_3881_Assessed.BSD_DegreeNonneg_p3803_prop

-- NEEDS_AUTHORING. Gate A. Prime 3821 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3803_3881.lean.
#check hasseprimset_BSD_Hasse_Points_3803_3881_Assessed.BSD_DegreeNonneg_p3821_prop

-- NEEDS_AUTHORING. Gate A. Prime 3823 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3803_3881.lean.
#check hasseprimset_BSD_Hasse_Points_3803_3881_Assessed.BSD_DegreeNonneg_p3823_prop

-- NEEDS_AUTHORING. Gate A. Prime 3889 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3889_3947.lean.
#check hasseprimset_BSD_Hasse_Points_3889_3947_Assessed.BSD_DegreeNonneg_p3889_prop

-- NEEDS_AUTHORING. Gate A. Prime 3907 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3889_3947.lean.
#check hasseprimset_BSD_Hasse_Points_3889_3947_Assessed.BSD_DegreeNonneg_p3907_prop

-- NEEDS_AUTHORING. Gate A. Prime 3911 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3889_3947.lean.
#check hasseprimset_BSD_Hasse_Points_3889_3947_Assessed.BSD_DegreeNonneg_p3911_prop

-- NEEDS_AUTHORING. Gate A. Prime 3967 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3967_4049.lean.
#check hasseprimset_BSD_Hasse_Points_3967_4049_Assessed.BSD_DegreeNonneg_p3967_prop

-- NEEDS_AUTHORING. Gate A. Prime 3989 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3967_4049.lean.
#check hasseprimset_BSD_Hasse_Points_3967_4049_Assessed.BSD_DegreeNonneg_p3989_prop

-- NEEDS_AUTHORING. Gate A. Prime 4001 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_3967_4049.lean.
#check hasseprimset_BSD_Hasse_Points_3967_4049_Assessed.BSD_DegreeNonneg_p4001_prop

-- NEEDS_AUTHORING. Gate A. Prime 4051 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4051_4129.lean.
#check hasseprimset_BSD_Hasse_Points_4051_4129_Assessed.BSD_DegreeNonneg_p4051_prop

-- NEEDS_AUTHORING. Gate A. Prime 4057 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4051_4129.lean.
#check hasseprimset_BSD_Hasse_Points_4051_4129_Assessed.BSD_DegreeNonneg_p4057_prop

-- NEEDS_AUTHORING. Gate A. Prime 4073 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4051_4129.lean.
#check hasseprimset_BSD_Hasse_Points_4051_4129_Assessed.BSD_DegreeNonneg_p4073_prop

-- NEEDS_AUTHORING. Gate A. Prime 4133 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4133_4219.lean.
#check hasseprimset_BSD_Hasse_Points_4133_4219_Assessed.BSD_DegreeNonneg_p4133_prop

-- NEEDS_AUTHORING. Gate A. Prime 4139 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4133_4219.lean.
#check hasseprimset_BSD_Hasse_Points_4133_4219_Assessed.BSD_DegreeNonneg_p4139_prop

-- NEEDS_AUTHORING. Gate A. Prime 4153 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4133_4219.lean.
#check hasseprimset_BSD_Hasse_Points_4133_4219_Assessed.BSD_DegreeNonneg_p4153_prop

-- NEEDS_AUTHORING. Gate A. Prime 4229 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4229_4283.lean.
#check hasseprimset_BSD_Hasse_Points_4229_4283_Assessed.BSD_DegreeNonneg_p4229_prop

-- NEEDS_AUTHORING. Gate A. Prime 4231 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4229_4283.lean.
#check hasseprimset_BSD_Hasse_Points_4229_4283_Assessed.BSD_DegreeNonneg_p4231_prop

-- NEEDS_AUTHORING. Gate A. Prime 4241 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4229_4283.lean.
#check hasseprimset_BSD_Hasse_Points_4229_4283_Assessed.BSD_DegreeNonneg_p4241_prop

-- NEEDS_AUTHORING. Gate A. Prime 4289 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4289_4391.lean.
#check hasseprimset_BSD_Hasse_Points_4289_4391_Assessed.BSD_DegreeNonneg_p4289_prop

-- NEEDS_AUTHORING. Gate A. Prime 4297 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4289_4391.lean.
#check hasseprimset_BSD_Hasse_Points_4289_4391_Assessed.BSD_DegreeNonneg_p4297_prop

-- NEEDS_AUTHORING. Gate A. Prime 4327 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4289_4391.lean.
#check hasseprimset_BSD_Hasse_Points_4289_4391_Assessed.BSD_DegreeNonneg_p4327_prop

-- NEEDS_AUTHORING. Gate A. Prime 4397 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4397_4481.lean.
#check hasseprimset_BSD_Hasse_Points_4397_4481_Assessed.BSD_DegreeNonneg_p4397_prop

-- NEEDS_AUTHORING. Gate A. Prime 4409 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4397_4481.lean.
#check hasseprimset_BSD_Hasse_Points_4397_4481_Assessed.BSD_DegreeNonneg_p4409_prop

-- NEEDS_AUTHORING. Gate A. Prime 4421 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4397_4481.lean.
#check hasseprimset_BSD_Hasse_Points_4397_4481_Assessed.BSD_DegreeNonneg_p4421_prop

-- NEEDS_AUTHORING. Gate A. Prime 4483 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4483_4561.lean.
#check hasseprimset_BSD_Hasse_Points_4483_4561_Assessed.BSD_DegreeNonneg_p4483_prop

-- NEEDS_AUTHORING. Gate A. Prime 4493 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4483_4561.lean.
#check hasseprimset_BSD_Hasse_Points_4483_4561_Assessed.BSD_DegreeNonneg_p4493_prop

-- NEEDS_AUTHORING. Gate A. Prime 4507 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4483_4561.lean.
#check hasseprimset_BSD_Hasse_Points_4483_4561_Assessed.BSD_DegreeNonneg_p4507_prop

-- NEEDS_AUTHORING. Gate A. Prime 4567 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4567_4649.lean.
#check hasseprimset_BSD_Hasse_Points_4567_4649_Assessed.BSD_DegreeNonneg_p4567_prop

-- NEEDS_AUTHORING. Gate A. Prime 4583 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4567_4649.lean.
#check hasseprimset_BSD_Hasse_Points_4567_4649_Assessed.BSD_DegreeNonneg_p4583_prop

-- NEEDS_AUTHORING. Gate A. Prime 4591 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4567_4649.lean.
#check hasseprimset_BSD_Hasse_Points_4567_4649_Assessed.BSD_DegreeNonneg_p4591_prop

-- NEEDS_AUTHORING. Gate A. Prime 4651 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4651_4729.lean.
#check hasseprimset_BSD_Hasse_Points_4651_4729_Assessed.BSD_DegreeNonneg_p4651_prop

-- NEEDS_AUTHORING. Gate A. Prime 4657 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4651_4729.lean.
#check hasseprimset_BSD_Hasse_Points_4651_4729_Assessed.BSD_DegreeNonneg_p4657_prop

-- NEEDS_AUTHORING. Gate A. Prime 4663 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4651_4729.lean.
#check hasseprimset_BSD_Hasse_Points_4651_4729_Assessed.BSD_DegreeNonneg_p4663_prop

-- NEEDS_AUTHORING. Gate A. Prime 4733 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4733_4813.lean.
#check hasseprimset_BSD_Hasse_Points_4733_4813_Assessed.BSD_DegreeNonneg_p4733_prop

-- NEEDS_AUTHORING. Gate A. Prime 4751 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4733_4813.lean.
#check hasseprimset_BSD_Hasse_Points_4733_4813_Assessed.BSD_DegreeNonneg_p4751_prop

-- NEEDS_AUTHORING. Gate A. Prime 4759 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4733_4813.lean.
#check hasseprimset_BSD_Hasse_Points_4733_4813_Assessed.BSD_DegreeNonneg_p4759_prop

-- NEEDS_AUTHORING. Gate A. Prime 4817 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4817_4931.lean.
#check hasseprimset_BSD_Hasse_Points_4817_4931_Assessed.BSD_DegreeNonneg_p4817_prop

-- NEEDS_AUTHORING. Gate A. Prime 4831 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4817_4931.lean.
#check hasseprimset_BSD_Hasse_Points_4817_4931_Assessed.BSD_DegreeNonneg_p4831_prop

-- NEEDS_AUTHORING. Gate A. Prime 4861 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4817_4931.lean.
#check hasseprimset_BSD_Hasse_Points_4817_4931_Assessed.BSD_DegreeNonneg_p4861_prop

-- NEEDS_AUTHORING. Gate A. Prime 4933 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4933_4993.lean.
#check hasseprimset_BSD_Hasse_Points_4933_4993_Assessed.BSD_DegreeNonneg_p4933_prop

-- NEEDS_AUTHORING. Gate A. Prime 4937 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4933_4993.lean.
#check hasseprimset_BSD_Hasse_Points_4933_4993_Assessed.BSD_DegreeNonneg_p4937_prop

-- NEEDS_AUTHORING. Gate A. Prime 4943 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch6.lean. Original file: hasseprimset/BSD_Hasse_Points_4933_4993.lean.
#check hasseprimset_BSD_Hasse_Points_4933_4993_Assessed.BSD_DegreeNonneg_p4943_prop

-- NEEDS_AUTHORING. Gate A. Prime 4999 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_4999_5077.lean.
#check hasseprimset_BSD_Hasse_Points_4999_5077_Assessed.BSD_DegreeNonneg_p4999_prop

-- NEEDS_AUTHORING. Gate A. Prime 5003 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_4999_5077.lean.
#check hasseprimset_BSD_Hasse_Points_4999_5077_Assessed.BSD_DegreeNonneg_p5003_prop

-- NEEDS_AUTHORING. Gate A. Prime 5009 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_4999_5077.lean.
#check hasseprimset_BSD_Hasse_Points_4999_5077_Assessed.BSD_DegreeNonneg_p5009_prop

-- NEEDS_AUTHORING. Gate A. Prime 5081 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5081_5167.lean.
#check hasseprimset_BSD_Hasse_Points_5081_5167_Assessed.BSD_DegreeNonneg_p5081_prop

-- NEEDS_AUTHORING. Gate A. Prime 5087 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5081_5167.lean.
#check hasseprimset_BSD_Hasse_Points_5081_5167_Assessed.BSD_DegreeNonneg_p5087_prop

-- NEEDS_AUTHORING. Gate A. Prime 5099 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5081_5167.lean.
#check hasseprimset_BSD_Hasse_Points_5081_5167_Assessed.BSD_DegreeNonneg_p5099_prop

-- NEEDS_AUTHORING. Gate A. Prime 5171 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5171_5261.lean.
#check hasseprimset_BSD_Hasse_Points_5171_5261_Assessed.BSD_DegreeNonneg_p5171_prop

-- NEEDS_AUTHORING. Gate A. Prime 5179 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5171_5261.lean.
#check hasseprimset_BSD_Hasse_Points_5171_5261_Assessed.BSD_DegreeNonneg_p5179_prop

-- NEEDS_AUTHORING. Gate A. Prime 5189 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5171_5261.lean.
#check hasseprimset_BSD_Hasse_Points_5171_5261_Assessed.BSD_DegreeNonneg_p5189_prop

-- NEEDS_AUTHORING. Gate A. Prime 5273 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5273_5351.lean.
#check hasseprimset_BSD_Hasse_Points_5273_5351_Assessed.BSD_DegreeNonneg_p5273_prop

-- NEEDS_AUTHORING. Gate A. Prime 5279 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5273_5351.lean.
#check hasseprimset_BSD_Hasse_Points_5273_5351_Assessed.BSD_DegreeNonneg_p5279_prop

-- NEEDS_AUTHORING. Gate A. Prime 5281 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5273_5351.lean.
#check hasseprimset_BSD_Hasse_Points_5273_5351_Assessed.BSD_DegreeNonneg_p5281_prop

-- NEEDS_AUTHORING. Gate A. Prime 5381 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5381_5437.lean.
#check hasseprimset_BSD_Hasse_Points_5381_5437_Assessed.BSD_DegreeNonneg_p5381_prop

-- NEEDS_AUTHORING. Gate A. Prime 5387 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5381_5437.lean.
#check hasseprimset_BSD_Hasse_Points_5381_5437_Assessed.BSD_DegreeNonneg_p5387_prop

-- NEEDS_AUTHORING. Gate A. Prime 5393 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5381_5437.lean.
#check hasseprimset_BSD_Hasse_Points_5381_5437_Assessed.BSD_DegreeNonneg_p5393_prop

-- NEEDS_AUTHORING. Gate A. Prime 5441 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5441_5507.lean.
#check hasseprimset_BSD_Hasse_Points_5441_5507_Assessed.BSD_DegreeNonneg_p5441_prop

-- NEEDS_AUTHORING. Gate A. Prime 5443 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5441_5507.lean.
#check hasseprimset_BSD_Hasse_Points_5441_5507_Assessed.BSD_DegreeNonneg_p5443_prop

-- NEEDS_AUTHORING. Gate A. Prime 5449 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5441_5507.lean.
#check hasseprimset_BSD_Hasse_Points_5441_5507_Assessed.BSD_DegreeNonneg_p5449_prop

-- NEEDS_AUTHORING. Gate A. Prime 5519 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5519_5591.lean.
#check hasseprimset_BSD_Hasse_Points_5519_5591_Assessed.BSD_DegreeNonneg_p5519_prop

-- NEEDS_AUTHORING. Gate A. Prime 5521 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5519_5591.lean.
#check hasseprimset_BSD_Hasse_Points_5519_5591_Assessed.BSD_DegreeNonneg_p5521_prop

-- NEEDS_AUTHORING. Gate A. Prime 5527 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5519_5591.lean.
#check hasseprimset_BSD_Hasse_Points_5519_5591_Assessed.BSD_DegreeNonneg_p5527_prop

-- NEEDS_AUTHORING. Gate A. Prime 5623 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5623_5683.lean.
#check hasseprimset_BSD_Hasse_Points_5623_5683_Assessed.BSD_DegreeNonneg_p5623_prop

-- NEEDS_AUTHORING. Gate A. Prime 5639 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5623_5683.lean.
#check hasseprimset_BSD_Hasse_Points_5623_5683_Assessed.BSD_DegreeNonneg_p5639_prop

-- NEEDS_AUTHORING. Gate A. Prime 5641 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5623_5683.lean.
#check hasseprimset_BSD_Hasse_Points_5623_5683_Assessed.BSD_DegreeNonneg_p5641_prop

-- NEEDS_AUTHORING. Gate A. Prime 5689 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5689_5779.lean.
#check hasseprimset_BSD_Hasse_Points_5689_5779_Assessed.BSD_DegreeNonneg_p5689_prop

-- NEEDS_AUTHORING. Gate A. Prime 5693 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5689_5779.lean.
#check hasseprimset_BSD_Hasse_Points_5689_5779_Assessed.BSD_DegreeNonneg_p5693_prop

-- NEEDS_AUTHORING. Gate A. Prime 5701 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5689_5779.lean.
#check hasseprimset_BSD_Hasse_Points_5689_5779_Assessed.BSD_DegreeNonneg_p5701_prop

-- NEEDS_AUTHORING. Gate A. Prime 5783 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5783_5849.lean.
#check hasseprimset_BSD_Hasse_Points_5783_5849_Assessed.BSD_DegreeNonneg_p5783_prop

-- NEEDS_AUTHORING. Gate A. Prime 5791 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5783_5849.lean.
#check hasseprimset_BSD_Hasse_Points_5783_5849_Assessed.BSD_DegreeNonneg_p5791_prop

-- NEEDS_AUTHORING. Gate A. Prime 5801 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5783_5849.lean.
#check hasseprimset_BSD_Hasse_Points_5783_5849_Assessed.BSD_DegreeNonneg_p5801_prop

-- NEEDS_AUTHORING. Gate A. Prime 5851 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5851_5923.lean.
#check hasseprimset_BSD_Hasse_Points_5851_5923_Assessed.BSD_DegreeNonneg_p5851_prop

-- NEEDS_AUTHORING. Gate A. Prime 5857 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5851_5923.lean.
#check hasseprimset_BSD_Hasse_Points_5851_5923_Assessed.BSD_DegreeNonneg_p5857_prop

-- NEEDS_AUTHORING. Gate A. Prime 5861 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5851_5923.lean.
#check hasseprimset_BSD_Hasse_Points_5851_5923_Assessed.BSD_DegreeNonneg_p5861_prop

-- NEEDS_AUTHORING. Gate A. Prime 5927 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5927_6043.lean.
#check hasseprimset_BSD_Hasse_Points_5927_6043_Assessed.BSD_DegreeNonneg_p5927_prop

-- NEEDS_AUTHORING. Gate A. Prime 5939 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5927_6043.lean.
#check hasseprimset_BSD_Hasse_Points_5927_6043_Assessed.BSD_DegreeNonneg_p5939_prop

-- NEEDS_AUTHORING. Gate A. Prime 5953 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_5927_6043.lean.
#check hasseprimset_BSD_Hasse_Points_5927_6043_Assessed.BSD_DegreeNonneg_p5953_prop

-- NEEDS_AUTHORING. Gate A. Prime 6047 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6047_6121.lean.
#check hasseprimset_BSD_Hasse_Points_6047_6121_Assessed.BSD_DegreeNonneg_p6047_prop

-- NEEDS_AUTHORING. Gate A. Prime 6053 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6047_6121.lean.
#check hasseprimset_BSD_Hasse_Points_6047_6121_Assessed.BSD_DegreeNonneg_p6053_prop

-- NEEDS_AUTHORING. Gate A. Prime 6067 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6047_6121.lean.
#check hasseprimset_BSD_Hasse_Points_6047_6121_Assessed.BSD_DegreeNonneg_p6067_prop

-- NEEDS_AUTHORING. Gate A. Prime 6131 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6131_6211.lean.
#check hasseprimset_BSD_Hasse_Points_6131_6211_Assessed.BSD_DegreeNonneg_p6131_prop

-- NEEDS_AUTHORING. Gate A. Prime 6133 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6131_6211.lean.
#check hasseprimset_BSD_Hasse_Points_6131_6211_Assessed.BSD_DegreeNonneg_p6133_prop

-- NEEDS_AUTHORING. Gate A. Prime 6143 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6131_6211.lean.
#check hasseprimset_BSD_Hasse_Points_6131_6211_Assessed.BSD_DegreeNonneg_p6143_prop

-- NEEDS_AUTHORING. Gate A. Prime 6217 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6217_6287.lean.
#check hasseprimset_BSD_Hasse_Points_6217_6287_Assessed.BSD_DegreeNonneg_p6217_prop

-- NEEDS_AUTHORING. Gate A. Prime 6221 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6217_6287.lean.
#check hasseprimset_BSD_Hasse_Points_6217_6287_Assessed.BSD_DegreeNonneg_p6221_prop

-- NEEDS_AUTHORING. Gate A. Prime 6229 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6217_6287.lean.
#check hasseprimset_BSD_Hasse_Points_6217_6287_Assessed.BSD_DegreeNonneg_p6229_prop

-- NEEDS_AUTHORING. Gate A. Prime 6299 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6299_6359.lean.
#check hasseprimset_BSD_Hasse_Points_6299_6359_Assessed.BSD_DegreeNonneg_p6299_prop

-- NEEDS_AUTHORING. Gate A. Prime 6301 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6299_6359.lean.
#check hasseprimset_BSD_Hasse_Points_6299_6359_Assessed.BSD_DegreeNonneg_p6301_prop

-- NEEDS_AUTHORING. Gate A. Prime 6311 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6299_6359.lean.
#check hasseprimset_BSD_Hasse_Points_6299_6359_Assessed.BSD_DegreeNonneg_p6311_prop

-- NEEDS_AUTHORING. Gate A. Prime 6361 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6361_6451.lean.
#check hasseprimset_BSD_Hasse_Points_6361_6451_Assessed.BSD_DegreeNonneg_p6361_prop

-- NEEDS_AUTHORING. Gate A. Prime 6367 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6361_6451.lean.
#check hasseprimset_BSD_Hasse_Points_6361_6451_Assessed.BSD_DegreeNonneg_p6367_prop

-- NEEDS_AUTHORING. Gate A. Prime 6373 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6361_6451.lean.
#check hasseprimset_BSD_Hasse_Points_6361_6451_Assessed.BSD_DegreeNonneg_p6373_prop

-- NEEDS_AUTHORING. Gate A. Prime 6469 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6469_6563.lean.
#check hasseprimset_BSD_Hasse_Points_6469_6563_Assessed.BSD_DegreeNonneg_p6469_prop

-- NEEDS_AUTHORING. Gate A. Prime 6473 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6469_6563.lean.
#check hasseprimset_BSD_Hasse_Points_6469_6563_Assessed.BSD_DegreeNonneg_p6473_prop

-- NEEDS_AUTHORING. Gate A. Prime 6481 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch7.lean. Original file: hasseprimset/BSD_Hasse_Points_6469_6563.lean.
#check hasseprimset_BSD_Hasse_Points_6469_6563_Assessed.BSD_DegreeNonneg_p6481_prop

-- NEEDS_AUTHORING. Gate A. Prime 6569 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6569_6659.lean.
#check hasseprimset_BSD_Hasse_Points_6569_6659_Assessed.BSD_DegreeNonneg_p6569_prop

-- NEEDS_AUTHORING. Gate A. Prime 6571 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6569_6659.lean.
#check hasseprimset_BSD_Hasse_Points_6569_6659_Assessed.BSD_DegreeNonneg_p6571_prop

-- NEEDS_AUTHORING. Gate A. Prime 6577 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6569_6659.lean.
#check hasseprimset_BSD_Hasse_Points_6569_6659_Assessed.BSD_DegreeNonneg_p6577_prop

-- NEEDS_AUTHORING. Gate A. Prime 6661 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6661_6733.lean.
#check hasseprimset_BSD_Hasse_Points_6661_6733_Assessed.BSD_DegreeNonneg_p6661_prop

-- NEEDS_AUTHORING. Gate A. Prime 6673 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6661_6733.lean.
#check hasseprimset_BSD_Hasse_Points_6661_6733_Assessed.BSD_DegreeNonneg_p6673_prop

-- NEEDS_AUTHORING. Gate A. Prime 6679 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6661_6733.lean.
#check hasseprimset_BSD_Hasse_Points_6661_6733_Assessed.BSD_DegreeNonneg_p6679_prop

-- NEEDS_AUTHORING. Gate A. Prime 6737 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6737_6827.lean.
#check hasseprimset_BSD_Hasse_Points_6737_6827_Assessed.BSD_DegreeNonneg_p6737_prop

-- NEEDS_AUTHORING. Gate A. Prime 6761 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6737_6827.lean.
#check hasseprimset_BSD_Hasse_Points_6737_6827_Assessed.BSD_DegreeNonneg_p6761_prop

-- NEEDS_AUTHORING. Gate A. Prime 6763 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6737_6827.lean.
#check hasseprimset_BSD_Hasse_Points_6737_6827_Assessed.BSD_DegreeNonneg_p6763_prop

-- NEEDS_AUTHORING. Gate A. Prime 6829 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6829_6907.lean.
#check hasseprimset_BSD_Hasse_Points_6829_6907_Assessed.BSD_DegreeNonneg_p6829_prop

-- NEEDS_AUTHORING. Gate A. Prime 6833 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6829_6907.lean.
#check hasseprimset_BSD_Hasse_Points_6829_6907_Assessed.BSD_DegreeNonneg_p6833_prop

-- NEEDS_AUTHORING. Gate A. Prime 6841 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6829_6907.lean.
#check hasseprimset_BSD_Hasse_Points_6829_6907_Assessed.BSD_DegreeNonneg_p6841_prop

-- NEEDS_AUTHORING. Gate A. Prime 6911 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6911_6983.lean.
#check hasseprimset_BSD_Hasse_Points_6911_6983_Assessed.BSD_DegreeNonneg_p6911_prop

-- NEEDS_AUTHORING. Gate A. Prime 6917 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6911_6983.lean.
#check hasseprimset_BSD_Hasse_Points_6911_6983_Assessed.BSD_DegreeNonneg_p6917_prop

-- NEEDS_AUTHORING. Gate A. Prime 6947 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6911_6983.lean.
#check hasseprimset_BSD_Hasse_Points_6911_6983_Assessed.BSD_DegreeNonneg_p6947_prop

-- NEEDS_AUTHORING. Gate A. Prime 6991 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6991_7069.lean.
#check hasseprimset_BSD_Hasse_Points_6991_7069_Assessed.BSD_DegreeNonneg_p6991_prop

-- NEEDS_AUTHORING. Gate A. Prime 6997 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6991_7069.lean.
#check hasseprimset_BSD_Hasse_Points_6991_7069_Assessed.BSD_DegreeNonneg_p6997_prop

-- NEEDS_AUTHORING. Gate A. Prime 7001 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_6991_7069.lean.
#check hasseprimset_BSD_Hasse_Points_6991_7069_Assessed.BSD_DegreeNonneg_p7001_prop

-- NEEDS_AUTHORING. Gate A. Prime 7079 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7079_7187.lean.
#check hasseprimset_BSD_Hasse_Points_7079_7187_Assessed.BSD_DegreeNonneg_p7079_prop

-- NEEDS_AUTHORING. Gate A. Prime 7103 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7079_7187.lean.
#check hasseprimset_BSD_Hasse_Points_7079_7187_Assessed.BSD_DegreeNonneg_p7103_prop

-- NEEDS_AUTHORING. Gate A. Prime 7109 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7079_7187.lean.
#check hasseprimset_BSD_Hasse_Points_7079_7187_Assessed.BSD_DegreeNonneg_p7109_prop

-- NEEDS_AUTHORING. Gate A. Prime 7193 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7193_7253.lean.
#check hasseprimset_BSD_Hasse_Points_7193_7253_Assessed.BSD_DegreeNonneg_p7193_prop

-- NEEDS_AUTHORING. Gate A. Prime 7207 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7193_7253.lean.
#check hasseprimset_BSD_Hasse_Points_7193_7253_Assessed.BSD_DegreeNonneg_p7207_prop

-- NEEDS_AUTHORING. Gate A. Prime 7211 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7193_7253.lean.
#check hasseprimset_BSD_Hasse_Points_7193_7253_Assessed.BSD_DegreeNonneg_p7211_prop

-- NEEDS_AUTHORING. Gate A. Prime 7283 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7283_7369.lean.
#check hasseprimset_BSD_Hasse_Points_7283_7369_Assessed.BSD_DegreeNonneg_p7283_prop

-- NEEDS_AUTHORING. Gate A. Prime 7297 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7283_7369.lean.
#check hasseprimset_BSD_Hasse_Points_7283_7369_Assessed.BSD_DegreeNonneg_p7297_prop

-- NEEDS_AUTHORING. Gate A. Prime 7307 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7283_7369.lean.
#check hasseprimset_BSD_Hasse_Points_7283_7369_Assessed.BSD_DegreeNonneg_p7307_prop

-- NEEDS_AUTHORING. Gate A. Prime 7393 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7393_7487.lean.
#check hasseprimset_BSD_Hasse_Points_7393_7487_Assessed.BSD_DegreeNonneg_p7393_prop

-- NEEDS_AUTHORING. Gate A. Prime 7411 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7393_7487.lean.
#check hasseprimset_BSD_Hasse_Points_7393_7487_Assessed.BSD_DegreeNonneg_p7411_prop

-- NEEDS_AUTHORING. Gate A. Prime 7417 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7393_7487.lean.
#check hasseprimset_BSD_Hasse_Points_7393_7487_Assessed.BSD_DegreeNonneg_p7417_prop

-- NEEDS_AUTHORING. Gate A. Prime 7489 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7489_7549.lean.
#check hasseprimset_BSD_Hasse_Points_7489_7549_Assessed.BSD_DegreeNonneg_p7489_prop

-- NEEDS_AUTHORING. Gate A. Prime 7499 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7489_7549.lean.
#check hasseprimset_BSD_Hasse_Points_7489_7549_Assessed.BSD_DegreeNonneg_p7499_prop

-- NEEDS_AUTHORING. Gate A. Prime 7507 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7489_7549.lean.
#check hasseprimset_BSD_Hasse_Points_7489_7549_Assessed.BSD_DegreeNonneg_p7507_prop

-- NEEDS_AUTHORING. Gate A. Prime 7559 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7559_7621.lean.
#check hasseprimset_BSD_Hasse_Points_7559_7621_Assessed.BSD_DegreeNonneg_p7559_prop

-- NEEDS_AUTHORING. Gate A. Prime 7561 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7559_7621.lean.
#check hasseprimset_BSD_Hasse_Points_7559_7621_Assessed.BSD_DegreeNonneg_p7561_prop

-- NEEDS_AUTHORING. Gate A. Prime 7573 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7559_7621.lean.
#check hasseprimset_BSD_Hasse_Points_7559_7621_Assessed.BSD_DegreeNonneg_p7573_prop

-- NEEDS_AUTHORING. Gate A. Prime 7639 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7639_7703.lean.
#check hasseprimset_BSD_Hasse_Points_7639_7703_Assessed.BSD_DegreeNonneg_p7639_prop

-- NEEDS_AUTHORING. Gate A. Prime 7643 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7639_7703.lean.
#check hasseprimset_BSD_Hasse_Points_7639_7703_Assessed.BSD_DegreeNonneg_p7643_prop

-- NEEDS_AUTHORING. Gate A. Prime 7649 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7639_7703.lean.
#check hasseprimset_BSD_Hasse_Points_7639_7703_Assessed.BSD_DegreeNonneg_p7649_prop

-- NEEDS_AUTHORING. Gate A. Prime 7717 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7717_7817.lean.
#check hasseprimset_BSD_Hasse_Points_7717_7817_Assessed.BSD_DegreeNonneg_p7717_prop

-- NEEDS_AUTHORING. Gate A. Prime 7723 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7717_7817.lean.
#check hasseprimset_BSD_Hasse_Points_7717_7817_Assessed.BSD_DegreeNonneg_p7723_prop

-- NEEDS_AUTHORING. Gate A. Prime 7727 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7717_7817.lean.
#check hasseprimset_BSD_Hasse_Points_7717_7817_Assessed.BSD_DegreeNonneg_p7727_prop

-- NEEDS_AUTHORING. Gate A. Prime 7823 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7823_7901.lean.
#check hasseprimset_BSD_Hasse_Points_7823_7901_Assessed.BSD_DegreeNonneg_p7823_prop

-- NEEDS_AUTHORING. Gate A. Prime 7829 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7823_7901.lean.
#check hasseprimset_BSD_Hasse_Points_7823_7901_Assessed.BSD_DegreeNonneg_p7829_prop

-- NEEDS_AUTHORING. Gate A. Prime 7841 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7823_7901.lean.
#check hasseprimset_BSD_Hasse_Points_7823_7901_Assessed.BSD_DegreeNonneg_p7841_prop

-- NEEDS_AUTHORING. Gate A. Prime 7907 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7907_8009.lean.
#check hasseprimset_BSD_Hasse_Points_7907_8009_Assessed.BSD_DegreeNonneg_p7907_prop

-- NEEDS_AUTHORING. Gate A. Prime 7919 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7907_8009.lean.
#check hasseprimset_BSD_Hasse_Points_7907_8009_Assessed.BSD_DegreeNonneg_p7919_prop

-- NEEDS_AUTHORING. Gate A. Prime 7927 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_7907_8009.lean.
#check hasseprimset_BSD_Hasse_Points_7907_8009_Assessed.BSD_DegreeNonneg_p7927_prop

-- NEEDS_AUTHORING. Gate A. Prime 8011 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_8011_8093.lean.
#check hasseprimset_BSD_Hasse_Points_8011_8093_Assessed.BSD_DegreeNonneg_p8011_prop

-- NEEDS_AUTHORING. Gate A. Prime 8017 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_8011_8093.lean.
#check hasseprimset_BSD_Hasse_Points_8011_8093_Assessed.BSD_DegreeNonneg_p8017_prop

-- NEEDS_AUTHORING. Gate A. Prime 8039 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_8011_8093.lean.
#check hasseprimset_BSD_Hasse_Points_8011_8093_Assessed.BSD_DegreeNonneg_p8039_prop

-- NEEDS_AUTHORING. Gate A. Prime 8101 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_8101_8191.lean.
#check hasseprimset_BSD_Hasse_Points_8101_8191_Assessed.BSD_DegreeNonneg_p8101_prop

-- NEEDS_AUTHORING. Gate A. Prime 8111 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_8101_8191.lean.
#check hasseprimset_BSD_Hasse_Points_8101_8191_Assessed.BSD_DegreeNonneg_p8111_prop

-- NEEDS_AUTHORING. Gate A. Prime 8117 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch8.lean. Original file: hasseprimset/BSD_Hasse_Points_8101_8191.lean.
#check hasseprimset_BSD_Hasse_Points_8101_8191_Assessed.BSD_DegreeNonneg_p8117_prop

-- NEEDS_AUTHORING. Gate A. Prime 8209 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8209_8273.lean.
#check hasseprimset_BSD_Hasse_Points_8209_8273_Assessed.BSD_DegreeNonneg_p8209_prop

-- NEEDS_AUTHORING. Gate A. Prime 8219 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8209_8273.lean.
#check hasseprimset_BSD_Hasse_Points_8209_8273_Assessed.BSD_DegreeNonneg_p8219_prop

-- NEEDS_AUTHORING. Gate A. Prime 8221 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8209_8273.lean.
#check hasseprimset_BSD_Hasse_Points_8209_8273_Assessed.BSD_DegreeNonneg_p8221_prop

-- NEEDS_AUTHORING. Gate A. Prime 8287 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8287_8369.lean.
#check hasseprimset_BSD_Hasse_Points_8287_8369_Assessed.BSD_DegreeNonneg_p8287_prop

-- NEEDS_AUTHORING. Gate A. Prime 8291 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8287_8369.lean.
#check hasseprimset_BSD_Hasse_Points_8287_8369_Assessed.BSD_DegreeNonneg_p8291_prop

-- NEEDS_AUTHORING. Gate A. Prime 8293 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8287_8369.lean.
#check hasseprimset_BSD_Hasse_Points_8287_8369_Assessed.BSD_DegreeNonneg_p8293_prop

-- NEEDS_AUTHORING. Gate A. Prime 8377 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8377_8461.lean.
#check hasseprimset_BSD_Hasse_Points_8377_8461_Assessed.BSD_DegreeNonneg_p8377_prop

-- NEEDS_AUTHORING. Gate A. Prime 8387 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8377_8461.lean.
#check hasseprimset_BSD_Hasse_Points_8377_8461_Assessed.BSD_DegreeNonneg_p8387_prop

-- NEEDS_AUTHORING. Gate A. Prime 8389 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8377_8461.lean.
#check hasseprimset_BSD_Hasse_Points_8377_8461_Assessed.BSD_DegreeNonneg_p8389_prop

-- NEEDS_AUTHORING. Gate A. Prime 8467 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8467_8573.lean.
#check hasseprimset_BSD_Hasse_Points_8467_8573_Assessed.BSD_DegreeNonneg_p8467_prop

-- NEEDS_AUTHORING. Gate A. Prime 8501 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8467_8573.lean.
#check hasseprimset_BSD_Hasse_Points_8467_8573_Assessed.BSD_DegreeNonneg_p8501_prop

-- NEEDS_AUTHORING. Gate A. Prime 8513 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8467_8573.lean.
#check hasseprimset_BSD_Hasse_Points_8467_8573_Assessed.BSD_DegreeNonneg_p8513_prop

-- NEEDS_AUTHORING. Gate A. Prime 8581 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8581_8663.lean.
#check hasseprimset_BSD_Hasse_Points_8581_8663_Assessed.BSD_DegreeNonneg_p8581_prop

-- NEEDS_AUTHORING. Gate A. Prime 8597 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8581_8663.lean.
#check hasseprimset_BSD_Hasse_Points_8581_8663_Assessed.BSD_DegreeNonneg_p8597_prop

-- NEEDS_AUTHORING. Gate A. Prime 8599 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8581_8663.lean.
#check hasseprimset_BSD_Hasse_Points_8581_8663_Assessed.BSD_DegreeNonneg_p8599_prop

-- NEEDS_AUTHORING. Gate A. Prime 8669 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8669_8731.lean.
#check hasseprimset_BSD_Hasse_Points_8669_8731_Assessed.BSD_DegreeNonneg_p8669_prop

-- NEEDS_AUTHORING. Gate A. Prime 8677 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8669_8731.lean.
#check hasseprimset_BSD_Hasse_Points_8669_8731_Assessed.BSD_DegreeNonneg_p8677_prop

-- NEEDS_AUTHORING. Gate A. Prime 8681 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8669_8731.lean.
#check hasseprimset_BSD_Hasse_Points_8669_8731_Assessed.BSD_DegreeNonneg_p8681_prop

-- NEEDS_AUTHORING. Gate A. Prime 8737 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8737_8819.lean.
#check hasseprimset_BSD_Hasse_Points_8737_8819_Assessed.BSD_DegreeNonneg_p8737_prop

-- NEEDS_AUTHORING. Gate A. Prime 8741 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8737_8819.lean.
#check hasseprimset_BSD_Hasse_Points_8737_8819_Assessed.BSD_DegreeNonneg_p8741_prop

-- NEEDS_AUTHORING. Gate A. Prime 8747 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8737_8819.lean.
#check hasseprimset_BSD_Hasse_Points_8737_8819_Assessed.BSD_DegreeNonneg_p8747_prop

-- NEEDS_AUTHORING. Gate A. Prime 8821 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8821_8893.lean.
#check hasseprimset_BSD_Hasse_Points_8821_8893_Assessed.BSD_DegreeNonneg_p8821_prop

-- NEEDS_AUTHORING. Gate A. Prime 8831 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8821_8893.lean.
#check hasseprimset_BSD_Hasse_Points_8821_8893_Assessed.BSD_DegreeNonneg_p8831_prop

-- NEEDS_AUTHORING. Gate A. Prime 8837 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8821_8893.lean.
#check hasseprimset_BSD_Hasse_Points_8821_8893_Assessed.BSD_DegreeNonneg_p8837_prop

-- NEEDS_AUTHORING. Gate A. Prime 8923 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8923_9001.lean.
#check hasseprimset_BSD_Hasse_Points_8923_9001_Assessed.BSD_DegreeNonneg_p8923_prop

-- NEEDS_AUTHORING. Gate A. Prime 8929 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8923_9001.lean.
#check hasseprimset_BSD_Hasse_Points_8923_9001_Assessed.BSD_DegreeNonneg_p8929_prop

-- NEEDS_AUTHORING. Gate A. Prime 8933 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_8923_9001.lean.
#check hasseprimset_BSD_Hasse_Points_8923_9001_Assessed.BSD_DegreeNonneg_p8933_prop

-- NEEDS_AUTHORING. Gate A. Prime 9007 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9007_9091.lean.
#check hasseprimset_BSD_Hasse_Points_9007_9091_Assessed.BSD_DegreeNonneg_p9007_prop

-- NEEDS_AUTHORING. Gate A. Prime 9011 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9007_9091.lean.
#check hasseprimset_BSD_Hasse_Points_9007_9091_Assessed.BSD_DegreeNonneg_p9011_prop

-- NEEDS_AUTHORING. Gate A. Prime 9013 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9007_9091.lean.
#check hasseprimset_BSD_Hasse_Points_9007_9091_Assessed.BSD_DegreeNonneg_p9013_prop

-- NEEDS_AUTHORING. Gate A. Prime 9103 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9103_9181.lean.
#check hasseprimset_BSD_Hasse_Points_9103_9181_Assessed.BSD_DegreeNonneg_p9103_prop

-- NEEDS_AUTHORING. Gate A. Prime 9109 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9103_9181.lean.
#check hasseprimset_BSD_Hasse_Points_9103_9181_Assessed.BSD_DegreeNonneg_p9109_prop

-- NEEDS_AUTHORING. Gate A. Prime 9127 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9103_9181.lean.
#check hasseprimset_BSD_Hasse_Points_9103_9181_Assessed.BSD_DegreeNonneg_p9127_prop

-- NEEDS_AUTHORING. Gate A. Prime 9187 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9187_9277.lean.
#check hasseprimset_BSD_Hasse_Points_9187_9277_Assessed.BSD_DegreeNonneg_p9187_prop

-- NEEDS_AUTHORING. Gate A. Prime 9199 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9187_9277.lean.
#check hasseprimset_BSD_Hasse_Points_9187_9277_Assessed.BSD_DegreeNonneg_p9199_prop

-- NEEDS_AUTHORING. Gate A. Prime 9203 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9187_9277.lean.
#check hasseprimset_BSD_Hasse_Points_9187_9277_Assessed.BSD_DegreeNonneg_p9203_prop

-- NEEDS_AUTHORING. Gate A. Prime 9281 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9281_9349.lean.
#check hasseprimset_BSD_Hasse_Points_9281_9349_Assessed.BSD_DegreeNonneg_p9281_prop

-- NEEDS_AUTHORING. Gate A. Prime 9283 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9281_9349.lean.
#check hasseprimset_BSD_Hasse_Points_9281_9349_Assessed.BSD_DegreeNonneg_p9283_prop

-- NEEDS_AUTHORING. Gate A. Prime 9293 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9281_9349.lean.
#check hasseprimset_BSD_Hasse_Points_9281_9349_Assessed.BSD_DegreeNonneg_p9293_prop

-- NEEDS_AUTHORING. Gate A. Prime 9371 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9371_9433.lean.
#check hasseprimset_BSD_Hasse_Points_9371_9433_Assessed.BSD_DegreeNonneg_p9371_prop

-- NEEDS_AUTHORING. Gate A. Prime 9377 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9371_9433.lean.
#check hasseprimset_BSD_Hasse_Points_9371_9433_Assessed.BSD_DegreeNonneg_p9377_prop

-- NEEDS_AUTHORING. Gate A. Prime 9391 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9371_9433.lean.
#check hasseprimset_BSD_Hasse_Points_9371_9433_Assessed.BSD_DegreeNonneg_p9391_prop

-- NEEDS_AUTHORING. Gate A. Prime 9437 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9437_9511.lean.
#check hasseprimset_BSD_Hasse_Points_9437_9511_Assessed.BSD_DegreeNonneg_p9437_prop

-- NEEDS_AUTHORING. Gate A. Prime 9439 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9437_9511.lean.
#check hasseprimset_BSD_Hasse_Points_9437_9511_Assessed.BSD_DegreeNonneg_p9439_prop

-- NEEDS_AUTHORING. Gate A. Prime 9461 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9437_9511.lean.
#check hasseprimset_BSD_Hasse_Points_9437_9511_Assessed.BSD_DegreeNonneg_p9461_prop

-- NEEDS_AUTHORING. Gate A. Prime 9521 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9521_9623.lean.
#check hasseprimset_BSD_Hasse_Points_9521_9623_Assessed.BSD_DegreeNonneg_p9521_prop

-- NEEDS_AUTHORING. Gate A. Prime 9533 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9521_9623.lean.
#check hasseprimset_BSD_Hasse_Points_9521_9623_Assessed.BSD_DegreeNonneg_p9533_prop

-- NEEDS_AUTHORING. Gate A. Prime 9539 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9521_9623.lean.
#check hasseprimset_BSD_Hasse_Points_9521_9623_Assessed.BSD_DegreeNonneg_p9539_prop

-- NEEDS_AUTHORING. Gate A. Prime 9629 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9629_9719.lean.
#check hasseprimset_BSD_Hasse_Points_9629_9719_Assessed.BSD_DegreeNonneg_p9629_prop

-- NEEDS_AUTHORING. Gate A. Prime 9631 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9629_9719.lean.
#check hasseprimset_BSD_Hasse_Points_9629_9719_Assessed.BSD_DegreeNonneg_p9631_prop

-- NEEDS_AUTHORING. Gate A. Prime 9643 is at least 1000, outside the 84 checked primes. Do not enumerate E143_Finset. Mathlib v4.12.0 has no general elliptic Hasse theorem to cite for this curve.
-- Assessed in BSD_Assessed_Batch9.lean. Original file: hasseprimset/BSD_Hasse_Points_9629_9719.lean.
#check hasseprimset_BSD_Hasse_Points_9629_9719_Assessed.BSD_DegreeNonneg_p9643_prop


/-! ## Group B — Class number. classGroupEquiv is absent. Lower-bound lemmas are outside the clean build. -/

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_AlgNorm.lean.
#check Towers_BSD_BSD_AlgNorm_Assessed.BSD_algNorm_gen_proof_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_BQF_Bridge_Closed.lean.
#check Towers_BSD_BSD_BQF_Bridge_Closed_Assessed.BSD_BQF_ClassNumber_bridge_CLOSED_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClassGroup_Generator_CLOSED.lean.
#check Towers_BSD_BSD_ClassGroup_Generator_CLOSED_Assessed.BSD_classGroup_gen_by_p2_CLOSED_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClassNum_Unconditional_CLOSED.lean.
#check Towers_BSD_BSD_ClassNum_Unconditional_CLOSED_Assessed.BSD_ClassNum_Unconditional_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClassNum_Unconditional_CLOSED.lean.
#check Towers_BSD_BSD_ClassNum_Unconditional_CLOSED_Assessed.BSD_classNumber_upper_gate_discharged_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClassNum_Upper_CLOSED.lean.
#check Towers_BSD_BSD_ClassNum_Upper_CLOSED_Assessed.BSD_BQF_ClassNumber_bridge_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClassNum_Upper_CLOSED.lean.
#check Towers_BSD_BSD_ClassNum_Upper_CLOSED_Assessed.BSD_classGroup_gen_by_p2_hyp_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClassNumberBounds.lean.
#check Towers_BSD_BSD_ClassNumberBounds_Assessed.BSD_orderOf_p2_OPEN_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClassNumberBounds.lean.
#check Towers_BSD_BSD_ClassNumberBounds_Assessed.BSD_classGroupCard_le_10_OPEN_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClassNumber_Completion_CLOSED.lean.
#check Towers_BSD_BSD_ClassNumber_Completion_CLOSED_Assessed.BSD_classNumber_completion_open_count_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClassNumber_UpperBound_CLOSED.lean.
#check Towers_BSD_BSD_ClassNumber_UpperBound_CLOSED_Assessed.BSD_small_norm_in_zpowers_OPEN_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_Clay_6gate_CLOSED.lean.
#check Towers_BSD_BSD_Clay_6gate_CLOSED_Assessed.BSD_classNumber_upper_DISCHARGED_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_Clay_Certificate.lean.
#check Towers_BSD_BSD_Clay_Certificate_Assessed.BSD_ClassNumber_Lower_Gate_Discharged_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_Discriminant.lean.
#check Towers_BSD_BSD_Discriminant_Assessed.BSD_finrank_proved_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_FormIdeal_CLOSED.lean.
#check Towers_BSD_BSD_FormIdeal_CLOSED_Assessed.BSD_FormIdeal_open_count_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_MasterProof.lean.
#check Towers_BSD_BSD_MasterProof_Assessed.BSD_classNumber_lower_bound_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_MasterProof.lean.
#check Towers_BSD_BSD_MasterProof_Assessed.BSD_classNumber_upper_OPEN_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_NormBridge.lean.
#check Towers_BSD_BSD_NormBridge_Assessed.BSD_algNorm_gen_CLOSED_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_NormFormBounds.lean.
#check Towers_BSD_BSD_NormFormBounds_Assessed.BSD_ClassNumber_Upper_OPEN_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_NormFormBounds.lean.
#check Towers_BSD_BSD_NormFormBounds_Assessed.BSD_ClassNumber_Lower_OPEN_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_OrderOf_CLOSED.lean.
#check Towers_BSD_BSD_OrderOf_CLOSED_Assessed.BSD_orderOf_p2_CLOSED_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_OrderOf_CLOSED.lean.
#check Towers_BSD_BSD_OrderOf_CLOSED_Assessed.BSD_OrderOf_all_CLOSED_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_OrderOf_CLOSED.lean.
#check Towers_BSD_BSD_OrderOf_CLOSED_Assessed.BSD_OrderOf_open_count_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_P2_Principal_CLOSED.lean.
#check Towers_BSD_BSD_P2_Principal_CLOSED_Assessed.BSD_p2_pow_10_principal_hyp_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_P2_Principal_CLOSED.lean.
#check Towers_BSD_BSD_P2_Principal_CLOSED_Assessed.BSD_p2_pow_10_principal_prop

-- NEEDS_AUTHORING. Gate B. Class number. Lower bound uses master_not_principal_1_to_9 and p2_OK outside the clean build. Upper bound needs BinaryQuadraticForm.classGroupEquiv, absent from Mathlib v4.12.0 (zero declarations). Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_ReducedForms.lean.
#check Towers_BSD_BSD_ReducedForms_Assessed.BSD_BQF_ClassNumber_bridge_OPEN_prop


/-! ## Group C — Registry derivative is the constant 0. The linear anchor is not the Hasse–Weil L-function. -/

-- NEEDS_AUTHORING. Gate C. Registry BSD_L143a1_DerivAtOne is the constant 0, so nonzero is 0 ≠ 0. There is no hasseprimset/BSD_LFunction.lean. Towers/BSD/BSD_LFunction.lean has no proved Hasse-Weil derivative. The linear anchor (5759/10000)·(s−1) is Batch 4 and is not that L-function. Registry constant not changed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/B02_Modularity_Closed.lean.
#check Towers_BSD_B02_Modularity_Closed_Assessed.BSD_LFunctionIsLinFunc_OPEN_prop

-- NEEDS_AUTHORING. Gate C. Registry BSD_L143a1_DerivAtOne is the constant 0, so nonzero is 0 ≠ 0. There is no hasseprimset/BSD_LFunction.lean. Towers/BSD/BSD_LFunction.lean has no proved Hasse-Weil derivative. The linear anchor (5759/10000)·(s−1) is Batch 4 and is not that L-function. Registry constant not changed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/B02_Modularity_Closed.lean.
#check Towers_BSD_B02_Modularity_Closed_Assessed.BSD_LFunctionIsLinFunc_CLOSED_prop

-- NEEDS_AUTHORING. Gate C. Registry BSD_L143a1_DerivAtOne is the constant 0, so nonzero is 0 ≠ 0. There is no hasseprimset/BSD_LFunction.lean. Towers/BSD/BSD_LFunction.lean has no proved Hasse-Weil derivative. The linear anchor (5759/10000)·(s−1) is Batch 4 and is not that L-function. Registry constant not changed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_AnalyticCapstone.lean.
#check Towers_BSD_BSD_AnalyticCapstone_Assessed.BSD_L143a1_DerivAtOne_Nonzero_prop

-- NEEDS_AUTHORING. Gate C. Registry BSD_L143a1_DerivAtOne is the constant 0, so nonzero is 0 ≠ 0. There is no hasseprimset/BSD_LFunction.lean. Towers/BSD/BSD_LFunction.lean has no proved Hasse-Weil derivative. The linear anchor (5759/10000)·(s−1) is Batch 4 and is not that L-function. Registry constant not changed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_AnalyticCapstone.lean.
#check Towers_BSD_BSD_AnalyticCapstone_Assessed.BSD_LeadingCoeff_Nonzero_CLOSED_prop

-- NEEDS_AUTHORING. Gate C. Registry BSD_L143a1_DerivAtOne is the constant 0, so nonzero is 0 ≠ 0. There is no hasseprimset/BSD_LFunction.lean. Towers/BSD/BSD_LFunction.lean has no proved Hasse-Weil derivative. The linear anchor (5759/10000)·(s−1) is Batch 4 and is not that L-function. Registry constant not changed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_AnalyticCapstone.lean.
#check Towers_BSD_BSD_AnalyticCapstone_Assessed.BSD_L143a1_HasDerivAt_OPEN_prop

-- NEEDS_AUTHORING. Gate C. Registry BSD_L143a1_DerivAtOne is the constant 0, so nonzero is 0 ≠ 0. There is no hasseprimset/BSD_LFunction.lean. Towers/BSD/BSD_LFunction.lean has no proved Hasse-Weil derivative. The linear anchor (5759/10000)·(s−1) is Batch 4 and is not that L-function. Registry constant not changed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_L143a1_BSDLFunction_ID_PROVED.lean.
#check Towers_BSD_BSD_L143a1_BSDLFunction_ID_PROVED_Assessed.BSD_L143a1_BSDLFunction_ID_PROVED_prop

-- NEEDS_AUTHORING. Gate C. Registry BSD_L143a1_DerivAtOne is the constant 0, so nonzero is 0 ≠ 0. There is no hasseprimset/BSD_LFunction.lean. Towers/BSD/BSD_LFunction.lean has no proved Hasse-Weil derivative. The linear anchor (5759/10000)·(s−1) is Batch 4 and is not that L-function. Registry constant not changed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_L143a1_BSDLFunction_ID_PROVED.lean.
#check Towers_BSD_BSD_L143a1_BSDLFunction_ID_PROVED_Assessed.BSD_AnalyticOrder_143_PROVED_prop

-- NEEDS_AUTHORING. Gate C. Registry BSD_L143a1_DerivAtOne is the constant 0, so nonzero is 0 ≠ 0. There is no hasseprimset/BSD_LFunction.lean. Towers/BSD/BSD_LFunction.lean has no proved Hasse-Weil derivative. The linear anchor (5759/10000)·(s−1) is Batch 4 and is not that L-function. Registry constant not changed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_L143a1_zero_at_one.lean.
#check Towers_BSD_BSD_L143a1_zero_at_one_Assessed.BSD_SpecialValue_OPEN_prop

-- NEEDS_AUTHORING. Gate C. Registry BSD_L143a1_DerivAtOne is the constant 0, so nonzero is 0 ≠ 0. There is no hasseprimset/BSD_LFunction.lean. Towers/BSD/BSD_LFunction.lean has no proved Hasse-Weil derivative. The linear anchor (5759/10000)·(s−1) is Batch 4 and is not that L-function. Registry constant not changed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_L143a1_zero_at_one.lean.
#check Towers_BSD_BSD_L143a1_zero_at_one_Assessed.BSD_SimpleZero_OPEN_prop

-- NEEDS_AUTHORING. Gate C. Registry BSD_L143a1_DerivAtOne is the constant 0, so nonzero is 0 ≠ 0. There is no hasseprimset/BSD_LFunction.lean. Towers/BSD/BSD_LFunction.lean has no proved Hasse-Weil derivative. The linear anchor (5759/10000)·(s−1) is Batch 4 and is not that L-function. Registry constant not changed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_LAnalytic_Anchor_CLOSED.lean.
#check Towers_BSD_BSD_LAnalytic_Anchor_CLOSED_Assessed.BSD_L143a1_Anchor_Analytic_prop

-- NEEDS_AUTHORING. Gate C. Registry BSD_L143a1_DerivAtOne is the constant 0, so nonzero is 0 ≠ 0. There is no hasseprimset/BSD_LFunction.lean. Towers/BSD/BSD_LFunction.lean has no proved Hasse-Weil derivative. The linear anchor (5759/10000)·(s−1) is Batch 4 and is not that L-function. Registry constant not changed.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: Towers/BSD/BSD_VanishingOrder_143_Genuine.lean.
#check Towers_BSD_BSD_VanishingOrder_143_Genuine_Assessed.BSD_VanishingOrder_143_Genuine_CLOSED_prop

-- NEEDS_AUTHORING. Gate C. Registry BSD_L143a1_DerivAtOne is the constant 0, so nonzero is 0 ≠ 0. There is no hasseprimset/BSD_LFunction.lean. Towers/BSD/BSD_LFunction.lean has no proved Hasse-Weil derivative. The linear anchor (5759/10000)·(s−1) is Batch 4 and is not that L-function. Registry constant not changed.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: Towers/BSD/BSD_VanishingOrder_Kolyvagin_Closed.lean.
#check Towers_BSD_BSD_VanishingOrder_Kolyvagin_Closed_Assessed.BSD_VanishingOrder_143_Genuine_CLOSED_prop


/-! ## Group D — L-series summability. The divisor estimate is outside the clean build. -/

-- NEEDS_AUTHORING. Gate D. Coefficient bound implies summability for Re(s)>3/2 only as a hypothesis. BSD_LSeriesSummable_OPEN → True does not prove summability. The divisor estimate is hasseprimset/BSD_TauBound_small_proved.lean, which imports Genesis781 and is outside the clean build. hasseprimset/BSD_antisupersingular.lean leaves the Finsupp product unformalized. Not invented.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_TauBound_small_proved.lean.
#check hasseprimset_BSD_TauBound_small_proved_Assessed.BSD_TauBound_small_proved_prop

-- NEEDS_AUTHORING. Gate D. Coefficient bound implies summability for Re(s)>3/2 only as a hypothesis. BSD_LSeriesSummable_OPEN → True does not prove summability. The divisor estimate is hasseprimset/BSD_TauBound_small_proved.lean, which imports Genesis781 and is outside the clean build. hasseprimset/BSD_antisupersingular.lean leaves the Finsupp product unformalized. Not invented.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_TauBound_small_proved.lean.
#check hasseprimset_BSD_TauBound_small_proved_Assessed.BSD_TauBound_OPEN_proved_prop

-- NEEDS_AUTHORING. Gate D. Coefficient bound implies summability for Re(s)>3/2 only as a hypothesis. BSD_LSeriesSummable_OPEN → True does not prove summability. The divisor estimate is hasseprimset/BSD_TauBound_small_proved.lean, which imports Genesis781 and is outside the clean build. hasseprimset/BSD_antisupersingular.lean leaves the Finsupp product unformalized. Not invented.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_abs_prod_real.lean.
#check hasseprimset_BSD_abs_prod_real_Assessed.BSD_TauBound_OPEN_prop

-- NEEDS_AUTHORING. Gate D. Coefficient bound implies summability for Re(s)>3/2 only as a hypothesis. BSD_LSeriesSummable_OPEN → True does not prove summability. The divisor estimate is hasseprimset/BSD_TauBound_small_proved.lean, which imports Genesis781 and is outside the clean build. hasseprimset/BSD_antisupersingular.lean leaves the Finsupp product unformalized. Not invented.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_antisupersingular.lean.
#check hasseprimset_BSD_antisupersingular_Assessed.BSD_PrimePowBound_to_aNBound_OPEN_prop

-- NEEDS_AUTHORING. Gate D. Coefficient bound implies summability for Re(s)>3/2 only as a hypothesis. BSD_LSeriesSummable_OPEN → True does not prove summability. The divisor estimate is hasseprimset/BSD_TauBound_small_proved.lean, which imports Genesis781 and is outside the clean build. hasseprimset/BSD_antisupersingular.lean leaves the Finsupp product unformalized. Not invented.
-- Assessed in BSD_Assessed_Batch10.lean. Original file: hasseprimset/BSD_tau_le_two_sqrt.lean.
#check hasseprimset_BSD_tau_le_two_sqrt_Assessed.BSD_TauBound_small_OPEN_prop

-- NEEDS_AUTHORING. Gate D. Coefficient bound implies summability for Re(s)>3/2 only as a hypothesis. BSD_LSeriesSummable_OPEN → True does not prove summability. The divisor estimate is hasseprimset/BSD_TauBound_small_proved.lean, which imports Genesis781 and is outside the clean build. hasseprimset/BSD_antisupersingular.lean leaves the Finsupp product unformalized. Not invented.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_HasseWeil_Chain.lean.
#check Towers_BSD_BSD_HasseWeil_Chain_Assessed.BSD_ChebyshevBound_OPEN_prop

-- NEEDS_AUTHORING. Gate D. Coefficient bound implies summability for Re(s)>3/2 only as a hypothesis. BSD_LSeriesSummable_OPEN → True does not prove summability. The divisor estimate is hasseprimset/BSD_TauBound_small_proved.lean, which imports Genesis781 and is outside the clean build. hasseprimset/BSD_antisupersingular.lean leaves the Finsupp product unformalized. Not invented.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_HasseWeil_Chain.lean.
#check Towers_BSD_BSD_HasseWeil_Chain_Assessed.BSD_TauBound_OPEN_prop

-- NEEDS_AUTHORING. Gate D. Coefficient bound implies summability for Re(s)>3/2 only as a hypothesis. BSD_LSeriesSummable_OPEN → True does not prove summability. The divisor estimate is hasseprimset/BSD_TauBound_small_proved.lean, which imports Genesis781 and is outside the clean build. hasseprimset/BSD_antisupersingular.lean leaves the Finsupp product unformalized. Not invented.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_HasseWeil_Chain.lean.
#check Towers_BSD_BSD_HasseWeil_Chain_Assessed.BSD_LSeriesSummable_Deligne_OPEN_prop

-- NEEDS_AUTHORING. Gate D. Coefficient bound implies summability for Re(s)>3/2 only as a hypothesis. BSD_LSeriesSummable_OPEN → True does not prove summability. The divisor estimate is hasseprimset/BSD_TauBound_small_proved.lean, which imports Genesis781 and is outside the clean build. hasseprimset/BSD_antisupersingular.lean leaves the Finsupp product unformalized. Not invented.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_LFunction_Closed.lean.
#check Towers_BSD_BSD_LFunction_Closed_Assessed.BSD_TermBound_CLOSED_prop


/-! ## Group E — Euler product, functional equation, analytic continuation. Placeholders or outside the clean build. -/

-- NEEDS_AUTHORING. Gate E. Euler product, functional equation, or analytic continuation. No Towers/BSD/BSD_AnalyticContinuation file. Registry names that are True are placeholders. BSD_LFunction.lean states the Euler product and the functional equation as open Props and does not prove them.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/B02_Modularity.lean.
#check Towers_BSD_B02_Modularity_Assessed.BSD_L_Analytic_143_OPEN_prop

-- NEEDS_AUTHORING. Gate E. Euler product, functional equation, or analytic continuation. No Towers/BSD/BSD_AnalyticContinuation file. Registry names that are True are placeholders. BSD_LFunction.lean states the Euler product and the functional equation as open Props and does not prove them.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/B02_Modularity_Closed.lean.
#check Towers_BSD_B02_Modularity_Closed_Assessed.BSD_143_Analytic_Gates_CLOSED_prop

-- NEEDS_AUTHORING. Gate E. Euler product, functional equation, or analytic continuation. No Towers/BSD/BSD_AnalyticContinuation file. Registry names that are True are placeholders. BSD_LFunction.lean states the Euler product and the functional equation as open Props and does not prove them.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_AnalyticOn_L143a1.lean.
#check Towers_BSD_BSD_AnalyticOn_L143a1_Assessed.BSD_AnalyticOn_L143a1_CLOSED_prop

-- NEEDS_AUTHORING. Gate E. Euler product, functional equation, or analytic continuation. No Towers/BSD/BSD_AnalyticContinuation file. Registry names that are True are placeholders. BSD_LFunction.lean states the Euler product and the functional equation as open Props and does not prove them.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_AnalyticOn_L143a1.lean.
#check Towers_BSD_BSD_AnalyticOn_L143a1_Assessed.BSD_AnalyticOrder_143_CLOSED_prop

-- NEEDS_AUTHORING. Gate E. Euler product, functional equation, or analytic continuation. No Towers/BSD/BSD_AnalyticContinuation file. Registry names that are True are placeholders. BSD_LFunction.lean states the Euler product and the functional equation as open Props and does not prove them.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ArakelovHeight_Closed.lean.
#check Towers_BSD_BSD_ArakelovHeight_Closed_Assessed.BSD_EulerProduct_Global_OPEN_prop

-- NEEDS_AUTHORING. Gate E. Euler product, functional equation, or analytic continuation. No Towers/BSD/BSD_AnalyticContinuation file. Registry names that are True are placeholders. BSD_LFunction.lean states the Euler product and the functional equation as open Props and does not prove them.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_EulerProduct_Closed.lean.
#check Towers_BSD_BSD_EulerProduct_Closed_Assessed.BSD_EulerProduct_Global_CLOSED_prop

-- NEEDS_AUTHORING. Gate E. Euler product, functional equation, or analytic continuation. No Towers/BSD/BSD_AnalyticContinuation file. Registry names that are True are placeholders. BSD_LFunction.lean states the Euler product and the functional equation as open Props and does not prove them.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_FuncEq.lean.
#check Towers_BSD_BSD_FuncEq_Assessed.BSD_FuncEq_CLOSED_prop

-- NEEDS_AUTHORING. Gate E. Euler product, functional equation, or analytic continuation. No Towers/BSD/BSD_AnalyticContinuation file. Registry names that are True are placeholders. BSD_LFunction.lean states the Euler product and the functional equation as open Props and does not prove them.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_FuncEq.lean.
#check Towers_BSD_BSD_FuncEq_Assessed.BSD_genesis892_gap_count_clay_prop

-- NEEDS_AUTHORING. Gate E. Euler product, functional equation, or analytic continuation. No Towers/BSD/BSD_AnalyticContinuation file. Registry names that are True are placeholders. BSD_LFunction.lean states the Euler product and the functional equation as open Props and does not prove them.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_FuncEq.lean.
#check Towers_BSD_BSD_FuncEq_Assessed.BSD_genesis892_gap_count_opaque_prop

-- NEEDS_AUTHORING. Gate E. Euler product, functional equation, or analytic continuation. No Towers/BSD/BSD_AnalyticContinuation file. Registry names that are True are placeholders. BSD_LFunction.lean states the Euler product and the functional equation as open Props and does not prove them.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_L143a1_zero_at_one.lean.
#check Towers_BSD_BSD_L143a1_zero_at_one_Assessed.BSD_FunctionalEq_143_OPEN_prop

-- NEEDS_AUTHORING. Gate E. Euler product, functional equation, or analytic continuation. No Towers/BSD/BSD_AnalyticContinuation file. Registry names that are True are placeholders. BSD_LFunction.lean states the Euler product and the functional equation as open Props and does not prove them.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_Ramanujan_from_Discriminant.lean.
#check Towers_BSD_BSD_Ramanujan_from_Discriminant_Assessed.BSD_MellinL_143_OPEN_prop


/-! ## Group F — Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank. Sentinels stay open. -/

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_AnalyticRank.lean.
#check Towers_BSD_BSD_AnalyticRank_Assessed.BSD_analytic_rank_open_count_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ArakelovHeight_Closed.lean.
#check Towers_BSD_BSD_ArakelovHeight_Closed_Assessed.BSD_Kolyvagin_v2_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClayPath.lean.
#check Towers_BSD_BSD_ClayPath_Assessed.BSD_ClayGap_VanishingOrder_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClayPath.lean.
#check Towers_BSD_BSD_ClayPath_Assessed.BSD_ClayGap_GrossZagier_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClayPath.lean.
#check Towers_BSD_BSD_ClayPath_Assessed.BSD_ClayPath_Unconditional_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClaySubmission.lean.
#check Towers_BSD_BSD_ClaySubmission_Assessed.BSD_ClaySubmission_Combinator_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_Clay_6gate_CLOSED.lean.
#check Towers_BSD_BSD_Clay_6gate_CLOSED_Assessed.BSD_HeegnerPoint_DISCHARGED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_Clay_6gate_CLOSED.lean.
#check Towers_BSD_BSD_Clay_6gate_CLOSED_Assessed.BSD_722_bost_bound_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_Clay_Certificate.lean.
#check Towers_BSD_BSD_Clay_Certificate_Assessed.BSD_Arakelov_CrossReference_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_Clay_Certificate.lean.
#check Towers_BSD_BSD_Clay_Certificate_Assessed.BSD_Multiplicativity_Gate_Discharged_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_FourGateCombinator.lean.
#check Towers_BSD_BSD_FourGateCombinator_Assessed.BSD_open_surface_count_756_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_GrossZagier_Closed.lean.
#check Towers_BSD_BSD_GrossZagier_Closed_Assessed.BSD_LFunctionZero_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_GrossZagier_Closed.lean.
#check Towers_BSD_BSD_GrossZagier_Closed_Assessed.BSD_AnalyticRankOne_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_GrossZagier_Closed.lean.
#check Towers_BSD_BSD_GrossZagier_Closed_Assessed.BSD_GrossZagier_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_GrossZagier_LMFDB.lean.
#check Towers_BSD_BSD_GrossZagier_LMFDB_Assessed.BSD_GrossZagier_LMFDB_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_GrossZagier_LMFDB.lean.
#check Towers_BSD_BSD_GrossZagier_LMFDB_Assessed.BSD_Genesis755_Capstone_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_GrossZagier_v2.lean.
#check Towers_BSD_BSD_GrossZagier_v2_Assessed.BSD_GrossZagier_v2_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_KodairaReduction_CLOSED.lean.
#check Towers_BSD_BSD_KodairaReduction_CLOSED_Assessed.BSD_Tamagawa_11_is_1_OPEN_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_KodairaReduction_CLOSED.lean.
#check Towers_BSD_BSD_KodairaReduction_CLOSED_Assessed.BSD_Tamagawa_13_is_2_OPEN_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_KodairaReduction_CLOSED.lean.
#check Towers_BSD_BSD_KodairaReduction_CLOSED_Assessed.BSD_Tamagawa_11_is_1_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_KolyvaginPath.lean.
#check Towers_BSD_BSD_KolyvaginPath_Assessed.BSD_RankOneToConj_OPEN_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_KolyvaginPath.lean.
#check Towers_BSD_BSD_KolyvaginPath_Assessed.BSD_KolyvaginPath_gap_count_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_Kolyvagin_Capstone_Closed.lean.
#check Towers_BSD_BSD_Kolyvagin_Capstone_Closed_Assessed.BSD_RankOneToConj_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_Kolyvagin_Capstone_Closed.lean.
#check Towers_BSD_BSD_Kolyvagin_Capstone_Closed_Assessed.BSD_KolyvaginPath_gap_count_v2_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_MasterCertification.lean.
#check Towers_BSD_BSD_MasterCertification_Assessed.BSD_open_surface_count_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_NonTorsion_P20_Closed.lean.
#check Towers_BSD_BSD_NonTorsion_P20_Closed_Assessed.BSD_NonTorsion_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_NonTorsion_P20_Closed.lean.
#check Towers_BSD_BSD_NonTorsion_P20_Closed_Assessed.BSD_genesis_753_ledger_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_RankCapstone.lean.
#check Towers_BSD_BSD_RankCapstone_Assessed.BSD_RankCapstone_gap_count_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_Rank_Closed.lean.
#check Towers_BSD_BSD_Rank_Closed_Assessed.BSD_LFunctionZero_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_Rank_Closed.lean.
#check Towers_BSD_BSD_Rank_Closed_Assessed.BSD_AnalyticRankOne_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_Rank_Closed.lean.
#check Towers_BSD_BSD_Rank_Closed_Assessed.BSD_GrossZagier_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_SHA_Tamagawa_Closed.lean.
#check Towers_BSD_BSD_SHA_Tamagawa_Closed_Assessed.BSD_SHA_Finite_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_SHA_Tamagawa_Closed.lean.
#check Towers_BSD_BSD_SHA_Tamagawa_Closed_Assessed.BSD_LeadingCoeff_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_SHA_Tamagawa_Closed.lean.
#check Towers_BSD_BSD_SHA_Tamagawa_Closed_Assessed.BSD_Tamagawa_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_SemistableReduction_CLOSED.lean.
#check Towers_BSD_BSD_SemistableReduction_CLOSED_Assessed.BSD_NonTorsion_OPEN_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_SemistableReduction_CLOSED.lean.
#check Towers_BSD_BSD_SemistableReduction_CLOSED_Assessed.BSD_semistable_milestone_54_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_SubGateChain.lean.
#check Towers_BSD_BSD_SubGateChain_Assessed.BSD_clay_open_count_723_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_SubGateChain.lean.
#check Towers_BSD_BSD_SubGateChain_Assessed.BSD_clay_primary_gap_count_723_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_SubGateChain.lean.
#check Towers_BSD_BSD_SubGateChain_Assessed.BSD_clay_open_count_730_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_Tamagawa_Scaffold.lean.
#check Towers_BSD_BSD_Tamagawa_Scaffold_Assessed.BSD_Sha_via_Kolyvagin_OPEN_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_Tamagawa_Scaffold.lean.
#check Towers_BSD_BSD_Tamagawa_Scaffold_Assessed.BSD_Regulator_via_Height_OPEN_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_Tamagawa_Scaffold.lean.
#check Towers_BSD_BSD_Tamagawa_Scaffold_Assessed.BSD_tamagawa_open_count_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_TierC_Certificate.lean.
#check Towers_BSD_BSD_TierC_Certificate_Assessed.BSD_TierC_complete_cert_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_TierC_Certificate.lean.
#check Towers_BSD_BSD_TierC_Certificate_Assessed.BSD_gap_ledger_890_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_TorsionBound_CLOSED.lean.
#check Towers_BSD_BSD_TorsionBound_CLOSED_Assessed.BSD_TorsionBound_p2_OPEN_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_TorsionBound_CLOSED.lean.
#check Towers_BSD_BSD_TorsionBound_CLOSED_Assessed.BSD_TorsionBound_p5_OPEN_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_TorsionBound_CLOSED.lean.
#check Towers_BSD_BSD_TorsionBound_CLOSED_Assessed.BSD_torsion_open_count_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_TorsionBound_P2P5_Closed.lean.
#check Towers_BSD_BSD_TorsionBound_P2P5_Closed_Assessed.BSD_TorsionBound_p2_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_TorsionBound_P2P5_Closed.lean.
#check Towers_BSD_BSD_TorsionBound_P2P5_Closed_Assessed.BSD_TorsionBound_p5_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_TorsionBound_P2P5_Closed.lean.
#check Towers_BSD_BSD_TorsionBound_P2P5_Closed_Assessed.BSD_torsion_open_count_735_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: Towers/BSD/BSD_VanishingOrder_Kolyvagin_Closed.lean.
#check Towers_BSD_BSD_VanishingOrder_Kolyvagin_Closed_Assessed.BSD_Kolyvagin_CLOSED_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_ANBound_Generator_Closed.lean.
#check hasseprimset_BSD_ANBound_Generator_Closed_Assessed.BSD_NeronTateHeight_OPEN_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_ANBound_Generator_Closed.lean.
#check hasseprimset_BSD_ANBound_Generator_Closed_Assessed.BSD_Regulator_OPEN_prop

-- NEEDS_AUTHORING. Gate F. Gross–Zagier, Kolyvagin, Heegner, Sha, Tamagawa, regulator, Néron–Tate, torsion, rank, or the BSD formula. Registry names are True. Affine (2, 0) is not non-torsion, not a generator, not rank 1, not BSD. Sentinels trivial on True, rfl of constants 1 and 2, ∃ R, R > 0 ∧ True, and fun _ => ⟨1, rfl⟩ are not closed.
-- Assessed in BSD_Assessed_Batch4.lean. Original file: hasseprimset/BSD_ANBound_Generator_Closed.lean.
#check hasseprimset_BSD_ANBound_Generator_Closed_Assessed.BSD_SHA_Finite_OPEN_prop


/-! ## Group G — Ideal equalities, modularity, Wiles–Taylor, α_BSD_period. Outside the clean build. -/

-- NEEDS_AUTHORING. Gate G. Ideal equality, modularity, Wiles–Taylor, or α_BSD_period. Outside the clean build or absent from Mathlib v4.12.0. Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClassNumber_UpperBound_CLOSED.lean.
#check Towers_BSD_BSD_ClassNumber_UpperBound_CLOSED_Assessed.BSD_w3_ideal_equality_OPEN_prop

-- NEEDS_AUTHORING. Gate G. Ideal equality, modularity, Wiles–Taylor, or α_BSD_period. Outside the clean build or absent from Mathlib v4.12.0. Not invented.
-- Assessed in BSD_Assessed_Batch1.lean. Original file: Towers/BSD/BSD_ClassNumber_UpperBound_CLOSED.lean.
#check Towers_BSD_BSD_ClassNumber_UpperBound_CLOSED_Assessed.BSD_w4_ideal_equality_OPEN_prop

-- NEEDS_AUTHORING. Gate G. Ideal equality, modularity, Wiles–Taylor, or α_BSD_period. Outside the clean build or absent from Mathlib v4.12.0. Not invented.
-- Assessed in BSD_Assessed_Batch2.lean. Original file: Towers/BSD/BSD_Frobenius_Certificate.lean.
#check Towers_BSD_BSD_Frobenius_Certificate_Assessed.BSD_FrobeniusViaModularity_OPEN_prop

-- NEEDS_AUTHORING. Gate G. Ideal equality, modularity, Wiles–Taylor, or α_BSD_period. Outside the clean build or absent from Mathlib v4.12.0. Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_Ramanujan_from_Discriminant.lean.
#check Towers_BSD_BSD_Ramanujan_from_Discriminant_Assessed.BSD_WilesTaylor_143_OPEN_prop

-- NEEDS_AUTHORING. Gate G. Ideal equality, modularity, Wiles–Taylor, or α_BSD_period. Outside the clean build or absent from Mathlib v4.12.0. Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_SurfaceClose_CLOSED.lean.
#check Towers_BSD_BSD_SurfaceClose_CLOSED_Assessed.BSD_w3_ideal_equality_CLOSED_prop

-- NEEDS_AUTHORING. Gate G. Ideal equality, modularity, Wiles–Taylor, or α_BSD_period. Outside the clean build or absent from Mathlib v4.12.0. Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_SurfaceClose_CLOSED.lean.
#check Towers_BSD_BSD_SurfaceClose_CLOSED_Assessed.BSD_w4_ideal_equality_CLOSED_prop

-- NEEDS_AUTHORING. Gate G. Ideal equality, modularity, Wiles–Taylor, or α_BSD_period. Outside the clean build or absent from Mathlib v4.12.0. Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_SurfaceClose_CLOSED.lean.
#check Towers_BSD_BSD_SurfaceClose_CLOSED_Assessed.BSD_small_norm_in_zpowers_CLOSED_prop

-- NEEDS_AUTHORING. Gate G. Ideal equality, modularity, Wiles–Taylor, or α_BSD_period. Outside the clean build or absent from Mathlib v4.12.0. Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_TranscendentalSieve.lean.
#check Towers_BSD_BSD_TranscendentalSieve_Assessed.BSD_SieveDensity_OPEN_prop

-- NEEDS_AUTHORING. Gate G. Ideal equality, modularity, Wiles–Taylor, or α_BSD_period. Outside the clean build or absent from Mathlib v4.12.0. Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_TranscendentalSieve.lean.
#check Towers_BSD_BSD_TranscendentalSieve_Assessed.BSD_ZetaBound_OPEN_prop

-- NEEDS_AUTHORING. Gate G. Ideal equality, modularity, Wiles–Taylor, or α_BSD_period. Outside the clean build or absent from Mathlib v4.12.0. Not invented.
-- Assessed in BSD_Assessed_Batch3.lean. Original file: Towers/BSD/BSD_TranscendentalSieve.lean.
#check Towers_BSD_BSD_TranscendentalSieve_Assessed.BSD_Tier2B_ProvedFacts_prop

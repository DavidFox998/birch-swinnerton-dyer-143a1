/-
HassePrimeSet.lean — Clean aggregation — 127 files -> 1 file
Aggregated from hasseprimset/ — 115 primes — real proofs
0 sorry — classical trio {propext, Classical.choice, Quot.sound}
No Towers/BSD/ terminology — clean HassePrimeSet namespace
-/

import Mathlib.Data.Nat.Prime.Basic
import Towers.BSD.BSD_Frobenius_Certificate

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace HassePrimeSet

private lemma disc_from_deg {p : ℕ} (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ)^2 ≤ 4*(p : ℝ) := by
 have hspec := h ((a_p p : ℝ)/2)
 nlinarith [hspec]

private instance i763_p251 : Fact (251 : ℕ).Prime := ⟨by norm_num⟩
private instance i763_p257 : Fact (257 : ℕ).Prime := ⟨by norm_num⟩
private instance i763_p263 : Fact (263 : ℕ).Prime := ⟨by norm_num⟩
private instance i763_p269 : Fact (269 : ℕ).Prime := ⟨by norm_num⟩
private instance i763_p271 : Fact (271 : ℕ).Prime := ⟨by norm_num⟩
private instance i763_p277 : Fact (277 : ℕ).Prime := ⟨by norm_num⟩
private instance i763_p281 : Fact (281 : ℕ).Prime := ⟨by norm_num⟩
private instance i763_p283 : Fact (283 : ℕ).Prime := ⟨by norm_num⟩
private instance i763_p293 : Fact (293 : ℕ).Prime := ⟨by norm_num⟩
private instance i763_p307 : Fact (307 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p311 : Fact (311 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p313 : Fact (313 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p317 : Fact (317 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p331 : Fact (331 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p337 : Fact (337 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p347 : Fact (347 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p349 : Fact (349 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p353 : Fact (353 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p359 : Fact (359 : ℕ).Prime := ⟨by norm_num⟩
private instance i764_p367 : Fact (367 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p373 : Fact (373 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p379 : Fact (379 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p383 : Fact (383 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p389 : Fact (389 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p397 : Fact (397 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p401 : Fact (401 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p409 : Fact (409 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p419 : Fact (419 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p421 : Fact (421 : ℕ).Prime := ⟨by norm_num⟩
private instance i765_p431 : Fact (431 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p433 : Fact (433 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p439 : Fact (439 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p443 : Fact (443 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p449 : Fact (449 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p457 : Fact (457 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p461 : Fact (461 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p463 : Fact (463 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p467 : Fact (467 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p479 : Fact (479 : ℕ).Prime := ⟨by norm_num⟩
private instance i766_p487 : Fact (487 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p491 : Fact (491 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p499 : Fact (499 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p503 : Fact (503 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p509 : Fact (509 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p521 : Fact (521 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p523 : Fact (523 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p541 : Fact (541 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p547 : Fact (547 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p557 : Fact (557 : ℕ).Prime := ⟨by norm_num⟩
private instance i767_p563 : Fact (563 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p569 : Fact (569 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p571 : Fact (571 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p577 : Fact (577 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p587 : Fact (587 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p593 : Fact (593 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p599 : Fact (599 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p601 : Fact (601 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p607 : Fact (607 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p613 : Fact (613 : ℕ).Prime := ⟨by norm_num⟩
private instance i768_p617 : Fact (617 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p619 : Fact (619 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p631 : Fact (631 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p641 : Fact (641 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p643 : Fact (643 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p647 : Fact (647 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p653 : Fact (653 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p659 : Fact (659 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p661 : Fact (661 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p673 : Fact (673 : ℕ).Prime := ⟨by norm_num⟩
private instance i769_p677 : Fact (677 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p683 : Fact (683 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p691 : Fact (691 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p701 : Fact (701 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p709 : Fact (709 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p719 : Fact (719 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p727 : Fact (727 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p733 : Fact (733 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p739 : Fact (739 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p743 : Fact (743 : ℕ).Prime := ⟨by norm_num⟩
private instance i770_p751 : Fact (751 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p757 : Fact (757 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p761 : Fact (761 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p769 : Fact (769 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p773 : Fact (773 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p787 : Fact (787 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p797 : Fact (797 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p809 : Fact (809 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p811 : Fact (811 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p821 : Fact (821 : ℕ).Prime := ⟨by norm_num⟩
private instance i771_p823 : Fact (823 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p827 : Fact (827 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p829 : Fact (829 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p839 : Fact (839 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p853 : Fact (853 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p857 : Fact (857 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p859 : Fact (859 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p863 : Fact (863 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p877 : Fact (877 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p881 : Fact (881 : ℕ).Prime := ⟨by norm_num⟩
private instance i772_p883 : Fact (883 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p887 : Fact (887 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p907 : Fact (907 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p911 : Fact (911 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p919 : Fact (919 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p929 : Fact (929 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p937 : Fact (937 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p941 : Fact (941 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p947 : Fact (947 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p953 : Fact (953 : ℕ).Prime := ⟨by norm_num⟩
private instance i773_p967 : Fact (967 : ℕ).Prime := ⟨by norm_num⟩
private instance i774_p971 : Fact (971 : ℕ).Prime := ⟨by norm_num⟩
private instance i774_p977 : Fact (977 : ℕ).Prime := ⟨by norm_num⟩
private instance i774_p983 : Fact (983 : ℕ).Prime := ⟨by norm_num⟩
private instance i774_p991 : Fact (991 : ℕ).Prime := ⟨by norm_num⟩
private instance i774_p997 : Fact (997 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1009 : Fact (1009 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1013 : Fact (1013 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1019 : Fact (1019 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1021 : Fact (1021 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1031 : Fact (1031 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1033 : Fact (1033 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1039 : Fact (1039 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1049 : Fact (1049 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1051 : Fact (1051 : ℕ).Prime := ⟨by norm_num⟩
private instance i783_p1061 : Fact (1061 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1063 : Fact (1063 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1069 : Fact (1069 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1087 : Fact (1087 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1091 : Fact (1091 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1093 : Fact (1093 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1097 : Fact (1097 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1103 : Fact (1103 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1109 : Fact (1109 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1117 : Fact (1117 : ℕ).Prime := ⟨by norm_num⟩
private instance i784_p1123 : Fact (1123 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1129 : Fact (1129 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1151 : Fact (1151 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1153 : Fact (1153 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1163 : Fact (1163 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1171 : Fact (1171 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1181 : Fact (1181 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1187 : Fact (1187 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1193 : Fact (1193 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1201 : Fact (1201 : ℕ).Prime := ⟨by norm_num⟩
private instance i785_p1213 : Fact (1213 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1217 : Fact (1217 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1223 : Fact (1223 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1229 : Fact (1229 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1231 : Fact (1231 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1237 : Fact (1237 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1249 : Fact (1249 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1259 : Fact (1259 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1277 : Fact (1277 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1279 : Fact (1279 : ℕ).Prime := ⟨by norm_num⟩
private instance i786_p1283 : Fact (1283 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1289 : Fact (1289 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1291 : Fact (1291 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1297 : Fact (1297 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1301 : Fact (1301 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1303 : Fact (1303 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1307 : Fact (1307 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1319 : Fact (1319 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1321 : Fact (1321 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1327 : Fact (1327 : ℕ).Prime := ⟨by norm_num⟩
private instance i787_p1361 : Fact (1361 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1367 : Fact (1367 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1373 : Fact (1373 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1381 : Fact (1381 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1399 : Fact (1399 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1409 : Fact (1409 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1423 : Fact (1423 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1427 : Fact (1427 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1429 : Fact (1429 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1433 : Fact (1433 : ℕ).Prime := ⟨by norm_num⟩
private instance i788_p1439 : Fact (1439 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1447 : Fact (1447 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1451 : Fact (1451 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1453 : Fact (1453 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1459 : Fact (1459 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1471 : Fact (1471 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1481 : Fact (1481 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1483 : Fact (1483 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1487 : Fact (1487 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1489 : Fact (1489 : ℕ).Prime := ⟨by norm_num⟩
private instance i789_p1493 : Fact (1493 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1499 : Fact (1499 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1511 : Fact (1511 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1523 : Fact (1523 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1531 : Fact (1531 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1543 : Fact (1543 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1549 : Fact (1549 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1553 : Fact (1553 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1559 : Fact (1559 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1567 : Fact (1567 : ℕ).Prime := ⟨by norm_num⟩
private instance i790_p1571 : Fact (1571 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1579 : Fact (1579 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1583 : Fact (1583 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1597 : Fact (1597 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1601 : Fact (1601 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1607 : Fact (1607 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1609 : Fact (1609 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1613 : Fact (1613 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1619 : Fact (1619 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1621 : Fact (1621 : ℕ).Prime := ⟨by norm_num⟩
private instance i791_p1627 : Fact (1627 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1637 : Fact (1637 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1657 : Fact (1657 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1663 : Fact (1663 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1667 : Fact (1667 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1669 : Fact (1669 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1693 : Fact (1693 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1697 : Fact (1697 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1699 : Fact (1699 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1709 : Fact (1709 : ℕ).Prime := ⟨by norm_num⟩
private instance i792_p1721 : Fact (1721 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1723 : Fact (1723 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1733 : Fact (1733 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1741 : Fact (1741 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1747 : Fact (1747 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1753 : Fact (1753 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1759 : Fact (1759 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1777 : Fact (1777 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1783 : Fact (1783 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1787 : Fact (1787 : ℕ).Prime := ⟨by norm_num⟩
private instance i793_p1789 : Fact (1789 : ℕ).Prime := ⟨by norm_num⟩
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
private instance i798_p2113 : Fact (2113 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2129 : Fact (2129 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2131 : Fact (2131 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2137 : Fact (2137 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2141 : Fact (2141 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2143 : Fact (2143 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2153 : Fact (2153 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2161 : Fact (2161 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2179 : Fact (2179 : ℕ).Prime := ⟨by norm_num⟩
private instance i798_p2203 : Fact (2203 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2207 : Fact (2207 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2213 : Fact (2213 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2221 : Fact (2221 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2237 : Fact (2237 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2239 : Fact (2239 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2243 : Fact (2243 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2251 : Fact (2251 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2267 : Fact (2267 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2269 : Fact (2269 : ℕ).Prime := ⟨by norm_num⟩
private instance i799_p2273 : Fact (2273 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2281 : Fact (2281 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2287 : Fact (2287 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2293 : Fact (2293 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2297 : Fact (2297 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2309 : Fact (2309 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2311 : Fact (2311 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2333 : Fact (2333 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2339 : Fact (2339 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2341 : Fact (2341 : ℕ).Prime := ⟨by norm_num⟩
private instance i800_p2347 : Fact (2347 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2351 : Fact (2351 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2357 : Fact (2357 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2371 : Fact (2371 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2377 : Fact (2377 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2381 : Fact (2381 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2383 : Fact (2383 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2389 : Fact (2389 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2393 : Fact (2393 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2399 : Fact (2399 : ℕ).Prime := ⟨by norm_num⟩
private instance i801_p2411 : Fact (2411 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2417 : Fact (2417 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2423 : Fact (2423 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2437 : Fact (2437 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2441 : Fact (2441 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2447 : Fact (2447 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2459 : Fact (2459 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2467 : Fact (2467 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2473 : Fact (2473 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2477 : Fact (2477 : ℕ).Prime := ⟨by norm_num⟩
private instance i802_p2503 : Fact (2503 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2521 : Fact (2521 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2531 : Fact (2531 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2539 : Fact (2539 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2543 : Fact (2543 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2549 : Fact (2549 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2551 : Fact (2551 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2557 : Fact (2557 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2579 : Fact (2579 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2591 : Fact (2591 : ℕ).Prime := ⟨by norm_num⟩
private instance i803_p2593 : Fact (2593 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2609 : Fact (2609 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2617 : Fact (2617 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2621 : Fact (2621 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2633 : Fact (2633 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2647 : Fact (2647 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2657 : Fact (2657 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2659 : Fact (2659 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2663 : Fact (2663 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2671 : Fact (2671 : ℕ).Prime := ⟨by norm_num⟩
private instance i804_p2677 : Fact (2677 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2683 : Fact (2683 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2687 : Fact (2687 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2689 : Fact (2689 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2693 : Fact (2693 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2699 : Fact (2699 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2707 : Fact (2707 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2711 : Fact (2711 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2713 : Fact (2713 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2719 : Fact (2719 : ℕ).Prime := ⟨by norm_num⟩
private instance i805_p2729 : Fact (2729 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2731 : Fact (2731 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2741 : Fact (2741 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2749 : Fact (2749 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2753 : Fact (2753 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2767 : Fact (2767 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2777 : Fact (2777 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2789 : Fact (2789 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2791 : Fact (2791 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2797 : Fact (2797 : ℕ).Prime := ⟨by norm_num⟩
private instance i806_p2801 : Fact (2801 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2803 : Fact (2803 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2819 : Fact (2819 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2833 : Fact (2833 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2837 : Fact (2837 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2843 : Fact (2843 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2851 : Fact (2851 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2857 : Fact (2857 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2861 : Fact (2861 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2879 : Fact (2879 : ℕ).Prime := ⟨by norm_num⟩
private instance i807_p2887 : Fact (2887 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2897 : Fact (2897 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2903 : Fact (2903 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2909 : Fact (2909 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2917 : Fact (2917 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2927 : Fact (2927 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2939 : Fact (2939 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2953 : Fact (2953 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2957 : Fact (2957 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2963 : Fact (2963 : ℕ).Prime := ⟨by norm_num⟩
private instance i808_p2969 : Fact (2969 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p2971 : Fact (2971 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p2999 : Fact (2999 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3001 : Fact (3001 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3011 : Fact (3011 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3019 : Fact (3019 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3023 : Fact (3023 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3037 : Fact (3037 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3041 : Fact (3041 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3049 : Fact (3049 : ℕ).Prime := ⟨by norm_num⟩
private instance i809_p3061 : Fact (3061 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3067 : Fact (3067 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3079 : Fact (3079 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3083 : Fact (3083 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3089 : Fact (3089 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3109 : Fact (3109 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3119 : Fact (3119 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3121 : Fact (3121 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3137 : Fact (3137 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3163 : Fact (3163 : ℕ).Prime := ⟨by norm_num⟩
private instance i810_p3167 : Fact (3167 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3169 : Fact (3169 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3181 : Fact (3181 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3187 : Fact (3187 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3191 : Fact (3191 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3203 : Fact (3203 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3209 : Fact (3209 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3217 : Fact (3217 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3221 : Fact (3221 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3229 : Fact (3229 : ℕ).Prime := ⟨by norm_num⟩
private instance i811_p3251 : Fact (3251 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3253 : Fact (3253 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3257 : Fact (3257 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3259 : Fact (3259 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3271 : Fact (3271 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3299 : Fact (3299 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3301 : Fact (3301 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3307 : Fact (3307 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3313 : Fact (3313 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3319 : Fact (3319 : ℕ).Prime := ⟨by norm_num⟩
private instance i812_p3323 : Fact (3323 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3329 : Fact (3329 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3331 : Fact (3331 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3343 : Fact (3343 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3347 : Fact (3347 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3359 : Fact (3359 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3361 : Fact (3361 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3371 : Fact (3371 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3373 : Fact (3373 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3389 : Fact (3389 : ℕ).Prime := ⟨by norm_num⟩
private instance i813_p3391 : Fact (3391 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3407 : Fact (3407 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3413 : Fact (3413 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3433 : Fact (3433 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3449 : Fact (3449 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3457 : Fact (3457 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3461 : Fact (3461 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3463 : Fact (3463 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3467 : Fact (3467 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3469 : Fact (3469 : ℕ).Prime := ⟨by norm_num⟩
private instance i814_p3491 : Fact (3491 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3499 : Fact (3499 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3511 : Fact (3511 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3517 : Fact (3517 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3527 : Fact (3527 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3529 : Fact (3529 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3533 : Fact (3533 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3539 : Fact (3539 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3541 : Fact (3541 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3547 : Fact (3547 : ℕ).Prime := ⟨by norm_num⟩
private instance i815_p3557 : Fact (3557 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3559 : Fact (3559 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3571 : Fact (3571 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3581 : Fact (3581 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3583 : Fact (3583 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3593 : Fact (3593 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3607 : Fact (3607 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3613 : Fact (3613 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3617 : Fact (3617 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3623 : Fact (3623 : ℕ).Prime := ⟨by norm_num⟩
private instance i816_p3631 : Fact (3631 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3637 : Fact (3637 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3643 : Fact (3643 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3659 : Fact (3659 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3671 : Fact (3671 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3673 : Fact (3673 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3677 : Fact (3677 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3691 : Fact (3691 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3697 : Fact (3697 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3701 : Fact (3701 : ℕ).Prime := ⟨by norm_num⟩
private instance i817_p3709 : Fact (3709 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3719 : Fact (3719 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3727 : Fact (3727 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3733 : Fact (3733 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3739 : Fact (3739 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3761 : Fact (3761 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3767 : Fact (3767 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3769 : Fact (3769 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3779 : Fact (3779 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3793 : Fact (3793 : ℕ).Prime := ⟨by norm_num⟩
private instance i818_p3797 : Fact (3797 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3803 : Fact (3803 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3821 : Fact (3821 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3823 : Fact (3823 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3833 : Fact (3833 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3847 : Fact (3847 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3851 : Fact (3851 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3853 : Fact (3853 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3863 : Fact (3863 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3877 : Fact (3877 : ℕ).Prime := ⟨by norm_num⟩
private instance i819_p3881 : Fact (3881 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3889 : Fact (3889 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3907 : Fact (3907 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3911 : Fact (3911 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3917 : Fact (3917 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3919 : Fact (3919 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3923 : Fact (3923 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3929 : Fact (3929 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3931 : Fact (3931 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3943 : Fact (3943 : ℕ).Prime := ⟨by norm_num⟩
private instance i820_p3947 : Fact (3947 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p3967 : Fact (3967 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p3989 : Fact (3989 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4001 : Fact (4001 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4003 : Fact (4003 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4007 : Fact (4007 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4013 : Fact (4013 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4019 : Fact (4019 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4021 : Fact (4021 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4027 : Fact (4027 : ℕ).Prime := ⟨by norm_num⟩
private instance i821_p4049 : Fact (4049 : ℕ).Prime := ⟨by norm_num⟩
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
private instance i823_p4133 : Fact (4133 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4139 : Fact (4139 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4153 : Fact (4153 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4157 : Fact (4157 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4159 : Fact (4159 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4177 : Fact (4177 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4201 : Fact (4201 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4211 : Fact (4211 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4217 : Fact (4217 : ℕ).Prime := ⟨by norm_num⟩
private instance i823_p4219 : Fact (4219 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4229 : Fact (4229 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4231 : Fact (4231 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4241 : Fact (4241 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4243 : Fact (4243 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4253 : Fact (4253 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4259 : Fact (4259 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4261 : Fact (4261 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4271 : Fact (4271 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4273 : Fact (4273 : ℕ).Prime := ⟨by norm_num⟩
private instance i824_p4283 : Fact (4283 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4289 : Fact (4289 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4297 : Fact (4297 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4327 : Fact (4327 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4337 : Fact (4337 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4339 : Fact (4339 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4349 : Fact (4349 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4357 : Fact (4357 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4363 : Fact (4363 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4373 : Fact (4373 : ℕ).Prime := ⟨by norm_num⟩
private instance i825_p4391 : Fact (4391 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4397 : Fact (4397 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4409 : Fact (4409 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4421 : Fact (4421 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4423 : Fact (4423 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4441 : Fact (4441 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4447 : Fact (4447 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4451 : Fact (4451 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4457 : Fact (4457 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4463 : Fact (4463 : ℕ).Prime := ⟨by norm_num⟩
private instance i826_p4481 : Fact (4481 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4483 : Fact (4483 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4493 : Fact (4493 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4507 : Fact (4507 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4513 : Fact (4513 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4517 : Fact (4517 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4519 : Fact (4519 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4523 : Fact (4523 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4547 : Fact (4547 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4549 : Fact (4549 : ℕ).Prime := ⟨by norm_num⟩
private instance i827_p4561 : Fact (4561 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4567 : Fact (4567 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4583 : Fact (4583 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4591 : Fact (4591 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4597 : Fact (4597 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4603 : Fact (4603 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4621 : Fact (4621 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4637 : Fact (4637 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4639 : Fact (4639 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4643 : Fact (4643 : ℕ).Prime := ⟨by norm_num⟩
private instance i828_p4649 : Fact (4649 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4651 : Fact (4651 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4657 : Fact (4657 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4663 : Fact (4663 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4673 : Fact (4673 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4679 : Fact (4679 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4691 : Fact (4691 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4703 : Fact (4703 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4721 : Fact (4721 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4723 : Fact (4723 : ℕ).Prime := ⟨by norm_num⟩
private instance i829_p4729 : Fact (4729 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4733 : Fact (4733 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4751 : Fact (4751 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4759 : Fact (4759 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4783 : Fact (4783 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4787 : Fact (4787 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4789 : Fact (4789 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4793 : Fact (4793 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4799 : Fact (4799 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4801 : Fact (4801 : ℕ).Prime := ⟨by norm_num⟩
private instance i830_p4813 : Fact (4813 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4817 : Fact (4817 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4831 : Fact (4831 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4861 : Fact (4861 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4871 : Fact (4871 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4877 : Fact (4877 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4889 : Fact (4889 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4903 : Fact (4903 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4909 : Fact (4909 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4919 : Fact (4919 : ℕ).Prime := ⟨by norm_num⟩
private instance i831_p4931 : Fact (4931 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4933 : Fact (4933 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4937 : Fact (4937 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4943 : Fact (4943 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4951 : Fact (4951 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4957 : Fact (4957 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4967 : Fact (4967 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4969 : Fact (4969 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4973 : Fact (4973 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4987 : Fact (4987 : ℕ).Prime := ⟨by norm_num⟩
private instance i832_p4993 : Fact (4993 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p4999 : Fact (4999 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5003 : Fact (5003 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5009 : Fact (5009 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5011 : Fact (5011 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5021 : Fact (5021 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5023 : Fact (5023 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5039 : Fact (5039 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5051 : Fact (5051 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5059 : Fact (5059 : ℕ).Prime := ⟨by norm_num⟩
private instance i833_p5077 : Fact (5077 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5081 : Fact (5081 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5087 : Fact (5087 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5099 : Fact (5099 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5101 : Fact (5101 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5107 : Fact (5107 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5113 : Fact (5113 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5119 : Fact (5119 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5147 : Fact (5147 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5153 : Fact (5153 : ℕ).Prime := ⟨by norm_num⟩
private instance i834_p5167 : Fact (5167 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5171 : Fact (5171 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5179 : Fact (5179 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5189 : Fact (5189 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5197 : Fact (5197 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5209 : Fact (5209 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5227 : Fact (5227 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5231 : Fact (5231 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5233 : Fact (5233 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5237 : Fact (5237 : ℕ).Prime := ⟨by norm_num⟩
private instance i835_p5261 : Fact (5261 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5273 : Fact (5273 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5279 : Fact (5279 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5281 : Fact (5281 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5297 : Fact (5297 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5303 : Fact (5303 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5309 : Fact (5309 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5323 : Fact (5323 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5333 : Fact (5333 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5347 : Fact (5347 : ℕ).Prime := ⟨by norm_num⟩
private instance i836_p5351 : Fact (5351 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5381 : Fact (5381 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5387 : Fact (5387 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5393 : Fact (5393 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5399 : Fact (5399 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5407 : Fact (5407 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5413 : Fact (5413 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5417 : Fact (5417 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5419 : Fact (5419 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5431 : Fact (5431 : ℕ).Prime := ⟨by norm_num⟩
private instance i837_p5437 : Fact (5437 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5441 : Fact (5441 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5443 : Fact (5443 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5449 : Fact (5449 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5471 : Fact (5471 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5477 : Fact (5477 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5479 : Fact (5479 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5483 : Fact (5483 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5501 : Fact (5501 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5503 : Fact (5503 : ℕ).Prime := ⟨by norm_num⟩
private instance i838_p5507 : Fact (5507 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5519 : Fact (5519 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5521 : Fact (5521 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5527 : Fact (5527 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5531 : Fact (5531 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5557 : Fact (5557 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5563 : Fact (5563 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5569 : Fact (5569 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5573 : Fact (5573 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5581 : Fact (5581 : ℕ).Prime := ⟨by norm_num⟩
private instance i839_p5591 : Fact (5591 : ℕ).Prime := ⟨by norm_num⟩
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
private instance i841_p5689 : Fact (5689 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5693 : Fact (5693 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5701 : Fact (5701 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5711 : Fact (5711 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5717 : Fact (5717 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5737 : Fact (5737 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5741 : Fact (5741 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5743 : Fact (5743 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5749 : Fact (5749 : ℕ).Prime := ⟨by norm_num⟩
private instance i841_p5779 : Fact (5779 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5783 : Fact (5783 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5791 : Fact (5791 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5801 : Fact (5801 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5807 : Fact (5807 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5813 : Fact (5813 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5821 : Fact (5821 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5827 : Fact (5827 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5839 : Fact (5839 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5843 : Fact (5843 : ℕ).Prime := ⟨by norm_num⟩
private instance i842_p5849 : Fact (5849 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5851 : Fact (5851 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5857 : Fact (5857 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5861 : Fact (5861 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5867 : Fact (5867 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5869 : Fact (5869 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5879 : Fact (5879 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5881 : Fact (5881 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5897 : Fact (5897 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5903 : Fact (5903 : ℕ).Prime := ⟨by norm_num⟩
private instance i843_p5923 : Fact (5923 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p5927 : Fact (5927 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p5939 : Fact (5939 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p5953 : Fact (5953 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p5981 : Fact (5981 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p5987 : Fact (5987 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p6007 : Fact (6007 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p6011 : Fact (6011 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p6029 : Fact (6029 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p6037 : Fact (6037 : ℕ).Prime := ⟨by norm_num⟩
private instance i844_p6043 : Fact (6043 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6047 : Fact (6047 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6053 : Fact (6053 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6067 : Fact (6067 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6073 : Fact (6073 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6079 : Fact (6079 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6089 : Fact (6089 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6091 : Fact (6091 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6101 : Fact (6101 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6113 : Fact (6113 : ℕ).Prime := ⟨by norm_num⟩
private instance i845_p6121 : Fact (6121 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6131 : Fact (6131 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6133 : Fact (6133 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6143 : Fact (6143 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6151 : Fact (6151 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6163 : Fact (6163 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6173 : Fact (6173 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6197 : Fact (6197 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6199 : Fact (6199 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6203 : Fact (6203 : ℕ).Prime := ⟨by norm_num⟩
private instance i846_p6211 : Fact (6211 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6217 : Fact (6217 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6221 : Fact (6221 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6229 : Fact (6229 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6247 : Fact (6247 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6257 : Fact (6257 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6263 : Fact (6263 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6269 : Fact (6269 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6271 : Fact (6271 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6277 : Fact (6277 : ℕ).Prime := ⟨by norm_num⟩
private instance i847_p6287 : Fact (6287 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6299 : Fact (6299 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6301 : Fact (6301 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6311 : Fact (6311 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6317 : Fact (6317 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6323 : Fact (6323 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6329 : Fact (6329 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6337 : Fact (6337 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6343 : Fact (6343 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6353 : Fact (6353 : ℕ).Prime := ⟨by norm_num⟩
private instance i848_p6359 : Fact (6359 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6361 : Fact (6361 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6367 : Fact (6367 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6373 : Fact (6373 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6379 : Fact (6379 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6389 : Fact (6389 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6397 : Fact (6397 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6421 : Fact (6421 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6427 : Fact (6427 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6449 : Fact (6449 : ℕ).Prime := ⟨by norm_num⟩
private instance i849_p6451 : Fact (6451 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6469 : Fact (6469 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6473 : Fact (6473 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6481 : Fact (6481 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6491 : Fact (6491 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6521 : Fact (6521 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6529 : Fact (6529 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6547 : Fact (6547 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6551 : Fact (6551 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6553 : Fact (6553 : ℕ).Prime := ⟨by norm_num⟩
private instance i850_p6563 : Fact (6563 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6569 : Fact (6569 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6571 : Fact (6571 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6577 : Fact (6577 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6581 : Fact (6581 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6599 : Fact (6599 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6607 : Fact (6607 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6619 : Fact (6619 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6637 : Fact (6637 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6653 : Fact (6653 : ℕ).Prime := ⟨by norm_num⟩
private instance i851_p6659 : Fact (6659 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6661 : Fact (6661 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6673 : Fact (6673 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6679 : Fact (6679 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6689 : Fact (6689 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6691 : Fact (6691 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6701 : Fact (6701 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6703 : Fact (6703 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6709 : Fact (6709 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6719 : Fact (6719 : ℕ).Prime := ⟨by norm_num⟩
private instance i852_p6733 : Fact (6733 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6737 : Fact (6737 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6761 : Fact (6761 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6763 : Fact (6763 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6779 : Fact (6779 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6781 : Fact (6781 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6791 : Fact (6791 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6793 : Fact (6793 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6803 : Fact (6803 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6823 : Fact (6823 : ℕ).Prime := ⟨by norm_num⟩
private instance i853_p6827 : Fact (6827 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6829 : Fact (6829 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6833 : Fact (6833 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6841 : Fact (6841 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6857 : Fact (6857 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6863 : Fact (6863 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6869 : Fact (6869 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6871 : Fact (6871 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6883 : Fact (6883 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6899 : Fact (6899 : ℕ).Prime := ⟨by norm_num⟩
private instance i854_p6907 : Fact (6907 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6911 : Fact (6911 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6917 : Fact (6917 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6947 : Fact (6947 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6949 : Fact (6949 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6959 : Fact (6959 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6961 : Fact (6961 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6967 : Fact (6967 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6971 : Fact (6971 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6977 : Fact (6977 : ℕ).Prime := ⟨by norm_num⟩
private instance i855_p6983 : Fact (6983 : ℕ).Prime := ⟨by norm_num⟩
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
private instance i857_p7079 : Fact (7079 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7103 : Fact (7103 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7109 : Fact (7109 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7121 : Fact (7121 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7127 : Fact (7127 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7129 : Fact (7129 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7151 : Fact (7151 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7159 : Fact (7159 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7177 : Fact (7177 : ℕ).Prime := ⟨by norm_num⟩
private instance i857_p7187 : Fact (7187 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7193 : Fact (7193 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7207 : Fact (7207 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7211 : Fact (7211 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7213 : Fact (7213 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7219 : Fact (7219 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7229 : Fact (7229 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7237 : Fact (7237 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7243 : Fact (7243 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7247 : Fact (7247 : ℕ).Prime := ⟨by norm_num⟩
private instance i858_p7253 : Fact (7253 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7283 : Fact (7283 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7297 : Fact (7297 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7307 : Fact (7307 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7309 : Fact (7309 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7321 : Fact (7321 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7331 : Fact (7331 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7333 : Fact (7333 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7349 : Fact (7349 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7351 : Fact (7351 : ℕ).Prime := ⟨by norm_num⟩
private instance i859_p7369 : Fact (7369 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7393 : Fact (7393 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7411 : Fact (7411 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7417 : Fact (7417 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7433 : Fact (7433 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7451 : Fact (7451 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7457 : Fact (7457 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7459 : Fact (7459 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7477 : Fact (7477 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7481 : Fact (7481 : ℕ).Prime := ⟨by norm_num⟩
private instance i860_p7487 : Fact (7487 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7489 : Fact (7489 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7499 : Fact (7499 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7507 : Fact (7507 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7517 : Fact (7517 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7523 : Fact (7523 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7529 : Fact (7529 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7537 : Fact (7537 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7541 : Fact (7541 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7547 : Fact (7547 : ℕ).Prime := ⟨by norm_num⟩
private instance i861_p7549 : Fact (7549 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7559 : Fact (7559 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7561 : Fact (7561 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7573 : Fact (7573 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7577 : Fact (7577 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7583 : Fact (7583 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7589 : Fact (7589 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7591 : Fact (7591 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7603 : Fact (7603 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7607 : Fact (7607 : ℕ).Prime := ⟨by norm_num⟩
private instance i862_p7621 : Fact (7621 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7639 : Fact (7639 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7643 : Fact (7643 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7649 : Fact (7649 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7669 : Fact (7669 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7673 : Fact (7673 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7681 : Fact (7681 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7687 : Fact (7687 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7691 : Fact (7691 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7699 : Fact (7699 : ℕ).Prime := ⟨by norm_num⟩
private instance i863_p7703 : Fact (7703 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7717 : Fact (7717 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7723 : Fact (7723 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7727 : Fact (7727 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7741 : Fact (7741 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7753 : Fact (7753 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7757 : Fact (7757 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7759 : Fact (7759 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7789 : Fact (7789 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7793 : Fact (7793 : ℕ).Prime := ⟨by norm_num⟩
private instance i864_p7817 : Fact (7817 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7823 : Fact (7823 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7829 : Fact (7829 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7841 : Fact (7841 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7853 : Fact (7853 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7867 : Fact (7867 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7873 : Fact (7873 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7877 : Fact (7877 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7879 : Fact (7879 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7883 : Fact (7883 : ℕ).Prime := ⟨by norm_num⟩
private instance i865_p7901 : Fact (7901 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7907 : Fact (7907 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7919 : Fact (7919 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7927 : Fact (7927 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7933 : Fact (7933 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7937 : Fact (7937 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7949 : Fact (7949 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7951 : Fact (7951 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7963 : Fact (7963 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p7993 : Fact (7993 : ℕ).Prime := ⟨by norm_num⟩
private instance i866_p8009 : Fact (8009 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8011 : Fact (8011 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8017 : Fact (8017 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8039 : Fact (8039 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8053 : Fact (8053 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8059 : Fact (8059 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8069 : Fact (8069 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8081 : Fact (8081 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8087 : Fact (8087 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8089 : Fact (8089 : ℕ).Prime := ⟨by norm_num⟩
private instance i867_p8093 : Fact (8093 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8101 : Fact (8101 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8111 : Fact (8111 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8117 : Fact (8117 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8123 : Fact (8123 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8147 : Fact (8147 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8161 : Fact (8161 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8167 : Fact (8167 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8171 : Fact (8171 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8179 : Fact (8179 : ℕ).Prime := ⟨by norm_num⟩
private instance i868_p8191 : Fact (8191 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8209 : Fact (8209 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8219 : Fact (8219 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8221 : Fact (8221 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8231 : Fact (8231 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8233 : Fact (8233 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8237 : Fact (8237 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8243 : Fact (8243 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8263 : Fact (8263 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8269 : Fact (8269 : ℕ).Prime := ⟨by norm_num⟩
private instance i869_p8273 : Fact (8273 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8287 : Fact (8287 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8291 : Fact (8291 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8293 : Fact (8293 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8297 : Fact (8297 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8311 : Fact (8311 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8317 : Fact (8317 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8329 : Fact (8329 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8353 : Fact (8353 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8363 : Fact (8363 : ℕ).Prime := ⟨by norm_num⟩
private instance i870_p8369 : Fact (8369 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8377 : Fact (8377 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8387 : Fact (8387 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8389 : Fact (8389 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8419 : Fact (8419 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8423 : Fact (8423 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8429 : Fact (8429 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8431 : Fact (8431 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8443 : Fact (8443 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8447 : Fact (8447 : ℕ).Prime := ⟨by norm_num⟩
private instance i871_p8461 : Fact (8461 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8467 : Fact (8467 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8501 : Fact (8501 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8513 : Fact (8513 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8521 : Fact (8521 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8527 : Fact (8527 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8537 : Fact (8537 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8539 : Fact (8539 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8543 : Fact (8543 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8563 : Fact (8563 : ℕ).Prime := ⟨by norm_num⟩
private instance i872_p8573 : Fact (8573 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8581 : Fact (8581 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8597 : Fact (8597 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8599 : Fact (8599 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8609 : Fact (8609 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8623 : Fact (8623 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8627 : Fact (8627 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8629 : Fact (8629 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8641 : Fact (8641 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8647 : Fact (8647 : ℕ).Prime := ⟨by norm_num⟩
private instance i873_p8663 : Fact (8663 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8669 : Fact (8669 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8677 : Fact (8677 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8681 : Fact (8681 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8689 : Fact (8689 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8693 : Fact (8693 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8699 : Fact (8699 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8707 : Fact (8707 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8713 : Fact (8713 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8719 : Fact (8719 : ℕ).Prime := ⟨by norm_num⟩
private instance i874_p8731 : Fact (8731 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8737 : Fact (8737 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8741 : Fact (8741 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8747 : Fact (8747 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8753 : Fact (8753 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8761 : Fact (8761 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8779 : Fact (8779 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8783 : Fact (8783 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8803 : Fact (8803 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8807 : Fact (8807 : ℕ).Prime := ⟨by norm_num⟩
private instance i875_p8819 : Fact (8819 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8821 : Fact (8821 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8831 : Fact (8831 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8837 : Fact (8837 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8839 : Fact (8839 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8849 : Fact (8849 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8861 : Fact (8861 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8863 : Fact (8863 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8867 : Fact (8867 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8887 : Fact (8887 : ℕ).Prime := ⟨by norm_num⟩
private instance i876_p8893 : Fact (8893 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8923 : Fact (8923 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8929 : Fact (8929 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8933 : Fact (8933 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8941 : Fact (8941 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8951 : Fact (8951 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8963 : Fact (8963 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8969 : Fact (8969 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8971 : Fact (8971 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p8999 : Fact (8999 : ℕ).Prime := ⟨by norm_num⟩
private instance i877_p9001 : Fact (9001 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9007 : Fact (9007 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9011 : Fact (9011 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9013 : Fact (9013 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9029 : Fact (9029 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9041 : Fact (9041 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9043 : Fact (9043 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9049 : Fact (9049 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9059 : Fact (9059 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9067 : Fact (9067 : ℕ).Prime := ⟨by norm_num⟩
private instance i878_p9091 : Fact (9091 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9103 : Fact (9103 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9109 : Fact (9109 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9127 : Fact (9127 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9133 : Fact (9133 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9137 : Fact (9137 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9151 : Fact (9151 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9157 : Fact (9157 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9161 : Fact (9161 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9173 : Fact (9173 : ℕ).Prime := ⟨by norm_num⟩
private instance i879_p9181 : Fact (9181 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9187 : Fact (9187 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9199 : Fact (9199 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9203 : Fact (9203 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9209 : Fact (9209 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9221 : Fact (9221 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9227 : Fact (9227 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9239 : Fact (9239 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9241 : Fact (9241 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9257 : Fact (9257 : ℕ).Prime := ⟨by norm_num⟩
private instance i880_p9277 : Fact (9277 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9281 : Fact (9281 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9283 : Fact (9283 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9293 : Fact (9293 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9311 : Fact (9311 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9319 : Fact (9319 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9323 : Fact (9323 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9337 : Fact (9337 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9341 : Fact (9341 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9343 : Fact (9343 : ℕ).Prime := ⟨by norm_num⟩
private instance i881_p9349 : Fact (9349 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9371 : Fact (9371 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9377 : Fact (9377 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9391 : Fact (9391 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9397 : Fact (9397 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9403 : Fact (9403 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9413 : Fact (9413 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9419 : Fact (9419 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9421 : Fact (9421 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9431 : Fact (9431 : ℕ).Prime := ⟨by norm_num⟩
private instance i882_p9433 : Fact (9433 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9437 : Fact (9437 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9439 : Fact (9439 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9461 : Fact (9461 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9463 : Fact (9463 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9467 : Fact (9467 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9473 : Fact (9473 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9479 : Fact (9479 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9491 : Fact (9491 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9497 : Fact (9497 : ℕ).Prime := ⟨by norm_num⟩
private instance i883_p9511 : Fact (9511 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9521 : Fact (9521 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9533 : Fact (9533 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9539 : Fact (9539 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9547 : Fact (9547 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9551 : Fact (9551 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9587 : Fact (9587 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9601 : Fact (9601 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9613 : Fact (9613 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9619 : Fact (9619 : ℕ).Prime := ⟨by norm_num⟩
private instance i884_p9623 : Fact (9623 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9629 : Fact (9629 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9631 : Fact (9631 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9643 : Fact (9643 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9649 : Fact (9649 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9661 : Fact (9661 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9677 : Fact (9677 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9679 : Fact (9679 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9689 : Fact (9689 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9697 : Fact (9697 : ℕ).Prime := ⟨by norm_num⟩
private instance i885_p9719 : Fact (9719 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9721 : Fact (9721 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9733 : Fact (9733 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9739 : Fact (9739 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9743 : Fact (9743 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9749 : Fact (9749 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9767 : Fact (9767 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9769 : Fact (9769 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9781 : Fact (9781 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9787 : Fact (9787 : ℕ).Prime := ⟨by norm_num⟩
private instance i886_p9791 : Fact (9791 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9803 : Fact (9803 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9811 : Fact (9811 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9817 : Fact (9817 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9829 : Fact (9829 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9833 : Fact (9833 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9839 : Fact (9839 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9851 : Fact (9851 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9857 : Fact (9857 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9859 : Fact (9859 : ℕ).Prime := ⟨by norm_num⟩
private instance i887_p9871 : Fact (9871 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9883 : Fact (9883 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9887 : Fact (9887 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9901 : Fact (9901 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9907 : Fact (9907 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9923 : Fact (9923 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9929 : Fact (9929 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9931 : Fact (9931 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9941 : Fact (9941 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9949 : Fact (9949 : ℕ).Prime := ⟨by norm_num⟩
private instance i888_p9967 : Fact (9967 : ℕ).Prime := ⟨by norm_num⟩
private instance i889_p9973 : Fact (9973 : ℕ).Prime := ⟨by norm_num⟩

-- §1 Point counts by decide
theorem BSD_E143_card_p251 : (E143_Finset 251).card = 230 := by decide
theorem BSD_E143_card_p257 : (E143_Finset 257).card = 239 := by decide
theorem BSD_E143_card_p263 : (E143_Finset 263).card = 281 := by decide
theorem BSD_E143_card_p269 : (E143_Finset 269).card = 299 := by decide
theorem BSD_E143_card_p271 : (E143_Finset 271).card = 243 := by decide
theorem BSD_E143_card_p277 : (E143_Finset 277).card = 251 := by decide
theorem BSD_E143_card_p281 : (E143_Finset 281).card = 263 := by decide
theorem BSD_E143_card_p283 : (E143_Finset 283).card = 313 := by decide
theorem BSD_E143_card_p293 : (E143_Finset 293).card = 279 := by decide
theorem BSD_E143_card_p307 : (E143_Finset 307).card = 307 := by decide
theorem BSD_E143_card_p311 : (E143_Finset 311).card = 303 := by decide
theorem BSD_E143_card_p313 : (E143_Finset 313).card = 310 := by decide
theorem BSD_E143_card_p317 : (E143_Finset 317).card = 318 := by decide
theorem BSD_E143_card_p331 : (E143_Finset 331).card = 342 := by decide
theorem BSD_E143_card_p337 : (E143_Finset 337).card = 357 := by decide
theorem BSD_E143_card_p347 : (E143_Finset 347).card = 329 := by decide
theorem BSD_E143_card_p349 : (E143_Finset 349).card = 333 := by decide
theorem BSD_E143_card_p353 : (E143_Finset 353).card = 368 := by decide
theorem BSD_E143_card_p359 : (E143_Finset 359).card = 337 := by decide
theorem BSD_E143_card_p367 : (E143_Finset 367).card = 364 := by decide
theorem BSD_E143_card_p373 : (E143_Finset 373).card = 347 := by decide
theorem BSD_E143_card_p379 : (E143_Finset 379).card = 390 := by decide
theorem BSD_E143_card_p383 : (E143_Finset 383).card = 402 := by decide
theorem BSD_E143_card_p389 : (E143_Finset 389).card = 380 := by decide
theorem BSD_E143_card_p397 : (E143_Finset 397).card = 415 := by decide
theorem BSD_E143_card_p401 : (E143_Finset 401).card = 419 := by decide
theorem BSD_E143_card_p409 : (E143_Finset 409).card = 427 := by decide
theorem BSD_E143_card_p419 : (E143_Finset 419).card = 447 := by decide
theorem BSD_E143_card_p421 : (E143_Finset 421).card = 443 := by decide
theorem BSD_E143_card_p431 : (E143_Finset 431).card = 471 := by decide
theorem BSD_E143_card_p433 : (E143_Finset 433).card = 400 := by decide
theorem BSD_E143_card_p439 : (E143_Finset 439).card = 433 := by decide
theorem BSD_E143_card_p443 : (E143_Finset 443).card = 466 := by decide
theorem BSD_E143_card_p449 : (E143_Finset 449).card = 428 := by decide
theorem BSD_E143_card_p457 : (E143_Finset 457).card = 473 := by decide
theorem BSD_E143_card_p461 : (E143_Finset 461).card = 451 := by decide
theorem BSD_E143_card_p463 : (E143_Finset 463).card = 472 := by decide
theorem BSD_E143_card_p467 : (E143_Finset 467).card = 490 := by decide
theorem BSD_E143_card_p479 : (E143_Finset 479).card = 443 := by decide
theorem BSD_E143_card_p487 : (E143_Finset 487).card = 462 := by decide
theorem BSD_E143_card_p491 : (E143_Finset 491).card = 479 := by decide
theorem BSD_E143_card_p499 : (E143_Finset 499).card = 471 := by decide
theorem BSD_E143_card_p503 : (E143_Finset 503).card = 473 := by decide
theorem BSD_E143_card_p509 : (E143_Finset 509).card = 500 := by decide
theorem BSD_E143_card_p521 : (E143_Finset 521).card = 516 := by decide
theorem BSD_E143_card_p523 : (E143_Finset 523).card = 537 := by decide
theorem BSD_E143_card_p541 : (E143_Finset 541).card = 571 := by decide
theorem BSD_E143_card_p547 : (E143_Finset 547).card = 539 := by decide
theorem BSD_E143_card_p557 : (E143_Finset 557).card = 545 := by decide
theorem BSD_E143_card_p563 : (E143_Finset 563).card = 545 := by decide
theorem BSD_E143_card_p569 : (E143_Finset 569).card = 601 := by decide
theorem BSD_E143_card_p571 : (E143_Finset 571).card = 531 := by decide
theorem BSD_E143_card_p577 : (E143_Finset 577).card = 546 := by decide
theorem BSD_E143_card_p587 : (E143_Finset 587).card = 599 := by decide
theorem BSD_E143_card_p593 : (E143_Finset 593).card = 569 := by decide
theorem BSD_E143_card_p599 : (E143_Finset 599).card = 575 := by decide
theorem BSD_E143_card_p601 : (E143_Finset 601).card = 623 := by decide
theorem BSD_E143_card_p607 : (E143_Finset 607).card = 629 := by decide
theorem BSD_E143_card_p613 : (E143_Finset 613).card = 615 := by decide
theorem BSD_E143_card_p617 : (E143_Finset 617).card = 575 := by decide
theorem BSD_E143_card_p619 : (E143_Finset 619).card = 626 := by decide
theorem BSD_E143_card_p631 : (E143_Finset 631).card = 658 := by decide
theorem BSD_E143_card_p641 : (E143_Finset 641).card = 674 := by decide
theorem BSD_E143_card_p643 : (E143_Finset 643).card = 692 := by decide
theorem BSD_E143_card_p647 : (E143_Finset 647).card = 662 := by decide
theorem BSD_E143_card_p653 : (E143_Finset 653).card = 666 := by decide
theorem BSD_E143_card_p659 : (E143_Finset 659).card = 703 := by decide
theorem BSD_E143_card_p661 : (E143_Finset 661).card = 630 := by decide
theorem BSD_E143_card_p673 : (E143_Finset 673).card = 669 := by decide
theorem BSD_E143_card_p677 : (E143_Finset 677).card = 671 := by decide
theorem BSD_E143_card_p683 : (E143_Finset 683).card = 687 := by decide
theorem BSD_E143_card_p691 : (E143_Finset 691).card = 736 := by decide
theorem BSD_E143_card_p701 : (E143_Finset 701).card = 711 := by decide
theorem BSD_E143_card_p709 : (E143_Finset 709).card = 744 := by decide
theorem BSD_E143_card_p719 : (E143_Finset 719).card = 760 := by decide
theorem BSD_E143_card_p727 : (E143_Finset 727).card = 708 := by decide
theorem BSD_E143_card_p733 : (E143_Finset 733).card = 779 := by decide
theorem BSD_E143_card_p739 : (E143_Finset 739).card = 741 := by decide
theorem BSD_E143_card_p743 : (E143_Finset 743).card = 701 := by decide
theorem BSD_E143_card_p751 : (E143_Finset 751).card = 790 := by decide
theorem BSD_E143_card_p757 : (E143_Finset 757).card = 727 := by decide
theorem BSD_E143_card_p761 : (E143_Finset 761).card = 795 := by decide
theorem BSD_E143_card_p769 : (E143_Finset 769).card = 769 := by decide
theorem BSD_E143_card_p773 : (E143_Finset 773).card = 743 := by decide
theorem BSD_E143_card_p787 : (E143_Finset 787).card = 775 := by decide
theorem BSD_E143_card_p797 : (E143_Finset 797).card = 780 := by decide
theorem BSD_E143_card_p809 : (E143_Finset 809).card = 785 := by decide
theorem BSD_E143_card_p811 : (E143_Finset 811).card = 847 := by decide
theorem BSD_E143_card_p821 : (E143_Finset 821).card = 821 := by decide
theorem BSD_E143_card_p823 : (E143_Finset 823).card = 852 := by decide
theorem BSD_E143_card_p827 : (E143_Finset 827).card = 777 := by decide
theorem BSD_E143_card_p829 : (E143_Finset 829).card = 800 := by decide
theorem BSD_E143_card_p839 : (E143_Finset 839).card = 786 := by decide
theorem BSD_E143_card_p853 : (E143_Finset 853).card = 903 := by decide
theorem BSD_E143_card_p857 : (E143_Finset 857).card = 889 := by decide
theorem BSD_E143_card_p859 : (E143_Finset 859).card = 846 := by decide
theorem BSD_E143_card_p863 : (E143_Finset 863).card = 815 := by decide
theorem BSD_E143_card_p877 : (E143_Finset 877).card = 839 := by decide
theorem BSD_E143_card_p881 : (E143_Finset 881).card = 848 := by decide
theorem BSD_E143_card_p883 : (E143_Finset 883).card = 855 := by decide
theorem BSD_E143_card_p887 : (E143_Finset 887).card = 875 := by decide
theorem BSD_E143_card_p907 : (E143_Finset 907).card = 855 := by decide
theorem BSD_E143_card_p911 : (E143_Finset 911).card = 919 := by decide
theorem BSD_E143_card_p919 : (E143_Finset 919).card = 879 := by decide
theorem BSD_E143_card_p929 : (E143_Finset 929).card = 971 := by decide
theorem BSD_E143_card_p937 : (E143_Finset 937).card = 949 := by decide
theorem BSD_E143_card_p941 : (E143_Finset 941).card = 977 := by decide
theorem BSD_E143_card_p947 : (E143_Finset 947).card = 956 := by decide
theorem BSD_E143_card_p953 : (E143_Finset 953).card = 983 := by decide
theorem BSD_E143_card_p967 : (E143_Finset 967).card = 939 := by decide
theorem BSD_E143_card_p971 : (E143_Finset 971).card = 1020 := by decide
theorem BSD_E143_card_p977 : (E143_Finset 977).card = 986 := by decide
theorem BSD_E143_card_p983 : (E143_Finset 983).card = 1014 := by decide
theorem BSD_E143_card_p991 : (E143_Finset 991).card = 959 := by decide
theorem BSD_E143_card_p997 : (E143_Finset 997).card = 1015 := by decide

-- §2 a_p values by omega
theorem BSD_ap_p251 : a_p 251 = (21 : ℤ) := by
  have h := BSD_E143_card_p251; unfold a_p; omega

theorem BSD_ap_p257 : a_p 257 = (18 : ℤ) := by
  have h := BSD_E143_card_p257; unfold a_p; omega

theorem BSD_ap_p263 : a_p 263 = (-18 : ℤ) := by
  have h := BSD_E143_card_p263; unfold a_p; omega

theorem BSD_ap_p269 : a_p 269 = (-30 : ℤ) := by
  have h := BSD_E143_card_p269; unfold a_p; omega

theorem BSD_ap_p271 : a_p 271 = (28 : ℤ) := by
  have h := BSD_E143_card_p271; unfold a_p; omega

theorem BSD_ap_p277 : a_p 277 = (26 : ℤ) := by
  have h := BSD_E143_card_p277; unfold a_p; omega

theorem BSD_ap_p281 : a_p 281 = (18 : ℤ) := by
  have h := BSD_E143_card_p281; unfold a_p; omega

theorem BSD_ap_p283 : a_p 283 = (-30 : ℤ) := by
  have h := BSD_E143_card_p283; unfold a_p; omega

theorem BSD_ap_p293 : a_p 293 = (14 : ℤ) := by
  have h := BSD_E143_card_p293; unfold a_p; omega

theorem BSD_ap_p307 : a_p 307 = (0 : ℤ) := by
  have h := BSD_E143_card_p307; unfold a_p; omega

theorem BSD_ap_p311 : a_p 311 = (8 : ℤ) := by
  have h := BSD_E143_card_p311; unfold a_p; omega

theorem BSD_ap_p313 : a_p 313 = (3 : ℤ) := by
  have h := BSD_E143_card_p313; unfold a_p; omega

theorem BSD_ap_p317 : a_p 317 = (-1 : ℤ) := by
  have h := BSD_E143_card_p317; unfold a_p; omega

theorem BSD_ap_p331 : a_p 331 = (-11 : ℤ) := by
  have h := BSD_E143_card_p331; unfold a_p; omega

theorem BSD_ap_p337 : a_p 337 = (-20 : ℤ) := by
  have h := BSD_E143_card_p337; unfold a_p; omega

theorem BSD_ap_p347 : a_p 347 = (18 : ℤ) := by
  have h := BSD_E143_card_p347; unfold a_p; omega

theorem BSD_ap_p349 : a_p 349 = (16 : ℤ) := by
  have h := BSD_E143_card_p349; unfold a_p; omega

theorem BSD_ap_p353 : a_p 353 = (-15 : ℤ) := by
  have h := BSD_E143_card_p353; unfold a_p; omega

theorem BSD_ap_p359 : a_p 359 = (22 : ℤ) := by
  have h := BSD_E143_card_p359; unfold a_p; omega

theorem BSD_ap_p367 : a_p 367 = (3 : ℤ) := by
  have h := BSD_E143_card_p367; unfold a_p; omega

theorem BSD_ap_p373 : a_p 373 = (26 : ℤ) := by
  have h := BSD_E143_card_p373; unfold a_p; omega

theorem BSD_ap_p379 : a_p 379 = (-11 : ℤ) := by
  have h := BSD_E143_card_p379; unfold a_p; omega

theorem BSD_ap_p383 : a_p 383 = (-19 : ℤ) := by
  have h := BSD_E143_card_p383; unfold a_p; omega

theorem BSD_ap_p389 : a_p 389 = (9 : ℤ) := by
  have h := BSD_E143_card_p389; unfold a_p; omega

theorem BSD_ap_p397 : a_p 397 = (-18 : ℤ) := by
  have h := BSD_E143_card_p397; unfold a_p; omega

theorem BSD_ap_p401 : a_p 401 = (-18 : ℤ) := by
  have h := BSD_E143_card_p401; unfold a_p; omega

theorem BSD_ap_p409 : a_p 409 = (-18 : ℤ) := by
  have h := BSD_E143_card_p409; unfold a_p; omega

theorem BSD_ap_p419 : a_p 419 = (-28 : ℤ) := by
  have h := BSD_E143_card_p419; unfold a_p; omega

theorem BSD_ap_p421 : a_p 421 = (-22 : ℤ) := by
  have h := BSD_E143_card_p421; unfold a_p; omega

theorem BSD_ap_p431 : a_p 431 = (-40 : ℤ) := by
  have h := BSD_E143_card_p431; unfold a_p; omega

theorem BSD_ap_p433 : a_p 433 = (33 : ℤ) := by
  have h := BSD_E143_card_p433; unfold a_p; omega

theorem BSD_ap_p439 : a_p 439 = (6 : ℤ) := by
  have h := BSD_E143_card_p439; unfold a_p; omega

theorem BSD_ap_p443 : a_p 443 = (-23 : ℤ) := by
  have h := BSD_E143_card_p443; unfold a_p; omega

theorem BSD_ap_p449 : a_p 449 = (21 : ℤ) := by
  have h := BSD_E143_card_p449; unfold a_p; omega

theorem BSD_ap_p457 : a_p 457 = (-16 : ℤ) := by
  have h := BSD_E143_card_p457; unfold a_p; omega

theorem BSD_ap_p461 : a_p 461 = (10 : ℤ) := by
  have h := BSD_E143_card_p461; unfold a_p; omega

theorem BSD_ap_p463 : a_p 463 = (-9 : ℤ) := by
  have h := BSD_E143_card_p463; unfold a_p; omega

theorem BSD_ap_p467 : a_p 467 = (-23 : ℤ) := by
  have h := BSD_E143_card_p467; unfold a_p; omega

theorem BSD_ap_p479 : a_p 479 = (36 : ℤ) := by
  have h := BSD_E143_card_p479; unfold a_p; omega

theorem BSD_ap_p487 : a_p 487 = (25 : ℤ) := by
  have h := BSD_E143_card_p487; unfold a_p; omega

theorem BSD_ap_p491 : a_p 491 = (12 : ℤ) := by
  have h := BSD_E143_card_p491; unfold a_p; omega

theorem BSD_ap_p499 : a_p 499 = (28 : ℤ) := by
  have h := BSD_E143_card_p499; unfold a_p; omega

theorem BSD_ap_p503 : a_p 503 = (30 : ℤ) := by
  have h := BSD_E143_card_p503; unfold a_p; omega

theorem BSD_ap_p509 : a_p 509 = (9 : ℤ) := by
  have h := BSD_E143_card_p509; unfold a_p; omega

theorem BSD_ap_p521 : a_p 521 = (5 : ℤ) := by
  have h := BSD_E143_card_p521; unfold a_p; omega

theorem BSD_ap_p523 : a_p 523 = (-14 : ℤ) := by
  have h := BSD_E143_card_p523; unfold a_p; omega

theorem BSD_ap_p541 : a_p 541 = (-30 : ℤ) := by
  have h := BSD_E143_card_p541; unfold a_p; omega

theorem BSD_ap_p547 : a_p 547 = (8 : ℤ) := by
  have h := BSD_E143_card_p547; unfold a_p; omega

theorem BSD_ap_p557 : a_p 557 = (12 : ℤ) := by
  have h := BSD_E143_card_p557; unfold a_p; omega

theorem BSD_ap_p563 : a_p 563 = (18 : ℤ) := by
  have h := BSD_E143_card_p563; unfold a_p; omega

theorem BSD_ap_p569 : a_p 569 = (-32 : ℤ) := by
  have h := BSD_E143_card_p569; unfold a_p; omega

theorem BSD_ap_p571 : a_p 571 = (40 : ℤ) := by
  have h := BSD_E143_card_p571; unfold a_p; omega

theorem BSD_ap_p577 : a_p 577 = (31 : ℤ) := by
  have h := BSD_E143_card_p577; unfold a_p; omega

theorem BSD_ap_p587 : a_p 587 = (-12 : ℤ) := by
  have h := BSD_E143_card_p587; unfold a_p; omega

theorem BSD_ap_p593 : a_p 593 = (24 : ℤ) := by
  have h := BSD_E143_card_p593; unfold a_p; omega

theorem BSD_ap_p599 : a_p 599 = (24 : ℤ) := by
  have h := BSD_E143_card_p599; unfold a_p; omega

theorem BSD_ap_p601 : a_p 601 = (-22 : ℤ) := by
  have h := BSD_E143_card_p601; unfold a_p; omega

theorem BSD_ap_p607 : a_p 607 = (-22 : ℤ) := by
  have h := BSD_E143_card_p607; unfold a_p; omega

theorem BSD_ap_p613 : a_p 613 = (-2 : ℤ) := by
  have h := BSD_E143_card_p613; unfold a_p; omega

theorem BSD_ap_p617 : a_p 617 = (42 : ℤ) := by
  have h := BSD_E143_card_p617; unfold a_p; omega

theorem BSD_ap_p619 : a_p 619 = (-7 : ℤ) := by
  have h := BSD_E143_card_p619; unfold a_p; omega

theorem BSD_ap_p631 : a_p 631 = (-27 : ℤ) := by
  have h := BSD_E143_card_p631; unfold a_p; omega

theorem BSD_ap_p641 : a_p 641 = (-33 : ℤ) := by
  have h := BSD_E143_card_p641; unfold a_p; omega

theorem BSD_ap_p643 : a_p 643 = (-49 : ℤ) := by
  have h := BSD_E143_card_p643; unfold a_p; omega

theorem BSD_ap_p647 : a_p 647 = (-15 : ℤ) := by
  have h := BSD_E143_card_p647; unfold a_p; omega

theorem BSD_ap_p653 : a_p 653 = (-13 : ℤ) := by
  have h := BSD_E143_card_p653; unfold a_p; omega

theorem BSD_ap_p659 : a_p 659 = (-44 : ℤ) := by
  have h := BSD_E143_card_p659; unfold a_p; omega

theorem BSD_ap_p661 : a_p 661 = (31 : ℤ) := by
  have h := BSD_E143_card_p661; unfold a_p; omega

theorem BSD_ap_p673 : a_p 673 = (4 : ℤ) := by
  have h := BSD_E143_card_p673; unfold a_p; omega

theorem BSD_ap_p677 : a_p 677 = (6 : ℤ) := by
  have h := BSD_E143_card_p677; unfold a_p; omega

theorem BSD_ap_p683 : a_p 683 = (-4 : ℤ) := by
  have h := BSD_E143_card_p683; unfold a_p; omega

theorem BSD_ap_p691 : a_p 691 = (-45 : ℤ) := by
  have h := BSD_E143_card_p691; unfold a_p; omega

theorem BSD_ap_p701 : a_p 701 = (-10 : ℤ) := by
  have h := BSD_E143_card_p701; unfold a_p; omega

theorem BSD_ap_p709 : a_p 709 = (-35 : ℤ) := by
  have h := BSD_E143_card_p709; unfold a_p; omega

theorem BSD_ap_p719 : a_p 719 = (-41 : ℤ) := by
  have h := BSD_E143_card_p719; unfold a_p; omega

theorem BSD_ap_p727 : a_p 727 = (19 : ℤ) := by
  have h := BSD_E143_card_p727; unfold a_p; omega

theorem BSD_ap_p733 : a_p 733 = (-46 : ℤ) := by
  have h := BSD_E143_card_p733; unfold a_p; omega

theorem BSD_ap_p739 : a_p 739 = (-2 : ℤ) := by
  have h := BSD_E143_card_p739; unfold a_p; omega

theorem BSD_ap_p743 : a_p 743 = (42 : ℤ) := by
  have h := BSD_E143_card_p743; unfold a_p; omega

theorem BSD_ap_p751 : a_p 751 = (-39 : ℤ) := by
  have h := BSD_E143_card_p751; unfold a_p; omega

theorem BSD_ap_p757 : a_p 757 = (30 : ℤ) := by
  have h := BSD_E143_card_p757; unfold a_p; omega

theorem BSD_ap_p761 : a_p 761 = (-34 : ℤ) := by
  have h := BSD_E143_card_p761; unfold a_p; omega

theorem BSD_ap_p769 : a_p 769 = (0 : ℤ) := by
  have h := BSD_E143_card_p769; unfold a_p; omega

theorem BSD_ap_p773 : a_p 773 = (30 : ℤ) := by
  have h := BSD_E143_card_p773; unfold a_p; omega

theorem BSD_ap_p787 : a_p 787 = (12 : ℤ) := by
  have h := BSD_E143_card_p787; unfold a_p; omega

theorem BSD_ap_p797 : a_p 797 = (17 : ℤ) := by
  have h := BSD_E143_card_p797; unfold a_p; omega

theorem BSD_ap_p809 : a_p 809 = (24 : ℤ) := by
  have h := BSD_E143_card_p809; unfold a_p; omega

theorem BSD_ap_p811 : a_p 811 = (-36 : ℤ) := by
  have h := BSD_E143_card_p811; unfold a_p; omega

theorem BSD_ap_p821 : a_p 821 = (0 : ℤ) := by
  have h := BSD_E143_card_p821; unfold a_p; omega

theorem BSD_ap_p823 : a_p 823 = (-29 : ℤ) := by
  have h := BSD_E143_card_p823; unfold a_p; omega

theorem BSD_ap_p827 : a_p 827 = (50 : ℤ) := by
  have h := BSD_E143_card_p827; unfold a_p; omega

theorem BSD_ap_p829 : a_p 829 = (29 : ℤ) := by
  have h := BSD_E143_card_p829; unfold a_p; omega

theorem BSD_ap_p839 : a_p 839 = (53 : ℤ) := by
  have h := BSD_E143_card_p839; unfold a_p; omega

theorem BSD_ap_p853 : a_p 853 = (-50 : ℤ) := by
  have h := BSD_E143_card_p853; unfold a_p; omega

theorem BSD_ap_p857 : a_p 857 = (-32 : ℤ) := by
  have h := BSD_E143_card_p857; unfold a_p; omega

theorem BSD_ap_p859 : a_p 859 = (13 : ℤ) := by
  have h := BSD_E143_card_p859; unfold a_p; omega

theorem BSD_ap_p863 : a_p 863 = (48 : ℤ) := by
  have h := BSD_E143_card_p863; unfold a_p; omega

theorem BSD_ap_p877 : a_p 877 = (38 : ℤ) := by
  have h := BSD_E143_card_p877; unfold a_p; omega

theorem BSD_ap_p881 : a_p 881 = (33 : ℤ) := by
  have h := BSD_E143_card_p881; unfold a_p; omega

theorem BSD_ap_p883 : a_p 883 = (28 : ℤ) := by
  have h := BSD_E143_card_p883; unfold a_p; omega

theorem BSD_ap_p887 : a_p 887 = (12 : ℤ) := by
  have h := BSD_E143_card_p887; unfold a_p; omega

theorem BSD_ap_p907 : a_p 907 = (52 : ℤ) := by
  have h := BSD_E143_card_p907; unfold a_p; omega

theorem BSD_ap_p911 : a_p 911 = (-8 : ℤ) := by
  have h := BSD_E143_card_p911; unfold a_p; omega

theorem BSD_ap_p919 : a_p 919 = (40 : ℤ) := by
  have h := BSD_E143_card_p919; unfold a_p; omega

theorem BSD_ap_p929 : a_p 929 = (-42 : ℤ) := by
  have h := BSD_E143_card_p929; unfold a_p; omega

theorem BSD_ap_p937 : a_p 937 = (-12 : ℤ) := by
  have h := BSD_E143_card_p937; unfold a_p; omega

theorem BSD_ap_p941 : a_p 941 = (-36 : ℤ) := by
  have h := BSD_E143_card_p941; unfold a_p; omega

theorem BSD_ap_p947 : a_p 947 = (-9 : ℤ) := by
  have h := BSD_E143_card_p947; unfold a_p; omega

theorem BSD_ap_p953 : a_p 953 = (-30 : ℤ) := by
  have h := BSD_E143_card_p953; unfold a_p; omega

theorem BSD_ap_p967 : a_p 967 = (28 : ℤ) := by
  have h := BSD_E143_card_p967; unfold a_p; omega

theorem BSD_ap_p971 : a_p 971 = (-49 : ℤ) := by
  have h := BSD_E143_card_p971; unfold a_p; omega

theorem BSD_ap_p977 : a_p 977 = (-9 : ℤ) := by
  have h := BSD_E143_card_p977; unfold a_p; omega

theorem BSD_ap_p983 : a_p 983 = (-31 : ℤ) := by
  have h := BSD_E143_card_p983; unfold a_p; omega

theorem BSD_ap_p991 : a_p 991 = (32 : ℤ) := by
  have h := BSD_E143_card_p991; unfold a_p; omega

theorem BSD_ap_p997 : a_p 997 = (-18 : ℤ) := by
  have h := BSD_E143_card_p997; unfold a_p; omega

theorem BSD_ap_p1009 : a_p 1009 = (-40 : ℤ) := by
  have h := BSD_E143_card_p1009; unfold a_p; omega

theorem BSD_ap_p1013 : a_p 1013 = (-37 : ℤ) := by
  have h := BSD_E143_card_p1013; unfold a_p; omega

theorem BSD_ap_p1019 : a_p 1019 = (30 : ℤ) := by
  have h := BSD_E143_card_p1019; unfold a_p; omega

theorem BSD_ap_p1021 : a_p 1021 = (26 : ℤ) := by
  have h := BSD_E143_card_p1021; unfold a_p; omega

theorem BSD_ap_p1031 : a_p 1031 = (-42 : ℤ) := by
  have h := BSD_E143_card_p1031; unfold a_p; omega

theorem BSD_ap_p1033 : a_p 1033 = (-24 : ℤ) := by
  have h := BSD_E143_card_p1033; unfold a_p; omega

theorem BSD_ap_p1039 : a_p 1039 = (49 : ℤ) := by
  have h := BSD_E143_card_p1039; unfold a_p; omega

theorem BSD_ap_p1049 : a_p 1049 = (29 : ℤ) := by
  have h := BSD_E143_card_p1049; unfold a_p; omega

theorem BSD_ap_p1051 : a_p 1051 = (50 : ℤ) := by
  have h := BSD_E143_card_p1051; unfold a_p; omega

theorem BSD_ap_p1061 : a_p 1061 = (-15 : ℤ) := by
  have h := BSD_E143_card_p1061; unfold a_p; omega

theorem BSD_ap_p1063 : a_p 1063 = (-20 : ℤ) := by
  have h := BSD_E143_card_p1063; unfold a_p; omega

theorem BSD_ap_p1069 : a_p 1069 = (32 : ℤ) := by
  have h := BSD_E143_card_p1069; unfold a_p; omega

theorem BSD_ap_p1087 : a_p 1087 = (-32 : ℤ) := by
  have h := BSD_E143_card_p1087; unfold a_p; omega

theorem BSD_ap_p1091 : a_p 1091 = (12 : ℤ) := by
  have h := BSD_E143_card_p1091; unfold a_p; omega

theorem BSD_ap_p1093 : a_p 1093 = (29 : ℤ) := by
  have h := BSD_E143_card_p1093; unfold a_p; omega

theorem BSD_ap_p1097 : a_p 1097 = (-62 : ℤ) := by
  have h := BSD_E143_card_p1097; unfold a_p; omega

theorem BSD_ap_p1103 : a_p 1103 = (7 : ℤ) := by
  have h := BSD_E143_card_p1103; unfold a_p; omega

theorem BSD_ap_p1109 : a_p 1109 = (10 : ℤ) := by
  have h := BSD_E143_card_p1109; unfold a_p; omega

theorem BSD_ap_p1117 : a_p 1117 = (12 : ℤ) := by
  have h := BSD_E143_card_p1117; unfold a_p; omega

theorem BSD_ap_p1123 : a_p 1123 = (40 : ℤ) := by
  have h := BSD_E143_card_p1123; unfold a_p; omega

theorem BSD_ap_p1129 : a_p 1129 = (-6 : ℤ) := by
  have h := BSD_E143_card_p1129; unfold a_p; omega

theorem BSD_ap_p1151 : a_p 1151 = (-30 : ℤ) := by
  have h := BSD_E143_card_p1151; unfold a_p; omega

theorem BSD_ap_p1153 : a_p 1153 = (5 : ℤ) := by
  have h := BSD_E143_card_p1153; unfold a_p; omega

theorem BSD_ap_p1163 : a_p 1163 = (36 : ℤ) := by
  have h := BSD_E143_card_p1163; unfold a_p; omega

theorem BSD_ap_p1171 : a_p 1171 = (61 : ℤ) := by
  have h := BSD_E143_card_p1171; unfold a_p; omega

theorem BSD_ap_p1181 : a_p 1181 = (42 : ℤ) := by
  have h := BSD_E143_card_p1181; unfold a_p; omega

theorem BSD_ap_p1187 : a_p 1187 = (-24 : ℤ) := by
  have h := BSD_E143_card_p1187; unfold a_p; omega

theorem BSD_ap_p1193 : a_p 1193 = (-9 : ℤ) := by
  have h := BSD_E143_card_p1193; unfold a_p; omega

theorem BSD_ap_p1201 : a_p 1201 = (22 : ℤ) := by
  have h := BSD_E143_card_p1201; unfold a_p; omega

theorem BSD_ap_p1213 : a_p 1213 = (-53 : ℤ) := by
  have h := BSD_E143_card_p1213; unfold a_p; omega

theorem BSD_ap_p1217 : a_p 1217 = (-12 : ℤ) := by
  have h := BSD_E143_card_p1217; unfold a_p; omega

theorem BSD_ap_p1223 : a_p 1223 = (0 : ℤ) := by
  have h := BSD_E143_card_p1223; unfold a_p; omega

theorem BSD_ap_p1229 : a_p 1229 = (-40 : ℤ) := by
  have h := BSD_E143_card_p1229; unfold a_p; omega

theorem BSD_ap_p1231 : a_p 1231 = (18 : ℤ) := by
  have h := BSD_E143_card_p1231; unfold a_p; omega

theorem BSD_ap_p1237 : a_p 1237 = (-50 : ℤ) := by
  have h := BSD_E143_card_p1237; unfold a_p; omega

theorem BSD_ap_p1249 : a_p 1249 = (2 : ℤ) := by
  have h := BSD_E143_card_p1249; unfold a_p; omega

theorem BSD_ap_p1259 : a_p 1259 = (-39 : ℤ) := by
  have h := BSD_E143_card_p1259; unfold a_p; omega

theorem BSD_ap_p1277 : a_p 1277 = (9 : ℤ) := by
  have h := BSD_E143_card_p1277; unfold a_p; omega

theorem BSD_ap_p1279 : a_p 1279 = (35 : ℤ) := by
  have h := BSD_E143_card_p1279; unfold a_p; omega

theorem BSD_ap_p1283 : a_p 1283 = (50 : ℤ) := by
  have h := BSD_E143_card_p1283; unfold a_p; omega

theorem BSD_ap_p1289 : a_p 1289 = (30 : ℤ) := by
  have h := BSD_E143_card_p1289; unfold a_p; omega

theorem BSD_ap_p1291 : a_p 1291 = (36 : ℤ) := by
  have h := BSD_E143_card_p1291; unfold a_p; omega

theorem BSD_ap_p1297 : a_p 1297 = (-48 : ℤ) := by
  have h := BSD_E143_card_p1297; unfold a_p; omega

theorem BSD_ap_p1301 : a_p 1301 = (-9 : ℤ) := by
  have h := BSD_E143_card_p1301; unfold a_p; omega

theorem BSD_ap_p1303 : a_p 1303 = (11 : ℤ) := by
  have h := BSD_E143_card_p1303; unfold a_p; omega

theorem BSD_ap_p1307 : a_p 1307 = (48 : ℤ) := by
  have h := BSD_E143_card_p1307; unfold a_p; omega

theorem BSD_ap_p1319 : a_p 1319 = (-2 : ℤ) := by
  have h := BSD_E143_card_p1319; unfold a_p; omega

theorem BSD_ap_p1321 : a_p 1321 = (41 : ℤ) := by
  have h := BSD_E143_card_p1321; unfold a_p; omega

theorem BSD_ap_p1327 : a_p 1327 = (-4 : ℤ) := by
  have h := BSD_E143_card_p1327; unfold a_p; omega

theorem BSD_ap_p1361 : a_p 1361 = (28 : ℤ) := by
  have h := BSD_E143_card_p1361; unfold a_p; omega

theorem BSD_ap_p1367 : a_p 1367 = (40 : ℤ) := by
  have h := BSD_E143_card_p1367; unfold a_p; omega

theorem BSD_ap_p1373 : a_p 1373 = (41 : ℤ) := by
  have h := BSD_E143_card_p1373; unfold a_p; omega

theorem BSD_ap_p1381 : a_p 1381 = (2 : ℤ) := by
  have h := BSD_E143_card_p1381; unfold a_p; omega

theorem BSD_ap_p1399 : a_p 1399 = (10 : ℤ) := by
  have h := BSD_E143_card_p1399; unfold a_p; omega

theorem BSD_ap_p1409 : a_p 1409 = (-45 : ℤ) := by
  have h := BSD_E143_card_p1409; unfold a_p; omega

theorem BSD_ap_p1423 : a_p 1423 = (-29 : ℤ) := by
  have h := BSD_E143_card_p1423; unfold a_p; omega

theorem BSD_ap_p1427 : a_p 1427 = (-30 : ℤ) := by
  have h := BSD_E143_card_p1427; unfold a_p; omega

theorem BSD_ap_p1429 : a_p 1429 = (-36 : ℤ) := by
  have h := BSD_E143_card_p1429; unfold a_p; omega

theorem BSD_ap_p1433 : a_p 1433 = (-30 : ℤ) := by
  have h := BSD_E143_card_p1433; unfold a_p; omega

theorem BSD_ap_p1439 : a_p 1439 = (-60 : ℤ) := by
  have h := BSD_E143_card_p1439; unfold a_p; omega

theorem BSD_ap_p1447 : a_p 1447 = (-28 : ℤ) := by
  have h := BSD_E143_card_p1447; unfold a_p; omega

theorem BSD_ap_p1451 : a_p 1451 = (0 : ℤ) := by
  have h := BSD_E143_card_p1451; unfold a_p; omega

theorem BSD_ap_p1453 : a_p 1453 = (-31 : ℤ) := by
  have h := BSD_E143_card_p1453; unfold a_p; omega

theorem BSD_ap_p1459 : a_p 1459 = (0 : ℤ) := by
  have h := BSD_E143_card_p1459; unfold a_p; omega

theorem BSD_ap_p1471 : a_p 1471 = (-52 : ℤ) := by
  have h := BSD_E143_card_p1471; unfold a_p; omega

theorem BSD_ap_p1481 : a_p 1481 = (46 : ℤ) := by
  have h := BSD_E143_card_p1481; unfold a_p; omega

theorem BSD_ap_p1483 : a_p 1483 = (-19 : ℤ) := by
  have h := BSD_E143_card_p1483; unfold a_p; omega

theorem BSD_ap_p1487 : a_p 1487 = (60 : ℤ) := by
  have h := BSD_E143_card_p1487; unfold a_p; omega

theorem BSD_ap_p1489 : a_p 1489 = (-9 : ℤ) := by
  have h := BSD_E143_card_p1489; unfold a_p; omega

theorem BSD_ap_p1493 : a_p 1493 = (-44 : ℤ) := by
  have h := BSD_E143_card_p1493; unfold a_p; omega

theorem BSD_ap_p1499 : a_p 1499 = (31 : ℤ) := by
  have h := BSD_E143_card_p1499; unfold a_p; omega

theorem BSD_ap_p1511 : a_p 1511 = (41 : ℤ) := by
  have h := BSD_E143_card_p1511; unfold a_p; omega

theorem BSD_ap_p1523 : a_p 1523 = (21 : ℤ) := by
  have h := BSD_E143_card_p1523; unfold a_p; omega

theorem BSD_ap_p1531 : a_p 1531 = (-22 : ℤ) := by
  have h := BSD_E143_card_p1531; unfold a_p; omega

theorem BSD_ap_p1543 : a_p 1543 = (56 : ℤ) := by
  have h := BSD_E143_card_p1543; unfold a_p; omega

theorem BSD_ap_p1549 : a_p 1549 = (-45 : ℤ) := by
  have h := BSD_E143_card_p1549; unfold a_p; omega

theorem BSD_ap_p1553 : a_p 1553 = (2 : ℤ) := by
  have h := BSD_E143_card_p1553; unfold a_p; omega

theorem BSD_ap_p1559 : a_p 1559 = (10 : ℤ) := by
  have h := BSD_E143_card_p1559; unfold a_p; omega

theorem BSD_ap_p1567 : a_p 1567 = (8 : ℤ) := by
  have h := BSD_E143_card_p1567; unfold a_p; omega

theorem BSD_ap_p1571 : a_p 1571 = (0 : ℤ) := by
  have h := BSD_E143_card_p1571; unfold a_p; omega

theorem BSD_ap_p1579 : a_p 1579 = (4 : ℤ) := by
  have h := BSD_E143_card_p1579; unfold a_p; omega

theorem BSD_ap_p1583 : a_p 1583 = (-22 : ℤ) := by
  have h := BSD_E143_card_p1583; unfold a_p; omega

theorem BSD_ap_p1597 : a_p 1597 = (36 : ℤ) := by
  have h := BSD_E143_card_p1597; unfold a_p; omega

theorem BSD_ap_p1601 : a_p 1601 = (46 : ℤ) := by
  have h := BSD_E143_card_p1601; unfold a_p; omega

theorem BSD_ap_p1607 : a_p 1607 = (-41 : ℤ) := by
  have h := BSD_E143_card_p1607; unfold a_p; omega

theorem BSD_ap_p1609 : a_p 1609 = (-2 : ℤ) := by
  have h := BSD_E143_card_p1609; unfold a_p; omega

theorem BSD_ap_p1613 : a_p 1613 = (-20 : ℤ) := by
  have h := BSD_E143_card_p1613; unfold a_p; omega

theorem BSD_ap_p1619 : a_p 1619 = (-40 : ℤ) := by
  have h := BSD_E143_card_p1619; unfold a_p; omega

theorem BSD_ap_p1621 : a_p 1621 = (-10 : ℤ) := by
  have h := BSD_E143_card_p1621; unfold a_p; omega

theorem BSD_ap_p1627 : a_p 1627 = (-8 : ℤ) := by
  have h := BSD_E143_card_p1627; unfold a_p; omega

theorem BSD_ap_p1637 : a_p 1637 = (-27 : ℤ) := by
  have h := BSD_E143_card_p1637; unfold a_p; omega

theorem BSD_ap_p1657 : a_p 1657 = (34 : ℤ) := by
  have h := BSD_E143_card_p1657; unfold a_p; omega

theorem BSD_ap_p1663 : a_p 1663 = (-58 : ℤ) := by
  have h := BSD_E143_card_p1663; unfold a_p; omega

theorem BSD_ap_p1667 : a_p 1667 = (34 : ℤ) := by
  have h := BSD_E143_card_p1667; unfold a_p; omega

theorem BSD_ap_p1669 : a_p 1669 = (-46 : ℤ) := by
  have h := BSD_E143_card_p1669; unfold a_p; omega

theorem BSD_ap_p1693 : a_p 1693 = (-56 : ℤ) := by
  have h := BSD_E143_card_p1693; unfold a_p; omega

theorem BSD_ap_p1697 : a_p 1697 = (66 : ℤ) := by
  have h := BSD_E143_card_p1697; unfold a_p; omega

theorem BSD_ap_p1699 : a_p 1699 = (12 : ℤ) := by
  have h := BSD_E143_card_p1699; unfold a_p; omega

theorem BSD_ap_p1709 : a_p 1709 = (45 : ℤ) := by
  have h := BSD_E143_card_p1709; unfold a_p; omega

theorem BSD_ap_p1721 : a_p 1721 = (39 : ℤ) := by
  have h := BSD_E143_card_p1721; unfold a_p; omega

theorem BSD_ap_p1723 : a_p 1723 = (58 : ℤ) := by
  have h := BSD_E143_card_p1723; unfold a_p; omega

theorem BSD_ap_p1733 : a_p 1733 = (44 : ℤ) := by
  have h := BSD_E143_card_p1733; unfold a_p; omega

theorem BSD_ap_p1741 : a_p 1741 = (-7 : ℤ) := by
  have h := BSD_E143_card_p1741; unfold a_p; omega

theorem BSD_ap_p1747 : a_p 1747 = (-55 : ℤ) := by
  have h := BSD_E143_card_p1747; unfold a_p; omega

theorem BSD_ap_p1753 : a_p 1753 = (-50 : ℤ) := by
  have h := BSD_E143_card_p1753; unfold a_p; omega

theorem BSD_ap_p1759 : a_p 1759 = (2 : ℤ) := by
  have h := BSD_E143_card_p1759; unfold a_p; omega

theorem BSD_ap_p1777 : a_p 1777 = (4 : ℤ) := by
  have h := BSD_E143_card_p1777; unfold a_p; omega

theorem BSD_ap_p1783 : a_p 1783 = (25 : ℤ) := by
  have h := BSD_E143_card_p1783; unfold a_p; omega

theorem BSD_ap_p1787 : a_p 1787 = (-27 : ℤ) := by
  have h := BSD_E143_card_p1787; unfold a_p; omega

theorem BSD_ap_p1789 : a_p 1789 = (18 : ℤ) := by
  have h := BSD_E143_card_p1789; unfold a_p; omega

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

theorem BSD_ap_p2113 : a_p 2113 = (46 : ℤ) := by
  have h := BSD_E143_card_p2113; unfold a_p; omega

theorem BSD_ap_p2129 : a_p 2129 = (-66 : ℤ) := by
  have h := BSD_E143_card_p2129; unfold a_p; omega

theorem BSD_ap_p2131 : a_p 2131 = (26 : ℤ) := by
  have h := BSD_E143_card_p2131; unfold a_p; omega

theorem BSD_ap_p2137 : a_p 2137 = (-37 : ℤ) := by
  have h := BSD_E143_card_p2137; unfold a_p; omega

theorem BSD_ap_p2141 : a_p 2141 = (30 : ℤ) := by
  have h := BSD_E143_card_p2141; unfold a_p; omega

theorem BSD_ap_p2143 : a_p 2143 = (-29 : ℤ) := by
  have h := BSD_E143_card_p2143; unfold a_p; omega

theorem BSD_ap_p2153 : a_p 2153 = (46 : ℤ) := by
  have h := BSD_E143_card_p2153; unfold a_p; omega

theorem BSD_ap_p2161 : a_p 2161 = (67 : ℤ) := by
  have h := BSD_E143_card_p2161; unfold a_p; omega

theorem BSD_ap_p2179 : a_p 2179 = (25 : ℤ) := by
  have h := BSD_E143_card_p2179; unfold a_p; omega

theorem BSD_ap_p2203 : a_p 2203 = (-71 : ℤ) := by
  have h := BSD_E143_card_p2203; unfold a_p; omega

theorem BSD_ap_p2207 : a_p 2207 = (78 : ℤ) := by
  have h := BSD_E143_card_p2207; unfold a_p; omega

theorem BSD_ap_p2213 : a_p 2213 = (52 : ℤ) := by
  have h := BSD_E143_card_p2213; unfold a_p; omega

theorem BSD_ap_p2221 : a_p 2221 = (62 : ℤ) := by
  have h := BSD_E143_card_p2221; unfold a_p; omega

theorem BSD_ap_p2237 : a_p 2237 = (-42 : ℤ) := by
  have h := BSD_E143_card_p2237; unfold a_p; omega

theorem BSD_ap_p2239 : a_p 2239 = (-50 : ℤ) := by
  have h := BSD_E143_card_p2239; unfold a_p; omega

theorem BSD_ap_p2243 : a_p 2243 = (-36 : ℤ) := by
  have h := BSD_E143_card_p2243; unfold a_p; omega

theorem BSD_ap_p2251 : a_p 2251 = (8 : ℤ) := by
  have h := BSD_E143_card_p2251; unfold a_p; omega

theorem BSD_ap_p2267 : a_p 2267 = (11 : ℤ) := by
  have h := BSD_E143_card_p2267; unfold a_p; omega

theorem BSD_ap_p2269 : a_p 2269 = (-1 : ℤ) := by
  have h := BSD_E143_card_p2269; unfold a_p; omega

theorem BSD_ap_p2273 : a_p 2273 = (-46 : ℤ) := by
  have h := BSD_E143_card_p2273; unfold a_p; omega

theorem BSD_ap_p2281 : a_p 2281 = (1 : ℤ) := by
  have h := BSD_E143_card_p2281; unfold a_p; omega

theorem BSD_ap_p2287 : a_p 2287 = (-14 : ℤ) := by
  have h := BSD_E143_card_p2287; unfold a_p; omega

theorem BSD_ap_p2293 : a_p 2293 = (-29 : ℤ) := by
  have h := BSD_E143_card_p2293; unfold a_p; omega

theorem BSD_ap_p2297 : a_p 2297 = (-37 : ℤ) := by
  have h := BSD_E143_card_p2297; unfold a_p; omega

theorem BSD_ap_p2309 : a_p 2309 = (-86 : ℤ) := by
  have h := BSD_E143_card_p2309; unfold a_p; omega

theorem BSD_ap_p2311 : a_p 2311 = (23 : ℤ) := by
  have h := BSD_E143_card_p2311; unfold a_p; omega

theorem BSD_ap_p2333 : a_p 2333 = (53 : ℤ) := by
  have h := BSD_E143_card_p2333; unfold a_p; omega

theorem BSD_ap_p2339 : a_p 2339 = (-70 : ℤ) := by
  have h := BSD_E143_card_p2339; unfold a_p; omega

theorem BSD_ap_p2341 : a_p 2341 = (63 : ℤ) := by
  have h := BSD_E143_card_p2341; unfold a_p; omega

theorem BSD_ap_p2347 : a_p 2347 = (-7 : ℤ) := by
  have h := BSD_E143_card_p2347; unfold a_p; omega

theorem BSD_ap_p2351 : a_p 2351 = (54 : ℤ) := by
  have h := BSD_E143_card_p2351; unfold a_p; omega

theorem BSD_ap_p2357 : a_p 2357 = (67 : ℤ) := by
  have h := BSD_E143_card_p2357; unfold a_p; omega

theorem BSD_ap_p2371 : a_p 2371 = (30 : ℤ) := by
  have h := BSD_E143_card_p2371; unfold a_p; omega

theorem BSD_ap_p2377 : a_p 2377 = (-31 : ℤ) := by
  have h := BSD_E143_card_p2377; unfold a_p; omega

theorem BSD_ap_p2381 : a_p 2381 = (-42 : ℤ) := by
  have h := BSD_E143_card_p2381; unfold a_p; omega

theorem BSD_ap_p2383 : a_p 2383 = (-8 : ℤ) := by
  have h := BSD_E143_card_p2383; unfold a_p; omega

theorem BSD_ap_p2389 : a_p 2389 = (24 : ℤ) := by
  have h := BSD_E143_card_p2389; unfold a_p; omega

theorem BSD_ap_p2393 : a_p 2393 = (-52 : ℤ) := by
  have h := BSD_E143_card_p2393; unfold a_p; omega

theorem BSD_ap_p2399 : a_p 2399 = (-73 : ℤ) := by
  have h := BSD_E143_card_p2399; unfold a_p; omega

theorem BSD_ap_p2411 : a_p 2411 = (12 : ℤ) := by
  have h := BSD_E143_card_p2411; unfold a_p; omega

theorem BSD_ap_p2417 : a_p 2417 = (-24 : ℤ) := by
  have h := BSD_E143_card_p2417; unfold a_p; omega

theorem BSD_ap_p2423 : a_p 2423 = (75 : ℤ) := by
  have h := BSD_E143_card_p2423; unfold a_p; omega

theorem BSD_ap_p2437 : a_p 2437 = (40 : ℤ) := by
  have h := BSD_E143_card_p2437; unfold a_p; omega

theorem BSD_ap_p2441 : a_p 2441 = (18 : ℤ) := by
  have h := BSD_E143_card_p2441; unfold a_p; omega

theorem BSD_ap_p2447 : a_p 2447 = (27 : ℤ) := by
  have h := BSD_E143_card_p2447; unfold a_p; omega

theorem BSD_ap_p2459 : a_p 2459 = (92 : ℤ) := by
  have h := BSD_E143_card_p2459; unfold a_p; omega

theorem BSD_ap_p2467 : a_p 2467 = (7 : ℤ) := by
  have h := BSD_E143_card_p2467; unfold a_p; omega

theorem BSD_ap_p2473 : a_p 2473 = (13 : ℤ) := by
  have h := BSD_E143_card_p2473; unfold a_p; omega

theorem BSD_ap_p2477 : a_p 2477 = (8 : ℤ) := by
  have h := BSD_E143_card_p2477; unfold a_p; omega

theorem BSD_ap_p2503 : a_p 2503 = (-12 : ℤ) := by
  have h := BSD_E143_card_p2503; unfold a_p; omega

theorem BSD_ap_p2521 : a_p 2521 = (-50 : ℤ) := by
  have h := BSD_E143_card_p2521; unfold a_p; omega

theorem BSD_ap_p2531 : a_p 2531 = (-3 : ℤ) := by
  have h := BSD_E143_card_p2531; unfold a_p; omega

theorem BSD_ap_p2539 : a_p 2539 = (-4 : ℤ) := by
  have h := BSD_E143_card_p2539; unfold a_p; omega

theorem BSD_ap_p2543 : a_p 2543 = (16 : ℤ) := by
  have h := BSD_E143_card_p2543; unfold a_p; omega

theorem BSD_ap_p2549 : a_p 2549 = (24 : ℤ) := by
  have h := BSD_E143_card_p2549; unfold a_p; omega

theorem BSD_ap_p2551 : a_p 2551 = (-16 : ℤ) := by
  have h := BSD_E143_card_p2551; unfold a_p; omega

theorem BSD_ap_p2557 : a_p 2557 = (-11 : ℤ) := by
  have h := BSD_E143_card_p2557; unfold a_p; omega

theorem BSD_ap_p2579 : a_p 2579 = (-92 : ℤ) := by
  have h := BSD_E143_card_p2579; unfold a_p; omega

theorem BSD_ap_p2591 : a_p 2591 = (-56 : ℤ) := by
  have h := BSD_E143_card_p2591; unfold a_p; omega

theorem BSD_ap_p2593 : a_p 2593 = (-68 : ℤ) := by
  have h := BSD_E143_card_p2593; unfold a_p; omega

theorem BSD_ap_p2609 : a_p 2609 = (80 : ℤ) := by
  have h := BSD_E143_card_p2609; unfold a_p; omega

theorem BSD_ap_p2617 : a_p 2617 = (-18 : ℤ) := by
  have h := BSD_E143_card_p2617; unfold a_p; omega

theorem BSD_ap_p2621 : a_p 2621 = (-78 : ℤ) := by
  have h := BSD_E143_card_p2621; unfold a_p; omega

theorem BSD_ap_p2633 : a_p 2633 = (-27 : ℤ) := by
  have h := BSD_E143_card_p2633; unfold a_p; omega

theorem BSD_ap_p2647 : a_p 2647 = (-48 : ℤ) := by
  have h := BSD_E143_card_p2647; unfold a_p; omega

theorem BSD_ap_p2657 : a_p 2657 = (66 : ℤ) := by
  have h := BSD_E143_card_p2657; unfold a_p; omega

theorem BSD_ap_p2659 : a_p 2659 = (48 : ℤ) := by
  have h := BSD_E143_card_p2659; unfold a_p; omega

theorem BSD_ap_p2663 : a_p 2663 = (-59 : ℤ) := by
  have h := BSD_E143_card_p2663; unfold a_p; omega

theorem BSD_ap_p2671 : a_p 2671 = (-48 : ℤ) := by
  have h := BSD_E143_card_p2671; unfold a_p; omega

theorem BSD_ap_p2677 : a_p 2677 = (77 : ℤ) := by
  have h := BSD_E143_card_p2677; unfold a_p; omega

theorem BSD_ap_p2683 : a_p 2683 = (-52 : ℤ) := by
  have h := BSD_E143_card_p2683; unfold a_p; omega

theorem BSD_ap_p2687 : a_p 2687 = (7 : ℤ) := by
  have h := BSD_E143_card_p2687; unfold a_p; omega

theorem BSD_ap_p2689 : a_p 2689 = (-77 : ℤ) := by
  have h := BSD_E143_card_p2689; unfold a_p; omega

theorem BSD_ap_p2693 : a_p 2693 = (-63 : ℤ) := by
  have h := BSD_E143_card_p2693; unfold a_p; omega

theorem BSD_ap_p2699 : a_p 2699 = (-9 : ℤ) := by
  have h := BSD_E143_card_p2699; unfold a_p; omega

theorem BSD_ap_p2707 : a_p 2707 = (23 : ℤ) := by
  have h := BSD_E143_card_p2707; unfold a_p; omega

theorem BSD_ap_p2711 : a_p 2711 = (81 : ℤ) := by
  have h := BSD_E143_card_p2711; unfold a_p; omega

theorem BSD_ap_p2713 : a_p 2713 = (58 : ℤ) := by
  have h := BSD_E143_card_p2713; unfold a_p; omega

theorem BSD_ap_p2719 : a_p 2719 = (-14 : ℤ) := by
  have h := BSD_E143_card_p2719; unfold a_p; omega

theorem BSD_ap_p2729 : a_p 2729 = (54 : ℤ) := by
  have h := BSD_E143_card_p2729; unfold a_p; omega

theorem BSD_ap_p2731 : a_p 2731 = (-68 : ℤ) := by
  have h := BSD_E143_card_p2731; unfold a_p; omega

theorem BSD_ap_p2741 : a_p 2741 = (22 : ℤ) := by
  have h := BSD_E143_card_p2741; unfold a_p; omega

theorem BSD_ap_p2749 : a_p 2749 = (26 : ℤ) := by
  have h := BSD_E143_card_p2749; unfold a_p; omega

theorem BSD_ap_p2753 : a_p 2753 = (21 : ℤ) := by
  have h := BSD_E143_card_p2753; unfold a_p; omega

theorem BSD_ap_p2767 : a_p 2767 = (-70 : ℤ) := by
  have h := BSD_E143_card_p2767; unfold a_p; omega

theorem BSD_ap_p2777 : a_p 2777 = (74 : ℤ) := by
  have h := BSD_E143_card_p2777; unfold a_p; omega

theorem BSD_ap_p2789 : a_p 2789 = (-94 : ℤ) := by
  have h := BSD_E143_card_p2789; unfold a_p; omega

theorem BSD_ap_p2791 : a_p 2791 = (-68 : ℤ) := by
  have h := BSD_E143_card_p2791; unfold a_p; omega

theorem BSD_ap_p2797 : a_p 2797 = (-30 : ℤ) := by
  have h := BSD_E143_card_p2797; unfold a_p; omega

theorem BSD_ap_p2801 : a_p 2801 = (8 : ℤ) := by
  have h := BSD_E143_card_p2801; unfold a_p; omega

theorem BSD_ap_p2803 : a_p 2803 = (28 : ℤ) := by
  have h := BSD_E143_card_p2803; unfold a_p; omega

theorem BSD_ap_p2819 : a_p 2819 = (-15 : ℤ) := by
  have h := BSD_E143_card_p2819; unfold a_p; omega

theorem BSD_ap_p2833 : a_p 2833 = (26 : ℤ) := by
  have h := BSD_E143_card_p2833; unfold a_p; omega

theorem BSD_ap_p2837 : a_p 2837 = (-44 : ℤ) := by
  have h := BSD_E143_card_p2837; unfold a_p; omega

theorem BSD_ap_p2843 : a_p 2843 = (60 : ℤ) := by
  have h := BSD_E143_card_p2843; unfold a_p; omega

theorem BSD_ap_p2851 : a_p 2851 = (-12 : ℤ) := by
  have h := BSD_E143_card_p2851; unfold a_p; omega

theorem BSD_ap_p2857 : a_p 2857 = (54 : ℤ) := by
  have h := BSD_E143_card_p2857; unfold a_p; omega

theorem BSD_ap_p2861 : a_p 2861 = (-39 : ℤ) := by
  have h := BSD_E143_card_p2861; unfold a_p; omega

theorem BSD_ap_p2879 : a_p 2879 = (-32 : ℤ) := by
  have h := BSD_E143_card_p2879; unfold a_p; omega

theorem BSD_ap_p2887 : a_p 2887 = (-57 : ℤ) := by
  have h := BSD_E143_card_p2887; unfold a_p; omega

theorem BSD_ap_p2897 : a_p 2897 = (26 : ℤ) := by
  have h := BSD_E143_card_p2897; unfold a_p; omega

theorem BSD_ap_p2903 : a_p 2903 = (26 : ℤ) := by
  have h := BSD_E143_card_p2903; unfold a_p; omega

theorem BSD_ap_p2909 : a_p 2909 = (-25 : ℤ) := by
  have h := BSD_E143_card_p2909; unfold a_p; omega

theorem BSD_ap_p2917 : a_p 2917 = (-84 : ℤ) := by
  have h := BSD_E143_card_p2917; unfold a_p; omega

theorem BSD_ap_p2927 : a_p 2927 = (48 : ℤ) := by
  have h := BSD_E143_card_p2927; unfold a_p; omega

theorem BSD_ap_p2939 : a_p 2939 = (12 : ℤ) := by
  have h := BSD_E143_card_p2939; unfold a_p; omega

theorem BSD_ap_p2953 : a_p 2953 = (6 : ℤ) := by
  have h := BSD_E143_card_p2953; unfold a_p; omega

theorem BSD_ap_p2957 : a_p 2957 = (-75 : ℤ) := by
  have h := BSD_E143_card_p2957; unfold a_p; omega

theorem BSD_ap_p2963 : a_p 2963 = (39 : ℤ) := by
  have h := BSD_E143_card_p2963; unfold a_p; omega

theorem BSD_ap_p2969 : a_p 2969 = (26 : ℤ) := by
  have h := BSD_E143_card_p2969; unfold a_p; omega

theorem BSD_ap_p2971 : a_p 2971 = (13 : ℤ) := by
  have h := BSD_E143_card_p2971; unfold a_p; omega

theorem BSD_ap_p2999 : a_p 2999 = (-36 : ℤ) := by
  have h := BSD_E143_card_p2999; unfold a_p; omega

theorem BSD_ap_p3001 : a_p 3001 = (1 : ℤ) := by
  have h := BSD_E143_card_p3001; unfold a_p; omega

theorem BSD_ap_p3011 : a_p 3011 = (44 : ℤ) := by
  have h := BSD_E143_card_p3011; unfold a_p; omega

theorem BSD_ap_p3019 : a_p 3019 = (-79 : ℤ) := by
  have h := BSD_E143_card_p3019; unfold a_p; omega

theorem BSD_ap_p3023 : a_p 3023 = (33 : ℤ) := by
  have h := BSD_E143_card_p3023; unfold a_p; omega

theorem BSD_ap_p3037 : a_p 3037 = (3 : ℤ) := by
  have h := BSD_E143_card_p3037; unfold a_p; omega

theorem BSD_ap_p3041 : a_p 3041 = (-54 : ℤ) := by
  have h := BSD_E143_card_p3041; unfold a_p; omega

theorem BSD_ap_p3049 : a_p 3049 = (-28 : ℤ) := by
  have h := BSD_E143_card_p3049; unfold a_p; omega

theorem BSD_ap_p3061 : a_p 3061 = (-37 : ℤ) := by
  have h := BSD_E143_card_p3061; unfold a_p; omega

theorem BSD_ap_p3067 : a_p 3067 = (-7 : ℤ) := by
  have h := BSD_E143_card_p3067; unfold a_p; omega

theorem BSD_ap_p3079 : a_p 3079 = (-38 : ℤ) := by
  have h := BSD_E143_card_p3079; unfold a_p; omega

theorem BSD_ap_p3083 : a_p 3083 = (3 : ℤ) := by
  have h := BSD_E143_card_p3083; unfold a_p; omega

theorem BSD_ap_p3089 : a_p 3089 = (11 : ℤ) := by
  have h := BSD_E143_card_p3089; unfold a_p; omega

theorem BSD_ap_p3109 : a_p 3109 = (54 : ℤ) := by
  have h := BSD_E143_card_p3109; unfold a_p; omega

theorem BSD_ap_p3119 : a_p 3119 = (-14 : ℤ) := by
  have h := BSD_E143_card_p3119; unfold a_p; omega

theorem BSD_ap_p3121 : a_p 3121 = (-32 : ℤ) := by
  have h := BSD_E143_card_p3121; unfold a_p; omega

theorem BSD_ap_p3137 : a_p 3137 = (-72 : ℤ) := by
  have h := BSD_E143_card_p3137; unfold a_p; omega

theorem BSD_ap_p3163 : a_p 3163 = (86 : ℤ) := by
  have h := BSD_E143_card_p3163; unfold a_p; omega

theorem BSD_ap_p3167 : a_p 3167 = (-6 : ℤ) := by
  have h := BSD_E143_card_p3167; unfold a_p; omega

theorem BSD_ap_p3169 : a_p 3169 = (-7 : ℤ) := by
  have h := BSD_E143_card_p3169; unfold a_p; omega

theorem BSD_ap_p3181 : a_p 3181 = (-12 : ℤ) := by
  have h := BSD_E143_card_p3181; unfold a_p; omega

theorem BSD_ap_p3187 : a_p 3187 = (-80 : ℤ) := by
  have h := BSD_E143_card_p3187; unfold a_p; omega

theorem BSD_ap_p3191 : a_p 3191 = (48 : ℤ) := by
  have h := BSD_E143_card_p3191; unfold a_p; omega

theorem BSD_ap_p3203 : a_p 3203 = (-62 : ℤ) := by
  have h := BSD_E143_card_p3203; unfold a_p; omega

theorem BSD_ap_p3209 : a_p 3209 = (-70 : ℤ) := by
  have h := BSD_E143_card_p3209; unfold a_p; omega

theorem BSD_ap_p3217 : a_p 3217 = (-7 : ℤ) := by
  have h := BSD_E143_card_p3217; unfold a_p; omega

theorem BSD_ap_p3221 : a_p 3221 = (-67 : ℤ) := by
  have h := BSD_E143_card_p3221; unfold a_p; omega

theorem BSD_ap_p3229 : a_p 3229 = (-28 : ℤ) := by
  have h := BSD_E143_card_p3229; unfold a_p; omega

theorem BSD_ap_p3251 : a_p 3251 = (-58 : ℤ) := by
  have h := BSD_E143_card_p3251; unfold a_p; omega

theorem BSD_ap_p3253 : a_p 3253 = (64 : ℤ) := by
  have h := BSD_E143_card_p3253; unfold a_p; omega

theorem BSD_ap_p3257 : a_p 3257 = (-82 : ℤ) := by
  have h := BSD_E143_card_p3257; unfold a_p; omega

theorem BSD_ap_p3259 : a_p 3259 = (-4 : ℤ) := by
  have h := BSD_E143_card_p3259; unfold a_p; omega

theorem BSD_ap_p3271 : a_p 3271 = (95 : ℤ) := by
  have h := BSD_E143_card_p3271; unfold a_p; omega

theorem BSD_ap_p3299 : a_p 3299 = (-20 : ℤ) := by
  have h := BSD_E143_card_p3299; unfold a_p; omega

theorem BSD_ap_p3301 : a_p 3301 = (-57 : ℤ) := by
  have h := BSD_E143_card_p3301; unfold a_p; omega

theorem BSD_ap_p3307 : a_p 3307 = (-8 : ℤ) := by
  have h := BSD_E143_card_p3307; unfold a_p; omega

theorem BSD_ap_p3313 : a_p 3313 = (12 : ℤ) := by
  have h := BSD_E143_card_p3313; unfold a_p; omega

theorem BSD_ap_p3319 : a_p 3319 = (34 : ℤ) := by
  have h := BSD_E143_card_p3319; unfold a_p; omega

theorem BSD_ap_p3323 : a_p 3323 = (-84 : ℤ) := by
  have h := BSD_E143_card_p3323; unfold a_p; omega

theorem BSD_ap_p3329 : a_p 3329 = (58 : ℤ) := by
  have h := BSD_E143_card_p3329; unfold a_p; omega

theorem BSD_ap_p3331 : a_p 3331 = (113 : ℤ) := by
  have h := BSD_E143_card_p3331; unfold a_p; omega

theorem BSD_ap_p3343 : a_p 3343 = (42 : ℤ) := by
  have h := BSD_E143_card_p3343; unfold a_p; omega

theorem BSD_ap_p3347 : a_p 3347 = (57 : ℤ) := by
  have h := BSD_E143_card_p3347; unfold a_p; omega

theorem BSD_ap_p3359 : a_p 3359 = (17 : ℤ) := by
  have h := BSD_E143_card_p3359; unfold a_p; omega

theorem BSD_ap_p3361 : a_p 3361 = (-90 : ℤ) := by
  have h := BSD_E143_card_p3361; unfold a_p; omega

theorem BSD_ap_p3371 : a_p 3371 = (-15 : ℤ) := by
  have h := BSD_E143_card_p3371; unfold a_p; omega

theorem BSD_ap_p3373 : a_p 3373 = (-64 : ℤ) := by
  have h := BSD_E143_card_p3373; unfold a_p; omega

theorem BSD_ap_p3389 : a_p 3389 = (-61 : ℤ) := by
  have h := BSD_E143_card_p3389; unfold a_p; omega

theorem BSD_ap_p3391 : a_p 3391 = (48 : ℤ) := by
  have h := BSD_E143_card_p3391; unfold a_p; omega

theorem BSD_ap_p3407 : a_p 3407 = (94 : ℤ) := by
  have h := BSD_E143_card_p3407; unfold a_p; omega

theorem BSD_ap_p3413 : a_p 3413 = (91 : ℤ) := by
  have h := BSD_E143_card_p3413; unfold a_p; omega

theorem BSD_ap_p3433 : a_p 3433 = (14 : ℤ) := by
  have h := BSD_E143_card_p3433; unfold a_p; omega

theorem BSD_ap_p3449 : a_p 3449 = (84 : ℤ) := by
  have h := BSD_E143_card_p3449; unfold a_p; omega

theorem BSD_ap_p3457 : a_p 3457 = (-5 : ℤ) := by
  have h := BSD_E143_card_p3457; unfold a_p; omega

theorem BSD_ap_p3461 : a_p 3461 = (16 : ℤ) := by
  have h := BSD_E143_card_p3461; unfold a_p; omega

theorem BSD_ap_p3463 : a_p 3463 = (-32 : ℤ) := by
  have h := BSD_E143_card_p3463; unfold a_p; omega

theorem BSD_ap_p3467 : a_p 3467 = (2 : ℤ) := by
  have h := BSD_E143_card_p3467; unfold a_p; omega

theorem BSD_ap_p3469 : a_p 3469 = (37 : ℤ) := by
  have h := BSD_E143_card_p3469; unfold a_p; omega

theorem BSD_ap_p3491 : a_p 3491 = (-89 : ℤ) := by
  have h := BSD_E143_card_p3491; unfold a_p; omega

theorem BSD_ap_p3499 : a_p 3499 = (-92 : ℤ) := by
  have h := BSD_E143_card_p3499; unfold a_p; omega

theorem BSD_ap_p3511 : a_p 3511 = (-32 : ℤ) := by
  have h := BSD_E143_card_p3511; unfold a_p; omega

theorem BSD_ap_p3517 : a_p 3517 = (18 : ℤ) := by
  have h := BSD_E143_card_p3517; unfold a_p; omega

theorem BSD_ap_p3527 : a_p 3527 = (56 : ℤ) := by
  have h := BSD_E143_card_p3527; unfold a_p; omega

theorem BSD_ap_p3529 : a_p 3529 = (19 : ℤ) := by
  have h := BSD_E143_card_p3529; unfold a_p; omega

theorem BSD_ap_p3533 : a_p 3533 = (-36 : ℤ) := by
  have h := BSD_E143_card_p3533; unfold a_p; omega

theorem BSD_ap_p3539 : a_p 3539 = (86 : ℤ) := by
  have h := BSD_E143_card_p3539; unfold a_p; omega

theorem BSD_ap_p3541 : a_p 3541 = (12 : ℤ) := by
  have h := BSD_E143_card_p3541; unfold a_p; omega

theorem BSD_ap_p3547 : a_p 3547 = (107 : ℤ) := by
  have h := BSD_E143_card_p3547; unfold a_p; omega

theorem BSD_ap_p3557 : a_p 3557 = (59 : ℤ) := by
  have h := BSD_E143_card_p3557; unfold a_p; omega

theorem BSD_ap_p3559 : a_p 3559 = (-16 : ℤ) := by
  have h := BSD_E143_card_p3559; unfold a_p; omega

theorem BSD_ap_p3571 : a_p 3571 = (-118 : ℤ) := by
  have h := BSD_E143_card_p3571; unfold a_p; omega

theorem BSD_ap_p3581 : a_p 3581 = (-96 : ℤ) := by
  have h := BSD_E143_card_p3581; unfold a_p; omega

theorem BSD_ap_p3583 : a_p 3583 = (50 : ℤ) := by
  have h := BSD_E143_card_p3583; unfold a_p; omega

theorem BSD_ap_p3593 : a_p 3593 = (76 : ℤ) := by
  have h := BSD_E143_card_p3593; unfold a_p; omega

theorem BSD_ap_p3607 : a_p 3607 = (42 : ℤ) := by
  have h := BSD_E143_card_p3607; unfold a_p; omega

theorem BSD_ap_p3613 : a_p 3613 = (14 : ℤ) := by
  have h := BSD_E143_card_p3613; unfold a_p; omega

theorem BSD_ap_p3617 : a_p 3617 = (-57 : ℤ) := by
  have h := BSD_E143_card_p3617; unfold a_p; omega

theorem BSD_ap_p3623 : a_p 3623 = (48 : ℤ) := by
  have h := BSD_E143_card_p3623; unfold a_p; omega

theorem BSD_ap_p3631 : a_p 3631 = (48 : ℤ) := by
  have h := BSD_E143_card_p3631; unfold a_p; omega

theorem BSD_ap_p3637 : a_p 3637 = (58 : ℤ) := by
  have h := BSD_E143_card_p3637; unfold a_p; omega

theorem BSD_ap_p3643 : a_p 3643 = (-74 : ℤ) := by
  have h := BSD_E143_card_p3643; unfold a_p; omega

theorem BSD_ap_p3659 : a_p 3659 = (102 : ℤ) := by
  have h := BSD_E143_card_p3659; unfold a_p; omega

theorem BSD_ap_p3671 : a_p 3671 = (96 : ℤ) := by
  have h := BSD_E143_card_p3671; unfold a_p; omega

theorem BSD_ap_p3673 : a_p 3673 = (-14 : ℤ) := by
  have h := BSD_E143_card_p3673; unfold a_p; omega

theorem BSD_ap_p3677 : a_p 3677 = (-6 : ℤ) := by
  have h := BSD_E143_card_p3677; unfold a_p; omega

theorem BSD_ap_p3691 : a_p 3691 = (58 : ℤ) := by
  have h := BSD_E143_card_p3691; unfold a_p; omega

theorem BSD_ap_p3697 : a_p 3697 = (-83 : ℤ) := by
  have h := BSD_E143_card_p3697; unfold a_p; omega

theorem BSD_ap_p3701 : a_p 3701 = (42 : ℤ) := by
  have h := BSD_E143_card_p3701; unfold a_p; omega

theorem BSD_ap_p3709 : a_p 3709 = (-38 : ℤ) := by
  have h := BSD_E143_card_p3709; unfold a_p; omega

theorem BSD_ap_p3719 : a_p 3719 = (93 : ℤ) := by
  have h := BSD_E143_card_p3719; unfold a_p; omega

theorem BSD_ap_p3727 : a_p 3727 = (3 : ℤ) := by
  have h := BSD_E143_card_p3727; unfold a_p; omega

theorem BSD_ap_p3733 : a_p 3733 = (38 : ℤ) := by
  have h := BSD_E143_card_p3733; unfold a_p; omega

theorem BSD_ap_p3739 : a_p 3739 = (30 : ℤ) := by
  have h := BSD_E143_card_p3739; unfold a_p; omega

theorem BSD_ap_p3761 : a_p 3761 = (44 : ℤ) := by
  have h := BSD_E143_card_p3761; unfold a_p; omega

theorem BSD_ap_p3767 : a_p 3767 = (-103 : ℤ) := by
  have h := BSD_E143_card_p3767; unfold a_p; omega

theorem BSD_ap_p3769 : a_p 3769 = (26 : ℤ) := by
  have h := BSD_E143_card_p3769; unfold a_p; omega

theorem BSD_ap_p3779 : a_p 3779 = (92 : ℤ) := by
  have h := BSD_E143_card_p3779; unfold a_p; omega

theorem BSD_ap_p3793 : a_p 3793 = (-38 : ℤ) := by
  have h := BSD_E143_card_p3793; unfold a_p; omega

theorem BSD_ap_p3797 : a_p 3797 = (-74 : ℤ) := by
  have h := BSD_E143_card_p3797; unfold a_p; omega

theorem BSD_ap_p3803 : a_p 3803 = (-14 : ℤ) := by
  have h := BSD_E143_card_p3803; unfold a_p; omega

theorem BSD_ap_p3821 : a_p 3821 = (61 : ℤ) := by
  have h := BSD_E143_card_p3821; unfold a_p; omega

theorem BSD_ap_p3823 : a_p 3823 = (-62 : ℤ) := by
  have h := BSD_E143_card_p3823; unfold a_p; omega

theorem BSD_ap_p3833 : a_p 3833 = (93 : ℤ) := by
  have h := BSD_E143_card_p3833; unfold a_p; omega

theorem BSD_ap_p3847 : a_p 3847 = (-88 : ℤ) := by
  have h := BSD_E143_card_p3847; unfold a_p; omega

theorem BSD_ap_p3851 : a_p 3851 = (-85 : ℤ) := by
  have h := BSD_E143_card_p3851; unfold a_p; omega

theorem BSD_ap_p3853 : a_p 3853 = (46 : ℤ) := by
  have h := BSD_E143_card_p3853; unfold a_p; omega

theorem BSD_ap_p3863 : a_p 3863 = (-84 : ℤ) := by
  have h := BSD_E143_card_p3863; unfold a_p; omega

theorem BSD_ap_p3877 : a_p 3877 = (6 : ℤ) := by
  have h := BSD_E143_card_p3877; unfold a_p; omega

theorem BSD_ap_p3881 : a_p 3881 = (105 : ℤ) := by
  have h := BSD_E143_card_p3881; unfold a_p; omega

theorem BSD_ap_p3889 : a_p 3889 = (38 : ℤ) := by
  have h := BSD_E143_card_p3889; unfold a_p; omega

theorem BSD_ap_p3907 : a_p 3907 = (58 : ℤ) := by
  have h := BSD_E143_card_p3907; unfold a_p; omega

theorem BSD_ap_p3911 : a_p 3911 = (64 : ℤ) := by
  have h := BSD_E143_card_p3911; unfold a_p; omega

theorem BSD_ap_p3917 : a_p 3917 = (-21 : ℤ) := by
  have h := BSD_E143_card_p3917; unfold a_p; omega

theorem BSD_ap_p3919 : a_p 3919 = (-112 : ℤ) := by
  have h := BSD_E143_card_p3919; unfold a_p; omega

theorem BSD_ap_p3923 : a_p 3923 = (-24 : ℤ) := by
  have h := BSD_E143_card_p3923; unfold a_p; omega

theorem BSD_ap_p3929 : a_p 3929 = (-74 : ℤ) := by
  have h := BSD_E143_card_p3929; unfold a_p; omega

theorem BSD_ap_p3931 : a_p 3931 = (-107 : ℤ) := by
  have h := BSD_E143_card_p3931; unfold a_p; omega

theorem BSD_ap_p3943 : a_p 3943 = (0 : ℤ) := by
  have h := BSD_E143_card_p3943; unfold a_p; omega

theorem BSD_ap_p3947 : a_p 3947 = (63 : ℤ) := by
  have h := BSD_E143_card_p3947; unfold a_p; omega

theorem BSD_ap_p3967 : a_p 3967 = (-24 : ℤ) := by
  have h := BSD_E143_card_p3967; unfold a_p; omega

theorem BSD_ap_p3989 : a_p 3989 = (-58 : ℤ) := by
  have h := BSD_E143_card_p3989; unfold a_p; omega

theorem BSD_ap_p4001 : a_p 4001 = (-6 : ℤ) := by
  have h := BSD_E143_card_p4001; unfold a_p; omega

theorem BSD_ap_p4003 : a_p 4003 = (114 : ℤ) := by
  have h := BSD_E143_card_p4003; unfold a_p; omega

theorem BSD_ap_p4007 : a_p 4007 = (-24 : ℤ) := by
  have h := BSD_E143_card_p4007; unfold a_p; omega

theorem BSD_ap_p4013 : a_p 4013 = (-46 : ℤ) := by
  have h := BSD_E143_card_p4013; unfold a_p; omega

theorem BSD_ap_p4019 : a_p 4019 = (5 : ℤ) := by
  have h := BSD_E143_card_p4019; unfold a_p; omega

theorem BSD_ap_p4021 : a_p 4021 = (32 : ℤ) := by
  have h := BSD_E143_card_p4021; unfold a_p; omega

theorem BSD_ap_p4027 : a_p 4027 = (28 : ℤ) := by
  have h := BSD_E143_card_p4027; unfold a_p; omega

theorem BSD_ap_p4049 : a_p 4049 = (99 : ℤ) := by
  have h := BSD_E143_card_p4049; unfold a_p; omega

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

theorem BSD_ap_p4133 : a_p 4133 = (102 : ℤ) := by
  have h := BSD_E143_card_p4133; unfold a_p; omega

theorem BSD_ap_p4139 : a_p 4139 = (-40 : ℤ) := by
  have h := BSD_E143_card_p4139; unfold a_p; omega

theorem BSD_ap_p4153 : a_p 4153 = (-42 : ℤ) := by
  have h := BSD_E143_card_p4153; unfold a_p; omega

theorem BSD_ap_p4157 : a_p 4157 = (58 : ℤ) := by
  have h := BSD_E143_card_p4157; unfold a_p; omega

theorem BSD_ap_p4159 : a_p 4159 = (-75 : ℤ) := by
  have h := BSD_E143_card_p4159; unfold a_p; omega

theorem BSD_ap_p4177 : a_p 4177 = (102 : ℤ) := by
  have h := BSD_E143_card_p4177; unfold a_p; omega

theorem BSD_ap_p4201 : a_p 4201 = (-22 : ℤ) := by
  have h := BSD_E143_card_p4201; unfold a_p; omega

theorem BSD_ap_p4211 : a_p 4211 = (-83 : ℤ) := by
  have h := BSD_E143_card_p4211; unfold a_p; omega

theorem BSD_ap_p4217 : a_p 4217 = (-105 : ℤ) := by
  have h := BSD_E143_card_p4217; unfold a_p; omega

theorem BSD_ap_p4219 : a_p 4219 = (-18 : ℤ) := by
  have h := BSD_E143_card_p4219; unfold a_p; omega

theorem BSD_ap_p4229 : a_p 4229 = (-15 : ℤ) := by
  have h := BSD_E143_card_p4229; unfold a_p; omega

theorem BSD_ap_p4231 : a_p 4231 = (-102 : ℤ) := by
  have h := BSD_E143_card_p4231; unfold a_p; omega

theorem BSD_ap_p4241 : a_p 4241 = (-58 : ℤ) := by
  have h := BSD_E143_card_p4241; unfold a_p; omega

theorem BSD_ap_p4243 : a_p 4243 = (26 : ℤ) := by
  have h := BSD_E143_card_p4243; unfold a_p; omega

theorem BSD_ap_p4253 : a_p 4253 = (-54 : ℤ) := by
  have h := BSD_E143_card_p4253; unfold a_p; omega

theorem BSD_ap_p4259 : a_p 4259 = (72 : ℤ) := by
  have h := BSD_E143_card_p4259; unfold a_p; omega

theorem BSD_ap_p4261 : a_p 4261 = (31 : ℤ) := by
  have h := BSD_E143_card_p4261; unfold a_p; omega

theorem BSD_ap_p4271 : a_p 4271 = (-75 : ℤ) := by
  have h := BSD_E143_card_p4271; unfold a_p; omega

theorem BSD_ap_p4273 : a_p 4273 = (51 : ℤ) := by
  have h := BSD_E143_card_p4273; unfold a_p; omega

theorem BSD_ap_p4283 : a_p 4283 = (13 : ℤ) := by
  have h := BSD_E143_card_p4283; unfold a_p; omega

theorem BSD_ap_p4289 : a_p 4289 = (-50 : ℤ) := by
  have h := BSD_E143_card_p4289; unfold a_p; omega

theorem BSD_ap_p4297 : a_p 4297 = (8 : ℤ) := by
  have h := BSD_E143_card_p4297; unfold a_p; omega

theorem BSD_ap_p4327 : a_p 4327 = (107 : ℤ) := by
  have h := BSD_E143_card_p4327; unfold a_p; omega

theorem BSD_ap_p4337 : a_p 4337 = (18 : ℤ) := by
  have h := BSD_E143_card_p4337; unfold a_p; omega

theorem BSD_ap_p4339 : a_p 4339 = (-77 : ℤ) := by
  have h := BSD_E143_card_p4339; unfold a_p; omega

theorem BSD_ap_p4349 : a_p 4349 = (-18 : ℤ) := by
  have h := BSD_E143_card_p4349; unfold a_p; omega

theorem BSD_ap_p4357 : a_p 4357 = (117 : ℤ) := by
  have h := BSD_E143_card_p4357; unfold a_p; omega

theorem BSD_ap_p4363 : a_p 4363 = (118 : ℤ) := by
  have h := BSD_E143_card_p4363; unfold a_p; omega

theorem BSD_ap_p4373 : a_p 4373 = (96 : ℤ) := by
  have h := BSD_E143_card_p4373; unfold a_p; omega

theorem BSD_ap_p4391 : a_p 4391 = (-108 : ℤ) := by
  have h := BSD_E143_card_p4391; unfold a_p; omega

theorem BSD_ap_p4397 : a_p 4397 = (52 : ℤ) := by
  have h := BSD_E143_card_p4397; unfold a_p; omega

theorem BSD_ap_p4409 : a_p 4409 = (54 : ℤ) := by
  have h := BSD_E143_card_p4409; unfold a_p; omega

theorem BSD_ap_p4421 : a_p 4421 = (12 : ℤ) := by
  have h := BSD_E143_card_p4421; unfold a_p; omega

theorem BSD_ap_p4423 : a_p 4423 = (61 : ℤ) := by
  have h := BSD_E143_card_p4423; unfold a_p; omega

theorem BSD_ap_p4441 : a_p 4441 = (64 : ℤ) := by
  have h := BSD_E143_card_p4441; unfold a_p; omega

theorem BSD_ap_p4447 : a_p 4447 = (-41 : ℤ) := by
  have h := BSD_E143_card_p4447; unfold a_p; omega

theorem BSD_ap_p4451 : a_p 4451 = (98 : ℤ) := by
  have h := BSD_E143_card_p4451; unfold a_p; omega

theorem BSD_ap_p4457 : a_p 4457 = (-42 : ℤ) := by
  have h := BSD_E143_card_p4457; unfold a_p; omega

theorem BSD_ap_p4463 : a_p 4463 = (108 : ℤ) := by
  have h := BSD_E143_card_p4463; unfold a_p; omega

theorem BSD_ap_p4481 : a_p 4481 = (102 : ℤ) := by
  have h := BSD_E143_card_p4481; unfold a_p; omega

theorem BSD_ap_p4483 : a_p 4483 = (-24 : ℤ) := by
  have h := BSD_E143_card_p4483; unfold a_p; omega

theorem BSD_ap_p4493 : a_p 4493 = (-21 : ℤ) := by
  have h := BSD_E143_card_p4493; unfold a_p; omega

theorem BSD_ap_p4507 : a_p 4507 = (-26 : ℤ) := by
  have h := BSD_E143_card_p4507; unfold a_p; omega

theorem BSD_ap_p4513 : a_p 4513 = (1 : ℤ) := by
  have h := BSD_E143_card_p4513; unfold a_p; omega

theorem BSD_ap_p4517 : a_p 4517 = (108 : ℤ) := by
  have h := BSD_E143_card_p4517; unfold a_p; omega

theorem BSD_ap_p4519 : a_p 4519 = (23 : ℤ) := by
  have h := BSD_E143_card_p4519; unfold a_p; omega

theorem BSD_ap_p4523 : a_p 4523 = (68 : ℤ) := by
  have h := BSD_E143_card_p4523; unfold a_p; omega

theorem BSD_ap_p4547 : a_p 4547 = (-12 : ℤ) := by
  have h := BSD_E143_card_p4547; unfold a_p; omega

theorem BSD_ap_p4549 : a_p 4549 = (76 : ℤ) := by
  have h := BSD_E143_card_p4549; unfold a_p; omega

theorem BSD_ap_p4561 : a_p 4561 = (34 : ℤ) := by
  have h := BSD_E143_card_p4561; unfold a_p; omega

theorem BSD_ap_p4567 : a_p 4567 = (-58 : ℤ) := by
  have h := BSD_E143_card_p4567; unfold a_p; omega

theorem BSD_ap_p4583 : a_p 4583 = (-84 : ℤ) := by
  have h := BSD_E143_card_p4583; unfold a_p; omega

theorem BSD_ap_p4591 : a_p 4591 = (-120 : ℤ) := by
  have h := BSD_E143_card_p4591; unfold a_p; omega

theorem BSD_ap_p4597 : a_p 4597 = (-16 : ℤ) := by
  have h := BSD_E143_card_p4597; unfold a_p; omega

theorem BSD_ap_p4603 : a_p 4603 = (-59 : ℤ) := by
  have h := BSD_E143_card_p4603; unfold a_p; omega

theorem BSD_ap_p4621 : a_p 4621 = (-30 : ℤ) := by
  have h := BSD_E143_card_p4621; unfold a_p; omega

theorem BSD_ap_p4637 : a_p 4637 = (-36 : ℤ) := by
  have h := BSD_E143_card_p4637; unfold a_p; omega

theorem BSD_ap_p4639 : a_p 4639 = (-68 : ℤ) := by
  have h := BSD_E143_card_p4639; unfold a_p; omega

theorem BSD_ap_p4643 : a_p 4643 = (-3 : ℤ) := by
  have h := BSD_E143_card_p4643; unfold a_p; omega

theorem BSD_ap_p4649 : a_p 4649 = (-100 : ℤ) := by
  have h := BSD_E143_card_p4649; unfold a_p; omega

theorem BSD_ap_p4651 : a_p 4651 = (7 : ℤ) := by
  have h := BSD_E143_card_p4651; unfold a_p; omega

theorem BSD_ap_p4657 : a_p 4657 = (41 : ℤ) := by
  have h := BSD_E143_card_p4657; unfold a_p; omega

theorem BSD_ap_p4663 : a_p 4663 = (-4 : ℤ) := by
  have h := BSD_E143_card_p4663; unfold a_p; omega

theorem BSD_ap_p4673 : a_p 4673 = (-94 : ℤ) := by
  have h := BSD_E143_card_p4673; unfold a_p; omega

theorem BSD_ap_p4679 : a_p 4679 = (-87 : ℤ) := by
  have h := BSD_E143_card_p4679; unfold a_p; omega

theorem BSD_ap_p4691 : a_p 4691 = (-5 : ℤ) := by
  have h := BSD_E143_card_p4691; unfold a_p; omega

theorem BSD_ap_p4703 : a_p 4703 = (12 : ℤ) := by
  have h := BSD_E143_card_p4703; unfold a_p; omega

theorem BSD_ap_p4721 : a_p 4721 = (88 : ℤ) := by
  have h := BSD_E143_card_p4721; unfold a_p; omega

theorem BSD_ap_p4723 : a_p 4723 = (-76 : ℤ) := by
  have h := BSD_E143_card_p4723; unfold a_p; omega

theorem BSD_ap_p4729 : a_p 4729 = (110 : ℤ) := by
  have h := BSD_E143_card_p4729; unfold a_p; omega

theorem BSD_ap_p4733 : a_p 4733 = (69 : ℤ) := by
  have h := BSD_E143_card_p4733; unfold a_p; omega

theorem BSD_ap_p4751 : a_p 4751 = (-84 : ℤ) := by
  have h := BSD_E143_card_p4751; unfold a_p; omega

theorem BSD_ap_p4759 : a_p 4759 = (28 : ℤ) := by
  have h := BSD_E143_card_p4759; unfold a_p; omega

theorem BSD_ap_p4783 : a_p 4783 = (51 : ℤ) := by
  have h := BSD_E143_card_p4783; unfold a_p; omega

theorem BSD_ap_p4787 : a_p 4787 = (-28 : ℤ) := by
  have h := BSD_E143_card_p4787; unfold a_p; omega

theorem BSD_ap_p4789 : a_p 4789 = (-86 : ℤ) := by
  have h := BSD_E143_card_p4789; unfold a_p; omega

theorem BSD_ap_p4793 : a_p 4793 = (-58 : ℤ) := by
  have h := BSD_E143_card_p4793; unfold a_p; omega

theorem BSD_ap_p4799 : a_p 4799 = (47 : ℤ) := by
  have h := BSD_E143_card_p4799; unfold a_p; omega

theorem BSD_ap_p4801 : a_p 4801 = (-75 : ℤ) := by
  have h := BSD_E143_card_p4801; unfold a_p; omega

theorem BSD_ap_p4813 : a_p 4813 = (-84 : ℤ) := by
  have h := BSD_E143_card_p4813; unfold a_p; omega

theorem BSD_ap_p4817 : a_p 4817 = (28 : ℤ) := by
  have h := BSD_E143_card_p4817; unfold a_p; omega

theorem BSD_ap_p4831 : a_p 4831 = (46 : ℤ) := by
  have h := BSD_E143_card_p4831; unfold a_p; omega

theorem BSD_ap_p4861 : a_p 4861 = (-10 : ℤ) := by
  have h := BSD_E143_card_p4861; unfold a_p; omega

theorem BSD_ap_p4871 : a_p 4871 = (-32 : ℤ) := by
  have h := BSD_E143_card_p4871; unfold a_p; omega

theorem BSD_ap_p4877 : a_p 4877 = (7 : ℤ) := by
  have h := BSD_E143_card_p4877; unfold a_p; omega

theorem BSD_ap_p4889 : a_p 4889 = (-55 : ℤ) := by
  have h := BSD_E143_card_p4889; unfold a_p; omega

theorem BSD_ap_p4903 : a_p 4903 = (38 : ℤ) := by
  have h := BSD_E143_card_p4903; unfold a_p; omega

theorem BSD_ap_p4909 : a_p 4909 = (1 : ℤ) := by
  have h := BSD_E143_card_p4909; unfold a_p; omega

theorem BSD_ap_p4919 : a_p 4919 = (94 : ℤ) := by
  have h := BSD_E143_card_p4919; unfold a_p; omega

theorem BSD_ap_p4931 : a_p 4931 = (48 : ℤ) := by
  have h := BSD_E143_card_p4931; unfold a_p; omega

theorem BSD_ap_p4933 : a_p 4933 = (102 : ℤ) := by
  have h := BSD_E143_card_p4933; unfold a_p; omega

theorem BSD_ap_p4937 : a_p 4937 = (90 : ℤ) := by
  have h := BSD_E143_card_p4937; unfold a_p; omega

theorem BSD_ap_p4943 : a_p 4943 = (-84 : ℤ) := by
  have h := BSD_E143_card_p4943; unfold a_p; omega

theorem BSD_ap_p4951 : a_p 4951 = (80 : ℤ) := by
  have h := BSD_E143_card_p4951; unfold a_p; omega

theorem BSD_ap_p4957 : a_p 4957 = (100 : ℤ) := by
  have h := BSD_E143_card_p4957; unfold a_p; omega

theorem BSD_ap_p4967 : a_p 4967 = (78 : ℤ) := by
  have h := BSD_E143_card_p4967; unfold a_p; omega

theorem BSD_ap_p4969 : a_p 4969 = (-40 : ℤ) := by
  have h := BSD_E143_card_p4969; unfold a_p; omega

theorem BSD_ap_p4973 : a_p 4973 = (69 : ℤ) := by
  have h := BSD_E143_card_p4973; unfold a_p; omega

theorem BSD_ap_p4987 : a_p 4987 = (12 : ℤ) := by
  have h := BSD_E143_card_p4987; unfold a_p; omega

theorem BSD_ap_p4993 : a_p 4993 = (60 : ℤ) := by
  have h := BSD_E143_card_p4993; unfold a_p; omega

theorem BSD_ap_p4999 : a_p 4999 = (-112 : ℤ) := by
  have h := BSD_E143_card_p4999; unfold a_p; omega

theorem BSD_ap_p5003 : a_p 5003 = (-103 : ℤ) := by
  have h := BSD_E143_card_p5003; unfold a_p; omega

theorem BSD_ap_p5009 : a_p 5009 = (7 : ℤ) := by
  have h := BSD_E143_card_p5009; unfold a_p; omega

theorem BSD_ap_p5011 : a_p 5011 = (108 : ℤ) := by
  have h := BSD_E143_card_p5011; unfold a_p; omega

theorem BSD_ap_p5021 : a_p 5021 = (85 : ℤ) := by
  have h := BSD_E143_card_p5021; unfold a_p; omega

theorem BSD_ap_p5023 : a_p 5023 = (72 : ℤ) := by
  have h := BSD_E143_card_p5023; unfold a_p; omega

theorem BSD_ap_p5039 : a_p 5039 = (17 : ℤ) := by
  have h := BSD_E143_card_p5039; unfold a_p; omega

theorem BSD_ap_p5051 : a_p 5051 = (102 : ℤ) := by
  have h := BSD_E143_card_p5051; unfold a_p; omega

theorem BSD_ap_p5059 : a_p 5059 = (22 : ℤ) := by
  have h := BSD_E143_card_p5059; unfold a_p; omega

theorem BSD_ap_p5077 : a_p 5077 = (14 : ℤ) := by
  have h := BSD_E143_card_p5077; unfold a_p; omega

theorem BSD_ap_p5081 : a_p 5081 = (-18 : ℤ) := by
  have h := BSD_E143_card_p5081; unfold a_p; omega

theorem BSD_ap_p5087 : a_p 5087 = (-103 : ℤ) := by
  have h := BSD_E143_card_p5087; unfold a_p; omega

theorem BSD_ap_p5099 : a_p 5099 = (112 : ℤ) := by
  have h := BSD_E143_card_p5099; unfold a_p; omega

theorem BSD_ap_p5101 : a_p 5101 = (38 : ℤ) := by
  have h := BSD_E143_card_p5101; unfold a_p; omega

theorem BSD_ap_p5107 : a_p 5107 = (-68 : ℤ) := by
  have h := BSD_E143_card_p5107; unfold a_p; omega

theorem BSD_ap_p5113 : a_p 5113 = (-139 : ℤ) := by
  have h := BSD_E143_card_p5113; unfold a_p; omega

theorem BSD_ap_p5119 : a_p 5119 = (-33 : ℤ) := by
  have h := BSD_E143_card_p5119; unfold a_p; omega

theorem BSD_ap_p5147 : a_p 5147 = (-96 : ℤ) := by
  have h := BSD_E143_card_p5147; unfold a_p; omega

theorem BSD_ap_p5153 : a_p 5153 = (-21 : ℤ) := by
  have h := BSD_E143_card_p5153; unfold a_p; omega

theorem BSD_ap_p5167 : a_p 5167 = (86 : ℤ) := by
  have h := BSD_E143_card_p5167; unfold a_p; omega

theorem BSD_ap_p5171 : a_p 5171 = (97 : ℤ) := by
  have h := BSD_E143_card_p5171; unfold a_p; omega

theorem BSD_ap_p5179 : a_p 5179 = (16 : ℤ) := by
  have h := BSD_E143_card_p5179; unfold a_p; omega

theorem BSD_ap_p5189 : a_p 5189 = (-36 : ℤ) := by
  have h := BSD_E143_card_p5189; unfold a_p; omega

theorem BSD_ap_p5197 : a_p 5197 = (107 : ℤ) := by
  have h := BSD_E143_card_p5197; unfold a_p; omega

theorem BSD_ap_p5209 : a_p 5209 = (6 : ℤ) := by
  have h := BSD_E143_card_p5209; unfold a_p; omega

theorem BSD_ap_p5227 : a_p 5227 = (-56 : ℤ) := by
  have h := BSD_E143_card_p5227; unfold a_p; omega

theorem BSD_ap_p5231 : a_p 5231 = (-10 : ℤ) := by
  have h := BSD_E143_card_p5231; unfold a_p; omega

theorem BSD_ap_p5233 : a_p 5233 = (52 : ℤ) := by
  have h := BSD_E143_card_p5233; unfold a_p; omega

theorem BSD_ap_p5237 : a_p 5237 = (65 : ℤ) := by
  have h := BSD_E143_card_p5237; unfold a_p; omega

theorem BSD_ap_p5261 : a_p 5261 = (-5 : ℤ) := by
  have h := BSD_E143_card_p5261; unfold a_p; omega

theorem BSD_ap_p5273 : a_p 5273 = (-135 : ℤ) := by
  have h := BSD_E143_card_p5273; unfold a_p; omega

theorem BSD_ap_p5279 : a_p 5279 = (-64 : ℤ) := by
  have h := BSD_E143_card_p5279; unfold a_p; omega

theorem BSD_ap_p5281 : a_p 5281 = (17 : ℤ) := by
  have h := BSD_E143_card_p5281; unfold a_p; omega

theorem BSD_ap_p5297 : a_p 5297 = (-132 : ℤ) := by
  have h := BSD_E143_card_p5297; unfold a_p; omega

theorem BSD_ap_p5303 : a_p 5303 = (63 : ℤ) := by
  have h := BSD_E143_card_p5303; unfold a_p; omega

theorem BSD_ap_p5309 : a_p 5309 = (36 : ℤ) := by
  have h := BSD_E143_card_p5309; unfold a_p; omega

theorem BSD_ap_p5323 : a_p 5323 = (-70 : ℤ) := by
  have h := BSD_E143_card_p5323; unfold a_p; omega

theorem BSD_ap_p5333 : a_p 5333 = (114 : ℤ) := by
  have h := BSD_E143_card_p5333; unfold a_p; omega

theorem BSD_ap_p5347 : a_p 5347 = (127 : ℤ) := by
  have h := BSD_E143_card_p5347; unfold a_p; omega

theorem BSD_ap_p5351 : a_p 5351 = (-5 : ℤ) := by
  have h := BSD_E143_card_p5351; unfold a_p; omega

theorem BSD_ap_p5381 : a_p 5381 = (12 : ℤ) := by
  have h := BSD_E143_card_p5381; unfold a_p; omega

theorem BSD_ap_p5387 : a_p 5387 = (-20 : ℤ) := by
  have h := BSD_E143_card_p5387; unfold a_p; omega

theorem BSD_ap_p5393 : a_p 5393 = (-21 : ℤ) := by
  have h := BSD_E143_card_p5393; unfold a_p; omega

theorem BSD_ap_p5399 : a_p 5399 = (133 : ℤ) := by
  have h := BSD_E143_card_p5399; unfold a_p; omega

theorem BSD_ap_p5407 : a_p 5407 = (-122 : ℤ) := by
  have h := BSD_E143_card_p5407; unfold a_p; omega

theorem BSD_ap_p5413 : a_p 5413 = (-22 : ℤ) := by
  have h := BSD_E143_card_p5413; unfold a_p; omega

theorem BSD_ap_p5417 : a_p 5417 = (78 : ℤ) := by
  have h := BSD_E143_card_p5417; unfold a_p; omega

theorem BSD_ap_p5419 : a_p 5419 = (-40 : ℤ) := by
  have h := BSD_E143_card_p5419; unfold a_p; omega

theorem BSD_ap_p5431 : a_p 5431 = (20 : ℤ) := by
  have h := BSD_E143_card_p5431; unfold a_p; omega

theorem BSD_ap_p5437 : a_p 5437 = (-6 : ℤ) := by
  have h := BSD_E143_card_p5437; unfold a_p; omega

theorem BSD_ap_p5441 : a_p 5441 = (52 : ℤ) := by
  have h := BSD_E143_card_p5441; unfold a_p; omega

theorem BSD_ap_p5443 : a_p 5443 = (93 : ℤ) := by
  have h := BSD_E143_card_p5443; unfold a_p; omega

theorem BSD_ap_p5449 : a_p 5449 = (125 : ℤ) := by
  have h := BSD_E143_card_p5449; unfold a_p; omega

theorem BSD_ap_p5471 : a_p 5471 = (-125 : ℤ) := by
  have h := BSD_E143_card_p5471; unfold a_p; omega

theorem BSD_ap_p5477 : a_p 5477 = (-116 : ℤ) := by
  have h := BSD_E143_card_p5477; unfold a_p; omega

theorem BSD_ap_p5479 : a_p 5479 = (-125 : ℤ) := by
  have h := BSD_E143_card_p5479; unfold a_p; omega

theorem BSD_ap_p5483 : a_p 5483 = (-36 : ℤ) := by
  have h := BSD_E143_card_p5483; unfold a_p; omega

theorem BSD_ap_p5501 : a_p 5501 = (-107 : ℤ) := by
  have h := BSD_E143_card_p5501; unfold a_p; omega

theorem BSD_ap_p5503 : a_p 5503 = (115 : ℤ) := by
  have h := BSD_E143_card_p5503; unfold a_p; omega

theorem BSD_ap_p5507 : a_p 5507 = (-32 : ℤ) := by
  have h := BSD_E143_card_p5507; unfold a_p; omega

theorem BSD_ap_p5519 : a_p 5519 = (66 : ℤ) := by
  have h := BSD_E143_card_p5519; unfold a_p; omega

theorem BSD_ap_p5521 : a_p 5521 = (24 : ℤ) := by
  have h := BSD_E143_card_p5521; unfold a_p; omega

theorem BSD_ap_p5527 : a_p 5527 = (-20 : ℤ) := by
  have h := BSD_E143_card_p5527; unfold a_p; omega

theorem BSD_ap_p5531 : a_p 5531 = (117 : ℤ) := by
  have h := BSD_E143_card_p5531; unfold a_p; omega

theorem BSD_ap_p5557 : a_p 5557 = (36 : ℤ) := by
  have h := BSD_E143_card_p5557; unfold a_p; omega

theorem BSD_ap_p5563 : a_p 5563 = (2 : ℤ) := by
  have h := BSD_E143_card_p5563; unfold a_p; omega

theorem BSD_ap_p5569 : a_p 5569 = (129 : ℤ) := by
  have h := BSD_E143_card_p5569; unfold a_p; omega

theorem BSD_ap_p5573 : a_p 5573 = (-36 : ℤ) := by
  have h := BSD_E143_card_p5573; unfold a_p; omega

theorem BSD_ap_p5581 : a_p 5581 = (-97 : ℤ) := by
  have h := BSD_E143_card_p5581; unfold a_p; omega

theorem BSD_ap_p5591 : a_p 5591 = (51 : ℤ) := by
  have h := BSD_E143_card_p5591; unfold a_p; omega

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

theorem BSD_ap_p5689 : a_p 5689 = (-28 : ℤ) := by
  have h := BSD_E143_card_p5689; unfold a_p; omega

theorem BSD_ap_p5693 : a_p 5693 = (-72 : ℤ) := by
  have h := BSD_E143_card_p5693; unfold a_p; omega

theorem BSD_ap_p5701 : a_p 5701 = (75 : ℤ) := by
  have h := BSD_E143_card_p5701; unfold a_p; omega

theorem BSD_ap_p5711 : a_p 5711 = (26 : ℤ) := by
  have h := BSD_E143_card_p5711; unfold a_p; omega

theorem BSD_ap_p5717 : a_p 5717 = (-76 : ℤ) := by
  have h := BSD_E143_card_p5717; unfold a_p; omega

theorem BSD_ap_p5737 : a_p 5737 = (-86 : ℤ) := by
  have h := BSD_E143_card_p5737; unfold a_p; omega

theorem BSD_ap_p5741 : a_p 5741 = (120 : ℤ) := by
  have h := BSD_E143_card_p5741; unfold a_p; omega

theorem BSD_ap_p5743 : a_p 5743 = (55 : ℤ) := by
  have h := BSD_E143_card_p5743; unfold a_p; omega

theorem BSD_ap_p5749 : a_p 5749 = (46 : ℤ) := by
  have h := BSD_E143_card_p5749; unfold a_p; omega

theorem BSD_ap_p5779 : a_p 5779 = (-5 : ℤ) := by
  have h := BSD_E143_card_p5779; unfold a_p; omega

theorem BSD_ap_p5783 : a_p 5783 = (14 : ℤ) := by
  have h := BSD_E143_card_p5783; unfold a_p; omega

theorem BSD_ap_p5791 : a_p 5791 = (76 : ℤ) := by
  have h := BSD_E143_card_p5791; unfold a_p; omega

theorem BSD_ap_p5801 : a_p 5801 = (50 : ℤ) := by
  have h := BSD_E143_card_p5801; unfold a_p; omega

theorem BSD_ap_p5807 : a_p 5807 = (-78 : ℤ) := by
  have h := BSD_E143_card_p5807; unfold a_p; omega

theorem BSD_ap_p5813 : a_p 5813 = (113 : ℤ) := by
  have h := BSD_E143_card_p5813; unfold a_p; omega

theorem BSD_ap_p5821 : a_p 5821 = (-58 : ℤ) := by
  have h := BSD_E143_card_p5821; unfold a_p; omega

theorem BSD_ap_p5827 : a_p 5827 = (64 : ℤ) := by
  have h := BSD_E143_card_p5827; unfold a_p; omega

theorem BSD_ap_p5839 : a_p 5839 = (-24 : ℤ) := by
  have h := BSD_E143_card_p5839; unfold a_p; omega

theorem BSD_ap_p5843 : a_p 5843 = (-112 : ℤ) := by
  have h := BSD_E143_card_p5843; unfold a_p; omega

theorem BSD_ap_p5849 : a_p 5849 = (-12 : ℤ) := by
  have h := BSD_E143_card_p5849; unfold a_p; omega

theorem BSD_ap_p5851 : a_p 5851 = (-118 : ℤ) := by
  have h := BSD_E143_card_p5851; unfold a_p; omega

theorem BSD_ap_p5857 : a_p 5857 = (65 : ℤ) := by
  have h := BSD_E143_card_p5857; unfold a_p; omega

theorem BSD_ap_p5861 : a_p 5861 = (-6 : ℤ) := by
  have h := BSD_E143_card_p5861; unfold a_p; omega

theorem BSD_ap_p5867 : a_p 5867 = (-15 : ℤ) := by
  have h := BSD_E143_card_p5867; unfold a_p; omega

theorem BSD_ap_p5869 : a_p 5869 = (-80 : ℤ) := by
  have h := BSD_E143_card_p5869; unfold a_p; omega

theorem BSD_ap_p5879 : a_p 5879 = (5 : ℤ) := by
  have h := BSD_E143_card_p5879; unfold a_p; omega

theorem BSD_ap_p5881 : a_p 5881 = (48 : ℤ) := by
  have h := BSD_E143_card_p5881; unfold a_p; omega

theorem BSD_ap_p5897 : a_p 5897 = (-97 : ℤ) := by
  have h := BSD_E143_card_p5897; unfold a_p; omega

theorem BSD_ap_p5903 : a_p 5903 = (-26 : ℤ) := by
  have h := BSD_E143_card_p5903; unfold a_p; omega

theorem BSD_ap_p5923 : a_p 5923 = (-7 : ℤ) := by
  have h := BSD_E143_card_p5923; unfold a_p; omega

theorem BSD_ap_p5927 : a_p 5927 = (51 : ℤ) := by
  have h := BSD_E143_card_p5927; unfold a_p; omega

theorem BSD_ap_p5939 : a_p 5939 = (74 : ℤ) := by
  have h := BSD_E143_card_p5939; unfold a_p; omega

theorem BSD_ap_p5953 : a_p 5953 = (72 : ℤ) := by
  have h := BSD_E143_card_p5953; unfold a_p; omega

theorem BSD_ap_p5981 : a_p 5981 = (-140 : ℤ) := by
  have h := BSD_E143_card_p5981; unfold a_p; omega

theorem BSD_ap_p5987 : a_p 5987 = (-121 : ℤ) := by
  have h := BSD_E143_card_p5987; unfold a_p; omega

theorem BSD_ap_p6007 : a_p 6007 = (-140 : ℤ) := by
  have h := BSD_E143_card_p6007; unfold a_p; omega

theorem BSD_ap_p6011 : a_p 6011 = (-105 : ℤ) := by
  have h := BSD_E143_card_p6011; unfold a_p; omega

theorem BSD_ap_p6029 : a_p 6029 = (21 : ℤ) := by
  have h := BSD_E143_card_p6029; unfold a_p; omega

theorem BSD_ap_p6037 : a_p 6037 = (53 : ℤ) := by
  have h := BSD_E143_card_p6037; unfold a_p; omega

theorem BSD_ap_p6043 : a_p 6043 = (17 : ℤ) := by
  have h := BSD_E143_card_p6043; unfold a_p; omega

theorem BSD_ap_p6047 : a_p 6047 = (40 : ℤ) := by
  have h := BSD_E143_card_p6047; unfold a_p; omega

theorem BSD_ap_p6053 : a_p 6053 = (78 : ℤ) := by
  have h := BSD_E143_card_p6053; unfold a_p; omega

theorem BSD_ap_p6067 : a_p 6067 = (34 : ℤ) := by
  have h := BSD_E143_card_p6067; unfold a_p; omega

theorem BSD_ap_p6073 : a_p 6073 = (6 : ℤ) := by
  have h := BSD_E143_card_p6073; unfold a_p; omega

theorem BSD_ap_p6079 : a_p 6079 = (50 : ℤ) := by
  have h := BSD_E143_card_p6079; unfold a_p; omega

theorem BSD_ap_p6089 : a_p 6089 = (90 : ℤ) := by
  have h := BSD_E143_card_p6089; unfold a_p; omega

theorem BSD_ap_p6091 : a_p 6091 = (-98 : ℤ) := by
  have h := BSD_E143_card_p6091; unfold a_p; omega

theorem BSD_ap_p6101 : a_p 6101 = (112 : ℤ) := by
  have h := BSD_E143_card_p6101; unfold a_p; omega

theorem BSD_ap_p6113 : a_p 6113 = (-58 : ℤ) := by
  have h := BSD_E143_card_p6113; unfold a_p; omega

theorem BSD_ap_p6121 : a_p 6121 = (-101 : ℤ) := by
  have h := BSD_E143_card_p6121; unfold a_p; omega

theorem BSD_ap_p6131 : a_p 6131 = (-5 : ℤ) := by
  have h := BSD_E143_card_p6131; unfold a_p; omega

theorem BSD_ap_p6133 : a_p 6133 = (-16 : ℤ) := by
  have h := BSD_E143_card_p6133; unfold a_p; omega

theorem BSD_ap_p6143 : a_p 6143 = (92 : ℤ) := by
  have h := BSD_E143_card_p6143; unfold a_p; omega

theorem BSD_ap_p6151 : a_p 6151 = (38 : ℤ) := by
  have h := BSD_E143_card_p6151; unfold a_p; omega

theorem BSD_ap_p6163 : a_p 6163 = (79 : ℤ) := by
  have h := BSD_E143_card_p6163; unfold a_p; omega

theorem BSD_ap_p6173 : a_p 6173 = (14 : ℤ) := by
  have h := BSD_E143_card_p6173; unfold a_p; omega

theorem BSD_ap_p6197 : a_p 6197 = (-99 : ℤ) := by
  have h := BSD_E143_card_p6197; unfold a_p; omega

theorem BSD_ap_p6199 : a_p 6199 = (52 : ℤ) := by
  have h := BSD_E143_card_p6199; unfold a_p; omega

theorem BSD_ap_p6203 : a_p 6203 = (16 : ℤ) := by
  have h := BSD_E143_card_p6203; unfold a_p; omega

theorem BSD_ap_p6211 : a_p 6211 = (-20 : ℤ) := by
  have h := BSD_E143_card_p6211; unfold a_p; omega

theorem BSD_ap_p6217 : a_p 6217 = (-58 : ℤ) := by
  have h := BSD_E143_card_p6217; unfold a_p; omega

theorem BSD_ap_p6221 : a_p 6221 = (-30 : ℤ) := by
  have h := BSD_E143_card_p6221; unfold a_p; omega

theorem BSD_ap_p6229 : a_p 6229 = (-49 : ℤ) := by
  have h := BSD_E143_card_p6229; unfold a_p; omega

theorem BSD_ap_p6247 : a_p 6247 = (-38 : ℤ) := by
  have h := BSD_E143_card_p6247; unfold a_p; omega

theorem BSD_ap_p6257 : a_p 6257 = (-19 : ℤ) := by
  have h := BSD_E143_card_p6257; unfold a_p; omega

theorem BSD_ap_p6263 : a_p 6263 = (7 : ℤ) := by
  have h := BSD_E143_card_p6263; unfold a_p; omega

theorem BSD_ap_p6269 : a_p 6269 = (90 : ℤ) := by
  have h := BSD_E143_card_p6269; unfold a_p; omega

theorem BSD_ap_p6271 : a_p 6271 = (-15 : ℤ) := by
  have h := BSD_E143_card_p6271; unfold a_p; omega

theorem BSD_ap_p6277 : a_p 6277 = (-22 : ℤ) := by
  have h := BSD_E143_card_p6277; unfold a_p; omega

theorem BSD_ap_p6287 : a_p 6287 = (126 : ℤ) := by
  have h := BSD_E143_card_p6287; unfold a_p; omega

theorem BSD_ap_p6299 : a_p 6299 = (30 : ℤ) := by
  have h := BSD_E143_card_p6299; unfold a_p; omega

theorem BSD_ap_p6301 : a_p 6301 = (9 : ℤ) := by
  have h := BSD_E143_card_p6301; unfold a_p; omega

theorem BSD_ap_p6311 : a_p 6311 = (-72 : ℤ) := by
  have h := BSD_E143_card_p6311; unfold a_p; omega

theorem BSD_ap_p6317 : a_p 6317 = (-63 : ℤ) := by
  have h := BSD_E143_card_p6317; unfold a_p; omega

theorem BSD_ap_p6323 : a_p 6323 = (39 : ℤ) := by
  have h := BSD_E143_card_p6323; unfold a_p; omega

theorem BSD_ap_p6329 : a_p 6329 = (22 : ℤ) := by
  have h := BSD_E143_card_p6329; unfold a_p; omega

theorem BSD_ap_p6337 : a_p 6337 = (-66 : ℤ) := by
  have h := BSD_E143_card_p6337; unfold a_p; omega

theorem BSD_ap_p6343 : a_p 6343 = (-96 : ℤ) := by
  have h := BSD_E143_card_p6343; unfold a_p; omega

theorem BSD_ap_p6353 : a_p 6353 = (-30 : ℤ) := by
  have h := BSD_E143_card_p6353; unfold a_p; omega

theorem BSD_ap_p6359 : a_p 6359 = (-120 : ℤ) := by
  have h := BSD_E143_card_p6359; unfold a_p; omega

theorem BSD_ap_p6361 : a_p 6361 = (-106 : ℤ) := by
  have h := BSD_E143_card_p6361; unfold a_p; omega

theorem BSD_ap_p6367 : a_p 6367 = (-32 : ℤ) := by
  have h := BSD_E143_card_p6367; unfold a_p; omega

theorem BSD_ap_p6373 : a_p 6373 = (-82 : ℤ) := by
  have h := BSD_E143_card_p6373; unfold a_p; omega

theorem BSD_ap_p6379 : a_p 6379 = (-54 : ℤ) := by
  have h := BSD_E143_card_p6379; unfold a_p; omega

theorem BSD_ap_p6389 : a_p 6389 = (99 : ℤ) := by
  have h := BSD_E143_card_p6389; unfold a_p; omega

theorem BSD_ap_p6397 : a_p 6397 = (-92 : ℤ) := by
  have h := BSD_E143_card_p6397; unfold a_p; omega

theorem BSD_ap_p6421 : a_p 6421 = (32 : ℤ) := by
  have h := BSD_E143_card_p6421; unfold a_p; omega

theorem BSD_ap_p6427 : a_p 6427 = (29 : ℤ) := by
  have h := BSD_E143_card_p6427; unfold a_p; omega

theorem BSD_ap_p6449 : a_p 6449 = (25 : ℤ) := by
  have h := BSD_E143_card_p6449; unfold a_p; omega

theorem BSD_ap_p6451 : a_p 6451 = (-12 : ℤ) := by
  have h := BSD_E143_card_p6451; unfold a_p; omega

theorem BSD_ap_p6469 : a_p 6469 = (31 : ℤ) := by
  have h := BSD_E143_card_p6469; unfold a_p; omega

theorem BSD_ap_p6473 : a_p 6473 = (33 : ℤ) := by
  have h := BSD_E143_card_p6473; unfold a_p; omega

theorem BSD_ap_p6481 : a_p 6481 = (146 : ℤ) := by
  have h := BSD_E143_card_p6481; unfold a_p; omega

theorem BSD_ap_p6491 : a_p 6491 = (-75 : ℤ) := by
  have h := BSD_E143_card_p6491; unfold a_p; omega

theorem BSD_ap_p6521 : a_p 6521 = (-9 : ℤ) := by
  have h := BSD_E143_card_p6521; unfold a_p; omega

theorem BSD_ap_p6529 : a_p 6529 = (-14 : ℤ) := by
  have h := BSD_E143_card_p6529; unfold a_p; omega

theorem BSD_ap_p6547 : a_p 6547 = (-58 : ℤ) := by
  have h := BSD_E143_card_p6547; unfold a_p; omega

theorem BSD_ap_p6551 : a_p 6551 = (-86 : ℤ) := by
  have h := BSD_E143_card_p6551; unfold a_p; omega

theorem BSD_ap_p6553 : a_p 6553 = (-20 : ℤ) := by
  have h := BSD_E143_card_p6553; unfold a_p; omega

theorem BSD_ap_p6563 : a_p 6563 = (100 : ℤ) := by
  have h := BSD_E143_card_p6563; unfold a_p; omega

theorem BSD_ap_p6569 : a_p 6569 = (18 : ℤ) := by
  have h := BSD_E143_card_p6569; unfold a_p; omega

theorem BSD_ap_p6571 : a_p 6571 = (20 : ℤ) := by
  have h := BSD_E143_card_p6571; unfold a_p; omega

theorem BSD_ap_p6577 : a_p 6577 = (-82 : ℤ) := by
  have h := BSD_E143_card_p6577; unfold a_p; omega

theorem BSD_ap_p6581 : a_p 6581 = (-129 : ℤ) := by
  have h := BSD_E143_card_p6581; unfold a_p; omega

theorem BSD_ap_p6599 : a_p 6599 = (-38 : ℤ) := by
  have h := BSD_E143_card_p6599; unfold a_p; omega

theorem BSD_ap_p6607 : a_p 6607 = (98 : ℤ) := by
  have h := BSD_E143_card_p6607; unfold a_p; omega

theorem BSD_ap_p6619 : a_p 6619 = (-110 : ℤ) := by
  have h := BSD_E143_card_p6619; unfold a_p; omega

theorem BSD_ap_p6637 : a_p 6637 = (-118 : ℤ) := by
  have h := BSD_E143_card_p6637; unfold a_p; omega

theorem BSD_ap_p6653 : a_p 6653 = (65 : ℤ) := by
  have h := BSD_E143_card_p6653; unfold a_p; omega

theorem BSD_ap_p6659 : a_p 6659 = (69 : ℤ) := by
  have h := BSD_E143_card_p6659; unfold a_p; omega

theorem BSD_ap_p6661 : a_p 6661 = (110 : ℤ) := by
  have h := BSD_E143_card_p6661; unfold a_p; omega

theorem BSD_ap_p6673 : a_p 6673 = (-156 : ℤ) := by
  have h := BSD_E143_card_p6673; unfold a_p; omega

theorem BSD_ap_p6679 : a_p 6679 = (-118 : ℤ) := by
  have h := BSD_E143_card_p6679; unfold a_p; omega

theorem BSD_ap_p6689 : a_p 6689 = (109 : ℤ) := by
  have h := BSD_E143_card_p6689; unfold a_p; omega

theorem BSD_ap_p6691 : a_p 6691 = (13 : ℤ) := by
  have h := BSD_E143_card_p6691; unfold a_p; omega

theorem BSD_ap_p6701 : a_p 6701 = (40 : ℤ) := by
  have h := BSD_E143_card_p6701; unfold a_p; omega

theorem BSD_ap_p6703 : a_p 6703 = (71 : ℤ) := by
  have h := BSD_E143_card_p6703; unfold a_p; omega

theorem BSD_ap_p6709 : a_p 6709 = (122 : ℤ) := by
  have h := BSD_E143_card_p6709; unfold a_p; omega

theorem BSD_ap_p6719 : a_p 6719 = (132 : ℤ) := by
  have h := BSD_E143_card_p6719; unfold a_p; omega

theorem BSD_ap_p6733 : a_p 6733 = (137 : ℤ) := by
  have h := BSD_E143_card_p6733; unfold a_p; omega

theorem BSD_ap_p6737 : a_p 6737 = (46 : ℤ) := by
  have h := BSD_E143_card_p6737; unfold a_p; omega

theorem BSD_ap_p6761 : a_p 6761 = (-76 : ℤ) := by
  have h := BSD_E143_card_p6761; unfold a_p; omega

theorem BSD_ap_p6763 : a_p 6763 = (-3 : ℤ) := by
  have h := BSD_E143_card_p6763; unfold a_p; omega

theorem BSD_ap_p6779 : a_p 6779 = (-20 : ℤ) := by
  have h := BSD_E143_card_p6779; unfold a_p; omega

theorem BSD_ap_p6781 : a_p 6781 = (-43 : ℤ) := by
  have h := BSD_E143_card_p6781; unfold a_p; omega

theorem BSD_ap_p6791 : a_p 6791 = (-5 : ℤ) := by
  have h := BSD_E143_card_p6791; unfold a_p; omega

theorem BSD_ap_p6793 : a_p 6793 = (62 : ℤ) := by
  have h := BSD_E143_card_p6793; unfold a_p; omega

theorem BSD_ap_p6803 : a_p 6803 = (57 : ℤ) := by
  have h := BSD_E143_card_p6803; unfold a_p; omega

theorem BSD_ap_p6823 : a_p 6823 = (88 : ℤ) := by
  have h := BSD_E143_card_p6823; unfold a_p; omega

theorem BSD_ap_p6827 : a_p 6827 = (-52 : ℤ) := by
  have h := BSD_E143_card_p6827; unfold a_p; omega

theorem BSD_ap_p6829 : a_p 6829 = (61 : ℤ) := by
  have h := BSD_E143_card_p6829; unfold a_p; omega

theorem BSD_ap_p6833 : a_p 6833 = (6 : ℤ) := by
  have h := BSD_E143_card_p6833; unfold a_p; omega

theorem BSD_ap_p6841 : a_p 6841 = (-84 : ℤ) := by
  have h := BSD_E143_card_p6841; unfold a_p; omega

theorem BSD_ap_p6857 : a_p 6857 = (27 : ℤ) := by
  have h := BSD_E143_card_p6857; unfold a_p; omega

theorem BSD_ap_p6863 : a_p 6863 = (-84 : ℤ) := by
  have h := BSD_E143_card_p6863; unfold a_p; omega

theorem BSD_ap_p6869 : a_p 6869 = (-25 : ℤ) := by
  have h := BSD_E143_card_p6869; unfold a_p; omega

theorem BSD_ap_p6871 : a_p 6871 = (-4 : ℤ) := by
  have h := BSD_E143_card_p6871; unfold a_p; omega

theorem BSD_ap_p6883 : a_p 6883 = (126 : ℤ) := by
  have h := BSD_E143_card_p6883; unfold a_p; omega

theorem BSD_ap_p6899 : a_p 6899 = (10 : ℤ) := by
  have h := BSD_E143_card_p6899; unfold a_p; omega

theorem BSD_ap_p6907 : a_p 6907 = (154 : ℤ) := by
  have h := BSD_E143_card_p6907; unfold a_p; omega

theorem BSD_ap_p6911 : a_p 6911 = (-8 : ℤ) := by
  have h := BSD_E143_card_p6911; unfold a_p; omega

theorem BSD_ap_p6917 : a_p 6917 = (38 : ℤ) := by
  have h := BSD_E143_card_p6917; unfold a_p; omega

theorem BSD_ap_p6947 : a_p 6947 = (66 : ℤ) := by
  have h := BSD_E143_card_p6947; unfold a_p; omega

theorem BSD_ap_p6949 : a_p 6949 = (-88 : ℤ) := by
  have h := BSD_E143_card_p6949; unfold a_p; omega

theorem BSD_ap_p6959 : a_p 6959 = (-72 : ℤ) := by
  have h := BSD_E143_card_p6959; unfold a_p; omega

theorem BSD_ap_p6961 : a_p 6961 = (-66 : ℤ) := by
  have h := BSD_E143_card_p6961; unfold a_p; omega

theorem BSD_ap_p6967 : a_p 6967 = (16 : ℤ) := by
  have h := BSD_E143_card_p6967; unfold a_p; omega

theorem BSD_ap_p6971 : a_p 6971 = (82 : ℤ) := by
  have h := BSD_E143_card_p6971; unfold a_p; omega

theorem BSD_ap_p6977 : a_p 6977 = (135 : ℤ) := by
  have h := BSD_E143_card_p6977; unfold a_p; omega

theorem BSD_ap_p6983 : a_p 6983 = (-111 : ℤ) := by
  have h := BSD_E143_card_p6983; unfold a_p; omega

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

theorem BSD_ap_p7079 : a_p 7079 = (18 : ℤ) := by
  have h := BSD_E143_card_p7079; unfold a_p; omega

theorem BSD_ap_p7103 : a_p 7103 = (-2 : ℤ) := by
  have h := BSD_E143_card_p7103; unfold a_p; omega

theorem BSD_ap_p7109 : a_p 7109 = (-31 : ℤ) := by
  have h := BSD_E143_card_p7109; unfold a_p; omega

theorem BSD_ap_p7121 : a_p 7121 = (-87 : ℤ) := by
  have h := BSD_E143_card_p7121; unfold a_p; omega

theorem BSD_ap_p7127 : a_p 7127 = (90 : ℤ) := by
  have h := BSD_E143_card_p7127; unfold a_p; omega

theorem BSD_ap_p7129 : a_p 7129 = (125 : ℤ) := by
  have h := BSD_E143_card_p7129; unfold a_p; omega

theorem BSD_ap_p7151 : a_p 7151 = (-45 : ℤ) := by
  have h := BSD_E143_card_p7151; unfold a_p; omega

theorem BSD_ap_p7159 : a_p 7159 = (7 : ℤ) := by
  have h := BSD_E143_card_p7159; unfold a_p; omega

theorem BSD_ap_p7177 : a_p 7177 = (-30 : ℤ) := by
  have h := BSD_E143_card_p7177; unfold a_p; omega

theorem BSD_ap_p7187 : a_p 7187 = (-93 : ℤ) := by
  have h := BSD_E143_card_p7187; unfold a_p; omega

theorem BSD_ap_p7193 : a_p 7193 = (-42 : ℤ) := by
  have h := BSD_E143_card_p7193; unfold a_p; omega

theorem BSD_ap_p7207 : a_p 7207 = (100 : ℤ) := by
  have h := BSD_E143_card_p7207; unfold a_p; omega

theorem BSD_ap_p7211 : a_p 7211 = (108 : ℤ) := by
  have h := BSD_E143_card_p7211; unfold a_p; omega

theorem BSD_ap_p7213 : a_p 7213 = (52 : ℤ) := by
  have h := BSD_E143_card_p7213; unfold a_p; omega

theorem BSD_ap_p7219 : a_p 7219 = (97 : ℤ) := by
  have h := BSD_E143_card_p7219; unfold a_p; omega

theorem BSD_ap_p7229 : a_p 7229 = (-102 : ℤ) := by
  have h := BSD_E143_card_p7229; unfold a_p; omega

theorem BSD_ap_p7237 : a_p 7237 = (40 : ℤ) := by
  have h := BSD_E143_card_p7237; unfold a_p; omega

theorem BSD_ap_p7243 : a_p 7243 = (-43 : ℤ) := by
  have h := BSD_E143_card_p7243; unfold a_p; omega

theorem BSD_ap_p7247 : a_p 7247 = (37 : ℤ) := by
  have h := BSD_E143_card_p7247; unfold a_p; omega

theorem BSD_ap_p7253 : a_p 7253 = (-97 : ℤ) := by
  have h := BSD_E143_card_p7253; unfold a_p; omega

theorem BSD_ap_p7283 : a_p 7283 = (-29 : ℤ) := by
  have h := BSD_E143_card_p7283; unfold a_p; omega

theorem BSD_ap_p7297 : a_p 7297 = (-130 : ℤ) := by
  have h := BSD_E143_card_p7297; unfold a_p; omega

theorem BSD_ap_p7307 : a_p 7307 = (-155 : ℤ) := by
  have h := BSD_E143_card_p7307; unfold a_p; omega

theorem BSD_ap_p7309 : a_p 7309 = (95 : ℤ) := by
  have h := BSD_E143_card_p7309; unfold a_p; omega

theorem BSD_ap_p7321 : a_p 7321 = (-62 : ℤ) := by
  have h := BSD_E143_card_p7321; unfold a_p; omega

theorem BSD_ap_p7331 : a_p 7331 = (-20 : ℤ) := by
  have h := BSD_E143_card_p7331; unfold a_p; omega

theorem BSD_ap_p7333 : a_p 7333 = (-16 : ℤ) := by
  have h := BSD_E143_card_p7333; unfold a_p; omega

theorem BSD_ap_p7349 : a_p 7349 = (-102 : ℤ) := by
  have h := BSD_E143_card_p7349; unfold a_p; omega

theorem BSD_ap_p7351 : a_p 7351 = (112 : ℤ) := by
  have h := BSD_E143_card_p7351; unfold a_p; omega

theorem BSD_ap_p7369 : a_p 7369 = (112 : ℤ) := by
  have h := BSD_E143_card_p7369; unfold a_p; omega

theorem BSD_ap_p7393 : a_p 7393 = (-147 : ℤ) := by
  have h := BSD_E143_card_p7393; unfold a_p; omega

theorem BSD_ap_p7411 : a_p 7411 = (116 : ℤ) := by
  have h := BSD_E143_card_p7411; unfold a_p; omega

theorem BSD_ap_p7417 : a_p 7417 = (-3 : ℤ) := by
  have h := BSD_E143_card_p7417; unfold a_p; omega

theorem BSD_ap_p7433 : a_p 7433 = (-132 : ℤ) := by
  have h := BSD_E143_card_p7433; unfold a_p; omega

theorem BSD_ap_p7451 : a_p 7451 = (-156 : ℤ) := by
  have h := BSD_E143_card_p7451; unfold a_p; omega

theorem BSD_ap_p7457 : a_p 7457 = (50 : ℤ) := by
  have h := BSD_E143_card_p7457; unfold a_p; omega

theorem BSD_ap_p7459 : a_p 7459 = (-121 : ℤ) := by
  have h := BSD_E143_card_p7459; unfold a_p; omega

theorem BSD_ap_p7477 : a_p 7477 = (-50 : ℤ) := by
  have h := BSD_E143_card_p7477; unfold a_p; omega

theorem BSD_ap_p7481 : a_p 7481 = (-129 : ℤ) := by
  have h := BSD_E143_card_p7481; unfold a_p; omega

theorem BSD_ap_p7487 : a_p 7487 = (-102 : ℤ) := by
  have h := BSD_E143_card_p7487; unfold a_p; omega

theorem BSD_ap_p7489 : a_p 7489 = (9 : ℤ) := by
  have h := BSD_E143_card_p7489; unfold a_p; omega

theorem BSD_ap_p7499 : a_p 7499 = (16 : ℤ) := by
  have h := BSD_E143_card_p7499; unfold a_p; omega

theorem BSD_ap_p7507 : a_p 7507 = (71 : ℤ) := by
  have h := BSD_E143_card_p7507; unfold a_p; omega

theorem BSD_ap_p7517 : a_p 7517 = (-90 : ℤ) := by
  have h := BSD_E143_card_p7517; unfold a_p; omega

theorem BSD_ap_p7523 : a_p 7523 = (154 : ℤ) := by
  have h := BSD_E143_card_p7523; unfold a_p; omega

theorem BSD_ap_p7529 : a_p 7529 = (27 : ℤ) := by
  have h := BSD_E143_card_p7529; unfold a_p; omega

theorem BSD_ap_p7537 : a_p 7537 = (54 : ℤ) := by
  have h := BSD_E143_card_p7537; unfold a_p; omega

theorem BSD_ap_p7541 : a_p 7541 = (-32 : ℤ) := by
  have h := BSD_E143_card_p7541; unfold a_p; omega

theorem BSD_ap_p7547 : a_p 7547 = (1 : ℤ) := by
  have h := BSD_E143_card_p7547; unfold a_p; omega

theorem BSD_ap_p7549 : a_p 7549 = (-1 : ℤ) := by
  have h := BSD_E143_card_p7549; unfold a_p; omega

theorem BSD_ap_p7559 : a_p 7559 = (42 : ℤ) := by
  have h := BSD_E143_card_p7559; unfold a_p; omega

theorem BSD_ap_p7561 : a_p 7561 = (70 : ℤ) := by
  have h := BSD_E143_card_p7561; unfold a_p; omega

theorem BSD_ap_p7573 : a_p 7573 = (-149 : ℤ) := by
  have h := BSD_E143_card_p7573; unfold a_p; omega

theorem BSD_ap_p7577 : a_p 7577 = (18 : ℤ) := by
  have h := BSD_E143_card_p7577; unfold a_p; omega

theorem BSD_ap_p7583 : a_p 7583 = (0 : ℤ) := by
  have h := BSD_E143_card_p7583; unfold a_p; omega

theorem BSD_ap_p7589 : a_p 7589 = (-150 : ℤ) := by
  have h := BSD_E143_card_p7589; unfold a_p; omega

theorem BSD_ap_p7591 : a_p 7591 = (31 : ℤ) := by
  have h := BSD_E143_card_p7591; unfold a_p; omega

theorem BSD_ap_p7603 : a_p 7603 = (146 : ℤ) := by
  have h := BSD_E143_card_p7603; unfold a_p; omega

theorem BSD_ap_p7607 : a_p 7607 = (22 : ℤ) := by
  have h := BSD_E143_card_p7607; unfold a_p; omega

theorem BSD_ap_p7621 : a_p 7621 = (-142 : ℤ) := by
  have h := BSD_E143_card_p7621; unfold a_p; omega

theorem BSD_ap_p7639 : a_p 7639 = (-97 : ℤ) := by
  have h := BSD_E143_card_p7639; unfold a_p; omega

theorem BSD_ap_p7643 : a_p 7643 = (-33 : ℤ) := by
  have h := BSD_E143_card_p7643; unfold a_p; omega

theorem BSD_ap_p7649 : a_p 7649 = (98 : ℤ) := by
  have h := BSD_E143_card_p7649; unfold a_p; omega

theorem BSD_ap_p7669 : a_p 7669 = (84 : ℤ) := by
  have h := BSD_E143_card_p7669; unfold a_p; omega

theorem BSD_ap_p7673 : a_p 7673 = (96 : ℤ) := by
  have h := BSD_E143_card_p7673; unfold a_p; omega

theorem BSD_ap_p7681 : a_p 7681 = (105 : ℤ) := by
  have h := BSD_E143_card_p7681; unfold a_p; omega

theorem BSD_ap_p7687 : a_p 7687 = (-5 : ℤ) := by
  have h := BSD_E143_card_p7687; unfold a_p; omega

theorem BSD_ap_p7691 : a_p 7691 = (-42 : ℤ) := by
  have h := BSD_E143_card_p7691; unfold a_p; omega

theorem BSD_ap_p7699 : a_p 7699 = (-70 : ℤ) := by
  have h := BSD_E143_card_p7699; unfold a_p; omega

theorem BSD_ap_p7703 : a_p 7703 = (-69 : ℤ) := by
  have h := BSD_E143_card_p7703; unfold a_p; omega

theorem BSD_ap_p7717 : a_p 7717 = (-32 : ℤ) := by
  have h := BSD_E143_card_p7717; unfold a_p; omega

theorem BSD_ap_p7723 : a_p 7723 = (29 : ℤ) := by
  have h := BSD_E143_card_p7723; unfold a_p; omega

theorem BSD_ap_p7727 : a_p 7727 = (147 : ℤ) := by
  have h := BSD_E143_card_p7727; unfold a_p; omega

theorem BSD_ap_p7741 : a_p 7741 = (76 : ℤ) := by
  have h := BSD_E143_card_p7741; unfold a_p; omega

theorem BSD_ap_p7753 : a_p 7753 = (77 : ℤ) := by
  have h := BSD_E143_card_p7753; unfold a_p; omega

theorem BSD_ap_p7757 : a_p 7757 = (-126 : ℤ) := by
  have h := BSD_E143_card_p7757; unfold a_p; omega

theorem BSD_ap_p7759 : a_p 7759 = (-167 : ℤ) := by
  have h := BSD_E143_card_p7759; unfold a_p; omega

theorem BSD_ap_p7789 : a_p 7789 = (-18 : ℤ) := by
  have h := BSD_E143_card_p7789; unfold a_p; omega

theorem BSD_ap_p7793 : a_p 7793 = (-39 : ℤ) := by
  have h := BSD_E143_card_p7793; unfold a_p; omega

theorem BSD_ap_p7817 : a_p 7817 = (140 : ℤ) := by
  have h := BSD_E143_card_p7817; unfold a_p; omega

theorem BSD_ap_p7823 : a_p 7823 = (108 : ℤ) := by
  have h := BSD_E143_card_p7823; unfold a_p; omega

theorem BSD_ap_p7829 : a_p 7829 = (72 : ℤ) := by
  have h := BSD_E143_card_p7829; unfold a_p; omega

theorem BSD_ap_p7841 : a_p 7841 = (-69 : ℤ) := by
  have h := BSD_E143_card_p7841; unfold a_p; omega

theorem BSD_ap_p7853 : a_p 7853 = (-6 : ℤ) := by
  have h := BSD_E143_card_p7853; unfold a_p; omega

theorem BSD_ap_p7867 : a_p 7867 = (-68 : ℤ) := by
  have h := BSD_E143_card_p7867; unfold a_p; omega

theorem BSD_ap_p7873 : a_p 7873 = (-112 : ℤ) := by
  have h := BSD_E143_card_p7873; unfold a_p; omega

theorem BSD_ap_p7877 : a_p 7877 = (114 : ℤ) := by
  have h := BSD_E143_card_p7877; unfold a_p; omega

theorem BSD_ap_p7879 : a_p 7879 = (79 : ℤ) := by
  have h := BSD_E143_card_p7879; unfold a_p; omega

theorem BSD_ap_p7883 : a_p 7883 = (22 : ℤ) := by
  have h := BSD_E143_card_p7883; unfold a_p; omega

theorem BSD_ap_p7901 : a_p 7901 = (-1 : ℤ) := by
  have h := BSD_E143_card_p7901; unfold a_p; omega

theorem BSD_ap_p7907 : a_p 7907 = (17 : ℤ) := by
  have h := BSD_E143_card_p7907; unfold a_p; omega

theorem BSD_ap_p7919 : a_p 7919 = (130 : ℤ) := by
  have h := BSD_E143_card_p7919; unfold a_p; omega

theorem BSD_ap_p7927 : a_p 7927 = (-174 : ℤ) := by
  have h := BSD_E143_card_p7927; unfold a_p; omega

theorem BSD_ap_p7933 : a_p 7933 = (132 : ℤ) := by
  have h := BSD_E143_card_p7933; unfold a_p; omega

theorem BSD_ap_p7937 : a_p 7937 = (162 : ℤ) := by
  have h := BSD_E143_card_p7937; unfold a_p; omega

theorem BSD_ap_p7949 : a_p 7949 = (90 : ℤ) := by
  have h := BSD_E143_card_p7949; unfold a_p; omega

theorem BSD_ap_p7951 : a_p 7951 = (-16 : ℤ) := by
  have h := BSD_E143_card_p7951; unfold a_p; omega

theorem BSD_ap_p7963 : a_p 7963 = (-92 : ℤ) := by
  have h := BSD_E143_card_p7963; unfold a_p; omega

theorem BSD_ap_p7993 : a_p 7993 = (74 : ℤ) := by
  have h := BSD_E143_card_p7993; unfold a_p; omega

theorem BSD_ap_p8009 : a_p 8009 = (109 : ℤ) := by
  have h := BSD_E143_card_p8009; unfold a_p; omega

theorem BSD_ap_p8011 : a_p 8011 = (-23 : ℤ) := by
  have h := BSD_E143_card_p8011; unfold a_p; omega

theorem BSD_ap_p8017 : a_p 8017 = (-6 : ℤ) := by
  have h := BSD_E143_card_p8017; unfold a_p; omega

theorem BSD_ap_p8039 : a_p 8039 = (-53 : ℤ) := by
  have h := BSD_E143_card_p8039; unfold a_p; omega

theorem BSD_ap_p8053 : a_p 8053 = (94 : ℤ) := by
  have h := BSD_E143_card_p8053; unfold a_p; omega

theorem BSD_ap_p8059 : a_p 8059 = (0 : ℤ) := by
  have h := BSD_E143_card_p8059; unfold a_p; omega

theorem BSD_ap_p8069 : a_p 8069 = (-92 : ℤ) := by
  have h := BSD_E143_card_p8069; unfold a_p; omega

theorem BSD_ap_p8081 : a_p 8081 = (-110 : ℤ) := by
  have h := BSD_E143_card_p8081; unfold a_p; omega

theorem BSD_ap_p8087 : a_p 8087 = (-110 : ℤ) := by
  have h := BSD_E143_card_p8087; unfold a_p; omega

theorem BSD_ap_p8089 : a_p 8089 = (99 : ℤ) := by
  have h := BSD_E143_card_p8089; unfold a_p; omega

theorem BSD_ap_p8093 : a_p 8093 = (88 : ℤ) := by
  have h := BSD_E143_card_p8093; unfold a_p; omega

theorem BSD_ap_p8101 : a_p 8101 = (-113 : ℤ) := by
  have h := BSD_E143_card_p8101; unfold a_p; omega

theorem BSD_ap_p8111 : a_p 8111 = (-44 : ℤ) := by
  have h := BSD_E143_card_p8111; unfold a_p; omega

theorem BSD_ap_p8117 : a_p 8117 = (72 : ℤ) := by
  have h := BSD_E143_card_p8117; unfold a_p; omega

theorem BSD_ap_p8123 : a_p 8123 = (60 : ℤ) := by
  have h := BSD_E143_card_p8123; unfold a_p; omega

theorem BSD_ap_p8147 : a_p 8147 = (-24 : ℤ) := by
  have h := BSD_E143_card_p8147; unfold a_p; omega

theorem BSD_ap_p8161 : a_p 8161 = (88 : ℤ) := by
  have h := BSD_E143_card_p8161; unfold a_p; omega

theorem BSD_ap_p8167 : a_p 8167 = (-101 : ℤ) := by
  have h := BSD_E143_card_p8167; unfold a_p; omega

theorem BSD_ap_p8171 : a_p 8171 = (-52 : ℤ) := by
  have h := BSD_E143_card_p8171; unfold a_p; omega

theorem BSD_ap_p8179 : a_p 8179 = (-140 : ℤ) := by
  have h := BSD_E143_card_p8179; unfold a_p; omega

theorem BSD_ap_p8191 : a_p 8191 = (126 : ℤ) := by
  have h := BSD_E143_card_p8191; unfold a_p; omega

theorem BSD_ap_p8209 : a_p 8209 = (59 : ℤ) := by
  have h := BSD_E143_card_p8209; unfold a_p; omega

theorem BSD_ap_p8219 : a_p 8219 = (22 : ℤ) := by
  have h := BSD_E143_card_p8219; unfold a_p; omega

theorem BSD_ap_p8221 : a_p 8221 = (15 : ℤ) := by
  have h := BSD_E143_card_p8221; unfold a_p; omega

theorem BSD_ap_p8231 : a_p 8231 = (93 : ℤ) := by
  have h := BSD_E143_card_p8231; unfold a_p; omega

theorem BSD_ap_p8233 : a_p 8233 = (-11 : ℤ) := by
  have h := BSD_E143_card_p8233; unfold a_p; omega

theorem BSD_ap_p8237 : a_p 8237 = (129 : ℤ) := by
  have h := BSD_E143_card_p8237; unfold a_p; omega

theorem BSD_ap_p8243 : a_p 8243 = (-21 : ℤ) := by
  have h := BSD_E143_card_p8243; unfold a_p; omega

theorem BSD_ap_p8263 : a_p 8263 = (116 : ℤ) := by
  have h := BSD_E143_card_p8263; unfold a_p; omega

theorem BSD_ap_p8269 : a_p 8269 = (-2 : ℤ) := by
  have h := BSD_E143_card_p8269; unfold a_p; omega

theorem BSD_ap_p8273 : a_p 8273 = (-142 : ℤ) := by
  have h := BSD_E143_card_p8273; unfold a_p; omega

theorem BSD_ap_p8287 : a_p 8287 = (48 : ℤ) := by
  have h := BSD_E143_card_p8287; unfold a_p; omega

theorem BSD_ap_p8291 : a_p 8291 = (-58 : ℤ) := by
  have h := BSD_E143_card_p8291; unfold a_p; omega

theorem BSD_ap_p8293 : a_p 8293 = (134 : ℤ) := by
  have h := BSD_E143_card_p8293; unfold a_p; omega

theorem BSD_ap_p8297 : a_p 8297 = (-69 : ℤ) := by
  have h := BSD_E143_card_p8297; unfold a_p; omega

theorem BSD_ap_p8311 : a_p 8311 = (-20 : ℤ) := by
  have h := BSD_E143_card_p8311; unfold a_p; omega

theorem BSD_ap_p8317 : a_p 8317 = (34 : ℤ) := by
  have h := BSD_E143_card_p8317; unfold a_p; omega

theorem BSD_ap_p8329 : a_p 8329 = (86 : ℤ) := by
  have h := BSD_E143_card_p8329; unfold a_p; omega

theorem BSD_ap_p8353 : a_p 8353 = (57 : ℤ) := by
  have h := BSD_E143_card_p8353; unfold a_p; omega

theorem BSD_ap_p8363 : a_p 8363 = (-136 : ℤ) := by
  have h := BSD_E143_card_p8363; unfold a_p; omega

theorem BSD_ap_p8369 : a_p 8369 = (66 : ℤ) := by
  have h := BSD_E143_card_p8369; unfold a_p; omega

theorem BSD_ap_p8377 : a_p 8377 = (-62 : ℤ) := by
  have h := BSD_E143_card_p8377; unfold a_p; omega

theorem BSD_ap_p8387 : a_p 8387 = (-12 : ℤ) := by
  have h := BSD_E143_card_p8387; unfold a_p; omega

theorem BSD_ap_p8389 : a_p 8389 = (-108 : ℤ) := by
  have h := BSD_E143_card_p8389; unfold a_p; omega

theorem BSD_ap_p8419 : a_p 8419 = (136 : ℤ) := by
  have h := BSD_E143_card_p8419; unfold a_p; omega

theorem BSD_ap_p8423 : a_p 8423 = (-52 : ℤ) := by
  have h := BSD_E143_card_p8423; unfold a_p; omega

theorem BSD_ap_p8429 : a_p 8429 = (-61 : ℤ) := by
  have h := BSD_E143_card_p8429; unfold a_p; omega

theorem BSD_ap_p8431 : a_p 8431 = (17 : ℤ) := by
  have h := BSD_E143_card_p8431; unfold a_p; omega

theorem BSD_ap_p8443 : a_p 8443 = (116 : ℤ) := by
  have h := BSD_E143_card_p8443; unfold a_p; omega

theorem BSD_ap_p8447 : a_p 8447 = (10 : ℤ) := by
  have h := BSD_E143_card_p8447; unfold a_p; omega

theorem BSD_ap_p8461 : a_p 8461 = (-176 : ℤ) := by
  have h := BSD_E143_card_p8461; unfold a_p; omega

theorem BSD_ap_p8467 : a_p 8467 = (-70 : ℤ) := by
  have h := BSD_E143_card_p8467; unfold a_p; omega

theorem BSD_ap_p8501 : a_p 8501 = (-107 : ℤ) := by
  have h := BSD_E143_card_p8501; unfold a_p; omega

theorem BSD_ap_p8513 : a_p 8513 = (-84 : ℤ) := by
  have h := BSD_E143_card_p8513; unfold a_p; omega

theorem BSD_ap_p8521 : a_p 8521 = (14 : ℤ) := by
  have h := BSD_E143_card_p8521; unfold a_p; omega

theorem BSD_ap_p8527 : a_p 8527 = (-174 : ℤ) := by
  have h := BSD_E143_card_p8527; unfold a_p; omega

theorem BSD_ap_p8537 : a_p 8537 = (129 : ℤ) := by
  have h := BSD_E143_card_p8537; unfold a_p; omega

theorem BSD_ap_p8539 : a_p 8539 = (-85 : ℤ) := by
  have h := BSD_E143_card_p8539; unfold a_p; omega

theorem BSD_ap_p8543 : a_p 8543 = (-66 : ℤ) := by
  have h := BSD_E143_card_p8543; unfold a_p; omega

theorem BSD_ap_p8563 : a_p 8563 = (36 : ℤ) := by
  have h := BSD_E143_card_p8563; unfold a_p; omega

theorem BSD_ap_p8573 : a_p 8573 = (78 : ℤ) := by
  have h := BSD_E143_card_p8573; unfold a_p; omega

theorem BSD_ap_p8581 : a_p 8581 = (-61 : ℤ) := by
  have h := BSD_E143_card_p8581; unfold a_p; omega

theorem BSD_ap_p8597 : a_p 8597 = (-76 : ℤ) := by
  have h := BSD_E143_card_p8597; unfold a_p; omega

theorem BSD_ap_p8599 : a_p 8599 = (-42 : ℤ) := by
  have h := BSD_E143_card_p8599; unfold a_p; omega

theorem BSD_ap_p8609 : a_p 8609 = (4 : ℤ) := by
  have h := BSD_E143_card_p8609; unfold a_p; omega

theorem BSD_ap_p8623 : a_p 8623 = (102 : ℤ) := by
  have h := BSD_E143_card_p8623; unfold a_p; omega

theorem BSD_ap_p8627 : a_p 8627 = (-175 : ℤ) := by
  have h := BSD_E143_card_p8627; unfold a_p; omega

theorem BSD_ap_p8629 : a_p 8629 = (133 : ℤ) := by
  have h := BSD_E143_card_p8629; unfold a_p; omega

theorem BSD_ap_p8641 : a_p 8641 = (136 : ℤ) := by
  have h := BSD_E143_card_p8641; unfold a_p; omega

theorem BSD_ap_p8647 : a_p 8647 = (-21 : ℤ) := by
  have h := BSD_E143_card_p8647; unfold a_p; omega

theorem BSD_ap_p8663 : a_p 8663 = (-142 : ℤ) := by
  have h := BSD_E143_card_p8663; unfold a_p; omega

theorem BSD_ap_p8669 : a_p 8669 = (-38 : ℤ) := by
  have h := BSD_E143_card_p8669; unfold a_p; omega

theorem BSD_ap_p8677 : a_p 8677 = (-58 : ℤ) := by
  have h := BSD_E143_card_p8677; unfold a_p; omega

theorem BSD_ap_p8681 : a_p 8681 = (42 : ℤ) := by
  have h := BSD_E143_card_p8681; unfold a_p; omega

theorem BSD_ap_p8689 : a_p 8689 = (46 : ℤ) := by
  have h := BSD_E143_card_p8689; unfold a_p; omega

theorem BSD_ap_p8693 : a_p 8693 = (106 : ℤ) := by
  have h := BSD_E143_card_p8693; unfold a_p; omega

theorem BSD_ap_p8699 : a_p 8699 = (153 : ℤ) := by
  have h := BSD_E143_card_p8699; unfold a_p; omega

theorem BSD_ap_p8707 : a_p 8707 = (22 : ℤ) := by
  have h := BSD_E143_card_p8707; unfold a_p; omega

theorem BSD_ap_p8713 : a_p 8713 = (91 : ℤ) := by
  have h := BSD_E143_card_p8713; unfold a_p; omega

theorem BSD_ap_p8719 : a_p 8719 = (170 : ℤ) := by
  have h := BSD_E143_card_p8719; unfold a_p; omega

theorem BSD_ap_p8731 : a_p 8731 = (52 : ℤ) := by
  have h := BSD_E143_card_p8731; unfold a_p; omega

theorem BSD_ap_p8737 : a_p 8737 = (-90 : ℤ) := by
  have h := BSD_E143_card_p8737; unfold a_p; omega

theorem BSD_ap_p8741 : a_p 8741 = (24 : ℤ) := by
  have h := BSD_E143_card_p8741; unfold a_p; omega

theorem BSD_ap_p8747 : a_p 8747 = (-170 : ℤ) := by
  have h := BSD_E143_card_p8747; unfold a_p; omega

theorem BSD_ap_p8753 : a_p 8753 = (38 : ℤ) := by
  have h := BSD_E143_card_p8753; unfold a_p; omega

theorem BSD_ap_p8761 : a_p 8761 = (-69 : ℤ) := by
  have h := BSD_E143_card_p8761; unfold a_p; omega

theorem BSD_ap_p8779 : a_p 8779 = (-65 : ℤ) := by
  have h := BSD_E143_card_p8779; unfold a_p; omega

theorem BSD_ap_p8783 : a_p 8783 = (-57 : ℤ) := by
  have h := BSD_E143_card_p8783; unfold a_p; omega

theorem BSD_ap_p8803 : a_p 8803 = (92 : ℤ) := by
  have h := BSD_E143_card_p8803; unfold a_p; omega

theorem BSD_ap_p8807 : a_p 8807 = (124 : ℤ) := by
  have h := BSD_E143_card_p8807; unfold a_p; omega

theorem BSD_ap_p8819 : a_p 8819 = (-54 : ℤ) := by
  have h := BSD_E143_card_p8819; unfold a_p; omega

theorem BSD_ap_p8821 : a_p 8821 = (10 : ℤ) := by
  have h := BSD_E143_card_p8821; unfold a_p; omega

theorem BSD_ap_p8831 : a_p 8831 = (-43 : ℤ) := by
  have h := BSD_E143_card_p8831; unfold a_p; omega

theorem BSD_ap_p8837 : a_p 8837 = (159 : ℤ) := by
  have h := BSD_E143_card_p8837; unfold a_p; omega

theorem BSD_ap_p8839 : a_p 8839 = (18 : ℤ) := by
  have h := BSD_E143_card_p8839; unfold a_p; omega

theorem BSD_ap_p8849 : a_p 8849 = (-6 : ℤ) := by
  have h := BSD_E143_card_p8849; unfold a_p; omega

theorem BSD_ap_p8861 : a_p 8861 = (72 : ℤ) := by
  have h := BSD_E143_card_p8861; unfold a_p; omega

theorem BSD_ap_p8863 : a_p 8863 = (52 : ℤ) := by
  have h := BSD_E143_card_p8863; unfold a_p; omega

theorem BSD_ap_p8867 : a_p 8867 = (47 : ℤ) := by
  have h := BSD_E143_card_p8867; unfold a_p; omega

theorem BSD_ap_p8887 : a_p 8887 = (-132 : ℤ) := by
  have h := BSD_E143_card_p8887; unfold a_p; omega

theorem BSD_ap_p8893 : a_p 8893 = (146 : ℤ) := by
  have h := BSD_E143_card_p8893; unfold a_p; omega

theorem BSD_ap_p8923 : a_p 8923 = (50 : ℤ) := by
  have h := BSD_E143_card_p8923; unfold a_p; omega

theorem BSD_ap_p8929 : a_p 8929 = (106 : ℤ) := by
  have h := BSD_E143_card_p8929; unfold a_p; omega

theorem BSD_ap_p8933 : a_p 8933 = (-69 : ℤ) := by
  have h := BSD_E143_card_p8933; unfold a_p; omega

theorem BSD_ap_p8941 : a_p 8941 = (87 : ℤ) := by
  have h := BSD_E143_card_p8941; unfold a_p; omega

theorem BSD_ap_p8951 : a_p 8951 = (98 : ℤ) := by
  have h := BSD_E143_card_p8951; unfold a_p; omega

theorem BSD_ap_p8963 : a_p 8963 = (-177 : ℤ) := by
  have h := BSD_E143_card_p8963; unfold a_p; omega

theorem BSD_ap_p8969 : a_p 8969 = (79 : ℤ) := by
  have h := BSD_E143_card_p8969; unfold a_p; omega

theorem BSD_ap_p8971 : a_p 8971 = (42 : ℤ) := by
  have h := BSD_E143_card_p8971; unfold a_p; omega

theorem BSD_ap_p8999 : a_p 8999 = (-23 : ℤ) := by
  have h := BSD_E143_card_p8999; unfold a_p; omega

theorem BSD_ap_p9001 : a_p 9001 = (51 : ℤ) := by
  have h := BSD_E143_card_p9001; unfold a_p; omega

theorem BSD_ap_p9007 : a_p 9007 = (143 : ℤ) := by
  have h := BSD_E143_card_p9007; unfold a_p; omega

theorem BSD_ap_p9011 : a_p 9011 = (96 : ℤ) := by
  have h := BSD_E143_card_p9011; unfold a_p; omega

theorem BSD_ap_p9013 : a_p 9013 = (67 : ℤ) := by
  have h := BSD_E143_card_p9013; unfold a_p; omega

theorem BSD_ap_p9029 : a_p 9029 = (105 : ℤ) := by
  have h := BSD_E143_card_p9029; unfold a_p; omega

theorem BSD_ap_p9041 : a_p 9041 = (-12 : ℤ) := by
  have h := BSD_E143_card_p9041; unfold a_p; omega

theorem BSD_ap_p9043 : a_p 9043 = (-132 : ℤ) := by
  have h := BSD_E143_card_p9043; unfold a_p; omega

theorem BSD_ap_p9049 : a_p 9049 = (44 : ℤ) := by
  have h := BSD_E143_card_p9049; unfold a_p; omega

theorem BSD_ap_p9059 : a_p 9059 = (-54 : ℤ) := by
  have h := BSD_E143_card_p9059; unfold a_p; omega

theorem BSD_ap_p9067 : a_p 9067 = (-65 : ℤ) := by
  have h := BSD_E143_card_p9067; unfold a_p; omega

theorem BSD_ap_p9091 : a_p 9091 = (163 : ℤ) := by
  have h := BSD_E143_card_p9091; unfold a_p; omega

theorem BSD_ap_p9103 : a_p 9103 = (-66 : ℤ) := by
  have h := BSD_E143_card_p9103; unfold a_p; omega

theorem BSD_ap_p9109 : a_p 9109 = (-55 : ℤ) := by
  have h := BSD_E143_card_p9109; unfold a_p; omega

theorem BSD_ap_p9127 : a_p 9127 = (-110 : ℤ) := by
  have h := BSD_E143_card_p9127; unfold a_p; omega

theorem BSD_ap_p9133 : a_p 9133 = (-107 : ℤ) := by
  have h := BSD_E143_card_p9133; unfold a_p; omega

theorem BSD_ap_p9137 : a_p 9137 = (-50 : ℤ) := by
  have h := BSD_E143_card_p9137; unfold a_p; omega

theorem BSD_ap_p9151 : a_p 9151 = (30 : ℤ) := by
  have h := BSD_E143_card_p9151; unfold a_p; omega

theorem BSD_ap_p9157 : a_p 9157 = (105 : ℤ) := by
  have h := BSD_E143_card_p9157; unfold a_p; omega

theorem BSD_ap_p9161 : a_p 9161 = (110 : ℤ) := by
  have h := BSD_E143_card_p9161; unfold a_p; omega

theorem BSD_ap_p9173 : a_p 9173 = (110 : ℤ) := by
  have h := BSD_E143_card_p9173; unfold a_p; omega

theorem BSD_ap_p9181 : a_p 9181 = (-150 : ℤ) := by
  have h := BSD_E143_card_p9181; unfold a_p; omega

theorem BSD_ap_p9187 : a_p 9187 = (-142 : ℤ) := by
  have h := BSD_E143_card_p9187; unfold a_p; omega

theorem BSD_ap_p9199 : a_p 9199 = (16 : ℤ) := by
  have h := BSD_E143_card_p9199; unfold a_p; omega

theorem BSD_ap_p9203 : a_p 9203 = (44 : ℤ) := by
  have h := BSD_E143_card_p9203; unfold a_p; omega

theorem BSD_ap_p9209 : a_p 9209 = (-12 : ℤ) := by
  have h := BSD_E143_card_p9209; unfold a_p; omega

theorem BSD_ap_p9221 : a_p 9221 = (-79 : ℤ) := by
  have h := BSD_E143_card_p9221; unfold a_p; omega

theorem BSD_ap_p9227 : a_p 9227 = (0 : ℤ) := by
  have h := BSD_E143_card_p9227; unfold a_p; omega

theorem BSD_ap_p9239 : a_p 9239 = (12 : ℤ) := by
  have h := BSD_E143_card_p9239; unfold a_p; omega

theorem BSD_ap_p9241 : a_p 9241 = (-39 : ℤ) := by
  have h := BSD_E143_card_p9241; unfold a_p; omega

theorem BSD_ap_p9257 : a_p 9257 = (118 : ℤ) := by
  have h := BSD_E143_card_p9257; unfold a_p; omega

theorem BSD_ap_p9277 : a_p 9277 = (17 : ℤ) := by
  have h := BSD_E143_card_p9277; unfold a_p; omega

theorem BSD_ap_p9281 : a_p 9281 = (-156 : ℤ) := by
  have h := BSD_E143_card_p9281; unfold a_p; omega

theorem BSD_ap_p9283 : a_p 9283 = (-94 : ℤ) := by
  have h := BSD_E143_card_p9283; unfold a_p; omega

theorem BSD_ap_p9293 : a_p 9293 = (14 : ℤ) := by
  have h := BSD_E143_card_p9293; unfold a_p; omega

theorem BSD_ap_p9311 : a_p 9311 = (131 : ℤ) := by
  have h := BSD_E143_card_p9311; unfold a_p; omega

theorem BSD_ap_p9319 : a_p 9319 = (-98 : ℤ) := by
  have h := BSD_E143_card_p9319; unfold a_p; omega

theorem BSD_ap_p9323 : a_p 9323 = (134 : ℤ) := by
  have h := BSD_E143_card_p9323; unfold a_p; omega

theorem BSD_ap_p9337 : a_p 9337 = (113 : ℤ) := by
  have h := BSD_E143_card_p9337; unfold a_p; omega

theorem BSD_ap_p9341 : a_p 9341 = (106 : ℤ) := by
  have h := BSD_E143_card_p9341; unfold a_p; omega

theorem BSD_ap_p9343 : a_p 9343 = (-183 : ℤ) := by
  have h := BSD_E143_card_p9343; unfold a_p; omega

theorem BSD_ap_p9349 : a_p 9349 = (-136 : ℤ) := by
  have h := BSD_E143_card_p9349; unfold a_p; omega

theorem BSD_ap_p9371 : a_p 9371 = (-12 : ℤ) := by
  have h := BSD_E143_card_p9371; unfold a_p; omega

theorem BSD_ap_p9377 : a_p 9377 = (70 : ℤ) := by
  have h := BSD_E143_card_p9377; unfold a_p; omega

theorem BSD_ap_p9391 : a_p 9391 = (-14 : ℤ) := by
  have h := BSD_E143_card_p9391; unfold a_p; omega

theorem BSD_ap_p9397 : a_p 9397 = (177 : ℤ) := by
  have h := BSD_E143_card_p9397; unfold a_p; omega

theorem BSD_ap_p9403 : a_p 9403 = (55 : ℤ) := by
  have h := BSD_E143_card_p9403; unfold a_p; omega

theorem BSD_ap_p9413 : a_p 9413 = (-106 : ℤ) := by
  have h := BSD_E143_card_p9413; unfold a_p; omega

theorem BSD_ap_p9419 : a_p 9419 = (40 : ℤ) := by
  have h := BSD_E143_card_p9419; unfold a_p; omega

theorem BSD_ap_p9421 : a_p 9421 = (-114 : ℤ) := by
  have h := BSD_E143_card_p9421; unfold a_p; omega

theorem BSD_ap_p9431 : a_p 9431 = (-64 : ℤ) := by
  have h := BSD_E143_card_p9431; unfold a_p; omega

theorem BSD_ap_p9433 : a_p 9433 = (-164 : ℤ) := by
  have h := BSD_E143_card_p9433; unfold a_p; omega

theorem BSD_ap_p9437 : a_p 9437 = (-52 : ℤ) := by
  have h := BSD_E143_card_p9437; unfold a_p; omega

theorem BSD_ap_p9439 : a_p 9439 = (33 : ℤ) := by
  have h := BSD_E143_card_p9439; unfold a_p; omega

theorem BSD_ap_p9461 : a_p 9461 = (170 : ℤ) := by
  have h := BSD_E143_card_p9461; unfold a_p; omega

theorem BSD_ap_p9463 : a_p 9463 = (184 : ℤ) := by
  have h := BSD_E143_card_p9463; unfold a_p; omega

theorem BSD_ap_p9467 : a_p 9467 = (-88 : ℤ) := by
  have h := BSD_E143_card_p9467; unfold a_p; omega

theorem BSD_ap_p9473 : a_p 9473 = (-44 : ℤ) := by
  have h := BSD_E143_card_p9473; unfold a_p; omega

theorem BSD_ap_p9479 : a_p 9479 = (22 : ℤ) := by
  have h := BSD_E143_card_p9479; unfold a_p; omega

theorem BSD_ap_p9491 : a_p 9491 = (-60 : ℤ) := by
  have h := BSD_E143_card_p9491; unfold a_p; omega

theorem BSD_ap_p9497 : a_p 9497 = (115 : ℤ) := by
  have h := BSD_E143_card_p9497; unfold a_p; omega

theorem BSD_ap_p9511 : a_p 9511 = (116 : ℤ) := by
  have h := BSD_E143_card_p9511; unfold a_p; omega

theorem BSD_ap_p9521 : a_p 9521 = (-50 : ℤ) := by
  have h := BSD_E143_card_p9521; unfold a_p; omega

theorem BSD_ap_p9533 : a_p 9533 = (74 : ℤ) := by
  have h := BSD_E143_card_p9533; unfold a_p; omega

theorem BSD_ap_p9539 : a_p 9539 = (0 : ℤ) := by
  have h := BSD_E143_card_p9539; unfold a_p; omega

theorem BSD_ap_p9547 : a_p 9547 = (98 : ℤ) := by
  have h := BSD_E143_card_p9547; unfold a_p; omega

theorem BSD_ap_p9551 : a_p 9551 = (139 : ℤ) := by
  have h := BSD_E143_card_p9551; unfold a_p; omega

theorem BSD_ap_p9587 : a_p 9587 = (-60 : ℤ) := by
  have h := BSD_E143_card_p9587; unfold a_p; omega

theorem BSD_ap_p9601 : a_p 9601 = (-111 : ℤ) := by
  have h := BSD_E143_card_p9601; unfold a_p; omega

theorem BSD_ap_p9613 : a_p 9613 = (-94 : ℤ) := by
  have h := BSD_E143_card_p9613; unfold a_p; omega

theorem BSD_ap_p9619 : a_p 9619 = (72 : ℤ) := by
  have h := BSD_E143_card_p9619; unfold a_p; omega

theorem BSD_ap_p9623 : a_p 9623 = (63 : ℤ) := by
  have h := BSD_E143_card_p9623; unfold a_p; omega

theorem BSD_ap_p9629 : a_p 9629 = (137 : ℤ) := by
  have h := BSD_E143_card_p9629; unfold a_p; omega

theorem BSD_ap_p9631 : a_p 9631 = (18 : ℤ) := by
  have h := BSD_E143_card_p9631; unfold a_p; omega

theorem BSD_ap_p9643 : a_p 9643 = (-46 : ℤ) := by
  have h := BSD_E143_card_p9643; unfold a_p; omega

theorem BSD_ap_p9649 : a_p 9649 = (-28 : ℤ) := by
  have h := BSD_E143_card_p9649; unfold a_p; omega

theorem BSD_ap_p9661 : a_p 9661 = (-47 : ℤ) := by
  have h := BSD_E143_card_p9661; unfold a_p; omega

theorem BSD_ap_p9677 : a_p 9677 = (-48 : ℤ) := by
  have h := BSD_E143_card_p9677; unfold a_p; omega

theorem BSD_ap_p9679 : a_p 9679 = (40 : ℤ) := by
  have h := BSD_E143_card_p9679; unfold a_p; omega

theorem BSD_ap_p9689 : a_p 9689 = (-15 : ℤ) := by
  have h := BSD_E143_card_p9689; unfold a_p; omega

theorem BSD_ap_p9697 : a_p 9697 = (46 : ℤ) := by
  have h := BSD_E143_card_p9697; unfold a_p; omega

theorem BSD_ap_p9719 : a_p 9719 = (-124 : ℤ) := by
  have h := BSD_E143_card_p9719; unfold a_p; omega

theorem BSD_ap_p9721 : a_p 9721 = (100 : ℤ) := by
  have h := BSD_E143_card_p9721; unfold a_p; omega

theorem BSD_ap_p9733 : a_p 9733 = (-19 : ℤ) := by
  have h := BSD_E143_card_p9733; unfold a_p; omega

theorem BSD_ap_p9739 : a_p 9739 = (-101 : ℤ) := by
  have h := BSD_E143_card_p9739; unfold a_p; omega

theorem BSD_ap_p9743 : a_p 9743 = (-44 : ℤ) := by
  have h := BSD_E143_card_p9743; unfold a_p; omega

theorem BSD_ap_p9749 : a_p 9749 = (86 : ℤ) := by
  have h := BSD_E143_card_p9749; unfold a_p; omega

theorem BSD_ap_p9767 : a_p 9767 = (18 : ℤ) := by
  have h := BSD_E143_card_p9767; unfold a_p; omega

theorem BSD_ap_p9769 : a_p 9769 = (61 : ℤ) := by
  have h := BSD_E143_card_p9769; unfold a_p; omega

theorem BSD_ap_p9781 : a_p 9781 = (88 : ℤ) := by
  have h := BSD_E143_card_p9781; unfold a_p; omega

theorem BSD_ap_p9787 : a_p 9787 = (-122 : ℤ) := by
  have h := BSD_E143_card_p9787; unfold a_p; omega

theorem BSD_ap_p9791 : a_p 9791 = (-112 : ℤ) := by
  have h := BSD_E143_card_p9791; unfold a_p; omega

theorem BSD_ap_p9803 : a_p 9803 = (-24 : ℤ) := by
  have h := BSD_E143_card_p9803; unfold a_p; omega

theorem BSD_ap_p9811 : a_p 9811 = (-18 : ℤ) := by
  have h := BSD_E143_card_p9811; unfold a_p; omega

theorem BSD_ap_p9817 : a_p 9817 = (90 : ℤ) := by
  have h := BSD_E143_card_p9817; unfold a_p; omega

theorem BSD_ap_p9829 : a_p 9829 = (14 : ℤ) := by
  have h := BSD_E143_card_p9829; unfold a_p; omega

theorem BSD_ap_p9833 : a_p 9833 = (6 : ℤ) := by
  have h := BSD_E143_card_p9833; unfold a_p; omega

theorem BSD_ap_p9839 : a_p 9839 = (-11 : ℤ) := by
  have h := BSD_E143_card_p9839; unfold a_p; omega

theorem BSD_ap_p9851 : a_p 9851 = (-66 : ℤ) := by
  have h := BSD_E143_card_p9851; unfold a_p; omega

theorem BSD_ap_p9857 : a_p 9857 = (-173 : ℤ) := by
  have h := BSD_E143_card_p9857; unfold a_p; omega

theorem BSD_ap_p9859 : a_p 9859 = (-23 : ℤ) := by
  have h := BSD_E143_card_p9859; unfold a_p; omega

theorem BSD_ap_p9871 : a_p 9871 = (-16 : ℤ) := by
  have h := BSD_E143_card_p9871; unfold a_p; omega

theorem BSD_ap_p9883 : a_p 9883 = (51 : ℤ) := by
  have h := BSD_E143_card_p9883; unfold a_p; omega

theorem BSD_ap_p9887 : a_p 9887 = (-27 : ℤ) := by
  have h := BSD_E143_card_p9887; unfold a_p; omega

theorem BSD_ap_p9901 : a_p 9901 = (-118 : ℤ) := by
  have h := BSD_E143_card_p9901; unfold a_p; omega

theorem BSD_ap_p9907 : a_p 9907 = (62 : ℤ) := by
  have h := BSD_E143_card_p9907; unfold a_p; omega

theorem BSD_ap_p9923 : a_p 9923 = (129 : ℤ) := by
  have h := BSD_E143_card_p9923; unfold a_p; omega

theorem BSD_ap_p9929 : a_p 9929 = (-146 : ℤ) := by
  have h := BSD_E143_card_p9929; unfold a_p; omega

theorem BSD_ap_p9931 : a_p 9931 = (-83 : ℤ) := by
  have h := BSD_E143_card_p9931; unfold a_p; omega

theorem BSD_ap_p9941 : a_p 9941 = (72 : ℤ) := by
  have h := BSD_E143_card_p9941; unfold a_p; omega

theorem BSD_ap_p9949 : a_p 9949 = (102 : ℤ) := by
  have h := BSD_E143_card_p9949; unfold a_p; omega

theorem BSD_ap_p9967 : a_p 9967 = (103 : ℤ) := by
  have h := BSD_E143_card_p9967; unfold a_p; omega

theorem BSD_ap_p9973 : a_p 9973 = (-48 : ℤ) := by
  have h := BSD_E143_card_p9973; unfold a_p; omega

-- §3 Degree non-negativity by completed square
theorem BSD_DegreeNonneg_p251 : BSD_FrobeniusDegreeNonneg_OPEN 251 := fun r => by
  have hap : (a_p 251 : ℝ) = 21 := by exact_mod_cast BSD_ap_p251
  have key : r ^ 2 - (a_p 251 : ℝ) * r + ((251 : ℕ) : ℝ) =
      (r - 21 / 2) ^ 2 + 563 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 21 / 2)]

theorem BSD_DegreeNonneg_p257 : BSD_FrobeniusDegreeNonneg_OPEN 257 := fun r => by
  have hap : (a_p 257 : ℝ) = 18 := by exact_mod_cast BSD_ap_p257
  have key : r ^ 2 - (a_p 257 : ℝ) * r + ((257 : ℕ) : ℝ) =
      (r - 9) ^ 2 + 176 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9)]

theorem BSD_DegreeNonneg_p263 : BSD_FrobeniusDegreeNonneg_OPEN 263 := fun r => by
  have hap : (a_p 263 : ℝ) = -18 := by exact_mod_cast BSD_ap_p263
  have key : r ^ 2 - (a_p 263 : ℝ) * r + ((263 : ℕ) : ℝ) =
      (r + 9) ^ 2 + 182 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9)]

theorem BSD_DegreeNonneg_p269 : BSD_FrobeniusDegreeNonneg_OPEN 269 := fun r => by
  have hap : (a_p 269 : ℝ) = -30 := by exact_mod_cast BSD_ap_p269
  have key : r ^ 2 - (a_p 269 : ℝ) * r + ((269 : ℕ) : ℝ) =
      (r + 15) ^ 2 + 44 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15)]

theorem BSD_DegreeNonneg_p271 : BSD_FrobeniusDegreeNonneg_OPEN 271 := fun r => by
  have hap : (a_p 271 : ℝ) = 28 := by exact_mod_cast BSD_ap_p271
  have key : r ^ 2 - (a_p 271 : ℝ) * r + ((271 : ℕ) : ℝ) =
      (r - 14) ^ 2 + 75 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 14)]

theorem BSD_DegreeNonneg_p277 : BSD_FrobeniusDegreeNonneg_OPEN 277 := fun r => by
  have hap : (a_p 277 : ℝ) = 26 := by exact_mod_cast BSD_ap_p277
  have key : r ^ 2 - (a_p 277 : ℝ) * r + ((277 : ℕ) : ℝ) =
      (r - 13) ^ 2 + 108 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 13)]

theorem BSD_DegreeNonneg_p281 : BSD_FrobeniusDegreeNonneg_OPEN 281 := fun r => by
  have hap : (a_p 281 : ℝ) = 18 := by exact_mod_cast BSD_ap_p281
  have key : r ^ 2 - (a_p 281 : ℝ) * r + ((281 : ℕ) : ℝ) =
      (r - 9) ^ 2 + 200 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9)]

theorem BSD_DegreeNonneg_p283 : BSD_FrobeniusDegreeNonneg_OPEN 283 := fun r => by
  have hap : (a_p 283 : ℝ) = -30 := by exact_mod_cast BSD_ap_p283
  have key : r ^ 2 - (a_p 283 : ℝ) * r + ((283 : ℕ) : ℝ) =
      (r + 15) ^ 2 + 58 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15)]

theorem BSD_DegreeNonneg_p293 : BSD_FrobeniusDegreeNonneg_OPEN 293 := fun r => by
  have hap : (a_p 293 : ℝ) = 14 := by exact_mod_cast BSD_ap_p293
  have key : r ^ 2 - (a_p 293 : ℝ) * r + ((293 : ℕ) : ℝ) =
      (r - 7) ^ 2 + 244 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 7)]

theorem BSD_DegreeNonneg_p307 : BSD_FrobeniusDegreeNonneg_OPEN 307 := fun r => by
  have hap : (a_p 307 : ℝ) = 0 := by exact_mod_cast BSD_ap_p307
  have key : r ^ 2 - (a_p 307 : ℝ) * r + ((307 : ℕ) : ℝ) =
      r ^ 2 + 307 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg r]

theorem BSD_DegreeNonneg_p311 : BSD_FrobeniusDegreeNonneg_OPEN 311 := fun r => by
  have hap : (a_p 311 : ℝ) = 8 := by exact_mod_cast BSD_ap_p311
  have key : r ^ 2 - (a_p 311 : ℝ) * r + ((311 : ℕ) : ℝ) =
      (r - 4) ^ 2 + 295 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 4)]

theorem BSD_DegreeNonneg_p313 : BSD_FrobeniusDegreeNonneg_OPEN 313 := fun r => by
  have hap : (a_p 313 : ℝ) = 3 := by exact_mod_cast BSD_ap_p313
  have key : r ^ 2 - (a_p 313 : ℝ) * r + ((313 : ℕ) : ℝ) =
      (r - 3 / 2) ^ 2 + 1243 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 3 / 2)]

theorem BSD_DegreeNonneg_p317 : BSD_FrobeniusDegreeNonneg_OPEN 317 := fun r => by
  have hap : (a_p 317 : ℝ) = -1 := by exact_mod_cast BSD_ap_p317
  have key : r ^ 2 - (a_p 317 : ℝ) * r + ((317 : ℕ) : ℝ) =
      (r + 1 / 2) ^ 2 + 1267 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1 / 2)]

theorem BSD_DegreeNonneg_p331 : BSD_FrobeniusDegreeNonneg_OPEN 331 := fun r => by
  have hap : (a_p 331 : ℝ) = -11 := by exact_mod_cast BSD_ap_p331
  have key : r ^ 2 - (a_p 331 : ℝ) * r + ((331 : ℕ) : ℝ) =
      (r + 11 / 2) ^ 2 + 1203 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 11 / 2)]

theorem BSD_DegreeNonneg_p337 : BSD_FrobeniusDegreeNonneg_OPEN 337 := fun r => by
  have hap : (a_p 337 : ℝ) = -20 := by exact_mod_cast BSD_ap_p337
  have key : r ^ 2 - (a_p 337 : ℝ) * r + ((337 : ℕ) : ℝ) =
      (r + 10) ^ 2 + 237 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 10)]

theorem BSD_DegreeNonneg_p347 : BSD_FrobeniusDegreeNonneg_OPEN 347 := fun r => by
  have hap : (a_p 347 : ℝ) = 18 := by exact_mod_cast BSD_ap_p347
  have key : r ^ 2 - (a_p 347 : ℝ) * r + ((347 : ℕ) : ℝ) =
      (r - 9) ^ 2 + 266 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9)]

theorem BSD_DegreeNonneg_p349 : BSD_FrobeniusDegreeNonneg_OPEN 349 := fun r => by
  have hap : (a_p 349 : ℝ) = 16 := by exact_mod_cast BSD_ap_p349
  have key : r ^ 2 - (a_p 349 : ℝ) * r + ((349 : ℕ) : ℝ) =
      (r - 8) ^ 2 + 285 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 8)]

theorem BSD_DegreeNonneg_p353 : BSD_FrobeniusDegreeNonneg_OPEN 353 := fun r => by
  have hap : (a_p 353 : ℝ) = -15 := by exact_mod_cast BSD_ap_p353
  have key : r ^ 2 - (a_p 353 : ℝ) * r + ((353 : ℕ) : ℝ) =
      (r + 15 / 2) ^ 2 + 1187 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15 / 2)]

theorem BSD_DegreeNonneg_p359 : BSD_FrobeniusDegreeNonneg_OPEN 359 := fun r => by
  have hap : (a_p 359 : ℝ) = 22 := by exact_mod_cast BSD_ap_p359
  have key : r ^ 2 - (a_p 359 : ℝ) * r + ((359 : ℕ) : ℝ) =
      (r - 11) ^ 2 + 238 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 11)]

theorem BSD_DegreeNonneg_p367 : BSD_FrobeniusDegreeNonneg_OPEN 367 := fun r => by
  have hap : (a_p 367 : ℝ) = 3 := by exact_mod_cast BSD_ap_p367
  have key : r ^ 2 - (a_p 367 : ℝ) * r + ((367 : ℕ) : ℝ) =
      (r - 3 / 2) ^ 2 + 1459 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 3 / 2)]

theorem BSD_DegreeNonneg_p373 : BSD_FrobeniusDegreeNonneg_OPEN 373 := fun r => by
  have hap : (a_p 373 : ℝ) = 26 := by exact_mod_cast BSD_ap_p373
  have key : r ^ 2 - (a_p 373 : ℝ) * r + ((373 : ℕ) : ℝ) =
      (r - 13) ^ 2 + 204 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 13)]

theorem BSD_DegreeNonneg_p379 : BSD_FrobeniusDegreeNonneg_OPEN 379 := fun r => by
  have hap : (a_p 379 : ℝ) = -11 := by exact_mod_cast BSD_ap_p379
  have key : r ^ 2 - (a_p 379 : ℝ) * r + ((379 : ℕ) : ℝ) =
      (r + 11 / 2) ^ 2 + 1395 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 11 / 2)]

theorem BSD_DegreeNonneg_p383 : BSD_FrobeniusDegreeNonneg_OPEN 383 := fun r => by
  have hap : (a_p 383 : ℝ) = -19 := by exact_mod_cast BSD_ap_p383
  have key : r ^ 2 - (a_p 383 : ℝ) * r + ((383 : ℕ) : ℝ) =
      (r + 19 / 2) ^ 2 + 1171 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 19 / 2)]

theorem BSD_DegreeNonneg_p389 : BSD_FrobeniusDegreeNonneg_OPEN 389 := fun r => by
  have hap : (a_p 389 : ℝ) = 9 := by exact_mod_cast BSD_ap_p389
  have key : r ^ 2 - (a_p 389 : ℝ) * r + ((389 : ℕ) : ℝ) =
      (r - 9 / 2) ^ 2 + 1475 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9 / 2)]

theorem BSD_DegreeNonneg_p397 : BSD_FrobeniusDegreeNonneg_OPEN 397 := fun r => by
  have hap : (a_p 397 : ℝ) = -18 := by exact_mod_cast BSD_ap_p397
  have key : r ^ 2 - (a_p 397 : ℝ) * r + ((397 : ℕ) : ℝ) =
      (r + 9) ^ 2 + 316 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9)]

theorem BSD_DegreeNonneg_p401 : BSD_FrobeniusDegreeNonneg_OPEN 401 := fun r => by
  have hap : (a_p 401 : ℝ) = -18 := by exact_mod_cast BSD_ap_p401
  have key : r ^ 2 - (a_p 401 : ℝ) * r + ((401 : ℕ) : ℝ) =
      (r + 9) ^ 2 + 320 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9)]

theorem BSD_DegreeNonneg_p409 : BSD_FrobeniusDegreeNonneg_OPEN 409 := fun r => by
  have hap : (a_p 409 : ℝ) = -18 := by exact_mod_cast BSD_ap_p409
  have key : r ^ 2 - (a_p 409 : ℝ) * r + ((409 : ℕ) : ℝ) =
      (r + 9) ^ 2 + 328 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9)]

theorem BSD_DegreeNonneg_p419 : BSD_FrobeniusDegreeNonneg_OPEN 419 := fun r => by
  have hap : (a_p 419 : ℝ) = -28 := by exact_mod_cast BSD_ap_p419
  have key : r ^ 2 - (a_p 419 : ℝ) * r + ((419 : ℕ) : ℝ) =
      (r + 14) ^ 2 + 223 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 14)]

theorem BSD_DegreeNonneg_p421 : BSD_FrobeniusDegreeNonneg_OPEN 421 := fun r => by
  have hap : (a_p 421 : ℝ) = -22 := by exact_mod_cast BSD_ap_p421
  have key : r ^ 2 - (a_p 421 : ℝ) * r + ((421 : ℕ) : ℝ) =
      (r + 11) ^ 2 + 300 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 11)]

theorem BSD_DegreeNonneg_p431 : BSD_FrobeniusDegreeNonneg_OPEN 431 := fun r => by
  have hap : (a_p 431 : ℝ) = -40 := by exact_mod_cast BSD_ap_p431
  have key : r ^ 2 - (a_p 431 : ℝ) * r + ((431 : ℕ) : ℝ) =
      (r + 20) ^ 2 + 31 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 20)]

theorem BSD_DegreeNonneg_p433 : BSD_FrobeniusDegreeNonneg_OPEN 433 := fun r => by
  have hap : (a_p 433 : ℝ) = 33 := by exact_mod_cast BSD_ap_p433
  have key : r ^ 2 - (a_p 433 : ℝ) * r + ((433 : ℕ) : ℝ) =
      (r - 33 / 2) ^ 2 + 643 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 33 / 2)]

theorem BSD_DegreeNonneg_p439 : BSD_FrobeniusDegreeNonneg_OPEN 439 := fun r => by
  have hap : (a_p 439 : ℝ) = 6 := by exact_mod_cast BSD_ap_p439
  have key : r ^ 2 - (a_p 439 : ℝ) * r + ((439 : ℕ) : ℝ) =
      (r - 3) ^ 2 + 430 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 3)]

theorem BSD_DegreeNonneg_p443 : BSD_FrobeniusDegreeNonneg_OPEN 443 := fun r => by
  have hap : (a_p 443 : ℝ) = -23 := by exact_mod_cast BSD_ap_p443
  have key : r ^ 2 - (a_p 443 : ℝ) * r + ((443 : ℕ) : ℝ) =
      (r + 23 / 2) ^ 2 + 1243 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 23 / 2)]

theorem BSD_DegreeNonneg_p449 : BSD_FrobeniusDegreeNonneg_OPEN 449 := fun r => by
  have hap : (a_p 449 : ℝ) = 21 := by exact_mod_cast BSD_ap_p449
  have key : r ^ 2 - (a_p 449 : ℝ) * r + ((449 : ℕ) : ℝ) =
      (r - 21 / 2) ^ 2 + 1355 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 21 / 2)]

theorem BSD_DegreeNonneg_p457 : BSD_FrobeniusDegreeNonneg_OPEN 457 := fun r => by
  have hap : (a_p 457 : ℝ) = -16 := by exact_mod_cast BSD_ap_p457
  have key : r ^ 2 - (a_p 457 : ℝ) * r + ((457 : ℕ) : ℝ) =
      (r + 8) ^ 2 + 393 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 8)]

theorem BSD_DegreeNonneg_p461 : BSD_FrobeniusDegreeNonneg_OPEN 461 := fun r => by
  have hap : (a_p 461 : ℝ) = 10 := by exact_mod_cast BSD_ap_p461
  have key : r ^ 2 - (a_p 461 : ℝ) * r + ((461 : ℕ) : ℝ) =
      (r - 5) ^ 2 + 436 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 5)]

theorem BSD_DegreeNonneg_p463 : BSD_FrobeniusDegreeNonneg_OPEN 463 := fun r => by
  have hap : (a_p 463 : ℝ) = -9 := by exact_mod_cast BSD_ap_p463
  have key : r ^ 2 - (a_p 463 : ℝ) * r + ((463 : ℕ) : ℝ) =
      (r + 9 / 2) ^ 2 + 1771 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9 / 2)]

theorem BSD_DegreeNonneg_p467 : BSD_FrobeniusDegreeNonneg_OPEN 467 := fun r => by
  have hap : (a_p 467 : ℝ) = -23 := by exact_mod_cast BSD_ap_p467
  have key : r ^ 2 - (a_p 467 : ℝ) * r + ((467 : ℕ) : ℝ) =
      (r + 23 / 2) ^ 2 + 1339 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 23 / 2)]

theorem BSD_DegreeNonneg_p479 : BSD_FrobeniusDegreeNonneg_OPEN 479 := fun r => by
  have hap : (a_p 479 : ℝ) = 36 := by exact_mod_cast BSD_ap_p479
  have key : r ^ 2 - (a_p 479 : ℝ) * r + ((479 : ℕ) : ℝ) =
      (r - 18) ^ 2 + 155 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 18)]

theorem BSD_DegreeNonneg_p487 : BSD_FrobeniusDegreeNonneg_OPEN 487 := fun r => by
  have hap : (a_p 487 : ℝ) = 25 := by exact_mod_cast BSD_ap_p487
  have key : r ^ 2 - (a_p 487 : ℝ) * r + ((487 : ℕ) : ℝ) =
      (r - 25 / 2) ^ 2 + 1323 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 25 / 2)]

theorem BSD_DegreeNonneg_p491 : BSD_FrobeniusDegreeNonneg_OPEN 491 := fun r => by
  have hap : (a_p 491 : ℝ) = 12 := by exact_mod_cast BSD_ap_p491
  have key : r ^ 2 - (a_p 491 : ℝ) * r + ((491 : ℕ) : ℝ) =
      (r - 6) ^ 2 + 455 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 6)]

theorem BSD_DegreeNonneg_p499 : BSD_FrobeniusDegreeNonneg_OPEN 499 := fun r => by
  have hap : (a_p 499 : ℝ) = 28 := by exact_mod_cast BSD_ap_p499
  have key : r ^ 2 - (a_p 499 : ℝ) * r + ((499 : ℕ) : ℝ) =
      (r - 14) ^ 2 + 303 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 14)]

theorem BSD_DegreeNonneg_p503 : BSD_FrobeniusDegreeNonneg_OPEN 503 := fun r => by
  have hap : (a_p 503 : ℝ) = 30 := by exact_mod_cast BSD_ap_p503
  have key : r ^ 2 - (a_p 503 : ℝ) * r + ((503 : ℕ) : ℝ) =
      (r - 15) ^ 2 + 278 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 15)]

theorem BSD_DegreeNonneg_p509 : BSD_FrobeniusDegreeNonneg_OPEN 509 := fun r => by
  have hap : (a_p 509 : ℝ) = 9 := by exact_mod_cast BSD_ap_p509
  have key : r ^ 2 - (a_p 509 : ℝ) * r + ((509 : ℕ) : ℝ) =
      (r - 9 / 2) ^ 2 + 1955 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9 / 2)]

theorem BSD_DegreeNonneg_p521 : BSD_FrobeniusDegreeNonneg_OPEN 521 := fun r => by
  have hap : (a_p 521 : ℝ) = 5 := by exact_mod_cast BSD_ap_p521
  have key : r ^ 2 - (a_p 521 : ℝ) * r + ((521 : ℕ) : ℝ) =
      (r - 5 / 2) ^ 2 + 2059 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 5 / 2)]

theorem BSD_DegreeNonneg_p523 : BSD_FrobeniusDegreeNonneg_OPEN 523 := fun r => by
  have hap : (a_p 523 : ℝ) = -14 := by exact_mod_cast BSD_ap_p523
  have key : r ^ 2 - (a_p 523 : ℝ) * r + ((523 : ℕ) : ℝ) =
      (r + 7) ^ 2 + 474 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 7)]

theorem BSD_DegreeNonneg_p541 : BSD_FrobeniusDegreeNonneg_OPEN 541 := fun r => by
  have hap : (a_p 541 : ℝ) = -30 := by exact_mod_cast BSD_ap_p541
  have key : r ^ 2 - (a_p 541 : ℝ) * r + ((541 : ℕ) : ℝ) =
      (r + 15) ^ 2 + 316 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15)]

theorem BSD_DegreeNonneg_p547 : BSD_FrobeniusDegreeNonneg_OPEN 547 := fun r => by
  have hap : (a_p 547 : ℝ) = 8 := by exact_mod_cast BSD_ap_p547
  have key : r ^ 2 - (a_p 547 : ℝ) * r + ((547 : ℕ) : ℝ) =
      (r - 4) ^ 2 + 531 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 4)]

theorem BSD_DegreeNonneg_p557 : BSD_FrobeniusDegreeNonneg_OPEN 557 := fun r => by
  have hap : (a_p 557 : ℝ) = 12 := by exact_mod_cast BSD_ap_p557
  have key : r ^ 2 - (a_p 557 : ℝ) * r + ((557 : ℕ) : ℝ) =
      (r - 6) ^ 2 + 521 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 6)]

theorem BSD_DegreeNonneg_p563 : BSD_FrobeniusDegreeNonneg_OPEN 563 := fun r => by
  have hap : (a_p 563 : ℝ) = 18 := by exact_mod_cast BSD_ap_p563
  have key : r ^ 2 - (a_p 563 : ℝ) * r + ((563 : ℕ) : ℝ) =
      (r - 9) ^ 2 + 482 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9)]

theorem BSD_DegreeNonneg_p569 : BSD_FrobeniusDegreeNonneg_OPEN 569 := fun r => by
  have hap : (a_p 569 : ℝ) = -32 := by exact_mod_cast BSD_ap_p569
  have key : r ^ 2 - (a_p 569 : ℝ) * r + ((569 : ℕ) : ℝ) =
      (r + 16) ^ 2 + 313 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 16)]

theorem BSD_DegreeNonneg_p571 : BSD_FrobeniusDegreeNonneg_OPEN 571 := fun r => by
  have hap : (a_p 571 : ℝ) = 40 := by exact_mod_cast BSD_ap_p571
  have key : r ^ 2 - (a_p 571 : ℝ) * r + ((571 : ℕ) : ℝ) =
      (r - 20) ^ 2 + 171 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 20)]

theorem BSD_DegreeNonneg_p577 : BSD_FrobeniusDegreeNonneg_OPEN 577 := fun r => by
  have hap : (a_p 577 : ℝ) = 31 := by exact_mod_cast BSD_ap_p577
  have key : r ^ 2 - (a_p 577 : ℝ) * r + ((577 : ℕ) : ℝ) =
      (r - 31 / 2) ^ 2 + 1347 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 31 / 2)]

theorem BSD_DegreeNonneg_p587 : BSD_FrobeniusDegreeNonneg_OPEN 587 := fun r => by
  have hap : (a_p 587 : ℝ) = -12 := by exact_mod_cast BSD_ap_p587
  have key : r ^ 2 - (a_p 587 : ℝ) * r + ((587 : ℕ) : ℝ) =
      (r + 6) ^ 2 + 551 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 6)]

theorem BSD_DegreeNonneg_p593 : BSD_FrobeniusDegreeNonneg_OPEN 593 := fun r => by
  have hap : (a_p 593 : ℝ) = 24 := by exact_mod_cast BSD_ap_p593
  have key : r ^ 2 - (a_p 593 : ℝ) * r + ((593 : ℕ) : ℝ) =
      (r - 12) ^ 2 + 449 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 12)]

theorem BSD_DegreeNonneg_p599 : BSD_FrobeniusDegreeNonneg_OPEN 599 := fun r => by
  have hap : (a_p 599 : ℝ) = 24 := by exact_mod_cast BSD_ap_p599
  have key : r ^ 2 - (a_p 599 : ℝ) * r + ((599 : ℕ) : ℝ) =
      (r - 12) ^ 2 + 455 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 12)]

theorem BSD_DegreeNonneg_p601 : BSD_FrobeniusDegreeNonneg_OPEN 601 := fun r => by
  have hap : (a_p 601 : ℝ) = -22 := by exact_mod_cast BSD_ap_p601
  have key : r ^ 2 - (a_p 601 : ℝ) * r + ((601 : ℕ) : ℝ) =
      (r + 11) ^ 2 + 480 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 11)]

theorem BSD_DegreeNonneg_p607 : BSD_FrobeniusDegreeNonneg_OPEN 607 := fun r => by
  have hap : (a_p 607 : ℝ) = -22 := by exact_mod_cast BSD_ap_p607
  have key : r ^ 2 - (a_p 607 : ℝ) * r + ((607 : ℕ) : ℝ) =
      (r + 11) ^ 2 + 486 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 11)]

theorem BSD_DegreeNonneg_p613 : BSD_FrobeniusDegreeNonneg_OPEN 613 := fun r => by
  have hap : (a_p 613 : ℝ) = -2 := by exact_mod_cast BSD_ap_p613
  have key : r ^ 2 - (a_p 613 : ℝ) * r + ((613 : ℕ) : ℝ) =
      (r + 1) ^ 2 + 612 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1)]

theorem BSD_DegreeNonneg_p617 : BSD_FrobeniusDegreeNonneg_OPEN 617 := fun r => by
  have hap : (a_p 617 : ℝ) = 42 := by exact_mod_cast BSD_ap_p617
  have key : r ^ 2 - (a_p 617 : ℝ) * r + ((617 : ℕ) : ℝ) =
      (r - 21) ^ 2 + 176 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 21)]

theorem BSD_DegreeNonneg_p619 : BSD_FrobeniusDegreeNonneg_OPEN 619 := fun r => by
  have hap : (a_p 619 : ℝ) = -7 := by exact_mod_cast BSD_ap_p619
  have key : r ^ 2 - (a_p 619 : ℝ) * r + ((619 : ℕ) : ℝ) =
      (r + 7 / 2) ^ 2 + 2427 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 7 / 2)]

theorem BSD_DegreeNonneg_p631 : BSD_FrobeniusDegreeNonneg_OPEN 631 := fun r => by
  have hap : (a_p 631 : ℝ) = -27 := by exact_mod_cast BSD_ap_p631
  have key : r ^ 2 - (a_p 631 : ℝ) * r + ((631 : ℕ) : ℝ) =
      (r + 27 / 2) ^ 2 + 1795 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 27 / 2)]

theorem BSD_DegreeNonneg_p641 : BSD_FrobeniusDegreeNonneg_OPEN 641 := fun r => by
  have hap : (a_p 641 : ℝ) = -33 := by exact_mod_cast BSD_ap_p641
  have key : r ^ 2 - (a_p 641 : ℝ) * r + ((641 : ℕ) : ℝ) =
      (r + 33 / 2) ^ 2 + 1475 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 33 / 2)]

theorem BSD_DegreeNonneg_p643 : BSD_FrobeniusDegreeNonneg_OPEN 643 := fun r => by
  have hap : (a_p 643 : ℝ) = -49 := by exact_mod_cast BSD_ap_p643
  have key : r ^ 2 - (a_p 643 : ℝ) * r + ((643 : ℕ) : ℝ) =
      (r + 49 / 2) ^ 2 + 171 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 49 / 2)]

theorem BSD_DegreeNonneg_p647 : BSD_FrobeniusDegreeNonneg_OPEN 647 := fun r => by
  have hap : (a_p 647 : ℝ) = -15 := by exact_mod_cast BSD_ap_p647
  have key : r ^ 2 - (a_p 647 : ℝ) * r + ((647 : ℕ) : ℝ) =
      (r + 15 / 2) ^ 2 + 2363 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15 / 2)]

theorem BSD_DegreeNonneg_p653 : BSD_FrobeniusDegreeNonneg_OPEN 653 := fun r => by
  have hap : (a_p 653 : ℝ) = -13 := by exact_mod_cast BSD_ap_p653
  have key : r ^ 2 - (a_p 653 : ℝ) * r + ((653 : ℕ) : ℝ) =
      (r + 13 / 2) ^ 2 + 2443 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 13 / 2)]

theorem BSD_DegreeNonneg_p659 : BSD_FrobeniusDegreeNonneg_OPEN 659 := fun r => by
  have hap : (a_p 659 : ℝ) = -44 := by exact_mod_cast BSD_ap_p659
  have key : r ^ 2 - (a_p 659 : ℝ) * r + ((659 : ℕ) : ℝ) =
      (r + 22) ^ 2 + 175 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 22)]

theorem BSD_DegreeNonneg_p661 : BSD_FrobeniusDegreeNonneg_OPEN 661 := fun r => by
  have hap : (a_p 661 : ℝ) = 31 := by exact_mod_cast BSD_ap_p661
  have key : r ^ 2 - (a_p 661 : ℝ) * r + ((661 : ℕ) : ℝ) =
      (r - 31 / 2) ^ 2 + 1683 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 31 / 2)]

theorem BSD_DegreeNonneg_p673 : BSD_FrobeniusDegreeNonneg_OPEN 673 := fun r => by
  have hap : (a_p 673 : ℝ) = 4 := by exact_mod_cast BSD_ap_p673
  have key : r ^ 2 - (a_p 673 : ℝ) * r + ((673 : ℕ) : ℝ) =
      (r - 2) ^ 2 + 669 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 2)]

theorem BSD_DegreeNonneg_p677 : BSD_FrobeniusDegreeNonneg_OPEN 677 := fun r => by
  have hap : (a_p 677 : ℝ) = 6 := by exact_mod_cast BSD_ap_p677
  have key : r ^ 2 - (a_p 677 : ℝ) * r + ((677 : ℕ) : ℝ) =
      (r - 3) ^ 2 + 668 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 3)]

theorem BSD_DegreeNonneg_p683 : BSD_FrobeniusDegreeNonneg_OPEN 683 := fun r => by
  have hap : (a_p 683 : ℝ) = -4 := by exact_mod_cast BSD_ap_p683
  have key : r ^ 2 - (a_p 683 : ℝ) * r + ((683 : ℕ) : ℝ) =
      (r + 2) ^ 2 + 679 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 2)]

theorem BSD_DegreeNonneg_p691 : BSD_FrobeniusDegreeNonneg_OPEN 691 := fun r => by
  have hap : (a_p 691 : ℝ) = -45 := by exact_mod_cast BSD_ap_p691
  have key : r ^ 2 - (a_p 691 : ℝ) * r + ((691 : ℕ) : ℝ) =
      (r + 45 / 2) ^ 2 + 739 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 45 / 2)]

theorem BSD_DegreeNonneg_p701 : BSD_FrobeniusDegreeNonneg_OPEN 701 := fun r => by
  have hap : (a_p 701 : ℝ) = -10 := by exact_mod_cast BSD_ap_p701
  have key : r ^ 2 - (a_p 701 : ℝ) * r + ((701 : ℕ) : ℝ) =
      (r + 5) ^ 2 + 676 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 5)]

theorem BSD_DegreeNonneg_p709 : BSD_FrobeniusDegreeNonneg_OPEN 709 := fun r => by
  have hap : (a_p 709 : ℝ) = -35 := by exact_mod_cast BSD_ap_p709
  have key : r ^ 2 - (a_p 709 : ℝ) * r + ((709 : ℕ) : ℝ) =
      (r + 35 / 2) ^ 2 + 1611 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 35 / 2)]

theorem BSD_DegreeNonneg_p719 : BSD_FrobeniusDegreeNonneg_OPEN 719 := fun r => by
  have hap : (a_p 719 : ℝ) = -41 := by exact_mod_cast BSD_ap_p719
  have key : r ^ 2 - (a_p 719 : ℝ) * r + ((719 : ℕ) : ℝ) =
      (r + 41 / 2) ^ 2 + 1195 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 41 / 2)]

theorem BSD_DegreeNonneg_p727 : BSD_FrobeniusDegreeNonneg_OPEN 727 := fun r => by
  have hap : (a_p 727 : ℝ) = 19 := by exact_mod_cast BSD_ap_p727
  have key : r ^ 2 - (a_p 727 : ℝ) * r + ((727 : ℕ) : ℝ) =
      (r - 19 / 2) ^ 2 + 2547 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 19 / 2)]

theorem BSD_DegreeNonneg_p733 : BSD_FrobeniusDegreeNonneg_OPEN 733 := fun r => by
  have hap : (a_p 733 : ℝ) = -46 := by exact_mod_cast BSD_ap_p733
  have key : r ^ 2 - (a_p 733 : ℝ) * r + ((733 : ℕ) : ℝ) =
      (r + 23) ^ 2 + 204 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 23)]

theorem BSD_DegreeNonneg_p739 : BSD_FrobeniusDegreeNonneg_OPEN 739 := fun r => by
  have hap : (a_p 739 : ℝ) = -2 := by exact_mod_cast BSD_ap_p739
  have key : r ^ 2 - (a_p 739 : ℝ) * r + ((739 : ℕ) : ℝ) =
      (r + 1) ^ 2 + 738 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 1)]

theorem BSD_DegreeNonneg_p743 : BSD_FrobeniusDegreeNonneg_OPEN 743 := fun r => by
  have hap : (a_p 743 : ℝ) = 42 := by exact_mod_cast BSD_ap_p743
  have key : r ^ 2 - (a_p 743 : ℝ) * r + ((743 : ℕ) : ℝ) =
      (r - 21) ^ 2 + 302 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 21)]

theorem BSD_DegreeNonneg_p751 : BSD_FrobeniusDegreeNonneg_OPEN 751 := fun r => by
  have hap : (a_p 751 : ℝ) = -39 := by exact_mod_cast BSD_ap_p751
  have key : r ^ 2 - (a_p 751 : ℝ) * r + ((751 : ℕ) : ℝ) =
      (r + 39 / 2) ^ 2 + 1483 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 39 / 2)]

theorem BSD_DegreeNonneg_p757 : BSD_FrobeniusDegreeNonneg_OPEN 757 := fun r => by
  have hap : (a_p 757 : ℝ) = 30 := by exact_mod_cast BSD_ap_p757
  have key : r ^ 2 - (a_p 757 : ℝ) * r + ((757 : ℕ) : ℝ) =
      (r - 15) ^ 2 + 532 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 15)]

theorem BSD_DegreeNonneg_p761 : BSD_FrobeniusDegreeNonneg_OPEN 761 := fun r => by
  have hap : (a_p 761 : ℝ) = -34 := by exact_mod_cast BSD_ap_p761
  have key : r ^ 2 - (a_p 761 : ℝ) * r + ((761 : ℕ) : ℝ) =
      (r + 17) ^ 2 + 472 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 17)]

theorem BSD_DegreeNonneg_p769 : BSD_FrobeniusDegreeNonneg_OPEN 769 := fun r => by
  have hap : (a_p 769 : ℝ) = 0 := by exact_mod_cast BSD_ap_p769
  have key : r ^ 2 - (a_p 769 : ℝ) * r + ((769 : ℕ) : ℝ) =
      r ^ 2 + 769 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r)]

theorem BSD_DegreeNonneg_p773 : BSD_FrobeniusDegreeNonneg_OPEN 773 := fun r => by
  have hap : (a_p 773 : ℝ) = 30 := by exact_mod_cast BSD_ap_p773
  have key : r ^ 2 - (a_p 773 : ℝ) * r + ((773 : ℕ) : ℝ) =
      (r - 15) ^ 2 + 548 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 15)]

theorem BSD_DegreeNonneg_p787 : BSD_FrobeniusDegreeNonneg_OPEN 787 := fun r => by
  have hap : (a_p 787 : ℝ) = 12 := by exact_mod_cast BSD_ap_p787
  have key : r ^ 2 - (a_p 787 : ℝ) * r + ((787 : ℕ) : ℝ) =
      (r - 6) ^ 2 + 751 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 6)]

theorem BSD_DegreeNonneg_p797 : BSD_FrobeniusDegreeNonneg_OPEN 797 := fun r => by
  have hap : (a_p 797 : ℝ) = 17 := by exact_mod_cast BSD_ap_p797
  have key : r ^ 2 - (a_p 797 : ℝ) * r + ((797 : ℕ) : ℝ) =
      (r - 17 / 2) ^ 2 + 2899 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 17 / 2)]

theorem BSD_DegreeNonneg_p809 : BSD_FrobeniusDegreeNonneg_OPEN 809 := fun r => by
  have hap : (a_p 809 : ℝ) = 24 := by exact_mod_cast BSD_ap_p809
  have key : r ^ 2 - (a_p 809 : ℝ) * r + ((809 : ℕ) : ℝ) =
      (r - 12) ^ 2 + 665 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 12)]

theorem BSD_DegreeNonneg_p811 : BSD_FrobeniusDegreeNonneg_OPEN 811 := fun r => by
  have hap : (a_p 811 : ℝ) = -36 := by exact_mod_cast BSD_ap_p811
  have key : r ^ 2 - (a_p 811 : ℝ) * r + ((811 : ℕ) : ℝ) =
      (r + 18) ^ 2 + 487 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 18)]

theorem BSD_DegreeNonneg_p821 : BSD_FrobeniusDegreeNonneg_OPEN 821 := fun r => by
  have hap : (a_p 821 : ℝ) = 0 := by exact_mod_cast BSD_ap_p821
  have key : r ^ 2 - (a_p 821 : ℝ) * r + ((821 : ℕ) : ℝ) =
      r ^ 2 + 821 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r)]

theorem BSD_DegreeNonneg_p823 : BSD_FrobeniusDegreeNonneg_OPEN 823 := fun r => by
  have hap : (a_p 823 : ℝ) = -29 := by exact_mod_cast BSD_ap_p823
  have key : r ^ 2 - (a_p 823 : ℝ) * r + ((823 : ℕ) : ℝ) =
      (r + 29 / 2) ^ 2 + 2451 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 29 / 2)]

theorem BSD_DegreeNonneg_p827 : BSD_FrobeniusDegreeNonneg_OPEN 827 := fun r => by
  have hap : (a_p 827 : ℝ) = 50 := by exact_mod_cast BSD_ap_p827
  have key : r ^ 2 - (a_p 827 : ℝ) * r + ((827 : ℕ) : ℝ) =
      (r - 25) ^ 2 + 202 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 25)]

theorem BSD_DegreeNonneg_p829 : BSD_FrobeniusDegreeNonneg_OPEN 829 := fun r => by
  have hap : (a_p 829 : ℝ) = 29 := by exact_mod_cast BSD_ap_p829
  have key : r ^ 2 - (a_p 829 : ℝ) * r + ((829 : ℕ) : ℝ) =
      (r - 29 / 2) ^ 2 + 2475 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 29 / 2)]

theorem BSD_DegreeNonneg_p839 : BSD_FrobeniusDegreeNonneg_OPEN 839 := fun r => by
  have hap : (a_p 839 : ℝ) = 53 := by exact_mod_cast BSD_ap_p839
  have key : r ^ 2 - (a_p 839 : ℝ) * r + ((839 : ℕ) : ℝ) =
      (r - 53 / 2) ^ 2 + 547 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 53 / 2)]

theorem BSD_DegreeNonneg_p853 : BSD_FrobeniusDegreeNonneg_OPEN 853 := fun r => by
  have hap : (a_p 853 : ℝ) = -50 := by exact_mod_cast BSD_ap_p853
  have key : r ^ 2 - (a_p 853 : ℝ) * r + ((853 : ℕ) : ℝ) =
      (r + 25) ^ 2 + 228 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 25)]

theorem BSD_DegreeNonneg_p857 : BSD_FrobeniusDegreeNonneg_OPEN 857 := fun r => by
  have hap : (a_p 857 : ℝ) = -32 := by exact_mod_cast BSD_ap_p857
  have key : r ^ 2 - (a_p 857 : ℝ) * r + ((857 : ℕ) : ℝ) =
      (r + 16) ^ 2 + 601 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 16)]

theorem BSD_DegreeNonneg_p859 : BSD_FrobeniusDegreeNonneg_OPEN 859 := fun r => by
  have hap : (a_p 859 : ℝ) = 13 := by exact_mod_cast BSD_ap_p859
  have key : r ^ 2 - (a_p 859 : ℝ) * r + ((859 : ℕ) : ℝ) =
      (r - 13 / 2) ^ 2 + 3267 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 13 / 2)]

theorem BSD_DegreeNonneg_p863 : BSD_FrobeniusDegreeNonneg_OPEN 863 := fun r => by
  have hap : (a_p 863 : ℝ) = 48 := by exact_mod_cast BSD_ap_p863
  have key : r ^ 2 - (a_p 863 : ℝ) * r + ((863 : ℕ) : ℝ) =
      (r - 24) ^ 2 + 287 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 24)]

theorem BSD_DegreeNonneg_p877 : BSD_FrobeniusDegreeNonneg_OPEN 877 := fun r => by
  have hap : (a_p 877 : ℝ) = 38 := by exact_mod_cast BSD_ap_p877
  have key : r ^ 2 - (a_p 877 : ℝ) * r + ((877 : ℕ) : ℝ) =
      (r - 19) ^ 2 + 516 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 19)]

theorem BSD_DegreeNonneg_p881 : BSD_FrobeniusDegreeNonneg_OPEN 881 := fun r => by
  have hap : (a_p 881 : ℝ) = 33 := by exact_mod_cast BSD_ap_p881
  have key : r ^ 2 - (a_p 881 : ℝ) * r + ((881 : ℕ) : ℝ) =
      (r - 33 / 2) ^ 2 + 2435 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 33 / 2)]

theorem BSD_DegreeNonneg_p883 : BSD_FrobeniusDegreeNonneg_OPEN 883 := fun r => by
  have hap : (a_p 883 : ℝ) = 28 := by exact_mod_cast BSD_ap_p883
  have key : r ^ 2 - (a_p 883 : ℝ) * r + ((883 : ℕ) : ℝ) =
      (r - 14) ^ 2 + 687 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 14)]

theorem BSD_DegreeNonneg_p887 : BSD_FrobeniusDegreeNonneg_OPEN 887 := fun r => by
  have hap : (a_p 887 : ℝ) = 12 := by exact_mod_cast BSD_ap_p887
  have key : r ^ 2 - (a_p 887 : ℝ) * r + ((887 : ℕ) : ℝ) =
      (r - 6) ^ 2 + 851 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 6)]

theorem BSD_DegreeNonneg_p907 : BSD_FrobeniusDegreeNonneg_OPEN 907 := fun r => by
  have hap : (a_p 907 : ℝ) = 52 := by exact_mod_cast BSD_ap_p907
  have key : r ^ 2 - (a_p 907 : ℝ) * r + ((907 : ℕ) : ℝ) =
      (r - 26) ^ 2 + 231 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 26)]

theorem BSD_DegreeNonneg_p911 : BSD_FrobeniusDegreeNonneg_OPEN 911 := fun r => by
  have hap : (a_p 911 : ℝ) = -8 := by exact_mod_cast BSD_ap_p911
  have key : r ^ 2 - (a_p 911 : ℝ) * r + ((911 : ℕ) : ℝ) =
      (r + 4) ^ 2 + 895 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 4)]

theorem BSD_DegreeNonneg_p919 : BSD_FrobeniusDegreeNonneg_OPEN 919 := fun r => by
  have hap : (a_p 919 : ℝ) = 40 := by exact_mod_cast BSD_ap_p919
  have key : r ^ 2 - (a_p 919 : ℝ) * r + ((919 : ℕ) : ℝ) =
      (r - 20) ^ 2 + 519 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 20)]

theorem BSD_DegreeNonneg_p929 : BSD_FrobeniusDegreeNonneg_OPEN 929 := fun r => by
  have hap : (a_p 929 : ℝ) = -42 := by exact_mod_cast BSD_ap_p929
  have key : r ^ 2 - (a_p 929 : ℝ) * r + ((929 : ℕ) : ℝ) =
      (r + 21) ^ 2 + 488 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 21)]

theorem BSD_DegreeNonneg_p937 : BSD_FrobeniusDegreeNonneg_OPEN 937 := fun r => by
  have hap : (a_p 937 : ℝ) = -12 := by exact_mod_cast BSD_ap_p937
  have key : r ^ 2 - (a_p 937 : ℝ) * r + ((937 : ℕ) : ℝ) =
      (r + 6) ^ 2 + 901 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 6)]

theorem BSD_DegreeNonneg_p941 : BSD_FrobeniusDegreeNonneg_OPEN 941 := fun r => by
  have hap : (a_p 941 : ℝ) = -36 := by exact_mod_cast BSD_ap_p941
  have key : r ^ 2 - (a_p 941 : ℝ) * r + ((941 : ℕ) : ℝ) =
      (r + 18) ^ 2 + 617 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 18)]

theorem BSD_DegreeNonneg_p947 : BSD_FrobeniusDegreeNonneg_OPEN 947 := fun r => by
  have hap : (a_p 947 : ℝ) = -9 := by exact_mod_cast BSD_ap_p947
  have key : r ^ 2 - (a_p 947 : ℝ) * r + ((947 : ℕ) : ℝ) =
      (r + 9 / 2) ^ 2 + 3707 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9 / 2)]

theorem BSD_DegreeNonneg_p953 : BSD_FrobeniusDegreeNonneg_OPEN 953 := fun r => by
  have hap : (a_p 953 : ℝ) = -30 := by exact_mod_cast BSD_ap_p953
  have key : r ^ 2 - (a_p 953 : ℝ) * r + ((953 : ℕ) : ℝ) =
      (r + 15) ^ 2 + 728 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15)]

theorem BSD_DegreeNonneg_p967 : BSD_FrobeniusDegreeNonneg_OPEN 967 := fun r => by
  have hap : (a_p 967 : ℝ) = 28 := by exact_mod_cast BSD_ap_p967
  have key : r ^ 2 - (a_p 967 : ℝ) * r + ((967 : ℕ) : ℝ) =
      (r - 14) ^ 2 + 771 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 14)]

theorem BSD_DegreeNonneg_p971 : BSD_FrobeniusDegreeNonneg_OPEN 971 := fun r => by
  have hap : (a_p 971 : ℝ) = -49 := by exact_mod_cast BSD_ap_p971
  have key : r ^ 2 - (a_p 971 : ℝ) * r + ((971 : ℕ) : ℝ) =
      (r + 49 / 2) ^ 2 + 1483 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 49 / 2)]

theorem BSD_DegreeNonneg_p977 : BSD_FrobeniusDegreeNonneg_OPEN 977 := fun r => by
  have hap : (a_p 977 : ℝ) = -9 := by exact_mod_cast BSD_ap_p977
  have key : r ^ 2 - (a_p 977 : ℝ) * r + ((977 : ℕ) : ℝ) =
      (r + 9 / 2) ^ 2 + 3827 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9 / 2)]

theorem BSD_DegreeNonneg_p983 : BSD_FrobeniusDegreeNonneg_OPEN 983 := fun r => by
  have hap : (a_p 983 : ℝ) = -31 := by exact_mod_cast BSD_ap_p983
  have key : r ^ 2 - (a_p 983 : ℝ) * r + ((983 : ℕ) : ℝ) =
      (r + 31 / 2) ^ 2 + 2971 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 31 / 2)]

theorem BSD_DegreeNonneg_p991 : BSD_FrobeniusDegreeNonneg_OPEN 991 := fun r => by
  have hap : (a_p 991 : ℝ) = 32 := by exact_mod_cast BSD_ap_p991
  have key : r ^ 2 - (a_p 991 : ℝ) * r + ((991 : ℕ) : ℝ) =
      (r - 16) ^ 2 + 735 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 16)]

theorem BSD_DegreeNonneg_p997 : BSD_FrobeniusDegreeNonneg_OPEN 997 := fun r => by
  have hap : (a_p 997 : ℝ) = -18 := by exact_mod_cast BSD_ap_p997
  have key : r ^ 2 - (a_p 997 : ℝ) * r + ((997 : ℕ) : ℝ) =
      (r + 9) ^ 2 + 916 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9)]

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

theorem BSD_DegreeNonneg_p1021 : BSD_FrobeniusDegreeNonneg_OPEN 1021 := fun r => by
  have hap : (a_p 1021 : ℝ) = 26 := by exact_mod_cast BSD_ap_p1021
  have key : r ^ 2 - (a_p 1021 : ℝ) * r + ((1021 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 3408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1031 : BSD_FrobeniusDegreeNonneg_OPEN 1031 := fun r => by
  have hap : (a_p 1031 : ℝ) = -42 := by exact_mod_cast BSD_ap_p1031
  have key : r ^ 2 - (a_p 1031 : ℝ) * r + ((1031 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 2360/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1033 : BSD_FrobeniusDegreeNonneg_OPEN 1033 := fun r => by
  have hap : (a_p 1033 : ℝ) = -24 := by exact_mod_cast BSD_ap_p1033
  have key : r ^ 2 - (a_p 1033 : ℝ) * r + ((1033 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 3556/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1039 : BSD_FrobeniusDegreeNonneg_OPEN 1039 := fun r => by
  have hap : (a_p 1039 : ℝ) = 49 := by exact_mod_cast BSD_ap_p1039
  have key : r ^ 2 - (a_p 1039 : ℝ) * r + ((1039 : ℕ) : ℝ) =
      (r - 49/2) ^ 2 + 1755/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (49 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1049 : BSD_FrobeniusDegreeNonneg_OPEN 1049 := fun r => by
  have hap : (a_p 1049 : ℝ) = 29 := by exact_mod_cast BSD_ap_p1049
  have key : r ^ 2 - (a_p 1049 : ℝ) * r + ((1049 : ℕ) : ℝ) =
      (r - 29/2) ^ 2 + 3355/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (29 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1051 : BSD_FrobeniusDegreeNonneg_OPEN 1051 := fun r => by
  have hap : (a_p 1051 : ℝ) = 50 := by exact_mod_cast BSD_ap_p1051
  have key : r ^ 2 - (a_p 1051 : ℝ) * r + ((1051 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 1704/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1061 : BSD_FrobeniusDegreeNonneg_OPEN 1061 := fun r => by
  have hap : (a_p 1061 : ℝ) = -15 := by exact_mod_cast BSD_ap_p1061
  have key : r ^ 2 - (a_p 1061 : ℝ) * r + ((1061 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 4019/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1091 : BSD_FrobeniusDegreeNonneg_OPEN 1091 := fun r => by
  have hap : (a_p 1091 : ℝ) = 12 := by exact_mod_cast BSD_ap_p1091
  have key : r ^ 2 - (a_p 1091 : ℝ) * r + ((1091 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 4220/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1093 : BSD_FrobeniusDegreeNonneg_OPEN 1093 := fun r => by
  have hap : (a_p 1093 : ℝ) = 29 := by exact_mod_cast BSD_ap_p1093
  have key : r ^ 2 - (a_p 1093 : ℝ) * r + ((1093 : ℕ) : ℝ) =
      (r - 29/2) ^ 2 + 3531/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (29 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1097 : BSD_FrobeniusDegreeNonneg_OPEN 1097 := fun r => by
  have hap : (a_p 1097 : ℝ) = -62 := by exact_mod_cast BSD_ap_p1097
  have key : r ^ 2 - (a_p 1097 : ℝ) * r + ((1097 : ℕ) : ℝ) =
      (r + 62/2) ^ 2 + 544/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (62 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1103 : BSD_FrobeniusDegreeNonneg_OPEN 1103 := fun r => by
  have hap : (a_p 1103 : ℝ) = 7 := by exact_mod_cast BSD_ap_p1103
  have key : r ^ 2 - (a_p 1103 : ℝ) * r + ((1103 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 4363/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1109 : BSD_FrobeniusDegreeNonneg_OPEN 1109 := fun r => by
  have hap : (a_p 1109 : ℝ) = 10 := by exact_mod_cast BSD_ap_p1109
  have key : r ^ 2 - (a_p 1109 : ℝ) * r + ((1109 : ℕ) : ℝ) =
      (r - 10/2) ^ 2 + 4336/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (10 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1117 : BSD_FrobeniusDegreeNonneg_OPEN 1117 := fun r => by
  have hap : (a_p 1117 : ℝ) = 12 := by exact_mod_cast BSD_ap_p1117
  have key : r ^ 2 - (a_p 1117 : ℝ) * r + ((1117 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 4324/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1123 : BSD_FrobeniusDegreeNonneg_OPEN 1123 := fun r => by
  have hap : (a_p 1123 : ℝ) = 40 := by exact_mod_cast BSD_ap_p1123
  have key : r ^ 2 - (a_p 1123 : ℝ) * r + ((1123 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 2892/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1163 : BSD_FrobeniusDegreeNonneg_OPEN 1163 := fun r => by
  have hap : (a_p 1163 : ℝ) = 36 := by exact_mod_cast BSD_ap_p1163
  have key : r ^ 2 - (a_p 1163 : ℝ) * r + ((1163 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 3356/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1171 : BSD_FrobeniusDegreeNonneg_OPEN 1171 := fun r => by
  have hap : (a_p 1171 : ℝ) = 61 := by exact_mod_cast BSD_ap_p1171
  have key : r ^ 2 - (a_p 1171 : ℝ) * r + ((1171 : ℕ) : ℝ) =
      (r - 61/2) ^ 2 + 963/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (61 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1181 : BSD_FrobeniusDegreeNonneg_OPEN 1181 := fun r => by
  have hap : (a_p 1181 : ℝ) = 42 := by exact_mod_cast BSD_ap_p1181
  have key : r ^ 2 - (a_p 1181 : ℝ) * r + ((1181 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 2960/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1187 : BSD_FrobeniusDegreeNonneg_OPEN 1187 := fun r => by
  have hap : (a_p 1187 : ℝ) = -24 := by exact_mod_cast BSD_ap_p1187
  have key : r ^ 2 - (a_p 1187 : ℝ) * r + ((1187 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 4172/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1193 : BSD_FrobeniusDegreeNonneg_OPEN 1193 := fun r => by
  have hap : (a_p 1193 : ℝ) = -9 := by exact_mod_cast BSD_ap_p1193
  have key : r ^ 2 - (a_p 1193 : ℝ) * r + ((1193 : ℕ) : ℝ) =
      (r + 9/2) ^ 2 + 4691/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (9 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1201 : BSD_FrobeniusDegreeNonneg_OPEN 1201 := fun r => by
  have hap : (a_p 1201 : ℝ) = 22 := by exact_mod_cast BSD_ap_p1201
  have key : r ^ 2 - (a_p 1201 : ℝ) * r + ((1201 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 4320/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1213 : BSD_FrobeniusDegreeNonneg_OPEN 1213 := fun r => by
  have hap : (a_p 1213 : ℝ) = -53 := by exact_mod_cast BSD_ap_p1213
  have key : r ^ 2 - (a_p 1213 : ℝ) * r + ((1213 : ℕ) : ℝ) =
      (r + 53/2) ^ 2 + 2043/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (53 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1231 : BSD_FrobeniusDegreeNonneg_OPEN 1231 := fun r => by
  have hap : (a_p 1231 : ℝ) = 18 := by exact_mod_cast BSD_ap_p1231
  have key : r ^ 2 - (a_p 1231 : ℝ) * r + ((1231 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 4600/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1237 : BSD_FrobeniusDegreeNonneg_OPEN 1237 := fun r => by
  have hap : (a_p 1237 : ℝ) = -50 := by exact_mod_cast BSD_ap_p1237
  have key : r ^ 2 - (a_p 1237 : ℝ) * r + ((1237 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 2448/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1249 : BSD_FrobeniusDegreeNonneg_OPEN 1249 := fun r => by
  have hap : (a_p 1249 : ℝ) = 2 := by exact_mod_cast BSD_ap_p1249
  have key : r ^ 2 - (a_p 1249 : ℝ) * r + ((1249 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 4992/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1259 : BSD_FrobeniusDegreeNonneg_OPEN 1259 := fun r => by
  have hap : (a_p 1259 : ℝ) = -39 := by exact_mod_cast BSD_ap_p1259
  have key : r ^ 2 - (a_p 1259 : ℝ) * r + ((1259 : ℕ) : ℝ) =
      (r + 39/2) ^ 2 + 3515/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (39 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1277 : BSD_FrobeniusDegreeNonneg_OPEN 1277 := fun r => by
  have hap : (a_p 1277 : ℝ) = 9 := by exact_mod_cast BSD_ap_p1277
  have key : r ^ 2 - (a_p 1277 : ℝ) * r + ((1277 : ℕ) : ℝ) =
      (r - 9/2) ^ 2 + 5027/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (9 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1279 : BSD_FrobeniusDegreeNonneg_OPEN 1279 := fun r => by
  have hap : (a_p 1279 : ℝ) = 35 := by exact_mod_cast BSD_ap_p1279
  have key : r ^ 2 - (a_p 1279 : ℝ) * r + ((1279 : ℕ) : ℝ) =
      (r - 35/2) ^ 2 + 3891/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (35 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1283 : BSD_FrobeniusDegreeNonneg_OPEN 1283 := fun r => by
  have hap : (a_p 1283 : ℝ) = 50 := by exact_mod_cast BSD_ap_p1283
  have key : r ^ 2 - (a_p 1283 : ℝ) * r + ((1283 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 2632/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1301 : BSD_FrobeniusDegreeNonneg_OPEN 1301 := fun r => by
  have hap : (a_p 1301 : ℝ) = -9 := by exact_mod_cast BSD_ap_p1301
  have key : r ^ 2 - (a_p 1301 : ℝ) * r + ((1301 : ℕ) : ℝ) =
      (r + 9/2) ^ 2 + 5123/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (9 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1303 : BSD_FrobeniusDegreeNonneg_OPEN 1303 := fun r => by
  have hap : (a_p 1303 : ℝ) = 11 := by exact_mod_cast BSD_ap_p1303
  have key : r ^ 2 - (a_p 1303 : ℝ) * r + ((1303 : ℕ) : ℝ) =
      (r - 11/2) ^ 2 + 5091/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (11 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1307 : BSD_FrobeniusDegreeNonneg_OPEN 1307 := fun r => by
  have hap : (a_p 1307 : ℝ) = 48 := by exact_mod_cast BSD_ap_p1307
  have key : r ^ 2 - (a_p 1307 : ℝ) * r + ((1307 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 2924/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1319 : BSD_FrobeniusDegreeNonneg_OPEN 1319 := fun r => by
  have hap : (a_p 1319 : ℝ) = -2 := by exact_mod_cast BSD_ap_p1319
  have key : r ^ 2 - (a_p 1319 : ℝ) * r + ((1319 : ℕ) : ℝ) =
      (r + 2/2) ^ 2 + 5272/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (2 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1321 : BSD_FrobeniusDegreeNonneg_OPEN 1321 := fun r => by
  have hap : (a_p 1321 : ℝ) = 41 := by exact_mod_cast BSD_ap_p1321
  have key : r ^ 2 - (a_p 1321 : ℝ) * r + ((1321 : ℕ) : ℝ) =
      (r - 41/2) ^ 2 + 3603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (41 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1327 : BSD_FrobeniusDegreeNonneg_OPEN 1327 := fun r => by
  have hap : (a_p 1327 : ℝ) = -4 := by exact_mod_cast BSD_ap_p1327
  have key : r ^ 2 - (a_p 1327 : ℝ) * r + ((1327 : ℕ) : ℝ) =
      (r + 4/2) ^ 2 + 5292/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (4 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1361 : BSD_FrobeniusDegreeNonneg_OPEN 1361 := fun r => by
  have hap : (a_p 1361 : ℝ) = 28 := by exact_mod_cast BSD_ap_p1361
  have key : r ^ 2 - (a_p 1361 : ℝ) * r + ((1361 : ℕ) : ℝ) =
      (r - 28/2) ^ 2 + 4660/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (28 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1399 : BSD_FrobeniusDegreeNonneg_OPEN 1399 := fun r => by
  have hap : (a_p 1399 : ℝ) = 10 := by exact_mod_cast BSD_ap_p1399
  have key : r ^ 2 - (a_p 1399 : ℝ) * r + ((1399 : ℕ) : ℝ) =
      (r - 10/2) ^ 2 + 5496/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (10 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1409 : BSD_FrobeniusDegreeNonneg_OPEN 1409 := fun r => by
  have hap : (a_p 1409 : ℝ) = -45 := by exact_mod_cast BSD_ap_p1409
  have key : r ^ 2 - (a_p 1409 : ℝ) * r + ((1409 : ℕ) : ℝ) =
      (r + 45/2) ^ 2 + 3611/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (45 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1423 : BSD_FrobeniusDegreeNonneg_OPEN 1423 := fun r => by
  have hap : (a_p 1423 : ℝ) = -29 := by exact_mod_cast BSD_ap_p1423
  have key : r ^ 2 - (a_p 1423 : ℝ) * r + ((1423 : ℕ) : ℝ) =
      (r + 29/2) ^ 2 + 4851/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (29 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1427 : BSD_FrobeniusDegreeNonneg_OPEN 1427 := fun r => by
  have hap : (a_p 1427 : ℝ) = -30 := by exact_mod_cast BSD_ap_p1427
  have key : r ^ 2 - (a_p 1427 : ℝ) * r + ((1427 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 4808/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1429 : BSD_FrobeniusDegreeNonneg_OPEN 1429 := fun r => by
  have hap : (a_p 1429 : ℝ) = -36 := by exact_mod_cast BSD_ap_p1429
  have key : r ^ 2 - (a_p 1429 : ℝ) * r + ((1429 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 4420/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1433 : BSD_FrobeniusDegreeNonneg_OPEN 1433 := fun r => by
  have hap : (a_p 1433 : ℝ) = -30 := by exact_mod_cast BSD_ap_p1433
  have key : r ^ 2 - (a_p 1433 : ℝ) * r + ((1433 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 4832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1439 : BSD_FrobeniusDegreeNonneg_OPEN 1439 := fun r => by
  have hap : (a_p 1439 : ℝ) = -60 := by exact_mod_cast BSD_ap_p1439
  have key : r ^ 2 - (a_p 1439 : ℝ) * r + ((1439 : ℕ) : ℝ) =
      (r + 60/2) ^ 2 + 2156/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (60 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1459 : BSD_FrobeniusDegreeNonneg_OPEN 1459 := fun r => by
  have hap : (a_p 1459 : ℝ) = 0 := by exact_mod_cast BSD_ap_p1459
  have key : r ^ 2 - (a_p 1459 : ℝ) * r + ((1459 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 5836/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1471 : BSD_FrobeniusDegreeNonneg_OPEN 1471 := fun r => by
  have hap : (a_p 1471 : ℝ) = -52 := by exact_mod_cast BSD_ap_p1471
  have key : r ^ 2 - (a_p 1471 : ℝ) * r + ((1471 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 3180/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1481 : BSD_FrobeniusDegreeNonneg_OPEN 1481 := fun r => by
  have hap : (a_p 1481 : ℝ) = 46 := by exact_mod_cast BSD_ap_p1481
  have key : r ^ 2 - (a_p 1481 : ℝ) * r + ((1481 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 3808/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1483 : BSD_FrobeniusDegreeNonneg_OPEN 1483 := fun r => by
  have hap : (a_p 1483 : ℝ) = -19 := by exact_mod_cast BSD_ap_p1483
  have key : r ^ 2 - (a_p 1483 : ℝ) * r + ((1483 : ℕ) : ℝ) =
      (r + 19/2) ^ 2 + 5571/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (19 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1487 : BSD_FrobeniusDegreeNonneg_OPEN 1487 := fun r => by
  have hap : (a_p 1487 : ℝ) = 60 := by exact_mod_cast BSD_ap_p1487
  have key : r ^ 2 - (a_p 1487 : ℝ) * r + ((1487 : ℕ) : ℝ) =
      (r - 60/2) ^ 2 + 2348/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (60 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1489 : BSD_FrobeniusDegreeNonneg_OPEN 1489 := fun r => by
  have hap : (a_p 1489 : ℝ) = -9 := by exact_mod_cast BSD_ap_p1489
  have key : r ^ 2 - (a_p 1489 : ℝ) * r + ((1489 : ℕ) : ℝ) =
      (r + 9/2) ^ 2 + 5875/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (9 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1493 : BSD_FrobeniusDegreeNonneg_OPEN 1493 := fun r => by
  have hap : (a_p 1493 : ℝ) = -44 := by exact_mod_cast BSD_ap_p1493
  have key : r ^ 2 - (a_p 1493 : ℝ) * r + ((1493 : ℕ) : ℝ) =
      (r + 44/2) ^ 2 + 4036/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (44 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1531 : BSD_FrobeniusDegreeNonneg_OPEN 1531 := fun r => by
  have hap : (a_p 1531 : ℝ) = -22 := by exact_mod_cast BSD_ap_p1531
  have key : r ^ 2 - (a_p 1531 : ℝ) * r + ((1531 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 5640/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1543 : BSD_FrobeniusDegreeNonneg_OPEN 1543 := fun r => by
  have hap : (a_p 1543 : ℝ) = 56 := by exact_mod_cast BSD_ap_p1543
  have key : r ^ 2 - (a_p 1543 : ℝ) * r + ((1543 : ℕ) : ℝ) =
      (r - 56/2) ^ 2 + 3036/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (56 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1549 : BSD_FrobeniusDegreeNonneg_OPEN 1549 := fun r => by
  have hap : (a_p 1549 : ℝ) = -45 := by exact_mod_cast BSD_ap_p1549
  have key : r ^ 2 - (a_p 1549 : ℝ) * r + ((1549 : ℕ) : ℝ) =
      (r + 45/2) ^ 2 + 4171/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (45 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1553 : BSD_FrobeniusDegreeNonneg_OPEN 1553 := fun r => by
  have hap : (a_p 1553 : ℝ) = 2 := by exact_mod_cast BSD_ap_p1553
  have key : r ^ 2 - (a_p 1553 : ℝ) * r + ((1553 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 6208/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1559 : BSD_FrobeniusDegreeNonneg_OPEN 1559 := fun r => by
  have hap : (a_p 1559 : ℝ) = 10 := by exact_mod_cast BSD_ap_p1559
  have key : r ^ 2 - (a_p 1559 : ℝ) * r + ((1559 : ℕ) : ℝ) =
      (r - 10/2) ^ 2 + 6136/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (10 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1567 : BSD_FrobeniusDegreeNonneg_OPEN 1567 := fun r => by
  have hap : (a_p 1567 : ℝ) = 8 := by exact_mod_cast BSD_ap_p1567
  have key : r ^ 2 - (a_p 1567 : ℝ) * r + ((1567 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 6204/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1571 : BSD_FrobeniusDegreeNonneg_OPEN 1571 := fun r => by
  have hap : (a_p 1571 : ℝ) = 0 := by exact_mod_cast BSD_ap_p1571
  have key : r ^ 2 - (a_p 1571 : ℝ) * r + ((1571 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 6284/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1601 : BSD_FrobeniusDegreeNonneg_OPEN 1601 := fun r => by
  have hap : (a_p 1601 : ℝ) = 46 := by exact_mod_cast BSD_ap_p1601
  have key : r ^ 2 - (a_p 1601 : ℝ) * r + ((1601 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 4288/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1607 : BSD_FrobeniusDegreeNonneg_OPEN 1607 := fun r => by
  have hap : (a_p 1607 : ℝ) = -41 := by exact_mod_cast BSD_ap_p1607
  have key : r ^ 2 - (a_p 1607 : ℝ) * r + ((1607 : ℕ) : ℝ) =
      (r + 41/2) ^ 2 + 4747/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (41 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1609 : BSD_FrobeniusDegreeNonneg_OPEN 1609 := fun r => by
  have hap : (a_p 1609 : ℝ) = -2 := by exact_mod_cast BSD_ap_p1609
  have key : r ^ 2 - (a_p 1609 : ℝ) * r + ((1609 : ℕ) : ℝ) =
      (r + 2/2) ^ 2 + 6432/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (2 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1613 : BSD_FrobeniusDegreeNonneg_OPEN 1613 := fun r => by
  have hap : (a_p 1613 : ℝ) = -20 := by exact_mod_cast BSD_ap_p1613
  have key : r ^ 2 - (a_p 1613 : ℝ) * r + ((1613 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 6052/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1619 : BSD_FrobeniusDegreeNonneg_OPEN 1619 := fun r => by
  have hap : (a_p 1619 : ℝ) = -40 := by exact_mod_cast BSD_ap_p1619
  have key : r ^ 2 - (a_p 1619 : ℝ) * r + ((1619 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 4876/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1621 : BSD_FrobeniusDegreeNonneg_OPEN 1621 := fun r => by
  have hap : (a_p 1621 : ℝ) = -10 := by exact_mod_cast BSD_ap_p1621
  have key : r ^ 2 - (a_p 1621 : ℝ) * r + ((1621 : ℕ) : ℝ) =
      (r + 10/2) ^ 2 + 6384/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (10 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1627 : BSD_FrobeniusDegreeNonneg_OPEN 1627 := fun r => by
  have hap : (a_p 1627 : ℝ) = -8 := by exact_mod_cast BSD_ap_p1627
  have key : r ^ 2 - (a_p 1627 : ℝ) * r + ((1627 : ℕ) : ℝ) =
      (r + 8/2) ^ 2 + 6444/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (8 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1667 : BSD_FrobeniusDegreeNonneg_OPEN 1667 := fun r => by
  have hap : (a_p 1667 : ℝ) = 34 := by exact_mod_cast BSD_ap_p1667
  have key : r ^ 2 - (a_p 1667 : ℝ) * r + ((1667 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 5512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1669 : BSD_FrobeniusDegreeNonneg_OPEN 1669 := fun r => by
  have hap : (a_p 1669 : ℝ) = -46 := by exact_mod_cast BSD_ap_p1669
  have key : r ^ 2 - (a_p 1669 : ℝ) * r + ((1669 : ℕ) : ℝ) =
      (r + 46/2) ^ 2 + 4560/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1693 : BSD_FrobeniusDegreeNonneg_OPEN 1693 := fun r => by
  have hap : (a_p 1693 : ℝ) = -56 := by exact_mod_cast BSD_ap_p1693
  have key : r ^ 2 - (a_p 1693 : ℝ) * r + ((1693 : ℕ) : ℝ) =
      (r + 56/2) ^ 2 + 3636/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (56 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1697 : BSD_FrobeniusDegreeNonneg_OPEN 1697 := fun r => by
  have hap : (a_p 1697 : ℝ) = 66 := by exact_mod_cast BSD_ap_p1697
  have key : r ^ 2 - (a_p 1697 : ℝ) * r + ((1697 : ℕ) : ℝ) =
      (r - 66/2) ^ 2 + 2432/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (66 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1699 : BSD_FrobeniusDegreeNonneg_OPEN 1699 := fun r => by
  have hap : (a_p 1699 : ℝ) = 12 := by exact_mod_cast BSD_ap_p1699
  have key : r ^ 2 - (a_p 1699 : ℝ) * r + ((1699 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 6652/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1709 : BSD_FrobeniusDegreeNonneg_OPEN 1709 := fun r => by
  have hap : (a_p 1709 : ℝ) = 45 := by exact_mod_cast BSD_ap_p1709
  have key : r ^ 2 - (a_p 1709 : ℝ) * r + ((1709 : ℕ) : ℝ) =
      (r - 45/2) ^ 2 + 4811/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (45 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1721 : BSD_FrobeniusDegreeNonneg_OPEN 1721 := fun r => by
  have hap : (a_p 1721 : ℝ) = 39 := by exact_mod_cast BSD_ap_p1721
  have key : r ^ 2 - (a_p 1721 : ℝ) * r + ((1721 : ℕ) : ℝ) =
      (r - 39/2) ^ 2 + 5363/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (39 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1747 : BSD_FrobeniusDegreeNonneg_OPEN 1747 := fun r => by
  have hap : (a_p 1747 : ℝ) = -55 := by exact_mod_cast BSD_ap_p1747
  have key : r ^ 2 - (a_p 1747 : ℝ) * r + ((1747 : ℕ) : ℝ) =
      (r + 55/2) ^ 2 + 3963/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (55 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1753 : BSD_FrobeniusDegreeNonneg_OPEN 1753 := fun r => by
  have hap : (a_p 1753 : ℝ) = -50 := by exact_mod_cast BSD_ap_p1753
  have key : r ^ 2 - (a_p 1753 : ℝ) * r + ((1753 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 4512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1759 : BSD_FrobeniusDegreeNonneg_OPEN 1759 := fun r => by
  have hap : (a_p 1759 : ℝ) = 2 := by exact_mod_cast BSD_ap_p1759
  have key : r ^ 2 - (a_p 1759 : ℝ) * r + ((1759 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 7032/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1777 : BSD_FrobeniusDegreeNonneg_OPEN 1777 := fun r => by
  have hap : (a_p 1777 : ℝ) = 4 := by exact_mod_cast BSD_ap_p1777
  have key : r ^ 2 - (a_p 1777 : ℝ) * r + ((1777 : ℕ) : ℝ) =
      (r - 4/2) ^ 2 + 7092/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (4 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1783 : BSD_FrobeniusDegreeNonneg_OPEN 1783 := fun r => by
  have hap : (a_p 1783 : ℝ) = 25 := by exact_mod_cast BSD_ap_p1783
  have key : r ^ 2 - (a_p 1783 : ℝ) * r + ((1783 : ℕ) : ℝ) =
      (r - 25/2) ^ 2 + 6507/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (25 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1787 : BSD_FrobeniusDegreeNonneg_OPEN 1787 := fun r => by
  have hap : (a_p 1787 : ℝ) = -27 := by exact_mod_cast BSD_ap_p1787
  have key : r ^ 2 - (a_p 1787 : ℝ) * r + ((1787 : ℕ) : ℝ) =
      (r + 27/2) ^ 2 + 6419/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (27 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1789 : BSD_FrobeniusDegreeNonneg_OPEN 1789 := fun r => by
  have hap : (a_p 1789 : ℝ) = 18 := by exact_mod_cast BSD_ap_p1789
  have key : r ^ 2 - (a_p 1789 : ℝ) * r + ((1789 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 6832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1831 : BSD_FrobeniusDegreeNonneg_OPEN 1831 := fun r => by
  have hap : (a_p 1831 : ℝ) = 47 := by exact_mod_cast BSD_ap_p1831
  have key : r ^ 2 - (a_p 1831 : ℝ) * r + ((1831 : ℕ) : ℝ) =
      (r - 47/2) ^ 2 + 5115/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (47 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1847 : BSD_FrobeniusDegreeNonneg_OPEN 1847 := fun r => by
  have hap : (a_p 1847 : ℝ) = -62 := by exact_mod_cast BSD_ap_p1847
  have key : r ^ 2 - (a_p 1847 : ℝ) * r + ((1847 : ℕ) : ℝ) =
      (r + 62/2) ^ 2 + 3544/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (62 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1861 : BSD_FrobeniusDegreeNonneg_OPEN 1861 := fun r => by
  have hap : (a_p 1861 : ℝ) = -20 := by exact_mod_cast BSD_ap_p1861
  have key : r ^ 2 - (a_p 1861 : ℝ) * r + ((1861 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 7044/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1867 : BSD_FrobeniusDegreeNonneg_OPEN 1867 := fun r => by
  have hap : (a_p 1867 : ℝ) = -22 := by exact_mod_cast BSD_ap_p1867
  have key : r ^ 2 - (a_p 1867 : ℝ) * r + ((1867 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 6984/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1871 : BSD_FrobeniusDegreeNonneg_OPEN 1871 := fun r => by
  have hap : (a_p 1871 : ℝ) = 21 := by exact_mod_cast BSD_ap_p1871
  have key : r ^ 2 - (a_p 1871 : ℝ) * r + ((1871 : ℕ) : ℝ) =
      (r - 21/2) ^ 2 + 7043/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (21 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1873 : BSD_FrobeniusDegreeNonneg_OPEN 1873 := fun r => by
  have hap : (a_p 1873 : ℝ) = -54 := by exact_mod_cast BSD_ap_p1873
  have key : r ^ 2 - (a_p 1873 : ℝ) * r + ((1873 : ℕ) : ℝ) =
      (r + 54/2) ^ 2 + 4576/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1877 : BSD_FrobeniusDegreeNonneg_OPEN 1877 := fun r => by
  have hap : (a_p 1877 : ℝ) = -76 := by exact_mod_cast BSD_ap_p1877
  have key : r ^ 2 - (a_p 1877 : ℝ) * r + ((1877 : ℕ) : ℝ) =
      (r + 76/2) ^ 2 + 1732/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (76 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1907 : BSD_FrobeniusDegreeNonneg_OPEN 1907 := fun r => by
  have hap : (a_p 1907 : ℝ) = -20 := by exact_mod_cast BSD_ap_p1907
  have key : r ^ 2 - (a_p 1907 : ℝ) * r + ((1907 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 7228/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1913 : BSD_FrobeniusDegreeNonneg_OPEN 1913 := fun r => by
  have hap : (a_p 1913 : ℝ) = 58 := by exact_mod_cast BSD_ap_p1913
  have key : r ^ 2 - (a_p 1913 : ℝ) * r + ((1913 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 4288/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1931 : BSD_FrobeniusDegreeNonneg_OPEN 1931 := fun r => by
  have hap : (a_p 1931 : ℝ) = -22 := by exact_mod_cast BSD_ap_p1931
  have key : r ^ 2 - (a_p 1931 : ℝ) * r + ((1931 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 7240/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1933 : BSD_FrobeniusDegreeNonneg_OPEN 1933 := fun r => by
  have hap : (a_p 1933 : ℝ) = 4 := by exact_mod_cast BSD_ap_p1933
  have key : r ^ 2 - (a_p 1933 : ℝ) * r + ((1933 : ℕ) : ℝ) =
      (r - 4/2) ^ 2 + 7716/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (4 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1949 : BSD_FrobeniusDegreeNonneg_OPEN 1949 := fun r => by
  have hap : (a_p 1949 : ℝ) = -22 := by exact_mod_cast BSD_ap_p1949
  have key : r ^ 2 - (a_p 1949 : ℝ) * r + ((1949 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 7312/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1951 : BSD_FrobeniusDegreeNonneg_OPEN 1951 := fun r => by
  have hap : (a_p 1951 : ℝ) = -63 := by exact_mod_cast BSD_ap_p1951
  have key : r ^ 2 - (a_p 1951 : ℝ) * r + ((1951 : ℕ) : ℝ) =
      (r + 63/2) ^ 2 + 3835/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (63 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1973 : BSD_FrobeniusDegreeNonneg_OPEN 1973 := fun r => by
  have hap : (a_p 1973 : ℝ) = -1 := by exact_mod_cast BSD_ap_p1973
  have key : r ^ 2 - (a_p 1973 : ℝ) * r + ((1973 : ℕ) : ℝ) =
      (r + 1/2) ^ 2 + 7891/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (1 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p1997 : BSD_FrobeniusDegreeNonneg_OPEN 1997 := fun r => by
  have hap : (a_p 1997 : ℝ) = 36 := by exact_mod_cast BSD_ap_p1997
  have key : r ^ 2 - (a_p 1997 : ℝ) * r + ((1997 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 6692/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p1999 : BSD_FrobeniusDegreeNonneg_OPEN 1999 := fun r => by
  have hap : (a_p 1999 : ℝ) = -22 := by exact_mod_cast BSD_ap_p1999
  have key : r ^ 2 - (a_p 1999 : ℝ) * r + ((1999 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 7512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2003 : BSD_FrobeniusDegreeNonneg_OPEN 2003 := fun r => by
  have hap : (a_p 2003 : ℝ) = 4 := by exact_mod_cast BSD_ap_p2003
  have key : r ^ 2 - (a_p 2003 : ℝ) * r + ((2003 : ℕ) : ℝ) =
      (r - 4/2) ^ 2 + 7996/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (4 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2011 : BSD_FrobeniusDegreeNonneg_OPEN 2011 := fun r => by
  have hap : (a_p 2011 : ℝ) = -5 := by exact_mod_cast BSD_ap_p2011
  have key : r ^ 2 - (a_p 2011 : ℝ) * r + ((2011 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 8019/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2017 : BSD_FrobeniusDegreeNonneg_OPEN 2017 := fun r => by
  have hap : (a_p 2017 : ℝ) = -15 := by exact_mod_cast BSD_ap_p2017
  have key : r ^ 2 - (a_p 2017 : ℝ) * r + ((2017 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 7843/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2027 : BSD_FrobeniusDegreeNonneg_OPEN 2027 := fun r => by
  have hap : (a_p 2027 : ℝ) = 67 := by exact_mod_cast BSD_ap_p2027
  have key : r ^ 2 - (a_p 2027 : ℝ) * r + ((2027 : ℕ) : ℝ) =
      (r - 67/2) ^ 2 + 3619/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (67 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2029 : BSD_FrobeniusDegreeNonneg_OPEN 2029 := fun r => by
  have hap : (a_p 2029 : ℝ) = -55 := by exact_mod_cast BSD_ap_p2029
  have key : r ^ 2 - (a_p 2029 : ℝ) * r + ((2029 : ℕ) : ℝ) =
      (r + 55/2) ^ 2 + 5091/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (55 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p2069 : BSD_FrobeniusDegreeNonneg_OPEN 2069 := fun r => by
  have hap : (a_p 2069 : ℝ) = -86 := by exact_mod_cast BSD_ap_p2069
  have key : r ^ 2 - (a_p 2069 : ℝ) * r + ((2069 : ℕ) : ℝ) =
      (r + 86/2) ^ 2 + 880/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (86 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2081 : BSD_FrobeniusDegreeNonneg_OPEN 2081 := fun r => by
  have hap : (a_p 2081 : ℝ) = 30 := by exact_mod_cast BSD_ap_p2081
  have key : r ^ 2 - (a_p 2081 : ℝ) * r + ((2081 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 7424/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2083 : BSD_FrobeniusDegreeNonneg_OPEN 2083 := fun r => by
  have hap : (a_p 2083 : ℝ) = -63 := by exact_mod_cast BSD_ap_p2083
  have key : r ^ 2 - (a_p 2083 : ℝ) * r + ((2083 : ℕ) : ℝ) =
      (r + 63/2) ^ 2 + 4363/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (63 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2087 : BSD_FrobeniusDegreeNonneg_OPEN 2087 := fun r => by
  have hap : (a_p 2087 : ℝ) = 68 := by exact_mod_cast BSD_ap_p2087
  have key : r ^ 2 - (a_p 2087 : ℝ) * r + ((2087 : ℕ) : ℝ) =
      (r - 68/2) ^ 2 + 3724/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (68 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2089 : BSD_FrobeniusDegreeNonneg_OPEN 2089 := fun r => by
  have hap : (a_p 2089 : ℝ) = 34 := by exact_mod_cast BSD_ap_p2089
  have key : r ^ 2 - (a_p 2089 : ℝ) * r + ((2089 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 7200/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2099 : BSD_FrobeniusDegreeNonneg_OPEN 2099 := fun r => by
  have hap : (a_p 2099 : ℝ) = -19 := by exact_mod_cast BSD_ap_p2099
  have key : r ^ 2 - (a_p 2099 : ℝ) * r + ((2099 : ℕ) : ℝ) =
      (r + 19/2) ^ 2 + 8035/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (19 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2111 : BSD_FrobeniusDegreeNonneg_OPEN 2111 := fun r => by
  have hap : (a_p 2111 : ℝ) = -24 := by exact_mod_cast BSD_ap_p2111
  have key : r ^ 2 - (a_p 2111 : ℝ) * r + ((2111 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 7868/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2113 : BSD_FrobeniusDegreeNonneg_OPEN 2113 := fun r => by
  have hap : (a_p 2113 : ℝ) = 46 := by exact_mod_cast BSD_ap_p2113
  have key : r ^ 2 - (a_p 2113 : ℝ) * r + ((2113 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 6336/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2129 : BSD_FrobeniusDegreeNonneg_OPEN 2129 := fun r => by
  have hap : (a_p 2129 : ℝ) = -66 := by exact_mod_cast BSD_ap_p2129
  have key : r ^ 2 - (a_p 2129 : ℝ) * r + ((2129 : ℕ) : ℝ) =
      (r + 66/2) ^ 2 + 4160/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (66 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2131 : BSD_FrobeniusDegreeNonneg_OPEN 2131 := fun r => by
  have hap : (a_p 2131 : ℝ) = 26 := by exact_mod_cast BSD_ap_p2131
  have key : r ^ 2 - (a_p 2131 : ℝ) * r + ((2131 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 7848/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2137 : BSD_FrobeniusDegreeNonneg_OPEN 2137 := fun r => by
  have hap : (a_p 2137 : ℝ) = -37 := by exact_mod_cast BSD_ap_p2137
  have key : r ^ 2 - (a_p 2137 : ℝ) * r + ((2137 : ℕ) : ℝ) =
      (r + 37/2) ^ 2 + 7179/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (37 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2141 : BSD_FrobeniusDegreeNonneg_OPEN 2141 := fun r => by
  have hap : (a_p 2141 : ℝ) = 30 := by exact_mod_cast BSD_ap_p2141
  have key : r ^ 2 - (a_p 2141 : ℝ) * r + ((2141 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 7664/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2143 : BSD_FrobeniusDegreeNonneg_OPEN 2143 := fun r => by
  have hap : (a_p 2143 : ℝ) = -29 := by exact_mod_cast BSD_ap_p2143
  have key : r ^ 2 - (a_p 2143 : ℝ) * r + ((2143 : ℕ) : ℝ) =
      (r + 29/2) ^ 2 + 7731/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (29 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2153 : BSD_FrobeniusDegreeNonneg_OPEN 2153 := fun r => by
  have hap : (a_p 2153 : ℝ) = 46 := by exact_mod_cast BSD_ap_p2153
  have key : r ^ 2 - (a_p 2153 : ℝ) * r + ((2153 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 6496/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2161 : BSD_FrobeniusDegreeNonneg_OPEN 2161 := fun r => by
  have hap : (a_p 2161 : ℝ) = 67 := by exact_mod_cast BSD_ap_p2161
  have key : r ^ 2 - (a_p 2161 : ℝ) * r + ((2161 : ℕ) : ℝ) =
      (r - 67/2) ^ 2 + 4155/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (67 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2179 : BSD_FrobeniusDegreeNonneg_OPEN 2179 := fun r => by
  have hap : (a_p 2179 : ℝ) = 25 := by exact_mod_cast BSD_ap_p2179
  have key : r ^ 2 - (a_p 2179 : ℝ) * r + ((2179 : ℕ) : ℝ) =
      (r - 25/2) ^ 2 + 8091/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (25 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2203 : BSD_FrobeniusDegreeNonneg_OPEN 2203 := fun r => by
  have hap : (a_p 2203 : ℝ) = -71 := by exact_mod_cast BSD_ap_p2203
  have key : r ^ 2 - (a_p 2203 : ℝ) * r + ((2203 : ℕ) : ℝ) =
      (r + 71/2) ^ 2 + 3771/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (71 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2207 : BSD_FrobeniusDegreeNonneg_OPEN 2207 := fun r => by
  have hap : (a_p 2207 : ℝ) = 78 := by exact_mod_cast BSD_ap_p2207
  have key : r ^ 2 - (a_p 2207 : ℝ) * r + ((2207 : ℕ) : ℝ) =
      (r - 78/2) ^ 2 + 2744/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (78 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2213 : BSD_FrobeniusDegreeNonneg_OPEN 2213 := fun r => by
  have hap : (a_p 2213 : ℝ) = 52 := by exact_mod_cast BSD_ap_p2213
  have key : r ^ 2 - (a_p 2213 : ℝ) * r + ((2213 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 6148/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2221 : BSD_FrobeniusDegreeNonneg_OPEN 2221 := fun r => by
  have hap : (a_p 2221 : ℝ) = 62 := by exact_mod_cast BSD_ap_p2221
  have key : r ^ 2 - (a_p 2221 : ℝ) * r + ((2221 : ℕ) : ℝ) =
      (r - 62/2) ^ 2 + 5040/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (62 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2237 : BSD_FrobeniusDegreeNonneg_OPEN 2237 := fun r => by
  have hap : (a_p 2237 : ℝ) = -42 := by exact_mod_cast BSD_ap_p2237
  have key : r ^ 2 - (a_p 2237 : ℝ) * r + ((2237 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 7184/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2239 : BSD_FrobeniusDegreeNonneg_OPEN 2239 := fun r => by
  have hap : (a_p 2239 : ℝ) = -50 := by exact_mod_cast BSD_ap_p2239
  have key : r ^ 2 - (a_p 2239 : ℝ) * r + ((2239 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 6456/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2243 : BSD_FrobeniusDegreeNonneg_OPEN 2243 := fun r => by
  have hap : (a_p 2243 : ℝ) = -36 := by exact_mod_cast BSD_ap_p2243
  have key : r ^ 2 - (a_p 2243 : ℝ) * r + ((2243 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 7676/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2251 : BSD_FrobeniusDegreeNonneg_OPEN 2251 := fun r => by
  have hap : (a_p 2251 : ℝ) = 8 := by exact_mod_cast BSD_ap_p2251
  have key : r ^ 2 - (a_p 2251 : ℝ) * r + ((2251 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 8940/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2267 : BSD_FrobeniusDegreeNonneg_OPEN 2267 := fun r => by
  have hap : (a_p 2267 : ℝ) = 11 := by exact_mod_cast BSD_ap_p2267
  have key : r ^ 2 - (a_p 2267 : ℝ) * r + ((2267 : ℕ) : ℝ) =
      (r - 11/2) ^ 2 + 8947/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (11 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2269 : BSD_FrobeniusDegreeNonneg_OPEN 2269 := fun r => by
  have hap : (a_p 2269 : ℝ) = -1 := by exact_mod_cast BSD_ap_p2269
  have key : r ^ 2 - (a_p 2269 : ℝ) * r + ((2269 : ℕ) : ℝ) =
      (r + 1/2) ^ 2 + 9075/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (1 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2273 : BSD_FrobeniusDegreeNonneg_OPEN 2273 := fun r => by
  have hap : (a_p 2273 : ℝ) = -46 := by exact_mod_cast BSD_ap_p2273
  have key : r ^ 2 - (a_p 2273 : ℝ) * r + ((2273 : ℕ) : ℝ) =
      (r + 46/2) ^ 2 + 6976/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2281 : BSD_FrobeniusDegreeNonneg_OPEN 2281 := fun r => by
  have hap : (a_p 2281 : ℝ) = 1 := by exact_mod_cast BSD_ap_p2281
  have key : r ^ 2 - (a_p 2281 : ℝ) * r + ((2281 : ℕ) : ℝ) =
      (r - 1/2) ^ 2 + 9123/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (1 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2287 : BSD_FrobeniusDegreeNonneg_OPEN 2287 := fun r => by
  have hap : (a_p 2287 : ℝ) = -14 := by exact_mod_cast BSD_ap_p2287
  have key : r ^ 2 - (a_p 2287 : ℝ) * r + ((2287 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 8952/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2293 : BSD_FrobeniusDegreeNonneg_OPEN 2293 := fun r => by
  have hap : (a_p 2293 : ℝ) = -29 := by exact_mod_cast BSD_ap_p2293
  have key : r ^ 2 - (a_p 2293 : ℝ) * r + ((2293 : ℕ) : ℝ) =
      (r + 29/2) ^ 2 + 8331/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (29 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2297 : BSD_FrobeniusDegreeNonneg_OPEN 2297 := fun r => by
  have hap : (a_p 2297 : ℝ) = -37 := by exact_mod_cast BSD_ap_p2297
  have key : r ^ 2 - (a_p 2297 : ℝ) * r + ((2297 : ℕ) : ℝ) =
      (r + 37/2) ^ 2 + 7819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (37 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2309 : BSD_FrobeniusDegreeNonneg_OPEN 2309 := fun r => by
  have hap : (a_p 2309 : ℝ) = -86 := by exact_mod_cast BSD_ap_p2309
  have key : r ^ 2 - (a_p 2309 : ℝ) * r + ((2309 : ℕ) : ℝ) =
      (r + 86/2) ^ 2 + 1840/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (86 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2311 : BSD_FrobeniusDegreeNonneg_OPEN 2311 := fun r => by
  have hap : (a_p 2311 : ℝ) = 23 := by exact_mod_cast BSD_ap_p2311
  have key : r ^ 2 - (a_p 2311 : ℝ) * r + ((2311 : ℕ) : ℝ) =
      (r - 23/2) ^ 2 + 8715/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (23 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2333 : BSD_FrobeniusDegreeNonneg_OPEN 2333 := fun r => by
  have hap : (a_p 2333 : ℝ) = 53 := by exact_mod_cast BSD_ap_p2333
  have key : r ^ 2 - (a_p 2333 : ℝ) * r + ((2333 : ℕ) : ℝ) =
      (r - 53/2) ^ 2 + 6523/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (53 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2339 : BSD_FrobeniusDegreeNonneg_OPEN 2339 := fun r => by
  have hap : (a_p 2339 : ℝ) = -70 := by exact_mod_cast BSD_ap_p2339
  have key : r ^ 2 - (a_p 2339 : ℝ) * r + ((2339 : ℕ) : ℝ) =
      (r + 70/2) ^ 2 + 4456/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (70 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2341 : BSD_FrobeniusDegreeNonneg_OPEN 2341 := fun r => by
  have hap : (a_p 2341 : ℝ) = 63 := by exact_mod_cast BSD_ap_p2341
  have key : r ^ 2 - (a_p 2341 : ℝ) * r + ((2341 : ℕ) : ℝ) =
      (r - 63/2) ^ 2 + 5395/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (63 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2347 : BSD_FrobeniusDegreeNonneg_OPEN 2347 := fun r => by
  have hap : (a_p 2347 : ℝ) = -7 := by exact_mod_cast BSD_ap_p2347
  have key : r ^ 2 - (a_p 2347 : ℝ) * r + ((2347 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 9339/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2351 : BSD_FrobeniusDegreeNonneg_OPEN 2351 := fun r => by
  have hap : (a_p 2351 : ℝ) = 54 := by exact_mod_cast BSD_ap_p2351
  have key : r ^ 2 - (a_p 2351 : ℝ) * r + ((2351 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 6488/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2357 : BSD_FrobeniusDegreeNonneg_OPEN 2357 := fun r => by
  have hap : (a_p 2357 : ℝ) = 67 := by exact_mod_cast BSD_ap_p2357
  have key : r ^ 2 - (a_p 2357 : ℝ) * r + ((2357 : ℕ) : ℝ) =
      (r - 67/2) ^ 2 + 4939/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (67 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2371 : BSD_FrobeniusDegreeNonneg_OPEN 2371 := fun r => by
  have hap : (a_p 2371 : ℝ) = 30 := by exact_mod_cast BSD_ap_p2371
  have key : r ^ 2 - (a_p 2371 : ℝ) * r + ((2371 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 8584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2377 : BSD_FrobeniusDegreeNonneg_OPEN 2377 := fun r => by
  have hap : (a_p 2377 : ℝ) = -31 := by exact_mod_cast BSD_ap_p2377
  have key : r ^ 2 - (a_p 2377 : ℝ) * r + ((2377 : ℕ) : ℝ) =
      (r + 31/2) ^ 2 + 8547/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (31 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2381 : BSD_FrobeniusDegreeNonneg_OPEN 2381 := fun r => by
  have hap : (a_p 2381 : ℝ) = -42 := by exact_mod_cast BSD_ap_p2381
  have key : r ^ 2 - (a_p 2381 : ℝ) * r + ((2381 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 7760/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2383 : BSD_FrobeniusDegreeNonneg_OPEN 2383 := fun r => by
  have hap : (a_p 2383 : ℝ) = -8 := by exact_mod_cast BSD_ap_p2383
  have key : r ^ 2 - (a_p 2383 : ℝ) * r + ((2383 : ℕ) : ℝ) =
      (r + 8/2) ^ 2 + 9468/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (8 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2389 : BSD_FrobeniusDegreeNonneg_OPEN 2389 := fun r => by
  have hap : (a_p 2389 : ℝ) = 24 := by exact_mod_cast BSD_ap_p2389
  have key : r ^ 2 - (a_p 2389 : ℝ) * r + ((2389 : ℕ) : ℝ) =
      (r - 24/2) ^ 2 + 8980/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2393 : BSD_FrobeniusDegreeNonneg_OPEN 2393 := fun r => by
  have hap : (a_p 2393 : ℝ) = -52 := by exact_mod_cast BSD_ap_p2393
  have key : r ^ 2 - (a_p 2393 : ℝ) * r + ((2393 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 6868/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2399 : BSD_FrobeniusDegreeNonneg_OPEN 2399 := fun r => by
  have hap : (a_p 2399 : ℝ) = -73 := by exact_mod_cast BSD_ap_p2399
  have key : r ^ 2 - (a_p 2399 : ℝ) * r + ((2399 : ℕ) : ℝ) =
      (r + 73/2) ^ 2 + 4267/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (73 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2411 : BSD_FrobeniusDegreeNonneg_OPEN 2411 := fun r => by
  have hap : (a_p 2411 : ℝ) = 12 := by exact_mod_cast BSD_ap_p2411
  have key : r ^ 2 - (a_p 2411 : ℝ) * r + ((2411 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 9500/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2417 : BSD_FrobeniusDegreeNonneg_OPEN 2417 := fun r => by
  have hap : (a_p 2417 : ℝ) = -24 := by exact_mod_cast BSD_ap_p2417
  have key : r ^ 2 - (a_p 2417 : ℝ) * r + ((2417 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 9092/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2423 : BSD_FrobeniusDegreeNonneg_OPEN 2423 := fun r => by
  have hap : (a_p 2423 : ℝ) = 75 := by exact_mod_cast BSD_ap_p2423
  have key : r ^ 2 - (a_p 2423 : ℝ) * r + ((2423 : ℕ) : ℝ) =
      (r - 75/2) ^ 2 + 4067/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (75 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2437 : BSD_FrobeniusDegreeNonneg_OPEN 2437 := fun r => by
  have hap : (a_p 2437 : ℝ) = 40 := by exact_mod_cast BSD_ap_p2437
  have key : r ^ 2 - (a_p 2437 : ℝ) * r + ((2437 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 8148/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2441 : BSD_FrobeniusDegreeNonneg_OPEN 2441 := fun r => by
  have hap : (a_p 2441 : ℝ) = 18 := by exact_mod_cast BSD_ap_p2441
  have key : r ^ 2 - (a_p 2441 : ℝ) * r + ((2441 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 9440/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2447 : BSD_FrobeniusDegreeNonneg_OPEN 2447 := fun r => by
  have hap : (a_p 2447 : ℝ) = 27 := by exact_mod_cast BSD_ap_p2447
  have key : r ^ 2 - (a_p 2447 : ℝ) * r + ((2447 : ℕ) : ℝ) =
      (r - 27/2) ^ 2 + 9059/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (27 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2459 : BSD_FrobeniusDegreeNonneg_OPEN 2459 := fun r => by
  have hap : (a_p 2459 : ℝ) = 92 := by exact_mod_cast BSD_ap_p2459
  have key : r ^ 2 - (a_p 2459 : ℝ) * r + ((2459 : ℕ) : ℝ) =
      (r - 92/2) ^ 2 + 1372/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (92 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2467 : BSD_FrobeniusDegreeNonneg_OPEN 2467 := fun r => by
  have hap : (a_p 2467 : ℝ) = 7 := by exact_mod_cast BSD_ap_p2467
  have key : r ^ 2 - (a_p 2467 : ℝ) * r + ((2467 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 9819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2473 : BSD_FrobeniusDegreeNonneg_OPEN 2473 := fun r => by
  have hap : (a_p 2473 : ℝ) = 13 := by exact_mod_cast BSD_ap_p2473
  have key : r ^ 2 - (a_p 2473 : ℝ) * r + ((2473 : ℕ) : ℝ) =
      (r - 13/2) ^ 2 + 9723/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (13 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2477 : BSD_FrobeniusDegreeNonneg_OPEN 2477 := fun r => by
  have hap : (a_p 2477 : ℝ) = 8 := by exact_mod_cast BSD_ap_p2477
  have key : r ^ 2 - (a_p 2477 : ℝ) * r + ((2477 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 9844/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2503 : BSD_FrobeniusDegreeNonneg_OPEN 2503 := fun r => by
  have hap : (a_p 2503 : ℝ) = -12 := by exact_mod_cast BSD_ap_p2503
  have key : r ^ 2 - (a_p 2503 : ℝ) * r + ((2503 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 9868/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2521 : BSD_FrobeniusDegreeNonneg_OPEN 2521 := fun r => by
  have hap : (a_p 2521 : ℝ) = -50 := by exact_mod_cast BSD_ap_p2521
  have key : r ^ 2 - (a_p 2521 : ℝ) * r + ((2521 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 7584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2531 : BSD_FrobeniusDegreeNonneg_OPEN 2531 := fun r => by
  have hap : (a_p 2531 : ℝ) = -3 := by exact_mod_cast BSD_ap_p2531
  have key : r ^ 2 - (a_p 2531 : ℝ) * r + ((2531 : ℕ) : ℝ) =
      (r + 3/2) ^ 2 + 10115/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (3 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2539 : BSD_FrobeniusDegreeNonneg_OPEN 2539 := fun r => by
  have hap : (a_p 2539 : ℝ) = -4 := by exact_mod_cast BSD_ap_p2539
  have key : r ^ 2 - (a_p 2539 : ℝ) * r + ((2539 : ℕ) : ℝ) =
      (r + 4/2) ^ 2 + 10140/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (4 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2543 : BSD_FrobeniusDegreeNonneg_OPEN 2543 := fun r => by
  have hap : (a_p 2543 : ℝ) = 16 := by exact_mod_cast BSD_ap_p2543
  have key : r ^ 2 - (a_p 2543 : ℝ) * r + ((2543 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 9916/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2549 : BSD_FrobeniusDegreeNonneg_OPEN 2549 := fun r => by
  have hap : (a_p 2549 : ℝ) = 24 := by exact_mod_cast BSD_ap_p2549
  have key : r ^ 2 - (a_p 2549 : ℝ) * r + ((2549 : ℕ) : ℝ) =
      (r - 24/2) ^ 2 + 9620/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2551 : BSD_FrobeniusDegreeNonneg_OPEN 2551 := fun r => by
  have hap : (a_p 2551 : ℝ) = -16 := by exact_mod_cast BSD_ap_p2551
  have key : r ^ 2 - (a_p 2551 : ℝ) * r + ((2551 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 9948/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2557 : BSD_FrobeniusDegreeNonneg_OPEN 2557 := fun r => by
  have hap : (a_p 2557 : ℝ) = -11 := by exact_mod_cast BSD_ap_p2557
  have key : r ^ 2 - (a_p 2557 : ℝ) * r + ((2557 : ℕ) : ℝ) =
      (r + 11/2) ^ 2 + 10107/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (11 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2579 : BSD_FrobeniusDegreeNonneg_OPEN 2579 := fun r => by
  have hap : (a_p 2579 : ℝ) = -92 := by exact_mod_cast BSD_ap_p2579
  have key : r ^ 2 - (a_p 2579 : ℝ) * r + ((2579 : ℕ) : ℝ) =
      (r + 92/2) ^ 2 + 1852/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (92 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2591 : BSD_FrobeniusDegreeNonneg_OPEN 2591 := fun r => by
  have hap : (a_p 2591 : ℝ) = -56 := by exact_mod_cast BSD_ap_p2591
  have key : r ^ 2 - (a_p 2591 : ℝ) * r + ((2591 : ℕ) : ℝ) =
      (r + 56/2) ^ 2 + 7228/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (56 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2593 : BSD_FrobeniusDegreeNonneg_OPEN 2593 := fun r => by
  have hap : (a_p 2593 : ℝ) = -68 := by exact_mod_cast BSD_ap_p2593
  have key : r ^ 2 - (a_p 2593 : ℝ) * r + ((2593 : ℕ) : ℝ) =
      (r + 68/2) ^ 2 + 5748/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (68 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2609 : BSD_FrobeniusDegreeNonneg_OPEN 2609 := fun r => by
  have hap : (a_p 2609 : ℝ) = 80 := by exact_mod_cast BSD_ap_p2609
  have key : r ^ 2 - (a_p 2609 : ℝ) * r + ((2609 : ℕ) : ℝ) =
      (r - 80/2) ^ 2 + 4036/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (80 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2617 : BSD_FrobeniusDegreeNonneg_OPEN 2617 := fun r => by
  have hap : (a_p 2617 : ℝ) = -18 := by exact_mod_cast BSD_ap_p2617
  have key : r ^ 2 - (a_p 2617 : ℝ) * r + ((2617 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 10144/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2621 : BSD_FrobeniusDegreeNonneg_OPEN 2621 := fun r => by
  have hap : (a_p 2621 : ℝ) = -78 := by exact_mod_cast BSD_ap_p2621
  have key : r ^ 2 - (a_p 2621 : ℝ) * r + ((2621 : ℕ) : ℝ) =
      (r + 78/2) ^ 2 + 4400/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (78 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2633 : BSD_FrobeniusDegreeNonneg_OPEN 2633 := fun r => by
  have hap : (a_p 2633 : ℝ) = -27 := by exact_mod_cast BSD_ap_p2633
  have key : r ^ 2 - (a_p 2633 : ℝ) * r + ((2633 : ℕ) : ℝ) =
      (r + 27/2) ^ 2 + 9803/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (27 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2647 : BSD_FrobeniusDegreeNonneg_OPEN 2647 := fun r => by
  have hap : (a_p 2647 : ℝ) = -48 := by exact_mod_cast BSD_ap_p2647
  have key : r ^ 2 - (a_p 2647 : ℝ) * r + ((2647 : ℕ) : ℝ) =
      (r + 48/2) ^ 2 + 8284/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2657 : BSD_FrobeniusDegreeNonneg_OPEN 2657 := fun r => by
  have hap : (a_p 2657 : ℝ) = 66 := by exact_mod_cast BSD_ap_p2657
  have key : r ^ 2 - (a_p 2657 : ℝ) * r + ((2657 : ℕ) : ℝ) =
      (r - 66/2) ^ 2 + 6272/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (66 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2659 : BSD_FrobeniusDegreeNonneg_OPEN 2659 := fun r => by
  have hap : (a_p 2659 : ℝ) = 48 := by exact_mod_cast BSD_ap_p2659
  have key : r ^ 2 - (a_p 2659 : ℝ) * r + ((2659 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 8332/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2663 : BSD_FrobeniusDegreeNonneg_OPEN 2663 := fun r => by
  have hap : (a_p 2663 : ℝ) = -59 := by exact_mod_cast BSD_ap_p2663
  have key : r ^ 2 - (a_p 2663 : ℝ) * r + ((2663 : ℕ) : ℝ) =
      (r + 59/2) ^ 2 + 7171/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (59 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2671 : BSD_FrobeniusDegreeNonneg_OPEN 2671 := fun r => by
  have hap : (a_p 2671 : ℝ) = -48 := by exact_mod_cast BSD_ap_p2671
  have key : r ^ 2 - (a_p 2671 : ℝ) * r + ((2671 : ℕ) : ℝ) =
      (r + 48/2) ^ 2 + 8380/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2677 : BSD_FrobeniusDegreeNonneg_OPEN 2677 := fun r => by
  have hap : (a_p 2677 : ℝ) = 77 := by exact_mod_cast BSD_ap_p2677
  have key : r ^ 2 - (a_p 2677 : ℝ) * r + ((2677 : ℕ) : ℝ) =
      (r - 77/2) ^ 2 + 4779/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (77 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2683 : BSD_FrobeniusDegreeNonneg_OPEN 2683 := fun r => by
  have hap : (a_p 2683 : ℝ) = -52 := by exact_mod_cast BSD_ap_p2683
  have key : r ^ 2 - (a_p 2683 : ℝ) * r + ((2683 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 8028/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2687 : BSD_FrobeniusDegreeNonneg_OPEN 2687 := fun r => by
  have hap : (a_p 2687 : ℝ) = 7 := by exact_mod_cast BSD_ap_p2687
  have key : r ^ 2 - (a_p 2687 : ℝ) * r + ((2687 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 10699/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2689 : BSD_FrobeniusDegreeNonneg_OPEN 2689 := fun r => by
  have hap : (a_p 2689 : ℝ) = -77 := by exact_mod_cast BSD_ap_p2689
  have key : r ^ 2 - (a_p 2689 : ℝ) * r + ((2689 : ℕ) : ℝ) =
      (r + 77/2) ^ 2 + 4827/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (77 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2693 : BSD_FrobeniusDegreeNonneg_OPEN 2693 := fun r => by
  have hap : (a_p 2693 : ℝ) = -63 := by exact_mod_cast BSD_ap_p2693
  have key : r ^ 2 - (a_p 2693 : ℝ) * r + ((2693 : ℕ) : ℝ) =
      (r + 63/2) ^ 2 + 6803/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (63 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2699 : BSD_FrobeniusDegreeNonneg_OPEN 2699 := fun r => by
  have hap : (a_p 2699 : ℝ) = -9 := by exact_mod_cast BSD_ap_p2699
  have key : r ^ 2 - (a_p 2699 : ℝ) * r + ((2699 : ℕ) : ℝ) =
      (r + 9/2) ^ 2 + 10715/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (9 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2707 : BSD_FrobeniusDegreeNonneg_OPEN 2707 := fun r => by
  have hap : (a_p 2707 : ℝ) = 23 := by exact_mod_cast BSD_ap_p2707
  have key : r ^ 2 - (a_p 2707 : ℝ) * r + ((2707 : ℕ) : ℝ) =
      (r - 23/2) ^ 2 + 10299/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (23 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2711 : BSD_FrobeniusDegreeNonneg_OPEN 2711 := fun r => by
  have hap : (a_p 2711 : ℝ) = 81 := by exact_mod_cast BSD_ap_p2711
  have key : r ^ 2 - (a_p 2711 : ℝ) * r + ((2711 : ℕ) : ℝ) =
      (r - 81/2) ^ 2 + 4283/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (81 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2713 : BSD_FrobeniusDegreeNonneg_OPEN 2713 := fun r => by
  have hap : (a_p 2713 : ℝ) = 58 := by exact_mod_cast BSD_ap_p2713
  have key : r ^ 2 - (a_p 2713 : ℝ) * r + ((2713 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 7488/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2719 : BSD_FrobeniusDegreeNonneg_OPEN 2719 := fun r => by
  have hap : (a_p 2719 : ℝ) = -14 := by exact_mod_cast BSD_ap_p2719
  have key : r ^ 2 - (a_p 2719 : ℝ) * r + ((2719 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 10680/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2729 : BSD_FrobeniusDegreeNonneg_OPEN 2729 := fun r => by
  have hap : (a_p 2729 : ℝ) = 54 := by exact_mod_cast BSD_ap_p2729
  have key : r ^ 2 - (a_p 2729 : ℝ) * r + ((2729 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 8000/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2731 : BSD_FrobeniusDegreeNonneg_OPEN 2731 := fun r => by
  have hap : (a_p 2731 : ℝ) = -68 := by exact_mod_cast BSD_ap_p2731
  have key : r ^ 2 - (a_p 2731 : ℝ) * r + ((2731 : ℕ) : ℝ) =
      (r + 68/2) ^ 2 + 6300/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (68 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2741 : BSD_FrobeniusDegreeNonneg_OPEN 2741 := fun r => by
  have hap : (a_p 2741 : ℝ) = 22 := by exact_mod_cast BSD_ap_p2741
  have key : r ^ 2 - (a_p 2741 : ℝ) * r + ((2741 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 10480/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2749 : BSD_FrobeniusDegreeNonneg_OPEN 2749 := fun r => by
  have hap : (a_p 2749 : ℝ) = 26 := by exact_mod_cast BSD_ap_p2749
  have key : r ^ 2 - (a_p 2749 : ℝ) * r + ((2749 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 10320/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2753 : BSD_FrobeniusDegreeNonneg_OPEN 2753 := fun r => by
  have hap : (a_p 2753 : ℝ) = 21 := by exact_mod_cast BSD_ap_p2753
  have key : r ^ 2 - (a_p 2753 : ℝ) * r + ((2753 : ℕ) : ℝ) =
      (r - 21/2) ^ 2 + 10571/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (21 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2767 : BSD_FrobeniusDegreeNonneg_OPEN 2767 := fun r => by
  have hap : (a_p 2767 : ℝ) = -70 := by exact_mod_cast BSD_ap_p2767
  have key : r ^ 2 - (a_p 2767 : ℝ) * r + ((2767 : ℕ) : ℝ) =
      (r + 70/2) ^ 2 + 6168/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (70 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2777 : BSD_FrobeniusDegreeNonneg_OPEN 2777 := fun r => by
  have hap : (a_p 2777 : ℝ) = 74 := by exact_mod_cast BSD_ap_p2777
  have key : r ^ 2 - (a_p 2777 : ℝ) * r + ((2777 : ℕ) : ℝ) =
      (r - 74/2) ^ 2 + 5632/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (74 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2789 : BSD_FrobeniusDegreeNonneg_OPEN 2789 := fun r => by
  have hap : (a_p 2789 : ℝ) = -94 := by exact_mod_cast BSD_ap_p2789
  have key : r ^ 2 - (a_p 2789 : ℝ) * r + ((2789 : ℕ) : ℝ) =
      (r + 94/2) ^ 2 + 2320/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (94 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2791 : BSD_FrobeniusDegreeNonneg_OPEN 2791 := fun r => by
  have hap : (a_p 2791 : ℝ) = -68 := by exact_mod_cast BSD_ap_p2791
  have key : r ^ 2 - (a_p 2791 : ℝ) * r + ((2791 : ℕ) : ℝ) =
      (r + 68/2) ^ 2 + 6540/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (68 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2797 : BSD_FrobeniusDegreeNonneg_OPEN 2797 := fun r => by
  have hap : (a_p 2797 : ℝ) = -30 := by exact_mod_cast BSD_ap_p2797
  have key : r ^ 2 - (a_p 2797 : ℝ) * r + ((2797 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 10288/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2801 : BSD_FrobeniusDegreeNonneg_OPEN 2801 := fun r => by
  have hap : (a_p 2801 : ℝ) = 8 := by exact_mod_cast BSD_ap_p2801
  have key : r ^ 2 - (a_p 2801 : ℝ) * r + ((2801 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 11140/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2803 : BSD_FrobeniusDegreeNonneg_OPEN 2803 := fun r => by
  have hap : (a_p 2803 : ℝ) = 28 := by exact_mod_cast BSD_ap_p2803
  have key : r ^ 2 - (a_p 2803 : ℝ) * r + ((2803 : ℕ) : ℝ) =
      (r - 28/2) ^ 2 + 10428/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (28 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2819 : BSD_FrobeniusDegreeNonneg_OPEN 2819 := fun r => by
  have hap : (a_p 2819 : ℝ) = -15 := by exact_mod_cast BSD_ap_p2819
  have key : r ^ 2 - (a_p 2819 : ℝ) * r + ((2819 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 11051/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2833 : BSD_FrobeniusDegreeNonneg_OPEN 2833 := fun r => by
  have hap : (a_p 2833 : ℝ) = 26 := by exact_mod_cast BSD_ap_p2833
  have key : r ^ 2 - (a_p 2833 : ℝ) * r + ((2833 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 10656/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2837 : BSD_FrobeniusDegreeNonneg_OPEN 2837 := fun r => by
  have hap : (a_p 2837 : ℝ) = -44 := by exact_mod_cast BSD_ap_p2837
  have key : r ^ 2 - (a_p 2837 : ℝ) * r + ((2837 : ℕ) : ℝ) =
      (r + 44/2) ^ 2 + 9412/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (44 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2843 : BSD_FrobeniusDegreeNonneg_OPEN 2843 := fun r => by
  have hap : (a_p 2843 : ℝ) = 60 := by exact_mod_cast BSD_ap_p2843
  have key : r ^ 2 - (a_p 2843 : ℝ) * r + ((2843 : ℕ) : ℝ) =
      (r - 60/2) ^ 2 + 7772/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (60 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2851 : BSD_FrobeniusDegreeNonneg_OPEN 2851 := fun r => by
  have hap : (a_p 2851 : ℝ) = -12 := by exact_mod_cast BSD_ap_p2851
  have key : r ^ 2 - (a_p 2851 : ℝ) * r + ((2851 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 11260/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2857 : BSD_FrobeniusDegreeNonneg_OPEN 2857 := fun r => by
  have hap : (a_p 2857 : ℝ) = 54 := by exact_mod_cast BSD_ap_p2857
  have key : r ^ 2 - (a_p 2857 : ℝ) * r + ((2857 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 8512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2861 : BSD_FrobeniusDegreeNonneg_OPEN 2861 := fun r => by
  have hap : (a_p 2861 : ℝ) = -39 := by exact_mod_cast BSD_ap_p2861
  have key : r ^ 2 - (a_p 2861 : ℝ) * r + ((2861 : ℕ) : ℝ) =
      (r + 39/2) ^ 2 + 9923/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (39 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2879 : BSD_FrobeniusDegreeNonneg_OPEN 2879 := fun r => by
  have hap : (a_p 2879 : ℝ) = -32 := by exact_mod_cast BSD_ap_p2879
  have key : r ^ 2 - (a_p 2879 : ℝ) * r + ((2879 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 10492/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2887 : BSD_FrobeniusDegreeNonneg_OPEN 2887 := fun r => by
  have hap : (a_p 2887 : ℝ) = -57 := by exact_mod_cast BSD_ap_p2887
  have key : r ^ 2 - (a_p 2887 : ℝ) * r + ((2887 : ℕ) : ℝ) =
      (r + 57/2) ^ 2 + 8299/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (57 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2897 : BSD_FrobeniusDegreeNonneg_OPEN 2897 := fun r => by
  have hap : (a_p 2897 : ℝ) = 26 := by exact_mod_cast BSD_ap_p2897
  have key : r ^ 2 - (a_p 2897 : ℝ) * r + ((2897 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 10912/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2903 : BSD_FrobeniusDegreeNonneg_OPEN 2903 := fun r => by
  have hap : (a_p 2903 : ℝ) = 26 := by exact_mod_cast BSD_ap_p2903
  have key : r ^ 2 - (a_p 2903 : ℝ) * r + ((2903 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 10936/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2909 : BSD_FrobeniusDegreeNonneg_OPEN 2909 := fun r => by
  have hap : (a_p 2909 : ℝ) = -25 := by exact_mod_cast BSD_ap_p2909
  have key : r ^ 2 - (a_p 2909 : ℝ) * r + ((2909 : ℕ) : ℝ) =
      (r + 25/2) ^ 2 + 11011/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (25 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2917 : BSD_FrobeniusDegreeNonneg_OPEN 2917 := fun r => by
  have hap : (a_p 2917 : ℝ) = -84 := by exact_mod_cast BSD_ap_p2917
  have key : r ^ 2 - (a_p 2917 : ℝ) * r + ((2917 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 4612/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2927 : BSD_FrobeniusDegreeNonneg_OPEN 2927 := fun r => by
  have hap : (a_p 2927 : ℝ) = 48 := by exact_mod_cast BSD_ap_p2927
  have key : r ^ 2 - (a_p 2927 : ℝ) * r + ((2927 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 9404/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2939 : BSD_FrobeniusDegreeNonneg_OPEN 2939 := fun r => by
  have hap : (a_p 2939 : ℝ) = 12 := by exact_mod_cast BSD_ap_p2939
  have key : r ^ 2 - (a_p 2939 : ℝ) * r + ((2939 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 11612/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2953 : BSD_FrobeniusDegreeNonneg_OPEN 2953 := fun r => by
  have hap : (a_p 2953 : ℝ) = 6 := by exact_mod_cast BSD_ap_p2953
  have key : r ^ 2 - (a_p 2953 : ℝ) * r + ((2953 : ℕ) : ℝ) =
      (r - 6/2) ^ 2 + 11776/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2957 : BSD_FrobeniusDegreeNonneg_OPEN 2957 := fun r => by
  have hap : (a_p 2957 : ℝ) = -75 := by exact_mod_cast BSD_ap_p2957
  have key : r ^ 2 - (a_p 2957 : ℝ) * r + ((2957 : ℕ) : ℝ) =
      (r + 75/2) ^ 2 + 6203/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (75 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2963 : BSD_FrobeniusDegreeNonneg_OPEN 2963 := fun r => by
  have hap : (a_p 2963 : ℝ) = 39 := by exact_mod_cast BSD_ap_p2963
  have key : r ^ 2 - (a_p 2963 : ℝ) * r + ((2963 : ℕ) : ℝ) =
      (r - 39/2) ^ 2 + 10331/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (39 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2969 : BSD_FrobeniusDegreeNonneg_OPEN 2969 := fun r => by
  have hap : (a_p 2969 : ℝ) = 26 := by exact_mod_cast BSD_ap_p2969
  have key : r ^ 2 - (a_p 2969 : ℝ) * r + ((2969 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 11200/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2971 : BSD_FrobeniusDegreeNonneg_OPEN 2971 := fun r => by
  have hap : (a_p 2971 : ℝ) = 13 := by exact_mod_cast BSD_ap_p2971
  have key : r ^ 2 - (a_p 2971 : ℝ) * r + ((2971 : ℕ) : ℝ) =
      (r - 13/2) ^ 2 + 11715/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (13 : ℝ)/2)]

theorem BSD_DegreeNonneg_p2999 : BSD_FrobeniusDegreeNonneg_OPEN 2999 := fun r => by
  have hap : (a_p 2999 : ℝ) = -36 := by exact_mod_cast BSD_ap_p2999
  have key : r ^ 2 - (a_p 2999 : ℝ) * r + ((2999 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 10700/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3001 : BSD_FrobeniusDegreeNonneg_OPEN 3001 := fun r => by
  have hap : (a_p 3001 : ℝ) = 1 := by exact_mod_cast BSD_ap_p3001
  have key : r ^ 2 - (a_p 3001 : ℝ) * r + ((3001 : ℕ) : ℝ) =
      (r - 1/2) ^ 2 + 12003/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (1 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3011 : BSD_FrobeniusDegreeNonneg_OPEN 3011 := fun r => by
  have hap : (a_p 3011 : ℝ) = 44 := by exact_mod_cast BSD_ap_p3011
  have key : r ^ 2 - (a_p 3011 : ℝ) * r + ((3011 : ℕ) : ℝ) =
      (r - 44/2) ^ 2 + 10108/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (44 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3019 : BSD_FrobeniusDegreeNonneg_OPEN 3019 := fun r => by
  have hap : (a_p 3019 : ℝ) = -79 := by exact_mod_cast BSD_ap_p3019
  have key : r ^ 2 - (a_p 3019 : ℝ) * r + ((3019 : ℕ) : ℝ) =
      (r + 79/2) ^ 2 + 5835/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (79 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3023 : BSD_FrobeniusDegreeNonneg_OPEN 3023 := fun r => by
  have hap : (a_p 3023 : ℝ) = 33 := by exact_mod_cast BSD_ap_p3023
  have key : r ^ 2 - (a_p 3023 : ℝ) * r + ((3023 : ℕ) : ℝ) =
      (r - 33/2) ^ 2 + 11003/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (33 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3037 : BSD_FrobeniusDegreeNonneg_OPEN 3037 := fun r => by
  have hap : (a_p 3037 : ℝ) = 3 := by exact_mod_cast BSD_ap_p3037
  have key : r ^ 2 - (a_p 3037 : ℝ) * r + ((3037 : ℕ) : ℝ) =
      (r - 3/2) ^ 2 + 12139/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (3 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3041 : BSD_FrobeniusDegreeNonneg_OPEN 3041 := fun r => by
  have hap : (a_p 3041 : ℝ) = -54 := by exact_mod_cast BSD_ap_p3041
  have key : r ^ 2 - (a_p 3041 : ℝ) * r + ((3041 : ℕ) : ℝ) =
      (r + 54/2) ^ 2 + 9248/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3049 : BSD_FrobeniusDegreeNonneg_OPEN 3049 := fun r => by
  have hap : (a_p 3049 : ℝ) = -28 := by exact_mod_cast BSD_ap_p3049
  have key : r ^ 2 - (a_p 3049 : ℝ) * r + ((3049 : ℕ) : ℝ) =
      (r + 28/2) ^ 2 + 11412/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (28 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3061 : BSD_FrobeniusDegreeNonneg_OPEN 3061 := fun r => by
  have hap : (a_p 3061 : ℝ) = -37 := by exact_mod_cast BSD_ap_p3061
  have key : r ^ 2 - (a_p 3061 : ℝ) * r + ((3061 : ℕ) : ℝ) =
      (r + 37/2) ^ 2 + 10875/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (37 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3067 : BSD_FrobeniusDegreeNonneg_OPEN 3067 := fun r => by
  have hap : (a_p 3067 : ℝ) = -7 := by exact_mod_cast BSD_ap_p3067
  have key : r ^ 2 - (a_p 3067 : ℝ) * r + ((3067 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 12219/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3079 : BSD_FrobeniusDegreeNonneg_OPEN 3079 := fun r => by
  have hap : (a_p 3079 : ℝ) = -38 := by exact_mod_cast BSD_ap_p3079
  have key : r ^ 2 - (a_p 3079 : ℝ) * r + ((3079 : ℕ) : ℝ) =
      (r + 38/2) ^ 2 + 10872/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3083 : BSD_FrobeniusDegreeNonneg_OPEN 3083 := fun r => by
  have hap : (a_p 3083 : ℝ) = 3 := by exact_mod_cast BSD_ap_p3083
  have key : r ^ 2 - (a_p 3083 : ℝ) * r + ((3083 : ℕ) : ℝ) =
      (r - 3/2) ^ 2 + 12323/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (3 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3089 : BSD_FrobeniusDegreeNonneg_OPEN 3089 := fun r => by
  have hap : (a_p 3089 : ℝ) = 11 := by exact_mod_cast BSD_ap_p3089
  have key : r ^ 2 - (a_p 3089 : ℝ) * r + ((3089 : ℕ) : ℝ) =
      (r - 11/2) ^ 2 + 12235/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (11 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3109 : BSD_FrobeniusDegreeNonneg_OPEN 3109 := fun r => by
  have hap : (a_p 3109 : ℝ) = 54 := by exact_mod_cast BSD_ap_p3109
  have key : r ^ 2 - (a_p 3109 : ℝ) * r + ((3109 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 9520/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3119 : BSD_FrobeniusDegreeNonneg_OPEN 3119 := fun r => by
  have hap : (a_p 3119 : ℝ) = -14 := by exact_mod_cast BSD_ap_p3119
  have key : r ^ 2 - (a_p 3119 : ℝ) * r + ((3119 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 12280/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3121 : BSD_FrobeniusDegreeNonneg_OPEN 3121 := fun r => by
  have hap : (a_p 3121 : ℝ) = -32 := by exact_mod_cast BSD_ap_p3121
  have key : r ^ 2 - (a_p 3121 : ℝ) * r + ((3121 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 11460/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3137 : BSD_FrobeniusDegreeNonneg_OPEN 3137 := fun r => by
  have hap : (a_p 3137 : ℝ) = -72 := by exact_mod_cast BSD_ap_p3137
  have key : r ^ 2 - (a_p 3137 : ℝ) * r + ((3137 : ℕ) : ℝ) =
      (r + 72/2) ^ 2 + 7364/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (72 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3163 : BSD_FrobeniusDegreeNonneg_OPEN 3163 := fun r => by
  have hap : (a_p 3163 : ℝ) = 86 := by exact_mod_cast BSD_ap_p3163
  have key : r ^ 2 - (a_p 3163 : ℝ) * r + ((3163 : ℕ) : ℝ) =
      (r - 86/2) ^ 2 + 5256/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (86 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3167 : BSD_FrobeniusDegreeNonneg_OPEN 3167 := fun r => by
  have hap : (a_p 3167 : ℝ) = -6 := by exact_mod_cast BSD_ap_p3167
  have key : r ^ 2 - (a_p 3167 : ℝ) * r + ((3167 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 12632/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3169 : BSD_FrobeniusDegreeNonneg_OPEN 3169 := fun r => by
  have hap : (a_p 3169 : ℝ) = -7 := by exact_mod_cast BSD_ap_p3169
  have key : r ^ 2 - (a_p 3169 : ℝ) * r + ((3169 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 12627/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3181 : BSD_FrobeniusDegreeNonneg_OPEN 3181 := fun r => by
  have hap : (a_p 3181 : ℝ) = -12 := by exact_mod_cast BSD_ap_p3181
  have key : r ^ 2 - (a_p 3181 : ℝ) * r + ((3181 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 12580/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3187 : BSD_FrobeniusDegreeNonneg_OPEN 3187 := fun r => by
  have hap : (a_p 3187 : ℝ) = -80 := by exact_mod_cast BSD_ap_p3187
  have key : r ^ 2 - (a_p 3187 : ℝ) * r + ((3187 : ℕ) : ℝ) =
      (r + 80/2) ^ 2 + 6348/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (80 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3191 : BSD_FrobeniusDegreeNonneg_OPEN 3191 := fun r => by
  have hap : (a_p 3191 : ℝ) = 48 := by exact_mod_cast BSD_ap_p3191
  have key : r ^ 2 - (a_p 3191 : ℝ) * r + ((3191 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 10460/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3203 : BSD_FrobeniusDegreeNonneg_OPEN 3203 := fun r => by
  have hap : (a_p 3203 : ℝ) = -62 := by exact_mod_cast BSD_ap_p3203
  have key : r ^ 2 - (a_p 3203 : ℝ) * r + ((3203 : ℕ) : ℝ) =
      (r + 62/2) ^ 2 + 8968/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (62 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3209 : BSD_FrobeniusDegreeNonneg_OPEN 3209 := fun r => by
  have hap : (a_p 3209 : ℝ) = -70 := by exact_mod_cast BSD_ap_p3209
  have key : r ^ 2 - (a_p 3209 : ℝ) * r + ((3209 : ℕ) : ℝ) =
      (r + 70/2) ^ 2 + 7936/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (70 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3217 : BSD_FrobeniusDegreeNonneg_OPEN 3217 := fun r => by
  have hap : (a_p 3217 : ℝ) = -7 := by exact_mod_cast BSD_ap_p3217
  have key : r ^ 2 - (a_p 3217 : ℝ) * r + ((3217 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 12819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3221 : BSD_FrobeniusDegreeNonneg_OPEN 3221 := fun r => by
  have hap : (a_p 3221 : ℝ) = -67 := by exact_mod_cast BSD_ap_p3221
  have key : r ^ 2 - (a_p 3221 : ℝ) * r + ((3221 : ℕ) : ℝ) =
      (r + 67/2) ^ 2 + 8395/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (67 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3229 : BSD_FrobeniusDegreeNonneg_OPEN 3229 := fun r => by
  have hap : (a_p 3229 : ℝ) = -28 := by exact_mod_cast BSD_ap_p3229
  have key : r ^ 2 - (a_p 3229 : ℝ) * r + ((3229 : ℕ) : ℝ) =
      (r + 28/2) ^ 2 + 12132/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (28 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3251 : BSD_FrobeniusDegreeNonneg_OPEN 3251 := fun r => by
  have hap : (a_p 3251 : ℝ) = -58 := by exact_mod_cast BSD_ap_p3251
  have key : r ^ 2 - (a_p 3251 : ℝ) * r + ((3251 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 9640/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3253 : BSD_FrobeniusDegreeNonneg_OPEN 3253 := fun r => by
  have hap : (a_p 3253 : ℝ) = 64 := by exact_mod_cast BSD_ap_p3253
  have key : r ^ 2 - (a_p 3253 : ℝ) * r + ((3253 : ℕ) : ℝ) =
      (r - 64/2) ^ 2 + 8916/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (64 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3257 : BSD_FrobeniusDegreeNonneg_OPEN 3257 := fun r => by
  have hap : (a_p 3257 : ℝ) = -82 := by exact_mod_cast BSD_ap_p3257
  have key : r ^ 2 - (a_p 3257 : ℝ) * r + ((3257 : ℕ) : ℝ) =
      (r + 82/2) ^ 2 + 6304/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (82 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3259 : BSD_FrobeniusDegreeNonneg_OPEN 3259 := fun r => by
  have hap : (a_p 3259 : ℝ) = -4 := by exact_mod_cast BSD_ap_p3259
  have key : r ^ 2 - (a_p 3259 : ℝ) * r + ((3259 : ℕ) : ℝ) =
      (r + 4/2) ^ 2 + 13020/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (4 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3271 : BSD_FrobeniusDegreeNonneg_OPEN 3271 := fun r => by
  have hap : (a_p 3271 : ℝ) = 95 := by exact_mod_cast BSD_ap_p3271
  have key : r ^ 2 - (a_p 3271 : ℝ) * r + ((3271 : ℕ) : ℝ) =
      (r - 95/2) ^ 2 + 4059/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (95 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3299 : BSD_FrobeniusDegreeNonneg_OPEN 3299 := fun r => by
  have hap : (a_p 3299 : ℝ) = -20 := by exact_mod_cast BSD_ap_p3299
  have key : r ^ 2 - (a_p 3299 : ℝ) * r + ((3299 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 12796/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3301 : BSD_FrobeniusDegreeNonneg_OPEN 3301 := fun r => by
  have hap : (a_p 3301 : ℝ) = -57 := by exact_mod_cast BSD_ap_p3301
  have key : r ^ 2 - (a_p 3301 : ℝ) * r + ((3301 : ℕ) : ℝ) =
      (r + 57/2) ^ 2 + 9955/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (57 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3307 : BSD_FrobeniusDegreeNonneg_OPEN 3307 := fun r => by
  have hap : (a_p 3307 : ℝ) = -8 := by exact_mod_cast BSD_ap_p3307
  have key : r ^ 2 - (a_p 3307 : ℝ) * r + ((3307 : ℕ) : ℝ) =
      (r + 8/2) ^ 2 + 13164/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (8 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3313 : BSD_FrobeniusDegreeNonneg_OPEN 3313 := fun r => by
  have hap : (a_p 3313 : ℝ) = 12 := by exact_mod_cast BSD_ap_p3313
  have key : r ^ 2 - (a_p 3313 : ℝ) * r + ((3313 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 13108/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3319 : BSD_FrobeniusDegreeNonneg_OPEN 3319 := fun r => by
  have hap : (a_p 3319 : ℝ) = 34 := by exact_mod_cast BSD_ap_p3319
  have key : r ^ 2 - (a_p 3319 : ℝ) * r + ((3319 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 12120/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3323 : BSD_FrobeniusDegreeNonneg_OPEN 3323 := fun r => by
  have hap : (a_p 3323 : ℝ) = -84 := by exact_mod_cast BSD_ap_p3323
  have key : r ^ 2 - (a_p 3323 : ℝ) * r + ((3323 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 6236/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3329 : BSD_FrobeniusDegreeNonneg_OPEN 3329 := fun r => by
  have hap : (a_p 3329 : ℝ) = 58 := by exact_mod_cast BSD_ap_p3329
  have key : r ^ 2 - (a_p 3329 : ℝ) * r + ((3329 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 9952/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3331 : BSD_FrobeniusDegreeNonneg_OPEN 3331 := fun r => by
  have hap : (a_p 3331 : ℝ) = 113 := by exact_mod_cast BSD_ap_p3331
  have key : r ^ 2 - (a_p 3331 : ℝ) * r + ((3331 : ℕ) : ℝ) =
      (r - 113/2) ^ 2 + 555/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (113 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3343 : BSD_FrobeniusDegreeNonneg_OPEN 3343 := fun r => by
  have hap : (a_p 3343 : ℝ) = 42 := by exact_mod_cast BSD_ap_p3343
  have key : r ^ 2 - (a_p 3343 : ℝ) * r + ((3343 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 11608/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3347 : BSD_FrobeniusDegreeNonneg_OPEN 3347 := fun r => by
  have hap : (a_p 3347 : ℝ) = 57 := by exact_mod_cast BSD_ap_p3347
  have key : r ^ 2 - (a_p 3347 : ℝ) * r + ((3347 : ℕ) : ℝ) =
      (r - 57/2) ^ 2 + 10139/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (57 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3359 : BSD_FrobeniusDegreeNonneg_OPEN 3359 := fun r => by
  have hap : (a_p 3359 : ℝ) = 17 := by exact_mod_cast BSD_ap_p3359
  have key : r ^ 2 - (a_p 3359 : ℝ) * r + ((3359 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 13147/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3361 : BSD_FrobeniusDegreeNonneg_OPEN 3361 := fun r => by
  have hap : (a_p 3361 : ℝ) = -90 := by exact_mod_cast BSD_ap_p3361
  have key : r ^ 2 - (a_p 3361 : ℝ) * r + ((3361 : ℕ) : ℝ) =
      (r + 90/2) ^ 2 + 5344/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (90 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3371 : BSD_FrobeniusDegreeNonneg_OPEN 3371 := fun r => by
  have hap : (a_p 3371 : ℝ) = -15 := by exact_mod_cast BSD_ap_p3371
  have key : r ^ 2 - (a_p 3371 : ℝ) * r + ((3371 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 13259/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3373 : BSD_FrobeniusDegreeNonneg_OPEN 3373 := fun r => by
  have hap : (a_p 3373 : ℝ) = -64 := by exact_mod_cast BSD_ap_p3373
  have key : r ^ 2 - (a_p 3373 : ℝ) * r + ((3373 : ℕ) : ℝ) =
      (r + 64/2) ^ 2 + 9396/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (64 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3389 : BSD_FrobeniusDegreeNonneg_OPEN 3389 := fun r => by
  have hap : (a_p 3389 : ℝ) = -61 := by exact_mod_cast BSD_ap_p3389
  have key : r ^ 2 - (a_p 3389 : ℝ) * r + ((3389 : ℕ) : ℝ) =
      (r + 61/2) ^ 2 + 9835/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (61 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3391 : BSD_FrobeniusDegreeNonneg_OPEN 3391 := fun r => by
  have hap : (a_p 3391 : ℝ) = 48 := by exact_mod_cast BSD_ap_p3391
  have key : r ^ 2 - (a_p 3391 : ℝ) * r + ((3391 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 11260/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3407 : BSD_FrobeniusDegreeNonneg_OPEN 3407 := fun r => by
  have hap : (a_p 3407 : ℝ) = 94 := by exact_mod_cast BSD_ap_p3407
  have key : r ^ 2 - (a_p 3407 : ℝ) * r + ((3407 : ℕ) : ℝ) =
      (r - 94/2) ^ 2 + 4792/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (94 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3413 : BSD_FrobeniusDegreeNonneg_OPEN 3413 := fun r => by
  have hap : (a_p 3413 : ℝ) = 91 := by exact_mod_cast BSD_ap_p3413
  have key : r ^ 2 - (a_p 3413 : ℝ) * r + ((3413 : ℕ) : ℝ) =
      (r - 91/2) ^ 2 + 5371/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (91 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3433 : BSD_FrobeniusDegreeNonneg_OPEN 3433 := fun r => by
  have hap : (a_p 3433 : ℝ) = 14 := by exact_mod_cast BSD_ap_p3433
  have key : r ^ 2 - (a_p 3433 : ℝ) * r + ((3433 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 13536/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3449 : BSD_FrobeniusDegreeNonneg_OPEN 3449 := fun r => by
  have hap : (a_p 3449 : ℝ) = 84 := by exact_mod_cast BSD_ap_p3449
  have key : r ^ 2 - (a_p 3449 : ℝ) * r + ((3449 : ℕ) : ℝ) =
      (r - 84/2) ^ 2 + 6740/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (84 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3457 : BSD_FrobeniusDegreeNonneg_OPEN 3457 := fun r => by
  have hap : (a_p 3457 : ℝ) = -5 := by exact_mod_cast BSD_ap_p3457
  have key : r ^ 2 - (a_p 3457 : ℝ) * r + ((3457 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 13803/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3461 : BSD_FrobeniusDegreeNonneg_OPEN 3461 := fun r => by
  have hap : (a_p 3461 : ℝ) = 16 := by exact_mod_cast BSD_ap_p3461
  have key : r ^ 2 - (a_p 3461 : ℝ) * r + ((3461 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 13588/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3463 : BSD_FrobeniusDegreeNonneg_OPEN 3463 := fun r => by
  have hap : (a_p 3463 : ℝ) = -32 := by exact_mod_cast BSD_ap_p3463
  have key : r ^ 2 - (a_p 3463 : ℝ) * r + ((3463 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 12828/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3467 : BSD_FrobeniusDegreeNonneg_OPEN 3467 := fun r => by
  have hap : (a_p 3467 : ℝ) = 2 := by exact_mod_cast BSD_ap_p3467
  have key : r ^ 2 - (a_p 3467 : ℝ) * r + ((3467 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 13864/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3469 : BSD_FrobeniusDegreeNonneg_OPEN 3469 := fun r => by
  have hap : (a_p 3469 : ℝ) = 37 := by exact_mod_cast BSD_ap_p3469
  have key : r ^ 2 - (a_p 3469 : ℝ) * r + ((3469 : ℕ) : ℝ) =
      (r - 37/2) ^ 2 + 12507/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (37 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3491 : BSD_FrobeniusDegreeNonneg_OPEN 3491 := fun r => by
  have hap : (a_p 3491 : ℝ) = -89 := by exact_mod_cast BSD_ap_p3491
  have key : r ^ 2 - (a_p 3491 : ℝ) * r + ((3491 : ℕ) : ℝ) =
      (r + 89/2) ^ 2 + 6043/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (89 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3499 : BSD_FrobeniusDegreeNonneg_OPEN 3499 := fun r => by
  have hap : (a_p 3499 : ℝ) = -92 := by exact_mod_cast BSD_ap_p3499
  have key : r ^ 2 - (a_p 3499 : ℝ) * r + ((3499 : ℕ) : ℝ) =
      (r + 92/2) ^ 2 + 5532/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (92 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3511 : BSD_FrobeniusDegreeNonneg_OPEN 3511 := fun r => by
  have hap : (a_p 3511 : ℝ) = -32 := by exact_mod_cast BSD_ap_p3511
  have key : r ^ 2 - (a_p 3511 : ℝ) * r + ((3511 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 13020/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3517 : BSD_FrobeniusDegreeNonneg_OPEN 3517 := fun r => by
  have hap : (a_p 3517 : ℝ) = 18 := by exact_mod_cast BSD_ap_p3517
  have key : r ^ 2 - (a_p 3517 : ℝ) * r + ((3517 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 13744/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3527 : BSD_FrobeniusDegreeNonneg_OPEN 3527 := fun r => by
  have hap : (a_p 3527 : ℝ) = 56 := by exact_mod_cast BSD_ap_p3527
  have key : r ^ 2 - (a_p 3527 : ℝ) * r + ((3527 : ℕ) : ℝ) =
      (r - 56/2) ^ 2 + 10972/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (56 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3529 : BSD_FrobeniusDegreeNonneg_OPEN 3529 := fun r => by
  have hap : (a_p 3529 : ℝ) = 19 := by exact_mod_cast BSD_ap_p3529
  have key : r ^ 2 - (a_p 3529 : ℝ) * r + ((3529 : ℕ) : ℝ) =
      (r - 19/2) ^ 2 + 13755/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (19 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3533 : BSD_FrobeniusDegreeNonneg_OPEN 3533 := fun r => by
  have hap : (a_p 3533 : ℝ) = -36 := by exact_mod_cast BSD_ap_p3533
  have key : r ^ 2 - (a_p 3533 : ℝ) * r + ((3533 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 12836/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3539 : BSD_FrobeniusDegreeNonneg_OPEN 3539 := fun r => by
  have hap : (a_p 3539 : ℝ) = 86 := by exact_mod_cast BSD_ap_p3539
  have key : r ^ 2 - (a_p 3539 : ℝ) * r + ((3539 : ℕ) : ℝ) =
      (r - 86/2) ^ 2 + 6760/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (86 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3541 : BSD_FrobeniusDegreeNonneg_OPEN 3541 := fun r => by
  have hap : (a_p 3541 : ℝ) = 12 := by exact_mod_cast BSD_ap_p3541
  have key : r ^ 2 - (a_p 3541 : ℝ) * r + ((3541 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 14020/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3547 : BSD_FrobeniusDegreeNonneg_OPEN 3547 := fun r => by
  have hap : (a_p 3547 : ℝ) = 107 := by exact_mod_cast BSD_ap_p3547
  have key : r ^ 2 - (a_p 3547 : ℝ) * r + ((3547 : ℕ) : ℝ) =
      (r - 107/2) ^ 2 + 2739/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (107 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3557 : BSD_FrobeniusDegreeNonneg_OPEN 3557 := fun r => by
  have hap : (a_p 3557 : ℝ) = 59 := by exact_mod_cast BSD_ap_p3557
  have key : r ^ 2 - (a_p 3557 : ℝ) * r + ((3557 : ℕ) : ℝ) =
      (r - 59/2) ^ 2 + 10747/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (59 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3559 : BSD_FrobeniusDegreeNonneg_OPEN 3559 := fun r => by
  have hap : (a_p 3559 : ℝ) = -16 := by exact_mod_cast BSD_ap_p3559
  have key : r ^ 2 - (a_p 3559 : ℝ) * r + ((3559 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 13980/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3571 : BSD_FrobeniusDegreeNonneg_OPEN 3571 := fun r => by
  have hap : (a_p 3571 : ℝ) = -118 := by exact_mod_cast BSD_ap_p3571
  have key : r ^ 2 - (a_p 3571 : ℝ) * r + ((3571 : ℕ) : ℝ) =
      (r + 118/2) ^ 2 + 360/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (118 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3581 : BSD_FrobeniusDegreeNonneg_OPEN 3581 := fun r => by
  have hap : (a_p 3581 : ℝ) = -96 := by exact_mod_cast BSD_ap_p3581
  have key : r ^ 2 - (a_p 3581 : ℝ) * r + ((3581 : ℕ) : ℝ) =
      (r + 96/2) ^ 2 + 5108/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (96 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3583 : BSD_FrobeniusDegreeNonneg_OPEN 3583 := fun r => by
  have hap : (a_p 3583 : ℝ) = 50 := by exact_mod_cast BSD_ap_p3583
  have key : r ^ 2 - (a_p 3583 : ℝ) * r + ((3583 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 11832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3593 : BSD_FrobeniusDegreeNonneg_OPEN 3593 := fun r => by
  have hap : (a_p 3593 : ℝ) = 76 := by exact_mod_cast BSD_ap_p3593
  have key : r ^ 2 - (a_p 3593 : ℝ) * r + ((3593 : ℕ) : ℝ) =
      (r - 76/2) ^ 2 + 8596/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (76 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3607 : BSD_FrobeniusDegreeNonneg_OPEN 3607 := fun r => by
  have hap : (a_p 3607 : ℝ) = 42 := by exact_mod_cast BSD_ap_p3607
  have key : r ^ 2 - (a_p 3607 : ℝ) * r + ((3607 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 12664/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3613 : BSD_FrobeniusDegreeNonneg_OPEN 3613 := fun r => by
  have hap : (a_p 3613 : ℝ) = 14 := by exact_mod_cast BSD_ap_p3613
  have key : r ^ 2 - (a_p 3613 : ℝ) * r + ((3613 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 14256/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3617 : BSD_FrobeniusDegreeNonneg_OPEN 3617 := fun r => by
  have hap : (a_p 3617 : ℝ) = -57 := by exact_mod_cast BSD_ap_p3617
  have key : r ^ 2 - (a_p 3617 : ℝ) * r + ((3617 : ℕ) : ℝ) =
      (r + 57/2) ^ 2 + 11219/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (57 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3623 : BSD_FrobeniusDegreeNonneg_OPEN 3623 := fun r => by
  have hap : (a_p 3623 : ℝ) = 48 := by exact_mod_cast BSD_ap_p3623
  have key : r ^ 2 - (a_p 3623 : ℝ) * r + ((3623 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 12188/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3631 : BSD_FrobeniusDegreeNonneg_OPEN 3631 := fun r => by
  have hap : (a_p 3631 : ℝ) = 48 := by exact_mod_cast BSD_ap_p3631
  have key : r ^ 2 - (a_p 3631 : ℝ) * r + ((3631 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 12220/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3637 : BSD_FrobeniusDegreeNonneg_OPEN 3637 := fun r => by
  have hap : (a_p 3637 : ℝ) = 58 := by exact_mod_cast BSD_ap_p3637
  have key : r ^ 2 - (a_p 3637 : ℝ) * r + ((3637 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 11184/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3643 : BSD_FrobeniusDegreeNonneg_OPEN 3643 := fun r => by
  have hap : (a_p 3643 : ℝ) = -74 := by exact_mod_cast BSD_ap_p3643
  have key : r ^ 2 - (a_p 3643 : ℝ) * r + ((3643 : ℕ) : ℝ) =
      (r + 74/2) ^ 2 + 9096/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (74 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3659 : BSD_FrobeniusDegreeNonneg_OPEN 3659 := fun r => by
  have hap : (a_p 3659 : ℝ) = 102 := by exact_mod_cast BSD_ap_p3659
  have key : r ^ 2 - (a_p 3659 : ℝ) * r + ((3659 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 4232/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3671 : BSD_FrobeniusDegreeNonneg_OPEN 3671 := fun r => by
  have hap : (a_p 3671 : ℝ) = 96 := by exact_mod_cast BSD_ap_p3671
  have key : r ^ 2 - (a_p 3671 : ℝ) * r + ((3671 : ℕ) : ℝ) =
      (r - 96/2) ^ 2 + 5468/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (96 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3673 : BSD_FrobeniusDegreeNonneg_OPEN 3673 := fun r => by
  have hap : (a_p 3673 : ℝ) = -14 := by exact_mod_cast BSD_ap_p3673
  have key : r ^ 2 - (a_p 3673 : ℝ) * r + ((3673 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 14496/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3677 : BSD_FrobeniusDegreeNonneg_OPEN 3677 := fun r => by
  have hap : (a_p 3677 : ℝ) = -6 := by exact_mod_cast BSD_ap_p3677
  have key : r ^ 2 - (a_p 3677 : ℝ) * r + ((3677 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 14672/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3691 : BSD_FrobeniusDegreeNonneg_OPEN 3691 := fun r => by
  have hap : (a_p 3691 : ℝ) = 58 := by exact_mod_cast BSD_ap_p3691
  have key : r ^ 2 - (a_p 3691 : ℝ) * r + ((3691 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 11400/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3697 : BSD_FrobeniusDegreeNonneg_OPEN 3697 := fun r => by
  have hap : (a_p 3697 : ℝ) = -83 := by exact_mod_cast BSD_ap_p3697
  have key : r ^ 2 - (a_p 3697 : ℝ) * r + ((3697 : ℕ) : ℝ) =
      (r + 83/2) ^ 2 + 7899/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (83 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3701 : BSD_FrobeniusDegreeNonneg_OPEN 3701 := fun r => by
  have hap : (a_p 3701 : ℝ) = 42 := by exact_mod_cast BSD_ap_p3701
  have key : r ^ 2 - (a_p 3701 : ℝ) * r + ((3701 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 13040/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3709 : BSD_FrobeniusDegreeNonneg_OPEN 3709 := fun r => by
  have hap : (a_p 3709 : ℝ) = -38 := by exact_mod_cast BSD_ap_p3709
  have key : r ^ 2 - (a_p 3709 : ℝ) * r + ((3709 : ℕ) : ℝ) =
      (r + 38/2) ^ 2 + 13392/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3719 : BSD_FrobeniusDegreeNonneg_OPEN 3719 := fun r => by
  have hap : (a_p 3719 : ℝ) = 93 := by exact_mod_cast BSD_ap_p3719
  have key : r ^ 2 - (a_p 3719 : ℝ) * r + ((3719 : ℕ) : ℝ) =
      (r - 93/2) ^ 2 + 6227/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (93 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3727 : BSD_FrobeniusDegreeNonneg_OPEN 3727 := fun r => by
  have hap : (a_p 3727 : ℝ) = 3 := by exact_mod_cast BSD_ap_p3727
  have key : r ^ 2 - (a_p 3727 : ℝ) * r + ((3727 : ℕ) : ℝ) =
      (r - 3/2) ^ 2 + 14899/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (3 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3733 : BSD_FrobeniusDegreeNonneg_OPEN 3733 := fun r => by
  have hap : (a_p 3733 : ℝ) = 38 := by exact_mod_cast BSD_ap_p3733
  have key : r ^ 2 - (a_p 3733 : ℝ) * r + ((3733 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 13488/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3739 : BSD_FrobeniusDegreeNonneg_OPEN 3739 := fun r => by
  have hap : (a_p 3739 : ℝ) = 30 := by exact_mod_cast BSD_ap_p3739
  have key : r ^ 2 - (a_p 3739 : ℝ) * r + ((3739 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 14056/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3761 : BSD_FrobeniusDegreeNonneg_OPEN 3761 := fun r => by
  have hap : (a_p 3761 : ℝ) = 44 := by exact_mod_cast BSD_ap_p3761
  have key : r ^ 2 - (a_p 3761 : ℝ) * r + ((3761 : ℕ) : ℝ) =
      (r - 44/2) ^ 2 + 13108/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (44 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3767 : BSD_FrobeniusDegreeNonneg_OPEN 3767 := fun r => by
  have hap : (a_p 3767 : ℝ) = -103 := by exact_mod_cast BSD_ap_p3767
  have key : r ^ 2 - (a_p 3767 : ℝ) * r + ((3767 : ℕ) : ℝ) =
      (r + 103/2) ^ 2 + 4459/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (103 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3769 : BSD_FrobeniusDegreeNonneg_OPEN 3769 := fun r => by
  have hap : (a_p 3769 : ℝ) = 26 := by exact_mod_cast BSD_ap_p3769
  have key : r ^ 2 - (a_p 3769 : ℝ) * r + ((3769 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 14400/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3779 : BSD_FrobeniusDegreeNonneg_OPEN 3779 := fun r => by
  have hap : (a_p 3779 : ℝ) = 92 := by exact_mod_cast BSD_ap_p3779
  have key : r ^ 2 - (a_p 3779 : ℝ) * r + ((3779 : ℕ) : ℝ) =
      (r - 92/2) ^ 2 + 6652/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (92 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3793 : BSD_FrobeniusDegreeNonneg_OPEN 3793 := fun r => by
  have hap : (a_p 3793 : ℝ) = -38 := by exact_mod_cast BSD_ap_p3793
  have key : r ^ 2 - (a_p 3793 : ℝ) * r + ((3793 : ℕ) : ℝ) =
      (r + 38/2) ^ 2 + 13728/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3797 : BSD_FrobeniusDegreeNonneg_OPEN 3797 := fun r => by
  have hap : (a_p 3797 : ℝ) = -74 := by exact_mod_cast BSD_ap_p3797
  have key : r ^ 2 - (a_p 3797 : ℝ) * r + ((3797 : ℕ) : ℝ) =
      (r + 74/2) ^ 2 + 9712/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (74 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3803 : BSD_FrobeniusDegreeNonneg_OPEN 3803 := fun r => by
  have hap : (a_p 3803 : ℝ) = -14 := by exact_mod_cast BSD_ap_p3803
  have key : r ^ 2 - (a_p 3803 : ℝ) * r + ((3803 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 15016/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3821 : BSD_FrobeniusDegreeNonneg_OPEN 3821 := fun r => by
  have hap : (a_p 3821 : ℝ) = 61 := by exact_mod_cast BSD_ap_p3821
  have key : r ^ 2 - (a_p 3821 : ℝ) * r + ((3821 : ℕ) : ℝ) =
      (r - 61/2) ^ 2 + 11563/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (61 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3823 : BSD_FrobeniusDegreeNonneg_OPEN 3823 := fun r => by
  have hap : (a_p 3823 : ℝ) = -62 := by exact_mod_cast BSD_ap_p3823
  have key : r ^ 2 - (a_p 3823 : ℝ) * r + ((3823 : ℕ) : ℝ) =
      (r + 62/2) ^ 2 + 11448/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (62 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3833 : BSD_FrobeniusDegreeNonneg_OPEN 3833 := fun r => by
  have hap : (a_p 3833 : ℝ) = 93 := by exact_mod_cast BSD_ap_p3833
  have key : r ^ 2 - (a_p 3833 : ℝ) * r + ((3833 : ℕ) : ℝ) =
      (r - 93/2) ^ 2 + 6683/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (93 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3847 : BSD_FrobeniusDegreeNonneg_OPEN 3847 := fun r => by
  have hap : (a_p 3847 : ℝ) = -88 := by exact_mod_cast BSD_ap_p3847
  have key : r ^ 2 - (a_p 3847 : ℝ) * r + ((3847 : ℕ) : ℝ) =
      (r + 88/2) ^ 2 + 7644/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (88 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3851 : BSD_FrobeniusDegreeNonneg_OPEN 3851 := fun r => by
  have hap : (a_p 3851 : ℝ) = -85 := by exact_mod_cast BSD_ap_p3851
  have key : r ^ 2 - (a_p 3851 : ℝ) * r + ((3851 : ℕ) : ℝ) =
      (r + 85/2) ^ 2 + 8179/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (85 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3853 : BSD_FrobeniusDegreeNonneg_OPEN 3853 := fun r => by
  have hap : (a_p 3853 : ℝ) = 46 := by exact_mod_cast BSD_ap_p3853
  have key : r ^ 2 - (a_p 3853 : ℝ) * r + ((3853 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 13296/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3863 : BSD_FrobeniusDegreeNonneg_OPEN 3863 := fun r => by
  have hap : (a_p 3863 : ℝ) = -84 := by exact_mod_cast BSD_ap_p3863
  have key : r ^ 2 - (a_p 3863 : ℝ) * r + ((3863 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 8396/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3877 : BSD_FrobeniusDegreeNonneg_OPEN 3877 := fun r => by
  have hap : (a_p 3877 : ℝ) = 6 := by exact_mod_cast BSD_ap_p3877
  have key : r ^ 2 - (a_p 3877 : ℝ) * r + ((3877 : ℕ) : ℝ) =
      (r - 6/2) ^ 2 + 15472/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3881 : BSD_FrobeniusDegreeNonneg_OPEN 3881 := fun r => by
  have hap : (a_p 3881 : ℝ) = 105 := by exact_mod_cast BSD_ap_p3881
  have key : r ^ 2 - (a_p 3881 : ℝ) * r + ((3881 : ℕ) : ℝ) =
      (r - 105/2) ^ 2 + 4499/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (105 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3889 : BSD_FrobeniusDegreeNonneg_OPEN 3889 := fun r => by
  have hap : (a_p 3889 : ℝ) = 38 := by exact_mod_cast BSD_ap_p3889
  have key : r ^ 2 - (a_p 3889 : ℝ) * r + ((3889 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 14112/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3907 : BSD_FrobeniusDegreeNonneg_OPEN 3907 := fun r => by
  have hap : (a_p 3907 : ℝ) = 58 := by exact_mod_cast BSD_ap_p3907
  have key : r ^ 2 - (a_p 3907 : ℝ) * r + ((3907 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 12264/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3911 : BSD_FrobeniusDegreeNonneg_OPEN 3911 := fun r => by
  have hap : (a_p 3911 : ℝ) = 64 := by exact_mod_cast BSD_ap_p3911
  have key : r ^ 2 - (a_p 3911 : ℝ) * r + ((3911 : ℕ) : ℝ) =
      (r - 64/2) ^ 2 + 11548/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (64 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3917 : BSD_FrobeniusDegreeNonneg_OPEN 3917 := fun r => by
  have hap : (a_p 3917 : ℝ) = -21 := by exact_mod_cast BSD_ap_p3917
  have key : r ^ 2 - (a_p 3917 : ℝ) * r + ((3917 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 15227/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3919 : BSD_FrobeniusDegreeNonneg_OPEN 3919 := fun r => by
  have hap : (a_p 3919 : ℝ) = -112 := by exact_mod_cast BSD_ap_p3919
  have key : r ^ 2 - (a_p 3919 : ℝ) * r + ((3919 : ℕ) : ℝ) =
      (r + 112/2) ^ 2 + 3132/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (112 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3923 : BSD_FrobeniusDegreeNonneg_OPEN 3923 := fun r => by
  have hap : (a_p 3923 : ℝ) = -24 := by exact_mod_cast BSD_ap_p3923
  have key : r ^ 2 - (a_p 3923 : ℝ) * r + ((3923 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 15116/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3929 : BSD_FrobeniusDegreeNonneg_OPEN 3929 := fun r => by
  have hap : (a_p 3929 : ℝ) = -74 := by exact_mod_cast BSD_ap_p3929
  have key : r ^ 2 - (a_p 3929 : ℝ) * r + ((3929 : ℕ) : ℝ) =
      (r + 74/2) ^ 2 + 10240/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (74 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3931 : BSD_FrobeniusDegreeNonneg_OPEN 3931 := fun r => by
  have hap : (a_p 3931 : ℝ) = -107 := by exact_mod_cast BSD_ap_p3931
  have key : r ^ 2 - (a_p 3931 : ℝ) * r + ((3931 : ℕ) : ℝ) =
      (r + 107/2) ^ 2 + 4275/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (107 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3943 : BSD_FrobeniusDegreeNonneg_OPEN 3943 := fun r => by
  have hap : (a_p 3943 : ℝ) = 0 := by exact_mod_cast BSD_ap_p3943
  have key : r ^ 2 - (a_p 3943 : ℝ) * r + ((3943 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 15772/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3947 : BSD_FrobeniusDegreeNonneg_OPEN 3947 := fun r => by
  have hap : (a_p 3947 : ℝ) = 63 := by exact_mod_cast BSD_ap_p3947
  have key : r ^ 2 - (a_p 3947 : ℝ) * r + ((3947 : ℕ) : ℝ) =
      (r - 63/2) ^ 2 + 11819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (63 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3967 : BSD_FrobeniusDegreeNonneg_OPEN 3967 := fun r => by
  have hap : (a_p 3967 : ℝ) = -24 := by exact_mod_cast BSD_ap_p3967
  have key : r ^ 2 - (a_p 3967 : ℝ) * r + ((3967 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 15292/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p3989 : BSD_FrobeniusDegreeNonneg_OPEN 3989 := fun r => by
  have hap : (a_p 3989 : ℝ) = -58 := by exact_mod_cast BSD_ap_p3989
  have key : r ^ 2 - (a_p 3989 : ℝ) * r + ((3989 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 12592/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4001 : BSD_FrobeniusDegreeNonneg_OPEN 4001 := fun r => by
  have hap : (a_p 4001 : ℝ) = -6 := by exact_mod_cast BSD_ap_p4001
  have key : r ^ 2 - (a_p 4001 : ℝ) * r + ((4001 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 15968/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4003 : BSD_FrobeniusDegreeNonneg_OPEN 4003 := fun r => by
  have hap : (a_p 4003 : ℝ) = 114 := by exact_mod_cast BSD_ap_p4003
  have key : r ^ 2 - (a_p 4003 : ℝ) * r + ((4003 : ℕ) : ℝ) =
      (r - 114/2) ^ 2 + 3016/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (114 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4007 : BSD_FrobeniusDegreeNonneg_OPEN 4007 := fun r => by
  have hap : (a_p 4007 : ℝ) = -24 := by exact_mod_cast BSD_ap_p4007
  have key : r ^ 2 - (a_p 4007 : ℝ) * r + ((4007 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 15452/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4013 : BSD_FrobeniusDegreeNonneg_OPEN 4013 := fun r => by
  have hap : (a_p 4013 : ℝ) = -46 := by exact_mod_cast BSD_ap_p4013
  have key : r ^ 2 - (a_p 4013 : ℝ) * r + ((4013 : ℕ) : ℝ) =
      (r + 46/2) ^ 2 + 13936/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4019 : BSD_FrobeniusDegreeNonneg_OPEN 4019 := fun r => by
  have hap : (a_p 4019 : ℝ) = 5 := by exact_mod_cast BSD_ap_p4019
  have key : r ^ 2 - (a_p 4019 : ℝ) * r + ((4019 : ℕ) : ℝ) =
      (r - 5/2) ^ 2 + 16051/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (5 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4021 : BSD_FrobeniusDegreeNonneg_OPEN 4021 := fun r => by
  have hap : (a_p 4021 : ℝ) = 32 := by exact_mod_cast BSD_ap_p4021
  have key : r ^ 2 - (a_p 4021 : ℝ) * r + ((4021 : ℕ) : ℝ) =
      (r - 32/2) ^ 2 + 15060/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4027 : BSD_FrobeniusDegreeNonneg_OPEN 4027 := fun r => by
  have hap : (a_p 4027 : ℝ) = 28 := by exact_mod_cast BSD_ap_p4027
  have key : r ^ 2 - (a_p 4027 : ℝ) * r + ((4027 : ℕ) : ℝ) =
      (r - 28/2) ^ 2 + 15324/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (28 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4049 : BSD_FrobeniusDegreeNonneg_OPEN 4049 := fun r => by
  have hap : (a_p 4049 : ℝ) = 99 := by exact_mod_cast BSD_ap_p4049
  have key : r ^ 2 - (a_p 4049 : ℝ) * r + ((4049 : ℕ) : ℝ) =
      (r - 99/2) ^ 2 + 6395/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (99 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4051 : BSD_FrobeniusDegreeNonneg_OPEN 4051 := fun r => by
  have hap : (a_p 4051 : ℝ) = -21 := by exact_mod_cast BSD_ap_p4051
  have key : r ^ 2 - (a_p 4051 : ℝ) * r + ((4051 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 15763/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4057 : BSD_FrobeniusDegreeNonneg_OPEN 4057 := fun r => by
  have hap : (a_p 4057 : ℝ) = -85 := by exact_mod_cast BSD_ap_p4057
  have key : r ^ 2 - (a_p 4057 : ℝ) * r + ((4057 : ℕ) : ℝ) =
      (r + 85/2) ^ 2 + 9003/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (85 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4073 : BSD_FrobeniusDegreeNonneg_OPEN 4073 := fun r => by
  have hap : (a_p 4073 : ℝ) = 41 := by exact_mod_cast BSD_ap_p4073
  have key : r ^ 2 - (a_p 4073 : ℝ) * r + ((4073 : ℕ) : ℝ) =
      (r - 41/2) ^ 2 + 14611/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (41 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4079 : BSD_FrobeniusDegreeNonneg_OPEN 4079 := fun r => by
  have hap : (a_p 4079 : ℝ) = -96 := by exact_mod_cast BSD_ap_p4079
  have key : r ^ 2 - (a_p 4079 : ℝ) * r + ((4079 : ℕ) : ℝ) =
      (r + 96/2) ^ 2 + 7100/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (96 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4091 : BSD_FrobeniusDegreeNonneg_OPEN 4091 := fun r => by
  have hap : (a_p 4091 : ℝ) = 0 := by exact_mod_cast BSD_ap_p4091
  have key : r ^ 2 - (a_p 4091 : ℝ) * r + ((4091 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 16364/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4093 : BSD_FrobeniusDegreeNonneg_OPEN 4093 := fun r => by
  have hap : (a_p 4093 : ℝ) = 94 := by exact_mod_cast BSD_ap_p4093
  have key : r ^ 2 - (a_p 4093 : ℝ) * r + ((4093 : ℕ) : ℝ) =
      (r - 94/2) ^ 2 + 7536/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (94 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4099 : BSD_FrobeniusDegreeNonneg_OPEN 4099 := fun r => by
  have hap : (a_p 4099 : ℝ) = 100 := by exact_mod_cast BSD_ap_p4099
  have key : r ^ 2 - (a_p 4099 : ℝ) * r + ((4099 : ℕ) : ℝ) =
      (r - 100/2) ^ 2 + 6396/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (100 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4111 : BSD_FrobeniusDegreeNonneg_OPEN 4111 := fun r => by
  have hap : (a_p 4111 : ℝ) = -20 := by exact_mod_cast BSD_ap_p4111
  have key : r ^ 2 - (a_p 4111 : ℝ) * r + ((4111 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 16044/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4127 : BSD_FrobeniusDegreeNonneg_OPEN 4127 := fun r => by
  have hap : (a_p 4127 : ℝ) = 98 := by exact_mod_cast BSD_ap_p4127
  have key : r ^ 2 - (a_p 4127 : ℝ) * r + ((4127 : ℕ) : ℝ) =
      (r - 98/2) ^ 2 + 6904/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (98 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4129 : BSD_FrobeniusDegreeNonneg_OPEN 4129 := fun r => by
  have hap : (a_p 4129 : ℝ) = -43 := by exact_mod_cast BSD_ap_p4129
  have key : r ^ 2 - (a_p 4129 : ℝ) * r + ((4129 : ℕ) : ℝ) =
      (r + 43/2) ^ 2 + 14667/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (43 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4133 : BSD_FrobeniusDegreeNonneg_OPEN 4133 := fun r => by
  have hap : (a_p 4133 : ℝ) = 102 := by exact_mod_cast BSD_ap_p4133
  have key : r ^ 2 - (a_p 4133 : ℝ) * r + ((4133 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 6128/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4139 : BSD_FrobeniusDegreeNonneg_OPEN 4139 := fun r => by
  have hap : (a_p 4139 : ℝ) = -40 := by exact_mod_cast BSD_ap_p4139
  have key : r ^ 2 - (a_p 4139 : ℝ) * r + ((4139 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 14956/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4153 : BSD_FrobeniusDegreeNonneg_OPEN 4153 := fun r => by
  have hap : (a_p 4153 : ℝ) = -42 := by exact_mod_cast BSD_ap_p4153
  have key : r ^ 2 - (a_p 4153 : ℝ) * r + ((4153 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 14848/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4157 : BSD_FrobeniusDegreeNonneg_OPEN 4157 := fun r => by
  have hap : (a_p 4157 : ℝ) = 58 := by exact_mod_cast BSD_ap_p4157
  have key : r ^ 2 - (a_p 4157 : ℝ) * r + ((4157 : ℕ) : ℝ) =
      (r - 58/2) ^ 2 + 13264/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4159 : BSD_FrobeniusDegreeNonneg_OPEN 4159 := fun r => by
  have hap : (a_p 4159 : ℝ) = -75 := by exact_mod_cast BSD_ap_p4159
  have key : r ^ 2 - (a_p 4159 : ℝ) * r + ((4159 : ℕ) : ℝ) =
      (r + 75/2) ^ 2 + 11011/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (75 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4177 : BSD_FrobeniusDegreeNonneg_OPEN 4177 := fun r => by
  have hap : (a_p 4177 : ℝ) = 102 := by exact_mod_cast BSD_ap_p4177
  have key : r ^ 2 - (a_p 4177 : ℝ) * r + ((4177 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 6304/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4201 : BSD_FrobeniusDegreeNonneg_OPEN 4201 := fun r => by
  have hap : (a_p 4201 : ℝ) = -22 := by exact_mod_cast BSD_ap_p4201
  have key : r ^ 2 - (a_p 4201 : ℝ) * r + ((4201 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 16320/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4211 : BSD_FrobeniusDegreeNonneg_OPEN 4211 := fun r => by
  have hap : (a_p 4211 : ℝ) = -83 := by exact_mod_cast BSD_ap_p4211
  have key : r ^ 2 - (a_p 4211 : ℝ) * r + ((4211 : ℕ) : ℝ) =
      (r + 83/2) ^ 2 + 9955/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (83 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4217 : BSD_FrobeniusDegreeNonneg_OPEN 4217 := fun r => by
  have hap : (a_p 4217 : ℝ) = -105 := by exact_mod_cast BSD_ap_p4217
  have key : r ^ 2 - (a_p 4217 : ℝ) * r + ((4217 : ℕ) : ℝ) =
      (r + 105/2) ^ 2 + 5843/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (105 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4219 : BSD_FrobeniusDegreeNonneg_OPEN 4219 := fun r => by
  have hap : (a_p 4219 : ℝ) = -18 := by exact_mod_cast BSD_ap_p4219
  have key : r ^ 2 - (a_p 4219 : ℝ) * r + ((4219 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 16552/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4229 : BSD_FrobeniusDegreeNonneg_OPEN 4229 := fun r => by
  have hap : (a_p 4229 : ℝ) = -15 := by exact_mod_cast BSD_ap_p4229
  have key : r ^ 2 - (a_p 4229 : ℝ) * r + ((4229 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 16691/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4231 : BSD_FrobeniusDegreeNonneg_OPEN 4231 := fun r => by
  have hap : (a_p 4231 : ℝ) = -102 := by exact_mod_cast BSD_ap_p4231
  have key : r ^ 2 - (a_p 4231 : ℝ) * r + ((4231 : ℕ) : ℝ) =
      (r + 102/2) ^ 2 + 6520/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (102 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4241 : BSD_FrobeniusDegreeNonneg_OPEN 4241 := fun r => by
  have hap : (a_p 4241 : ℝ) = -58 := by exact_mod_cast BSD_ap_p4241
  have key : r ^ 2 - (a_p 4241 : ℝ) * r + ((4241 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 13600/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4243 : BSD_FrobeniusDegreeNonneg_OPEN 4243 := fun r => by
  have hap : (a_p 4243 : ℝ) = 26 := by exact_mod_cast BSD_ap_p4243
  have key : r ^ 2 - (a_p 4243 : ℝ) * r + ((4243 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 16296/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4253 : BSD_FrobeniusDegreeNonneg_OPEN 4253 := fun r => by
  have hap : (a_p 4253 : ℝ) = -54 := by exact_mod_cast BSD_ap_p4253
  have key : r ^ 2 - (a_p 4253 : ℝ) * r + ((4253 : ℕ) : ℝ) =
      (r + 54/2) ^ 2 + 14096/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4259 : BSD_FrobeniusDegreeNonneg_OPEN 4259 := fun r => by
  have hap : (a_p 4259 : ℝ) = 72 := by exact_mod_cast BSD_ap_p4259
  have key : r ^ 2 - (a_p 4259 : ℝ) * r + ((4259 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 11852/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4261 : BSD_FrobeniusDegreeNonneg_OPEN 4261 := fun r => by
  have hap : (a_p 4261 : ℝ) = 31 := by exact_mod_cast BSD_ap_p4261
  have key : r ^ 2 - (a_p 4261 : ℝ) * r + ((4261 : ℕ) : ℝ) =
      (r - 31/2) ^ 2 + 16083/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (31 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4271 : BSD_FrobeniusDegreeNonneg_OPEN 4271 := fun r => by
  have hap : (a_p 4271 : ℝ) = -75 := by exact_mod_cast BSD_ap_p4271
  have key : r ^ 2 - (a_p 4271 : ℝ) * r + ((4271 : ℕ) : ℝ) =
      (r + 75/2) ^ 2 + 11459/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (75 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4273 : BSD_FrobeniusDegreeNonneg_OPEN 4273 := fun r => by
  have hap : (a_p 4273 : ℝ) = 51 := by exact_mod_cast BSD_ap_p4273
  have key : r ^ 2 - (a_p 4273 : ℝ) * r + ((4273 : ℕ) : ℝ) =
      (r - 51/2) ^ 2 + 14491/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (51 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4283 : BSD_FrobeniusDegreeNonneg_OPEN 4283 := fun r => by
  have hap : (a_p 4283 : ℝ) = 13 := by exact_mod_cast BSD_ap_p4283
  have key : r ^ 2 - (a_p 4283 : ℝ) * r + ((4283 : ℕ) : ℝ) =
      (r - 13/2) ^ 2 + 16963/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (13 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4289 : BSD_FrobeniusDegreeNonneg_OPEN 4289 := fun r => by
  have hap : (a_p 4289 : ℝ) = -50 := by exact_mod_cast BSD_ap_p4289
  have key : r ^ 2 - (a_p 4289 : ℝ) * r + ((4289 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 14656/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4297 : BSD_FrobeniusDegreeNonneg_OPEN 4297 := fun r => by
  have hap : (a_p 4297 : ℝ) = 8 := by exact_mod_cast BSD_ap_p4297
  have key : r ^ 2 - (a_p 4297 : ℝ) * r + ((4297 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 17124/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4327 : BSD_FrobeniusDegreeNonneg_OPEN 4327 := fun r => by
  have hap : (a_p 4327 : ℝ) = 107 := by exact_mod_cast BSD_ap_p4327
  have key : r ^ 2 - (a_p 4327 : ℝ) * r + ((4327 : ℕ) : ℝ) =
      (r - 107/2) ^ 2 + 5859/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (107 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4337 : BSD_FrobeniusDegreeNonneg_OPEN 4337 := fun r => by
  have hap : (a_p 4337 : ℝ) = 18 := by exact_mod_cast BSD_ap_p4337
  have key : r ^ 2 - (a_p 4337 : ℝ) * r + ((4337 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 17024/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4339 : BSD_FrobeniusDegreeNonneg_OPEN 4339 := fun r => by
  have hap : (a_p 4339 : ℝ) = -77 := by exact_mod_cast BSD_ap_p4339
  have key : r ^ 2 - (a_p 4339 : ℝ) * r + ((4339 : ℕ) : ℝ) =
      (r + 77/2) ^ 2 + 11427/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (77 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4349 : BSD_FrobeniusDegreeNonneg_OPEN 4349 := fun r => by
  have hap : (a_p 4349 : ℝ) = -18 := by exact_mod_cast BSD_ap_p4349
  have key : r ^ 2 - (a_p 4349 : ℝ) * r + ((4349 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 17072/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4357 : BSD_FrobeniusDegreeNonneg_OPEN 4357 := fun r => by
  have hap : (a_p 4357 : ℝ) = 117 := by exact_mod_cast BSD_ap_p4357
  have key : r ^ 2 - (a_p 4357 : ℝ) * r + ((4357 : ℕ) : ℝ) =
      (r - 117/2) ^ 2 + 3739/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (117 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4363 : BSD_FrobeniusDegreeNonneg_OPEN 4363 := fun r => by
  have hap : (a_p 4363 : ℝ) = 118 := by exact_mod_cast BSD_ap_p4363
  have key : r ^ 2 - (a_p 4363 : ℝ) * r + ((4363 : ℕ) : ℝ) =
      (r - 118/2) ^ 2 + 3528/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (118 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4373 : BSD_FrobeniusDegreeNonneg_OPEN 4373 := fun r => by
  have hap : (a_p 4373 : ℝ) = 96 := by exact_mod_cast BSD_ap_p4373
  have key : r ^ 2 - (a_p 4373 : ℝ) * r + ((4373 : ℕ) : ℝ) =
      (r - 96/2) ^ 2 + 8276/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (96 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4391 : BSD_FrobeniusDegreeNonneg_OPEN 4391 := fun r => by
  have hap : (a_p 4391 : ℝ) = -108 := by exact_mod_cast BSD_ap_p4391
  have key : r ^ 2 - (a_p 4391 : ℝ) * r + ((4391 : ℕ) : ℝ) =
      (r + 108/2) ^ 2 + 5900/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (108 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4397 : BSD_FrobeniusDegreeNonneg_OPEN 4397 := fun r => by
  have hap : (a_p 4397 : ℝ) = 52 := by exact_mod_cast BSD_ap_p4397
  have key : r ^ 2 - (a_p 4397 : ℝ) * r + ((4397 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 14884/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4409 : BSD_FrobeniusDegreeNonneg_OPEN 4409 := fun r => by
  have hap : (a_p 4409 : ℝ) = 54 := by exact_mod_cast BSD_ap_p4409
  have key : r ^ 2 - (a_p 4409 : ℝ) * r + ((4409 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 14720/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4421 : BSD_FrobeniusDegreeNonneg_OPEN 4421 := fun r => by
  have hap : (a_p 4421 : ℝ) = 12 := by exact_mod_cast BSD_ap_p4421
  have key : r ^ 2 - (a_p 4421 : ℝ) * r + ((4421 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 17540/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4423 : BSD_FrobeniusDegreeNonneg_OPEN 4423 := fun r => by
  have hap : (a_p 4423 : ℝ) = 61 := by exact_mod_cast BSD_ap_p4423
  have key : r ^ 2 - (a_p 4423 : ℝ) * r + ((4423 : ℕ) : ℝ) =
      (r - 61/2) ^ 2 + 13971/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (61 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4441 : BSD_FrobeniusDegreeNonneg_OPEN 4441 := fun r => by
  have hap : (a_p 4441 : ℝ) = 64 := by exact_mod_cast BSD_ap_p4441
  have key : r ^ 2 - (a_p 4441 : ℝ) * r + ((4441 : ℕ) : ℝ) =
      (r - 64/2) ^ 2 + 13668/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (64 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4447 : BSD_FrobeniusDegreeNonneg_OPEN 4447 := fun r => by
  have hap : (a_p 4447 : ℝ) = -41 := by exact_mod_cast BSD_ap_p4447
  have key : r ^ 2 - (a_p 4447 : ℝ) * r + ((4447 : ℕ) : ℝ) =
      (r + 41/2) ^ 2 + 16107/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (41 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4451 : BSD_FrobeniusDegreeNonneg_OPEN 4451 := fun r => by
  have hap : (a_p 4451 : ℝ) = 98 := by exact_mod_cast BSD_ap_p4451
  have key : r ^ 2 - (a_p 4451 : ℝ) * r + ((4451 : ℕ) : ℝ) =
      (r - 98/2) ^ 2 + 8200/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (98 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4457 : BSD_FrobeniusDegreeNonneg_OPEN 4457 := fun r => by
  have hap : (a_p 4457 : ℝ) = -42 := by exact_mod_cast BSD_ap_p4457
  have key : r ^ 2 - (a_p 4457 : ℝ) * r + ((4457 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 16064/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4463 : BSD_FrobeniusDegreeNonneg_OPEN 4463 := fun r => by
  have hap : (a_p 4463 : ℝ) = 108 := by exact_mod_cast BSD_ap_p4463
  have key : r ^ 2 - (a_p 4463 : ℝ) * r + ((4463 : ℕ) : ℝ) =
      (r - 108/2) ^ 2 + 6188/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (108 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4481 : BSD_FrobeniusDegreeNonneg_OPEN 4481 := fun r => by
  have hap : (a_p 4481 : ℝ) = 102 := by exact_mod_cast BSD_ap_p4481
  have key : r ^ 2 - (a_p 4481 : ℝ) * r + ((4481 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 7520/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4483 : BSD_FrobeniusDegreeNonneg_OPEN 4483 := fun r => by
  have hap : (a_p 4483 : ℝ) = -24 := by exact_mod_cast BSD_ap_p4483
  have key : r ^ 2 - (a_p 4483 : ℝ) * r + ((4483 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 17356/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4493 : BSD_FrobeniusDegreeNonneg_OPEN 4493 := fun r => by
  have hap : (a_p 4493 : ℝ) = -21 := by exact_mod_cast BSD_ap_p4493
  have key : r ^ 2 - (a_p 4493 : ℝ) * r + ((4493 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 17531/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4507 : BSD_FrobeniusDegreeNonneg_OPEN 4507 := fun r => by
  have hap : (a_p 4507 : ℝ) = -26 := by exact_mod_cast BSD_ap_p4507
  have key : r ^ 2 - (a_p 4507 : ℝ) * r + ((4507 : ℕ) : ℝ) =
      (r + 26/2) ^ 2 + 17352/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (26 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4513 : BSD_FrobeniusDegreeNonneg_OPEN 4513 := fun r => by
  have hap : (a_p 4513 : ℝ) = 1 := by exact_mod_cast BSD_ap_p4513
  have key : r ^ 2 - (a_p 4513 : ℝ) * r + ((4513 : ℕ) : ℝ) =
      (r - 1/2) ^ 2 + 18051/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (1 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4517 : BSD_FrobeniusDegreeNonneg_OPEN 4517 := fun r => by
  have hap : (a_p 4517 : ℝ) = 108 := by exact_mod_cast BSD_ap_p4517
  have key : r ^ 2 - (a_p 4517 : ℝ) * r + ((4517 : ℕ) : ℝ) =
      (r - 108/2) ^ 2 + 6404/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (108 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4519 : BSD_FrobeniusDegreeNonneg_OPEN 4519 := fun r => by
  have hap : (a_p 4519 : ℝ) = 23 := by exact_mod_cast BSD_ap_p4519
  have key : r ^ 2 - (a_p 4519 : ℝ) * r + ((4519 : ℕ) : ℝ) =
      (r - 23/2) ^ 2 + 17547/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (23 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4523 : BSD_FrobeniusDegreeNonneg_OPEN 4523 := fun r => by
  have hap : (a_p 4523 : ℝ) = 68 := by exact_mod_cast BSD_ap_p4523
  have key : r ^ 2 - (a_p 4523 : ℝ) * r + ((4523 : ℕ) : ℝ) =
      (r - 68/2) ^ 2 + 13468/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (68 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4547 : BSD_FrobeniusDegreeNonneg_OPEN 4547 := fun r => by
  have hap : (a_p 4547 : ℝ) = -12 := by exact_mod_cast BSD_ap_p4547
  have key : r ^ 2 - (a_p 4547 : ℝ) * r + ((4547 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 18044/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4549 : BSD_FrobeniusDegreeNonneg_OPEN 4549 := fun r => by
  have hap : (a_p 4549 : ℝ) = 76 := by exact_mod_cast BSD_ap_p4549
  have key : r ^ 2 - (a_p 4549 : ℝ) * r + ((4549 : ℕ) : ℝ) =
      (r - 76/2) ^ 2 + 12420/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (76 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4561 : BSD_FrobeniusDegreeNonneg_OPEN 4561 := fun r => by
  have hap : (a_p 4561 : ℝ) = 34 := by exact_mod_cast BSD_ap_p4561
  have key : r ^ 2 - (a_p 4561 : ℝ) * r + ((4561 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 17088/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4567 : BSD_FrobeniusDegreeNonneg_OPEN 4567 := fun r => by
  have hap : (a_p 4567 : ℝ) = -58 := by exact_mod_cast BSD_ap_p4567
  have key : r ^ 2 - (a_p 4567 : ℝ) * r + ((4567 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 14904/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4583 : BSD_FrobeniusDegreeNonneg_OPEN 4583 := fun r => by
  have hap : (a_p 4583 : ℝ) = -84 := by exact_mod_cast BSD_ap_p4583
  have key : r ^ 2 - (a_p 4583 : ℝ) * r + ((4583 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 11276/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4591 : BSD_FrobeniusDegreeNonneg_OPEN 4591 := fun r => by
  have hap : (a_p 4591 : ℝ) = -120 := by exact_mod_cast BSD_ap_p4591
  have key : r ^ 2 - (a_p 4591 : ℝ) * r + ((4591 : ℕ) : ℝ) =
      (r + 120/2) ^ 2 + 3964/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (120 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4597 : BSD_FrobeniusDegreeNonneg_OPEN 4597 := fun r => by
  have hap : (a_p 4597 : ℝ) = -16 := by exact_mod_cast BSD_ap_p4597
  have key : r ^ 2 - (a_p 4597 : ℝ) * r + ((4597 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 18132/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4603 : BSD_FrobeniusDegreeNonneg_OPEN 4603 := fun r => by
  have hap : (a_p 4603 : ℝ) = -59 := by exact_mod_cast BSD_ap_p4603
  have key : r ^ 2 - (a_p 4603 : ℝ) * r + ((4603 : ℕ) : ℝ) =
      (r + 59/2) ^ 2 + 14931/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (59 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4621 : BSD_FrobeniusDegreeNonneg_OPEN 4621 := fun r => by
  have hap : (a_p 4621 : ℝ) = -30 := by exact_mod_cast BSD_ap_p4621
  have key : r ^ 2 - (a_p 4621 : ℝ) * r + ((4621 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 17584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4637 : BSD_FrobeniusDegreeNonneg_OPEN 4637 := fun r => by
  have hap : (a_p 4637 : ℝ) = -36 := by exact_mod_cast BSD_ap_p4637
  have key : r ^ 2 - (a_p 4637 : ℝ) * r + ((4637 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 17252/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4639 : BSD_FrobeniusDegreeNonneg_OPEN 4639 := fun r => by
  have hap : (a_p 4639 : ℝ) = -68 := by exact_mod_cast BSD_ap_p4639
  have key : r ^ 2 - (a_p 4639 : ℝ) * r + ((4639 : ℕ) : ℝ) =
      (r + 68/2) ^ 2 + 13932/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (68 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4643 : BSD_FrobeniusDegreeNonneg_OPEN 4643 := fun r => by
  have hap : (a_p 4643 : ℝ) = -3 := by exact_mod_cast BSD_ap_p4643
  have key : r ^ 2 - (a_p 4643 : ℝ) * r + ((4643 : ℕ) : ℝ) =
      (r + 3/2) ^ 2 + 18563/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (3 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4649 : BSD_FrobeniusDegreeNonneg_OPEN 4649 := fun r => by
  have hap : (a_p 4649 : ℝ) = -100 := by exact_mod_cast BSD_ap_p4649
  have key : r ^ 2 - (a_p 4649 : ℝ) * r + ((4649 : ℕ) : ℝ) =
      (r + 100/2) ^ 2 + 8596/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (100 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4651 : BSD_FrobeniusDegreeNonneg_OPEN 4651 := fun r => by
  have hap : (a_p 4651 : ℝ) = 7 := by exact_mod_cast BSD_ap_p4651
  have key : r ^ 2 - (a_p 4651 : ℝ) * r + ((4651 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 18555/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4657 : BSD_FrobeniusDegreeNonneg_OPEN 4657 := fun r => by
  have hap : (a_p 4657 : ℝ) = 41 := by exact_mod_cast BSD_ap_p4657
  have key : r ^ 2 - (a_p 4657 : ℝ) * r + ((4657 : ℕ) : ℝ) =
      (r - 41/2) ^ 2 + 16947/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (41 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4663 : BSD_FrobeniusDegreeNonneg_OPEN 4663 := fun r => by
  have hap : (a_p 4663 : ℝ) = -4 := by exact_mod_cast BSD_ap_p4663
  have key : r ^ 2 - (a_p 4663 : ℝ) * r + ((4663 : ℕ) : ℝ) =
      (r + 4/2) ^ 2 + 18636/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (4 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4673 : BSD_FrobeniusDegreeNonneg_OPEN 4673 := fun r => by
  have hap : (a_p 4673 : ℝ) = -94 := by exact_mod_cast BSD_ap_p4673
  have key : r ^ 2 - (a_p 4673 : ℝ) * r + ((4673 : ℕ) : ℝ) =
      (r + 94/2) ^ 2 + 9856/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (94 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4679 : BSD_FrobeniusDegreeNonneg_OPEN 4679 := fun r => by
  have hap : (a_p 4679 : ℝ) = -87 := by exact_mod_cast BSD_ap_p4679
  have key : r ^ 2 - (a_p 4679 : ℝ) * r + ((4679 : ℕ) : ℝ) =
      (r + 87/2) ^ 2 + 11147/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (87 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4691 : BSD_FrobeniusDegreeNonneg_OPEN 4691 := fun r => by
  have hap : (a_p 4691 : ℝ) = -5 := by exact_mod_cast BSD_ap_p4691
  have key : r ^ 2 - (a_p 4691 : ℝ) * r + ((4691 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 18739/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4703 : BSD_FrobeniusDegreeNonneg_OPEN 4703 := fun r => by
  have hap : (a_p 4703 : ℝ) = 12 := by exact_mod_cast BSD_ap_p4703
  have key : r ^ 2 - (a_p 4703 : ℝ) * r + ((4703 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 18668/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4721 : BSD_FrobeniusDegreeNonneg_OPEN 4721 := fun r => by
  have hap : (a_p 4721 : ℝ) = 88 := by exact_mod_cast BSD_ap_p4721
  have key : r ^ 2 - (a_p 4721 : ℝ) * r + ((4721 : ℕ) : ℝ) =
      (r - 88/2) ^ 2 + 11140/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (88 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4723 : BSD_FrobeniusDegreeNonneg_OPEN 4723 := fun r => by
  have hap : (a_p 4723 : ℝ) = -76 := by exact_mod_cast BSD_ap_p4723
  have key : r ^ 2 - (a_p 4723 : ℝ) * r + ((4723 : ℕ) : ℝ) =
      (r + 76/2) ^ 2 + 13116/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (76 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4729 : BSD_FrobeniusDegreeNonneg_OPEN 4729 := fun r => by
  have hap : (a_p 4729 : ℝ) = 110 := by exact_mod_cast BSD_ap_p4729
  have key : r ^ 2 - (a_p 4729 : ℝ) * r + ((4729 : ℕ) : ℝ) =
      (r - 110/2) ^ 2 + 6816/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (110 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4733 : BSD_FrobeniusDegreeNonneg_OPEN 4733 := fun r => by
  have hap : (a_p 4733 : ℝ) = 69 := by exact_mod_cast BSD_ap_p4733
  have key : r ^ 2 - (a_p 4733 : ℝ) * r + ((4733 : ℕ) : ℝ) =
      (r - 69/2) ^ 2 + 14171/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (69 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4751 : BSD_FrobeniusDegreeNonneg_OPEN 4751 := fun r => by
  have hap : (a_p 4751 : ℝ) = -84 := by exact_mod_cast BSD_ap_p4751
  have key : r ^ 2 - (a_p 4751 : ℝ) * r + ((4751 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 11948/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4759 : BSD_FrobeniusDegreeNonneg_OPEN 4759 := fun r => by
  have hap : (a_p 4759 : ℝ) = 28 := by exact_mod_cast BSD_ap_p4759
  have key : r ^ 2 - (a_p 4759 : ℝ) * r + ((4759 : ℕ) : ℝ) =
      (r - 28/2) ^ 2 + 18252/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (28 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4783 : BSD_FrobeniusDegreeNonneg_OPEN 4783 := fun r => by
  have hap : (a_p 4783 : ℝ) = 51 := by exact_mod_cast BSD_ap_p4783
  have key : r ^ 2 - (a_p 4783 : ℝ) * r + ((4783 : ℕ) : ℝ) =
      (r - 51/2) ^ 2 + 16531/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (51 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4787 : BSD_FrobeniusDegreeNonneg_OPEN 4787 := fun r => by
  have hap : (a_p 4787 : ℝ) = -28 := by exact_mod_cast BSD_ap_p4787
  have key : r ^ 2 - (a_p 4787 : ℝ) * r + ((4787 : ℕ) : ℝ) =
      (r + 28/2) ^ 2 + 18364/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (28 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4789 : BSD_FrobeniusDegreeNonneg_OPEN 4789 := fun r => by
  have hap : (a_p 4789 : ℝ) = -86 := by exact_mod_cast BSD_ap_p4789
  have key : r ^ 2 - (a_p 4789 : ℝ) * r + ((4789 : ℕ) : ℝ) =
      (r + 86/2) ^ 2 + 11760/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (86 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4793 : BSD_FrobeniusDegreeNonneg_OPEN 4793 := fun r => by
  have hap : (a_p 4793 : ℝ) = -58 := by exact_mod_cast BSD_ap_p4793
  have key : r ^ 2 - (a_p 4793 : ℝ) * r + ((4793 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 15808/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4799 : BSD_FrobeniusDegreeNonneg_OPEN 4799 := fun r => by
  have hap : (a_p 4799 : ℝ) = 47 := by exact_mod_cast BSD_ap_p4799
  have key : r ^ 2 - (a_p 4799 : ℝ) * r + ((4799 : ℕ) : ℝ) =
      (r - 47/2) ^ 2 + 16987/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (47 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4801 : BSD_FrobeniusDegreeNonneg_OPEN 4801 := fun r => by
  have hap : (a_p 4801 : ℝ) = -75 := by exact_mod_cast BSD_ap_p4801
  have key : r ^ 2 - (a_p 4801 : ℝ) * r + ((4801 : ℕ) : ℝ) =
      (r + 75/2) ^ 2 + 13579/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (75 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4813 : BSD_FrobeniusDegreeNonneg_OPEN 4813 := fun r => by
  have hap : (a_p 4813 : ℝ) = -84 := by exact_mod_cast BSD_ap_p4813
  have key : r ^ 2 - (a_p 4813 : ℝ) * r + ((4813 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 12196/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4817 : BSD_FrobeniusDegreeNonneg_OPEN 4817 := fun r => by
  have hap : (a_p 4817 : ℝ) = 28 := by exact_mod_cast BSD_ap_p4817
  have key : r ^ 2 - (a_p 4817 : ℝ) * r + ((4817 : ℕ) : ℝ) =
      (r - 28/2) ^ 2 + 18484/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (28 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4831 : BSD_FrobeniusDegreeNonneg_OPEN 4831 := fun r => by
  have hap : (a_p 4831 : ℝ) = 46 := by exact_mod_cast BSD_ap_p4831
  have key : r ^ 2 - (a_p 4831 : ℝ) * r + ((4831 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 17208/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4861 : BSD_FrobeniusDegreeNonneg_OPEN 4861 := fun r => by
  have hap : (a_p 4861 : ℝ) = -10 := by exact_mod_cast BSD_ap_p4861
  have key : r ^ 2 - (a_p 4861 : ℝ) * r + ((4861 : ℕ) : ℝ) =
      (r + 10/2) ^ 2 + 19344/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (10 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4871 : BSD_FrobeniusDegreeNonneg_OPEN 4871 := fun r => by
  have hap : (a_p 4871 : ℝ) = -32 := by exact_mod_cast BSD_ap_p4871
  have key : r ^ 2 - (a_p 4871 : ℝ) * r + ((4871 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 18460/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4877 : BSD_FrobeniusDegreeNonneg_OPEN 4877 := fun r => by
  have hap : (a_p 4877 : ℝ) = 7 := by exact_mod_cast BSD_ap_p4877
  have key : r ^ 2 - (a_p 4877 : ℝ) * r + ((4877 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 19459/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4889 : BSD_FrobeniusDegreeNonneg_OPEN 4889 := fun r => by
  have hap : (a_p 4889 : ℝ) = -55 := by exact_mod_cast BSD_ap_p4889
  have key : r ^ 2 - (a_p 4889 : ℝ) * r + ((4889 : ℕ) : ℝ) =
      (r + 55/2) ^ 2 + 16531/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (55 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4903 : BSD_FrobeniusDegreeNonneg_OPEN 4903 := fun r => by
  have hap : (a_p 4903 : ℝ) = 38 := by exact_mod_cast BSD_ap_p4903
  have key : r ^ 2 - (a_p 4903 : ℝ) * r + ((4903 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 18168/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4909 : BSD_FrobeniusDegreeNonneg_OPEN 4909 := fun r => by
  have hap : (a_p 4909 : ℝ) = 1 := by exact_mod_cast BSD_ap_p4909
  have key : r ^ 2 - (a_p 4909 : ℝ) * r + ((4909 : ℕ) : ℝ) =
      (r - 1/2) ^ 2 + 19635/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (1 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4919 : BSD_FrobeniusDegreeNonneg_OPEN 4919 := fun r => by
  have hap : (a_p 4919 : ℝ) = 94 := by exact_mod_cast BSD_ap_p4919
  have key : r ^ 2 - (a_p 4919 : ℝ) * r + ((4919 : ℕ) : ℝ) =
      (r - 94/2) ^ 2 + 10840/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (94 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4931 : BSD_FrobeniusDegreeNonneg_OPEN 4931 := fun r => by
  have hap : (a_p 4931 : ℝ) = 48 := by exact_mod_cast BSD_ap_p4931
  have key : r ^ 2 - (a_p 4931 : ℝ) * r + ((4931 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 17420/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4933 : BSD_FrobeniusDegreeNonneg_OPEN 4933 := fun r => by
  have hap : (a_p 4933 : ℝ) = 102 := by exact_mod_cast BSD_ap_p4933
  have key : r ^ 2 - (a_p 4933 : ℝ) * r + ((4933 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 9328/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4937 : BSD_FrobeniusDegreeNonneg_OPEN 4937 := fun r => by
  have hap : (a_p 4937 : ℝ) = 90 := by exact_mod_cast BSD_ap_p4937
  have key : r ^ 2 - (a_p 4937 : ℝ) * r + ((4937 : ℕ) : ℝ) =
      (r - 90/2) ^ 2 + 11648/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (90 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4943 : BSD_FrobeniusDegreeNonneg_OPEN 4943 := fun r => by
  have hap : (a_p 4943 : ℝ) = -84 := by exact_mod_cast BSD_ap_p4943
  have key : r ^ 2 - (a_p 4943 : ℝ) * r + ((4943 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 12716/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4951 : BSD_FrobeniusDegreeNonneg_OPEN 4951 := fun r => by
  have hap : (a_p 4951 : ℝ) = 80 := by exact_mod_cast BSD_ap_p4951
  have key : r ^ 2 - (a_p 4951 : ℝ) * r + ((4951 : ℕ) : ℝ) =
      (r - 80/2) ^ 2 + 13404/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (80 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4957 : BSD_FrobeniusDegreeNonneg_OPEN 4957 := fun r => by
  have hap : (a_p 4957 : ℝ) = 100 := by exact_mod_cast BSD_ap_p4957
  have key : r ^ 2 - (a_p 4957 : ℝ) * r + ((4957 : ℕ) : ℝ) =
      (r - 100/2) ^ 2 + 9828/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (100 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4967 : BSD_FrobeniusDegreeNonneg_OPEN 4967 := fun r => by
  have hap : (a_p 4967 : ℝ) = 78 := by exact_mod_cast BSD_ap_p4967
  have key : r ^ 2 - (a_p 4967 : ℝ) * r + ((4967 : ℕ) : ℝ) =
      (r - 78/2) ^ 2 + 13784/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (78 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4969 : BSD_FrobeniusDegreeNonneg_OPEN 4969 := fun r => by
  have hap : (a_p 4969 : ℝ) = -40 := by exact_mod_cast BSD_ap_p4969
  have key : r ^ 2 - (a_p 4969 : ℝ) * r + ((4969 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 18276/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4973 : BSD_FrobeniusDegreeNonneg_OPEN 4973 := fun r => by
  have hap : (a_p 4973 : ℝ) = 69 := by exact_mod_cast BSD_ap_p4973
  have key : r ^ 2 - (a_p 4973 : ℝ) * r + ((4973 : ℕ) : ℝ) =
      (r - 69/2) ^ 2 + 15131/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (69 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4987 : BSD_FrobeniusDegreeNonneg_OPEN 4987 := fun r => by
  have hap : (a_p 4987 : ℝ) = 12 := by exact_mod_cast BSD_ap_p4987
  have key : r ^ 2 - (a_p 4987 : ℝ) * r + ((4987 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 19804/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4993 : BSD_FrobeniusDegreeNonneg_OPEN 4993 := fun r => by
  have hap : (a_p 4993 : ℝ) = 60 := by exact_mod_cast BSD_ap_p4993
  have key : r ^ 2 - (a_p 4993 : ℝ) * r + ((4993 : ℕ) : ℝ) =
      (r - 60/2) ^ 2 + 16372/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (60 : ℝ)/2)]

theorem BSD_DegreeNonneg_p4999 : BSD_FrobeniusDegreeNonneg_OPEN 4999 := fun r => by
  have hap : (a_p 4999 : ℝ) = -112 := by exact_mod_cast BSD_ap_p4999
  have key : r ^ 2 - (a_p 4999 : ℝ) * r + ((4999 : ℕ) : ℝ) =
      (r + 112/2) ^ 2 + 7452/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (112 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5003 : BSD_FrobeniusDegreeNonneg_OPEN 5003 := fun r => by
  have hap : (a_p 5003 : ℝ) = -103 := by exact_mod_cast BSD_ap_p5003
  have key : r ^ 2 - (a_p 5003 : ℝ) * r + ((5003 : ℕ) : ℝ) =
      (r + 103/2) ^ 2 + 9403/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (103 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5009 : BSD_FrobeniusDegreeNonneg_OPEN 5009 := fun r => by
  have hap : (a_p 5009 : ℝ) = 7 := by exact_mod_cast BSD_ap_p5009
  have key : r ^ 2 - (a_p 5009 : ℝ) * r + ((5009 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 19987/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5011 : BSD_FrobeniusDegreeNonneg_OPEN 5011 := fun r => by
  have hap : (a_p 5011 : ℝ) = 108 := by exact_mod_cast BSD_ap_p5011
  have key : r ^ 2 - (a_p 5011 : ℝ) * r + ((5011 : ℕ) : ℝ) =
      (r - 108/2) ^ 2 + 8380/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (108 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5021 : BSD_FrobeniusDegreeNonneg_OPEN 5021 := fun r => by
  have hap : (a_p 5021 : ℝ) = 85 := by exact_mod_cast BSD_ap_p5021
  have key : r ^ 2 - (a_p 5021 : ℝ) * r + ((5021 : ℕ) : ℝ) =
      (r - 85/2) ^ 2 + 12859/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (85 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5023 : BSD_FrobeniusDegreeNonneg_OPEN 5023 := fun r => by
  have hap : (a_p 5023 : ℝ) = 72 := by exact_mod_cast BSD_ap_p5023
  have key : r ^ 2 - (a_p 5023 : ℝ) * r + ((5023 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 14908/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5039 : BSD_FrobeniusDegreeNonneg_OPEN 5039 := fun r => by
  have hap : (a_p 5039 : ℝ) = 17 := by exact_mod_cast BSD_ap_p5039
  have key : r ^ 2 - (a_p 5039 : ℝ) * r + ((5039 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 19867/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5051 : BSD_FrobeniusDegreeNonneg_OPEN 5051 := fun r => by
  have hap : (a_p 5051 : ℝ) = 102 := by exact_mod_cast BSD_ap_p5051
  have key : r ^ 2 - (a_p 5051 : ℝ) * r + ((5051 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 9800/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5059 : BSD_FrobeniusDegreeNonneg_OPEN 5059 := fun r => by
  have hap : (a_p 5059 : ℝ) = 22 := by exact_mod_cast BSD_ap_p5059
  have key : r ^ 2 - (a_p 5059 : ℝ) * r + ((5059 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 19752/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5077 : BSD_FrobeniusDegreeNonneg_OPEN 5077 := fun r => by
  have hap : (a_p 5077 : ℝ) = 14 := by exact_mod_cast BSD_ap_p5077
  have key : r ^ 2 - (a_p 5077 : ℝ) * r + ((5077 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 20112/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5081 : BSD_FrobeniusDegreeNonneg_OPEN 5081 := fun r => by
  have hap : (a_p 5081 : ℝ) = -18 := by exact_mod_cast BSD_ap_p5081
  have key : r ^ 2 - (a_p 5081 : ℝ) * r + ((5081 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 20000/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5087 : BSD_FrobeniusDegreeNonneg_OPEN 5087 := fun r => by
  have hap : (a_p 5087 : ℝ) = -103 := by exact_mod_cast BSD_ap_p5087
  have key : r ^ 2 - (a_p 5087 : ℝ) * r + ((5087 : ℕ) : ℝ) =
      (r + 103/2) ^ 2 + 9739/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (103 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5099 : BSD_FrobeniusDegreeNonneg_OPEN 5099 := fun r => by
  have hap : (a_p 5099 : ℝ) = 112 := by exact_mod_cast BSD_ap_p5099
  have key : r ^ 2 - (a_p 5099 : ℝ) * r + ((5099 : ℕ) : ℝ) =
      (r - 112/2) ^ 2 + 7852/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (112 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5101 : BSD_FrobeniusDegreeNonneg_OPEN 5101 := fun r => by
  have hap : (a_p 5101 : ℝ) = 38 := by exact_mod_cast BSD_ap_p5101
  have key : r ^ 2 - (a_p 5101 : ℝ) * r + ((5101 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 18960/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5107 : BSD_FrobeniusDegreeNonneg_OPEN 5107 := fun r => by
  have hap : (a_p 5107 : ℝ) = -68 := by exact_mod_cast BSD_ap_p5107
  have key : r ^ 2 - (a_p 5107 : ℝ) * r + ((5107 : ℕ) : ℝ) =
      (r + 68/2) ^ 2 + 15804/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (68 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5113 : BSD_FrobeniusDegreeNonneg_OPEN 5113 := fun r => by
  have hap : (a_p 5113 : ℝ) = -139 := by exact_mod_cast BSD_ap_p5113
  have key : r ^ 2 - (a_p 5113 : ℝ) * r + ((5113 : ℕ) : ℝ) =
      (r + 139/2) ^ 2 + 1131/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (139 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5119 : BSD_FrobeniusDegreeNonneg_OPEN 5119 := fun r => by
  have hap : (a_p 5119 : ℝ) = -33 := by exact_mod_cast BSD_ap_p5119
  have key : r ^ 2 - (a_p 5119 : ℝ) * r + ((5119 : ℕ) : ℝ) =
      (r + 33/2) ^ 2 + 19387/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (33 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5147 : BSD_FrobeniusDegreeNonneg_OPEN 5147 := fun r => by
  have hap : (a_p 5147 : ℝ) = -96 := by exact_mod_cast BSD_ap_p5147
  have key : r ^ 2 - (a_p 5147 : ℝ) * r + ((5147 : ℕ) : ℝ) =
      (r + 96/2) ^ 2 + 11372/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (96 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5153 : BSD_FrobeniusDegreeNonneg_OPEN 5153 := fun r => by
  have hap : (a_p 5153 : ℝ) = -21 := by exact_mod_cast BSD_ap_p5153
  have key : r ^ 2 - (a_p 5153 : ℝ) * r + ((5153 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 20171/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5167 : BSD_FrobeniusDegreeNonneg_OPEN 5167 := fun r => by
  have hap : (a_p 5167 : ℝ) = 86 := by exact_mod_cast BSD_ap_p5167
  have key : r ^ 2 - (a_p 5167 : ℝ) * r + ((5167 : ℕ) : ℝ) =
      (r - 86/2) ^ 2 + 13272/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (86 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5171 : BSD_FrobeniusDegreeNonneg_OPEN 5171 := fun r => by
  have hap : (a_p 5171 : ℝ) = 97 := by exact_mod_cast BSD_ap_p5171
  have key : r ^ 2 - (a_p 5171 : ℝ) * r + ((5171 : ℕ) : ℝ) =
      (r - 97/2) ^ 2 + 11275/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (97 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5179 : BSD_FrobeniusDegreeNonneg_OPEN 5179 := fun r => by
  have hap : (a_p 5179 : ℝ) = 16 := by exact_mod_cast BSD_ap_p5179
  have key : r ^ 2 - (a_p 5179 : ℝ) * r + ((5179 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 20460/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5189 : BSD_FrobeniusDegreeNonneg_OPEN 5189 := fun r => by
  have hap : (a_p 5189 : ℝ) = -36 := by exact_mod_cast BSD_ap_p5189
  have key : r ^ 2 - (a_p 5189 : ℝ) * r + ((5189 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 19460/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5197 : BSD_FrobeniusDegreeNonneg_OPEN 5197 := fun r => by
  have hap : (a_p 5197 : ℝ) = 107 := by exact_mod_cast BSD_ap_p5197
  have key : r ^ 2 - (a_p 5197 : ℝ) * r + ((5197 : ℕ) : ℝ) =
      (r - 107/2) ^ 2 + 9339/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (107 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5209 : BSD_FrobeniusDegreeNonneg_OPEN 5209 := fun r => by
  have hap : (a_p 5209 : ℝ) = 6 := by exact_mod_cast BSD_ap_p5209
  have key : r ^ 2 - (a_p 5209 : ℝ) * r + ((5209 : ℕ) : ℝ) =
      (r - 6/2) ^ 2 + 20800/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5227 : BSD_FrobeniusDegreeNonneg_OPEN 5227 := fun r => by
  have hap : (a_p 5227 : ℝ) = -56 := by exact_mod_cast BSD_ap_p5227
  have key : r ^ 2 - (a_p 5227 : ℝ) * r + ((5227 : ℕ) : ℝ) =
      (r + 56/2) ^ 2 + 17772/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (56 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5231 : BSD_FrobeniusDegreeNonneg_OPEN 5231 := fun r => by
  have hap : (a_p 5231 : ℝ) = -10 := by exact_mod_cast BSD_ap_p5231
  have key : r ^ 2 - (a_p 5231 : ℝ) * r + ((5231 : ℕ) : ℝ) =
      (r + 10/2) ^ 2 + 20824/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (10 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5233 : BSD_FrobeniusDegreeNonneg_OPEN 5233 := fun r => by
  have hap : (a_p 5233 : ℝ) = 52 := by exact_mod_cast BSD_ap_p5233
  have key : r ^ 2 - (a_p 5233 : ℝ) * r + ((5233 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 18228/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5237 : BSD_FrobeniusDegreeNonneg_OPEN 5237 := fun r => by
  have hap : (a_p 5237 : ℝ) = 65 := by exact_mod_cast BSD_ap_p5237
  have key : r ^ 2 - (a_p 5237 : ℝ) * r + ((5237 : ℕ) : ℝ) =
      (r - 65/2) ^ 2 + 16723/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (65 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5261 : BSD_FrobeniusDegreeNonneg_OPEN 5261 := fun r => by
  have hap : (a_p 5261 : ℝ) = -5 := by exact_mod_cast BSD_ap_p5261
  have key : r ^ 2 - (a_p 5261 : ℝ) * r + ((5261 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 21019/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5273 : BSD_FrobeniusDegreeNonneg_OPEN 5273 := fun r => by
  have hap : (a_p 5273 : ℝ) = -135 := by exact_mod_cast BSD_ap_p5273
  have key : r ^ 2 - (a_p 5273 : ℝ) * r + ((5273 : ℕ) : ℝ) =
      (r + 135/2) ^ 2 + 2867/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (135 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5279 : BSD_FrobeniusDegreeNonneg_OPEN 5279 := fun r => by
  have hap : (a_p 5279 : ℝ) = -64 := by exact_mod_cast BSD_ap_p5279
  have key : r ^ 2 - (a_p 5279 : ℝ) * r + ((5279 : ℕ) : ℝ) =
      (r + 64/2) ^ 2 + 17020/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (64 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5281 : BSD_FrobeniusDegreeNonneg_OPEN 5281 := fun r => by
  have hap : (a_p 5281 : ℝ) = 17 := by exact_mod_cast BSD_ap_p5281
  have key : r ^ 2 - (a_p 5281 : ℝ) * r + ((5281 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 20835/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5297 : BSD_FrobeniusDegreeNonneg_OPEN 5297 := fun r => by
  have hap : (a_p 5297 : ℝ) = -132 := by exact_mod_cast BSD_ap_p5297
  have key : r ^ 2 - (a_p 5297 : ℝ) * r + ((5297 : ℕ) : ℝ) =
      (r + 132/2) ^ 2 + 3764/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (132 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5303 : BSD_FrobeniusDegreeNonneg_OPEN 5303 := fun r => by
  have hap : (a_p 5303 : ℝ) = 63 := by exact_mod_cast BSD_ap_p5303
  have key : r ^ 2 - (a_p 5303 : ℝ) * r + ((5303 : ℕ) : ℝ) =
      (r - 63/2) ^ 2 + 17243/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (63 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5309 : BSD_FrobeniusDegreeNonneg_OPEN 5309 := fun r => by
  have hap : (a_p 5309 : ℝ) = 36 := by exact_mod_cast BSD_ap_p5309
  have key : r ^ 2 - (a_p 5309 : ℝ) * r + ((5309 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 19940/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5323 : BSD_FrobeniusDegreeNonneg_OPEN 5323 := fun r => by
  have hap : (a_p 5323 : ℝ) = -70 := by exact_mod_cast BSD_ap_p5323
  have key : r ^ 2 - (a_p 5323 : ℝ) * r + ((5323 : ℕ) : ℝ) =
      (r + 70/2) ^ 2 + 16392/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (70 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5333 : BSD_FrobeniusDegreeNonneg_OPEN 5333 := fun r => by
  have hap : (a_p 5333 : ℝ) = 114 := by exact_mod_cast BSD_ap_p5333
  have key : r ^ 2 - (a_p 5333 : ℝ) * r + ((5333 : ℕ) : ℝ) =
      (r - 114/2) ^ 2 + 8336/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (114 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5347 : BSD_FrobeniusDegreeNonneg_OPEN 5347 := fun r => by
  have hap : (a_p 5347 : ℝ) = 127 := by exact_mod_cast BSD_ap_p5347
  have key : r ^ 2 - (a_p 5347 : ℝ) * r + ((5347 : ℕ) : ℝ) =
      (r - 127/2) ^ 2 + 5259/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (127 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5351 : BSD_FrobeniusDegreeNonneg_OPEN 5351 := fun r => by
  have hap : (a_p 5351 : ℝ) = -5 := by exact_mod_cast BSD_ap_p5351
  have key : r ^ 2 - (a_p 5351 : ℝ) * r + ((5351 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 21379/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5381 : BSD_FrobeniusDegreeNonneg_OPEN 5381 := fun r => by
  have hap : (a_p 5381 : ℝ) = 12 := by exact_mod_cast BSD_ap_p5381
  have key : r ^ 2 - (a_p 5381 : ℝ) * r + ((5381 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 21380/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5387 : BSD_FrobeniusDegreeNonneg_OPEN 5387 := fun r => by
  have hap : (a_p 5387 : ℝ) = -20 := by exact_mod_cast BSD_ap_p5387
  have key : r ^ 2 - (a_p 5387 : ℝ) * r + ((5387 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 21148/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5393 : BSD_FrobeniusDegreeNonneg_OPEN 5393 := fun r => by
  have hap : (a_p 5393 : ℝ) = -21 := by exact_mod_cast BSD_ap_p5393
  have key : r ^ 2 - (a_p 5393 : ℝ) * r + ((5393 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 21131/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5399 : BSD_FrobeniusDegreeNonneg_OPEN 5399 := fun r => by
  have hap : (a_p 5399 : ℝ) = 133 := by exact_mod_cast BSD_ap_p5399
  have key : r ^ 2 - (a_p 5399 : ℝ) * r + ((5399 : ℕ) : ℝ) =
      (r - 133/2) ^ 2 + 3907/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (133 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5407 : BSD_FrobeniusDegreeNonneg_OPEN 5407 := fun r => by
  have hap : (a_p 5407 : ℝ) = -122 := by exact_mod_cast BSD_ap_p5407
  have key : r ^ 2 - (a_p 5407 : ℝ) * r + ((5407 : ℕ) : ℝ) =
      (r + 122/2) ^ 2 + 6744/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (122 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5413 : BSD_FrobeniusDegreeNonneg_OPEN 5413 := fun r => by
  have hap : (a_p 5413 : ℝ) = -22 := by exact_mod_cast BSD_ap_p5413
  have key : r ^ 2 - (a_p 5413 : ℝ) * r + ((5413 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 21168/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5417 : BSD_FrobeniusDegreeNonneg_OPEN 5417 := fun r => by
  have hap : (a_p 5417 : ℝ) = 78 := by exact_mod_cast BSD_ap_p5417
  have key : r ^ 2 - (a_p 5417 : ℝ) * r + ((5417 : ℕ) : ℝ) =
      (r - 78/2) ^ 2 + 15584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (78 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5419 : BSD_FrobeniusDegreeNonneg_OPEN 5419 := fun r => by
  have hap : (a_p 5419 : ℝ) = -40 := by exact_mod_cast BSD_ap_p5419
  have key : r ^ 2 - (a_p 5419 : ℝ) * r + ((5419 : ℕ) : ℝ) =
      (r + 40/2) ^ 2 + 20076/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5431 : BSD_FrobeniusDegreeNonneg_OPEN 5431 := fun r => by
  have hap : (a_p 5431 : ℝ) = 20 := by exact_mod_cast BSD_ap_p5431
  have key : r ^ 2 - (a_p 5431 : ℝ) * r + ((5431 : ℕ) : ℝ) =
      (r - 20/2) ^ 2 + 21324/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5437 : BSD_FrobeniusDegreeNonneg_OPEN 5437 := fun r => by
  have hap : (a_p 5437 : ℝ) = -6 := by exact_mod_cast BSD_ap_p5437
  have key : r ^ 2 - (a_p 5437 : ℝ) * r + ((5437 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 21712/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5441 : BSD_FrobeniusDegreeNonneg_OPEN 5441 := fun r => by
  have hap : (a_p 5441 : ℝ) = 52 := by exact_mod_cast BSD_ap_p5441
  have key : r ^ 2 - (a_p 5441 : ℝ) * r + ((5441 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 19060/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5443 : BSD_FrobeniusDegreeNonneg_OPEN 5443 := fun r => by
  have hap : (a_p 5443 : ℝ) = 93 := by exact_mod_cast BSD_ap_p5443
  have key : r ^ 2 - (a_p 5443 : ℝ) * r + ((5443 : ℕ) : ℝ) =
      (r - 93/2) ^ 2 + 13123/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (93 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5449 : BSD_FrobeniusDegreeNonneg_OPEN 5449 := fun r => by
  have hap : (a_p 5449 : ℝ) = 125 := by exact_mod_cast BSD_ap_p5449
  have key : r ^ 2 - (a_p 5449 : ℝ) * r + ((5449 : ℕ) : ℝ) =
      (r - 125/2) ^ 2 + 6171/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (125 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5471 : BSD_FrobeniusDegreeNonneg_OPEN 5471 := fun r => by
  have hap : (a_p 5471 : ℝ) = -125 := by exact_mod_cast BSD_ap_p5471
  have key : r ^ 2 - (a_p 5471 : ℝ) * r + ((5471 : ℕ) : ℝ) =
      (r + 125/2) ^ 2 + 6259/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (125 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5477 : BSD_FrobeniusDegreeNonneg_OPEN 5477 := fun r => by
  have hap : (a_p 5477 : ℝ) = -116 := by exact_mod_cast BSD_ap_p5477
  have key : r ^ 2 - (a_p 5477 : ℝ) * r + ((5477 : ℕ) : ℝ) =
      (r + 116/2) ^ 2 + 8452/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (116 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5479 : BSD_FrobeniusDegreeNonneg_OPEN 5479 := fun r => by
  have hap : (a_p 5479 : ℝ) = -125 := by exact_mod_cast BSD_ap_p5479
  have key : r ^ 2 - (a_p 5479 : ℝ) * r + ((5479 : ℕ) : ℝ) =
      (r + 125/2) ^ 2 + 6291/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (125 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5483 : BSD_FrobeniusDegreeNonneg_OPEN 5483 := fun r => by
  have hap : (a_p 5483 : ℝ) = -36 := by exact_mod_cast BSD_ap_p5483
  have key : r ^ 2 - (a_p 5483 : ℝ) * r + ((5483 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 20636/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5501 : BSD_FrobeniusDegreeNonneg_OPEN 5501 := fun r => by
  have hap : (a_p 5501 : ℝ) = -107 := by exact_mod_cast BSD_ap_p5501
  have key : r ^ 2 - (a_p 5501 : ℝ) * r + ((5501 : ℕ) : ℝ) =
      (r + 107/2) ^ 2 + 10555/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (107 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5503 : BSD_FrobeniusDegreeNonneg_OPEN 5503 := fun r => by
  have hap : (a_p 5503 : ℝ) = 115 := by exact_mod_cast BSD_ap_p5503
  have key : r ^ 2 - (a_p 5503 : ℝ) * r + ((5503 : ℕ) : ℝ) =
      (r - 115/2) ^ 2 + 8787/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (115 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5507 : BSD_FrobeniusDegreeNonneg_OPEN 5507 := fun r => by
  have hap : (a_p 5507 : ℝ) = -32 := by exact_mod_cast BSD_ap_p5507
  have key : r ^ 2 - (a_p 5507 : ℝ) * r + ((5507 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 21004/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5519 : BSD_FrobeniusDegreeNonneg_OPEN 5519 := fun r => by
  have hap : (a_p 5519 : ℝ) = 66 := by exact_mod_cast BSD_ap_p5519
  have key : r ^ 2 - (a_p 5519 : ℝ) * r + ((5519 : ℕ) : ℝ) =
      (r - 66/2) ^ 2 + 17720/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (66 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5521 : BSD_FrobeniusDegreeNonneg_OPEN 5521 := fun r => by
  have hap : (a_p 5521 : ℝ) = 24 := by exact_mod_cast BSD_ap_p5521
  have key : r ^ 2 - (a_p 5521 : ℝ) * r + ((5521 : ℕ) : ℝ) =
      (r - 24/2) ^ 2 + 21508/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5527 : BSD_FrobeniusDegreeNonneg_OPEN 5527 := fun r => by
  have hap : (a_p 5527 : ℝ) = -20 := by exact_mod_cast BSD_ap_p5527
  have key : r ^ 2 - (a_p 5527 : ℝ) * r + ((5527 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 21708/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5531 : BSD_FrobeniusDegreeNonneg_OPEN 5531 := fun r => by
  have hap : (a_p 5531 : ℝ) = 117 := by exact_mod_cast BSD_ap_p5531
  have key : r ^ 2 - (a_p 5531 : ℝ) * r + ((5531 : ℕ) : ℝ) =
      (r - 117/2) ^ 2 + 8435/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (117 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5557 : BSD_FrobeniusDegreeNonneg_OPEN 5557 := fun r => by
  have hap : (a_p 5557 : ℝ) = 36 := by exact_mod_cast BSD_ap_p5557
  have key : r ^ 2 - (a_p 5557 : ℝ) * r + ((5557 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 20932/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5563 : BSD_FrobeniusDegreeNonneg_OPEN 5563 := fun r => by
  have hap : (a_p 5563 : ℝ) = 2 := by exact_mod_cast BSD_ap_p5563
  have key : r ^ 2 - (a_p 5563 : ℝ) * r + ((5563 : ℕ) : ℝ) =
      (r - 2/2) ^ 2 + 22248/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (2 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5569 : BSD_FrobeniusDegreeNonneg_OPEN 5569 := fun r => by
  have hap : (a_p 5569 : ℝ) = 129 := by exact_mod_cast BSD_ap_p5569
  have key : r ^ 2 - (a_p 5569 : ℝ) * r + ((5569 : ℕ) : ℝ) =
      (r - 129/2) ^ 2 + 5635/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (129 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5573 : BSD_FrobeniusDegreeNonneg_OPEN 5573 := fun r => by
  have hap : (a_p 5573 : ℝ) = -36 := by exact_mod_cast BSD_ap_p5573
  have key : r ^ 2 - (a_p 5573 : ℝ) * r + ((5573 : ℕ) : ℝ) =
      (r + 36/2) ^ 2 + 20996/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5581 : BSD_FrobeniusDegreeNonneg_OPEN 5581 := fun r => by
  have hap : (a_p 5581 : ℝ) = -97 := by exact_mod_cast BSD_ap_p5581
  have key : r ^ 2 - (a_p 5581 : ℝ) * r + ((5581 : ℕ) : ℝ) =
      (r + 97/2) ^ 2 + 12915/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (97 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5591 : BSD_FrobeniusDegreeNonneg_OPEN 5591 := fun r => by
  have hap : (a_p 5591 : ℝ) = 51 := by exact_mod_cast BSD_ap_p5591
  have key : r ^ 2 - (a_p 5591 : ℝ) * r + ((5591 : ℕ) : ℝ) =
      (r - 51/2) ^ 2 + 19763/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (51 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5623 : BSD_FrobeniusDegreeNonneg_OPEN 5623 := fun r => by
  have hap : (a_p 5623 : ℝ) = -78 := by exact_mod_cast BSD_ap_p5623
  have key : r ^ 2 - (a_p 5623 : ℝ) * r + ((5623 : ℕ) : ℝ) =
      (r + 78/2) ^ 2 + 16408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (78 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5639 : BSD_FrobeniusDegreeNonneg_OPEN 5639 := fun r => by
  have hap : (a_p 5639 : ℝ) = 76 := by exact_mod_cast BSD_ap_p5639
  have key : r ^ 2 - (a_p 5639 : ℝ) * r + ((5639 : ℕ) : ℝ) =
      (r - 76/2) ^ 2 + 16780/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (76 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5641 : BSD_FrobeniusDegreeNonneg_OPEN 5641 := fun r => by
  have hap : (a_p 5641 : ℝ) = -31 := by exact_mod_cast BSD_ap_p5641
  have key : r ^ 2 - (a_p 5641 : ℝ) * r + ((5641 : ℕ) : ℝ) =
      (r + 31/2) ^ 2 + 21603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (31 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5647 : BSD_FrobeniusDegreeNonneg_OPEN 5647 := fun r => by
  have hap : (a_p 5647 : ℝ) = 115 := by exact_mod_cast BSD_ap_p5647
  have key : r ^ 2 - (a_p 5647 : ℝ) * r + ((5647 : ℕ) : ℝ) =
      (r - 115/2) ^ 2 + 9363/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (115 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5651 : BSD_FrobeniusDegreeNonneg_OPEN 5651 := fun r => by
  have hap : (a_p 5651 : ℝ) = -112 := by exact_mod_cast BSD_ap_p5651
  have key : r ^ 2 - (a_p 5651 : ℝ) * r + ((5651 : ℕ) : ℝ) =
      (r + 112/2) ^ 2 + 10060/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (112 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5653 : BSD_FrobeniusDegreeNonneg_OPEN 5653 := fun r => by
  have hap : (a_p 5653 : ℝ) = -52 := by exact_mod_cast BSD_ap_p5653
  have key : r ^ 2 - (a_p 5653 : ℝ) * r + ((5653 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 19908/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5657 : BSD_FrobeniusDegreeNonneg_OPEN 5657 := fun r => by
  have hap : (a_p 5657 : ℝ) = -71 := by exact_mod_cast BSD_ap_p5657
  have key : r ^ 2 - (a_p 5657 : ℝ) * r + ((5657 : ℕ) : ℝ) =
      (r + 71/2) ^ 2 + 17587/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (71 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5659 : BSD_FrobeniusDegreeNonneg_OPEN 5659 := fun r => by
  have hap : (a_p 5659 : ℝ) = -93 := by exact_mod_cast BSD_ap_p5659
  have key : r ^ 2 - (a_p 5659 : ℝ) * r + ((5659 : ℕ) : ℝ) =
      (r + 93/2) ^ 2 + 13987/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (93 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5669 : BSD_FrobeniusDegreeNonneg_OPEN 5669 := fun r => by
  have hap : (a_p 5669 : ℝ) = -30 := by exact_mod_cast BSD_ap_p5669
  have key : r ^ 2 - (a_p 5669 : ℝ) * r + ((5669 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 21776/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5683 : BSD_FrobeniusDegreeNonneg_OPEN 5683 := fun r => by
  have hap : (a_p 5683 : ℝ) = -136 := by exact_mod_cast BSD_ap_p5683
  have key : r ^ 2 - (a_p 5683 : ℝ) * r + ((5683 : ℕ) : ℝ) =
      (r + 136/2) ^ 2 + 4236/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (136 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5689 : BSD_FrobeniusDegreeNonneg_OPEN 5689 := fun r => by
  have hap : (a_p 5689 : ℝ) = -28 := by exact_mod_cast BSD_ap_p5689
  have key : r ^ 2 - (a_p 5689 : ℝ) * r + ((5689 : ℕ) : ℝ) =
      (r + 28/2) ^ 2 + 21972/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (28 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5693 : BSD_FrobeniusDegreeNonneg_OPEN 5693 := fun r => by
  have hap : (a_p 5693 : ℝ) = -72 := by exact_mod_cast BSD_ap_p5693
  have key : r ^ 2 - (a_p 5693 : ℝ) * r + ((5693 : ℕ) : ℝ) =
      (r + 72/2) ^ 2 + 17588/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (72 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5701 : BSD_FrobeniusDegreeNonneg_OPEN 5701 := fun r => by
  have hap : (a_p 5701 : ℝ) = 75 := by exact_mod_cast BSD_ap_p5701
  have key : r ^ 2 - (a_p 5701 : ℝ) * r + ((5701 : ℕ) : ℝ) =
      (r - 75/2) ^ 2 + 17179/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (75 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5711 : BSD_FrobeniusDegreeNonneg_OPEN 5711 := fun r => by
  have hap : (a_p 5711 : ℝ) = 26 := by exact_mod_cast BSD_ap_p5711
  have key : r ^ 2 - (a_p 5711 : ℝ) * r + ((5711 : ℕ) : ℝ) =
      (r - 26/2) ^ 2 + 22168/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (26 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5717 : BSD_FrobeniusDegreeNonneg_OPEN 5717 := fun r => by
  have hap : (a_p 5717 : ℝ) = -76 := by exact_mod_cast BSD_ap_p5717
  have key : r ^ 2 - (a_p 5717 : ℝ) * r + ((5717 : ℕ) : ℝ) =
      (r + 76/2) ^ 2 + 17092/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (76 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5737 : BSD_FrobeniusDegreeNonneg_OPEN 5737 := fun r => by
  have hap : (a_p 5737 : ℝ) = -86 := by exact_mod_cast BSD_ap_p5737
  have key : r ^ 2 - (a_p 5737 : ℝ) * r + ((5737 : ℕ) : ℝ) =
      (r + 86/2) ^ 2 + 15552/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (86 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5741 : BSD_FrobeniusDegreeNonneg_OPEN 5741 := fun r => by
  have hap : (a_p 5741 : ℝ) = 120 := by exact_mod_cast BSD_ap_p5741
  have key : r ^ 2 - (a_p 5741 : ℝ) * r + ((5741 : ℕ) : ℝ) =
      (r - 120/2) ^ 2 + 8564/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (120 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5743 : BSD_FrobeniusDegreeNonneg_OPEN 5743 := fun r => by
  have hap : (a_p 5743 : ℝ) = 55 := by exact_mod_cast BSD_ap_p5743
  have key : r ^ 2 - (a_p 5743 : ℝ) * r + ((5743 : ℕ) : ℝ) =
      (r - 55/2) ^ 2 + 19947/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (55 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5749 : BSD_FrobeniusDegreeNonneg_OPEN 5749 := fun r => by
  have hap : (a_p 5749 : ℝ) = 46 := by exact_mod_cast BSD_ap_p5749
  have key : r ^ 2 - (a_p 5749 : ℝ) * r + ((5749 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 20880/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5779 : BSD_FrobeniusDegreeNonneg_OPEN 5779 := fun r => by
  have hap : (a_p 5779 : ℝ) = -5 := by exact_mod_cast BSD_ap_p5779
  have key : r ^ 2 - (a_p 5779 : ℝ) * r + ((5779 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 23091/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5783 : BSD_FrobeniusDegreeNonneg_OPEN 5783 := fun r => by
  have hap : (a_p 5783 : ℝ) = 14 := by exact_mod_cast BSD_ap_p5783
  have key : r ^ 2 - (a_p 5783 : ℝ) * r + ((5783 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 22936/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5791 : BSD_FrobeniusDegreeNonneg_OPEN 5791 := fun r => by
  have hap : (a_p 5791 : ℝ) = 76 := by exact_mod_cast BSD_ap_p5791
  have key : r ^ 2 - (a_p 5791 : ℝ) * r + ((5791 : ℕ) : ℝ) =
      (r - 76/2) ^ 2 + 17388/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (76 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5801 : BSD_FrobeniusDegreeNonneg_OPEN 5801 := fun r => by
  have hap : (a_p 5801 : ℝ) = 50 := by exact_mod_cast BSD_ap_p5801
  have key : r ^ 2 - (a_p 5801 : ℝ) * r + ((5801 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 20704/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5807 : BSD_FrobeniusDegreeNonneg_OPEN 5807 := fun r => by
  have hap : (a_p 5807 : ℝ) = -78 := by exact_mod_cast BSD_ap_p5807
  have key : r ^ 2 - (a_p 5807 : ℝ) * r + ((5807 : ℕ) : ℝ) =
      (r + 78/2) ^ 2 + 17144/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (78 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5813 : BSD_FrobeniusDegreeNonneg_OPEN 5813 := fun r => by
  have hap : (a_p 5813 : ℝ) = 113 := by exact_mod_cast BSD_ap_p5813
  have key : r ^ 2 - (a_p 5813 : ℝ) * r + ((5813 : ℕ) : ℝ) =
      (r - 113/2) ^ 2 + 10483/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (113 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5821 : BSD_FrobeniusDegreeNonneg_OPEN 5821 := fun r => by
  have hap : (a_p 5821 : ℝ) = -58 := by exact_mod_cast BSD_ap_p5821
  have key : r ^ 2 - (a_p 5821 : ℝ) * r + ((5821 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 19920/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5827 : BSD_FrobeniusDegreeNonneg_OPEN 5827 := fun r => by
  have hap : (a_p 5827 : ℝ) = 64 := by exact_mod_cast BSD_ap_p5827
  have key : r ^ 2 - (a_p 5827 : ℝ) * r + ((5827 : ℕ) : ℝ) =
      (r - 64/2) ^ 2 + 19212/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (64 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5839 : BSD_FrobeniusDegreeNonneg_OPEN 5839 := fun r => by
  have hap : (a_p 5839 : ℝ) = -24 := by exact_mod_cast BSD_ap_p5839
  have key : r ^ 2 - (a_p 5839 : ℝ) * r + ((5839 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 22780/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5843 : BSD_FrobeniusDegreeNonneg_OPEN 5843 := fun r => by
  have hap : (a_p 5843 : ℝ) = -112 := by exact_mod_cast BSD_ap_p5843
  have key : r ^ 2 - (a_p 5843 : ℝ) * r + ((5843 : ℕ) : ℝ) =
      (r + 112/2) ^ 2 + 10828/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (112 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5849 : BSD_FrobeniusDegreeNonneg_OPEN 5849 := fun r => by
  have hap : (a_p 5849 : ℝ) = -12 := by exact_mod_cast BSD_ap_p5849
  have key : r ^ 2 - (a_p 5849 : ℝ) * r + ((5849 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 23252/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5851 : BSD_FrobeniusDegreeNonneg_OPEN 5851 := fun r => by
  have hap : (a_p 5851 : ℝ) = -118 := by exact_mod_cast BSD_ap_p5851
  have key : r ^ 2 - (a_p 5851 : ℝ) * r + ((5851 : ℕ) : ℝ) =
      (r + 118/2) ^ 2 + 9480/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (118 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5857 : BSD_FrobeniusDegreeNonneg_OPEN 5857 := fun r => by
  have hap : (a_p 5857 : ℝ) = 65 := by exact_mod_cast BSD_ap_p5857
  have key : r ^ 2 - (a_p 5857 : ℝ) * r + ((5857 : ℕ) : ℝ) =
      (r - 65/2) ^ 2 + 19203/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (65 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5861 : BSD_FrobeniusDegreeNonneg_OPEN 5861 := fun r => by
  have hap : (a_p 5861 : ℝ) = -6 := by exact_mod_cast BSD_ap_p5861
  have key : r ^ 2 - (a_p 5861 : ℝ) * r + ((5861 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 23408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5867 : BSD_FrobeniusDegreeNonneg_OPEN 5867 := fun r => by
  have hap : (a_p 5867 : ℝ) = -15 := by exact_mod_cast BSD_ap_p5867
  have key : r ^ 2 - (a_p 5867 : ℝ) * r + ((5867 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 23243/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5869 : BSD_FrobeniusDegreeNonneg_OPEN 5869 := fun r => by
  have hap : (a_p 5869 : ℝ) = -80 := by exact_mod_cast BSD_ap_p5869
  have key : r ^ 2 - (a_p 5869 : ℝ) * r + ((5869 : ℕ) : ℝ) =
      (r + 80/2) ^ 2 + 17076/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (80 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5879 : BSD_FrobeniusDegreeNonneg_OPEN 5879 := fun r => by
  have hap : (a_p 5879 : ℝ) = 5 := by exact_mod_cast BSD_ap_p5879
  have key : r ^ 2 - (a_p 5879 : ℝ) * r + ((5879 : ℕ) : ℝ) =
      (r - 5/2) ^ 2 + 23491/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (5 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5881 : BSD_FrobeniusDegreeNonneg_OPEN 5881 := fun r => by
  have hap : (a_p 5881 : ℝ) = 48 := by exact_mod_cast BSD_ap_p5881
  have key : r ^ 2 - (a_p 5881 : ℝ) * r + ((5881 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 21220/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5897 : BSD_FrobeniusDegreeNonneg_OPEN 5897 := fun r => by
  have hap : (a_p 5897 : ℝ) = -97 := by exact_mod_cast BSD_ap_p5897
  have key : r ^ 2 - (a_p 5897 : ℝ) * r + ((5897 : ℕ) : ℝ) =
      (r + 97/2) ^ 2 + 14179/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (97 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5903 : BSD_FrobeniusDegreeNonneg_OPEN 5903 := fun r => by
  have hap : (a_p 5903 : ℝ) = -26 := by exact_mod_cast BSD_ap_p5903
  have key : r ^ 2 - (a_p 5903 : ℝ) * r + ((5903 : ℕ) : ℝ) =
      (r + 26/2) ^ 2 + 22936/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (26 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5923 : BSD_FrobeniusDegreeNonneg_OPEN 5923 := fun r => by
  have hap : (a_p 5923 : ℝ) = -7 := by exact_mod_cast BSD_ap_p5923
  have key : r ^ 2 - (a_p 5923 : ℝ) * r + ((5923 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 23643/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5927 : BSD_FrobeniusDegreeNonneg_OPEN 5927 := fun r => by
  have hap : (a_p 5927 : ℝ) = 51 := by exact_mod_cast BSD_ap_p5927
  have key : r ^ 2 - (a_p 5927 : ℝ) * r + ((5927 : ℕ) : ℝ) =
      (r - 51/2) ^ 2 + 21107/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (51 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5939 : BSD_FrobeniusDegreeNonneg_OPEN 5939 := fun r => by
  have hap : (a_p 5939 : ℝ) = 74 := by exact_mod_cast BSD_ap_p5939
  have key : r ^ 2 - (a_p 5939 : ℝ) * r + ((5939 : ℕ) : ℝ) =
      (r - 74/2) ^ 2 + 18280/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (74 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5953 : BSD_FrobeniusDegreeNonneg_OPEN 5953 := fun r => by
  have hap : (a_p 5953 : ℝ) = 72 := by exact_mod_cast BSD_ap_p5953
  have key : r ^ 2 - (a_p 5953 : ℝ) * r + ((5953 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 18628/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5981 : BSD_FrobeniusDegreeNonneg_OPEN 5981 := fun r => by
  have hap : (a_p 5981 : ℝ) = -140 := by exact_mod_cast BSD_ap_p5981
  have key : r ^ 2 - (a_p 5981 : ℝ) * r + ((5981 : ℕ) : ℝ) =
      (r + 140/2) ^ 2 + 4324/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (140 : ℝ)/2)]

theorem BSD_DegreeNonneg_p5987 : BSD_FrobeniusDegreeNonneg_OPEN 5987 := fun r => by
  have hap : (a_p 5987 : ℝ) = -121 := by exact_mod_cast BSD_ap_p5987
  have key : r ^ 2 - (a_p 5987 : ℝ) * r + ((5987 : ℕ) : ℝ) =
      (r + 121/2) ^ 2 + 9307/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (121 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6007 : BSD_FrobeniusDegreeNonneg_OPEN 6007 := fun r => by
  have hap : (a_p 6007 : ℝ) = -140 := by exact_mod_cast BSD_ap_p6007
  have key : r ^ 2 - (a_p 6007 : ℝ) * r + ((6007 : ℕ) : ℝ) =
      (r + 140/2) ^ 2 + 4428/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (140 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6011 : BSD_FrobeniusDegreeNonneg_OPEN 6011 := fun r => by
  have hap : (a_p 6011 : ℝ) = -105 := by exact_mod_cast BSD_ap_p6011
  have key : r ^ 2 - (a_p 6011 : ℝ) * r + ((6011 : ℕ) : ℝ) =
      (r + 105/2) ^ 2 + 13019/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (105 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6029 : BSD_FrobeniusDegreeNonneg_OPEN 6029 := fun r => by
  have hap : (a_p 6029 : ℝ) = 21 := by exact_mod_cast BSD_ap_p6029
  have key : r ^ 2 - (a_p 6029 : ℝ) * r + ((6029 : ℕ) : ℝ) =
      (r - 21/2) ^ 2 + 23675/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (21 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6037 : BSD_FrobeniusDegreeNonneg_OPEN 6037 := fun r => by
  have hap : (a_p 6037 : ℝ) = 53 := by exact_mod_cast BSD_ap_p6037
  have key : r ^ 2 - (a_p 6037 : ℝ) * r + ((6037 : ℕ) : ℝ) =
      (r - 53/2) ^ 2 + 21339/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (53 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6043 : BSD_FrobeniusDegreeNonneg_OPEN 6043 := fun r => by
  have hap : (a_p 6043 : ℝ) = 17 := by exact_mod_cast BSD_ap_p6043
  have key : r ^ 2 - (a_p 6043 : ℝ) * r + ((6043 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 23883/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6047 : BSD_FrobeniusDegreeNonneg_OPEN 6047 := fun r => by
  have hap : (a_p 6047 : ℝ) = 40 := by exact_mod_cast BSD_ap_p6047
  have key : r ^ 2 - (a_p 6047 : ℝ) * r + ((6047 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 22588/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6053 : BSD_FrobeniusDegreeNonneg_OPEN 6053 := fun r => by
  have hap : (a_p 6053 : ℝ) = 78 := by exact_mod_cast BSD_ap_p6053
  have key : r ^ 2 - (a_p 6053 : ℝ) * r + ((6053 : ℕ) : ℝ) =
      (r - 78/2) ^ 2 + 18128/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (78 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6067 : BSD_FrobeniusDegreeNonneg_OPEN 6067 := fun r => by
  have hap : (a_p 6067 : ℝ) = 34 := by exact_mod_cast BSD_ap_p6067
  have key : r ^ 2 - (a_p 6067 : ℝ) * r + ((6067 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 23112/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6073 : BSD_FrobeniusDegreeNonneg_OPEN 6073 := fun r => by
  have hap : (a_p 6073 : ℝ) = 6 := by exact_mod_cast BSD_ap_p6073
  have key : r ^ 2 - (a_p 6073 : ℝ) * r + ((6073 : ℕ) : ℝ) =
      (r - 6/2) ^ 2 + 24256/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6079 : BSD_FrobeniusDegreeNonneg_OPEN 6079 := fun r => by
  have hap : (a_p 6079 : ℝ) = 50 := by exact_mod_cast BSD_ap_p6079
  have key : r ^ 2 - (a_p 6079 : ℝ) * r + ((6079 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 21816/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6089 : BSD_FrobeniusDegreeNonneg_OPEN 6089 := fun r => by
  have hap : (a_p 6089 : ℝ) = 90 := by exact_mod_cast BSD_ap_p6089
  have key : r ^ 2 - (a_p 6089 : ℝ) * r + ((6089 : ℕ) : ℝ) =
      (r - 90/2) ^ 2 + 16256/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (90 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6091 : BSD_FrobeniusDegreeNonneg_OPEN 6091 := fun r => by
  have hap : (a_p 6091 : ℝ) = -98 := by exact_mod_cast BSD_ap_p6091
  have key : r ^ 2 - (a_p 6091 : ℝ) * r + ((6091 : ℕ) : ℝ) =
      (r + 98/2) ^ 2 + 14760/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (98 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6101 : BSD_FrobeniusDegreeNonneg_OPEN 6101 := fun r => by
  have hap : (a_p 6101 : ℝ) = 112 := by exact_mod_cast BSD_ap_p6101
  have key : r ^ 2 - (a_p 6101 : ℝ) * r + ((6101 : ℕ) : ℝ) =
      (r - 112/2) ^ 2 + 11860/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (112 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6113 : BSD_FrobeniusDegreeNonneg_OPEN 6113 := fun r => by
  have hap : (a_p 6113 : ℝ) = -58 := by exact_mod_cast BSD_ap_p6113
  have key : r ^ 2 - (a_p 6113 : ℝ) * r + ((6113 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 21088/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6121 : BSD_FrobeniusDegreeNonneg_OPEN 6121 := fun r => by
  have hap : (a_p 6121 : ℝ) = -101 := by exact_mod_cast BSD_ap_p6121
  have key : r ^ 2 - (a_p 6121 : ℝ) * r + ((6121 : ℕ) : ℝ) =
      (r + 101/2) ^ 2 + 14283/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (101 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6131 : BSD_FrobeniusDegreeNonneg_OPEN 6131 := fun r => by
  have hap : (a_p 6131 : ℝ) = -5 := by exact_mod_cast BSD_ap_p6131
  have key : r ^ 2 - (a_p 6131 : ℝ) * r + ((6131 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 24499/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6133 : BSD_FrobeniusDegreeNonneg_OPEN 6133 := fun r => by
  have hap : (a_p 6133 : ℝ) = -16 := by exact_mod_cast BSD_ap_p6133
  have key : r ^ 2 - (a_p 6133 : ℝ) * r + ((6133 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 24276/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6143 : BSD_FrobeniusDegreeNonneg_OPEN 6143 := fun r => by
  have hap : (a_p 6143 : ℝ) = 92 := by exact_mod_cast BSD_ap_p6143
  have key : r ^ 2 - (a_p 6143 : ℝ) * r + ((6143 : ℕ) : ℝ) =
      (r - 92/2) ^ 2 + 16108/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (92 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6151 : BSD_FrobeniusDegreeNonneg_OPEN 6151 := fun r => by
  have hap : (a_p 6151 : ℝ) = 38 := by exact_mod_cast BSD_ap_p6151
  have key : r ^ 2 - (a_p 6151 : ℝ) * r + ((6151 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 23160/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6163 : BSD_FrobeniusDegreeNonneg_OPEN 6163 := fun r => by
  have hap : (a_p 6163 : ℝ) = 79 := by exact_mod_cast BSD_ap_p6163
  have key : r ^ 2 - (a_p 6163 : ℝ) * r + ((6163 : ℕ) : ℝ) =
      (r - 79/2) ^ 2 + 18411/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (79 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6173 : BSD_FrobeniusDegreeNonneg_OPEN 6173 := fun r => by
  have hap : (a_p 6173 : ℝ) = 14 := by exact_mod_cast BSD_ap_p6173
  have key : r ^ 2 - (a_p 6173 : ℝ) * r + ((6173 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 24496/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6197 : BSD_FrobeniusDegreeNonneg_OPEN 6197 := fun r => by
  have hap : (a_p 6197 : ℝ) = -99 := by exact_mod_cast BSD_ap_p6197
  have key : r ^ 2 - (a_p 6197 : ℝ) * r + ((6197 : ℕ) : ℝ) =
      (r + 99/2) ^ 2 + 14987/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (99 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6199 : BSD_FrobeniusDegreeNonneg_OPEN 6199 := fun r => by
  have hap : (a_p 6199 : ℝ) = 52 := by exact_mod_cast BSD_ap_p6199
  have key : r ^ 2 - (a_p 6199 : ℝ) * r + ((6199 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 22092/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6203 : BSD_FrobeniusDegreeNonneg_OPEN 6203 := fun r => by
  have hap : (a_p 6203 : ℝ) = 16 := by exact_mod_cast BSD_ap_p6203
  have key : r ^ 2 - (a_p 6203 : ℝ) * r + ((6203 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 24556/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6211 : BSD_FrobeniusDegreeNonneg_OPEN 6211 := fun r => by
  have hap : (a_p 6211 : ℝ) = -20 := by exact_mod_cast BSD_ap_p6211
  have key : r ^ 2 - (a_p 6211 : ℝ) * r + ((6211 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 24444/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6217 : BSD_FrobeniusDegreeNonneg_OPEN 6217 := fun r => by
  have hap : (a_p 6217 : ℝ) = -58 := by exact_mod_cast BSD_ap_p6217
  have key : r ^ 2 - (a_p 6217 : ℝ) * r + ((6217 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 21504/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6221 : BSD_FrobeniusDegreeNonneg_OPEN 6221 := fun r => by
  have hap : (a_p 6221 : ℝ) = -30 := by exact_mod_cast BSD_ap_p6221
  have key : r ^ 2 - (a_p 6221 : ℝ) * r + ((6221 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 23984/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6229 : BSD_FrobeniusDegreeNonneg_OPEN 6229 := fun r => by
  have hap : (a_p 6229 : ℝ) = -49 := by exact_mod_cast BSD_ap_p6229
  have key : r ^ 2 - (a_p 6229 : ℝ) * r + ((6229 : ℕ) : ℝ) =
      (r + 49/2) ^ 2 + 22515/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (49 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6247 : BSD_FrobeniusDegreeNonneg_OPEN 6247 := fun r => by
  have hap : (a_p 6247 : ℝ) = -38 := by exact_mod_cast BSD_ap_p6247
  have key : r ^ 2 - (a_p 6247 : ℝ) * r + ((6247 : ℕ) : ℝ) =
      (r + 38/2) ^ 2 + 23544/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6257 : BSD_FrobeniusDegreeNonneg_OPEN 6257 := fun r => by
  have hap : (a_p 6257 : ℝ) = -19 := by exact_mod_cast BSD_ap_p6257
  have key : r ^ 2 - (a_p 6257 : ℝ) * r + ((6257 : ℕ) : ℝ) =
      (r + 19/2) ^ 2 + 24667/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (19 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6263 : BSD_FrobeniusDegreeNonneg_OPEN 6263 := fun r => by
  have hap : (a_p 6263 : ℝ) = 7 := by exact_mod_cast BSD_ap_p6263
  have key : r ^ 2 - (a_p 6263 : ℝ) * r + ((6263 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 25003/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6269 : BSD_FrobeniusDegreeNonneg_OPEN 6269 := fun r => by
  have hap : (a_p 6269 : ℝ) = 90 := by exact_mod_cast BSD_ap_p6269
  have key : r ^ 2 - (a_p 6269 : ℝ) * r + ((6269 : ℕ) : ℝ) =
      (r - 90/2) ^ 2 + 16976/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (90 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6271 : BSD_FrobeniusDegreeNonneg_OPEN 6271 := fun r => by
  have hap : (a_p 6271 : ℝ) = -15 := by exact_mod_cast BSD_ap_p6271
  have key : r ^ 2 - (a_p 6271 : ℝ) * r + ((6271 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 24859/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6277 : BSD_FrobeniusDegreeNonneg_OPEN 6277 := fun r => by
  have hap : (a_p 6277 : ℝ) = -22 := by exact_mod_cast BSD_ap_p6277
  have key : r ^ 2 - (a_p 6277 : ℝ) * r + ((6277 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 24624/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6287 : BSD_FrobeniusDegreeNonneg_OPEN 6287 := fun r => by
  have hap : (a_p 6287 : ℝ) = 126 := by exact_mod_cast BSD_ap_p6287
  have key : r ^ 2 - (a_p 6287 : ℝ) * r + ((6287 : ℕ) : ℝ) =
      (r - 126/2) ^ 2 + 9272/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (126 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6299 : BSD_FrobeniusDegreeNonneg_OPEN 6299 := fun r => by
  have hap : (a_p 6299 : ℝ) = 30 := by exact_mod_cast BSD_ap_p6299
  have key : r ^ 2 - (a_p 6299 : ℝ) * r + ((6299 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 24296/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6301 : BSD_FrobeniusDegreeNonneg_OPEN 6301 := fun r => by
  have hap : (a_p 6301 : ℝ) = 9 := by exact_mod_cast BSD_ap_p6301
  have key : r ^ 2 - (a_p 6301 : ℝ) * r + ((6301 : ℕ) : ℝ) =
      (r - 9/2) ^ 2 + 25123/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (9 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6311 : BSD_FrobeniusDegreeNonneg_OPEN 6311 := fun r => by
  have hap : (a_p 6311 : ℝ) = -72 := by exact_mod_cast BSD_ap_p6311
  have key : r ^ 2 - (a_p 6311 : ℝ) * r + ((6311 : ℕ) : ℝ) =
      (r + 72/2) ^ 2 + 20060/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (72 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6317 : BSD_FrobeniusDegreeNonneg_OPEN 6317 := fun r => by
  have hap : (a_p 6317 : ℝ) = -63 := by exact_mod_cast BSD_ap_p6317
  have key : r ^ 2 - (a_p 6317 : ℝ) * r + ((6317 : ℕ) : ℝ) =
      (r + 63/2) ^ 2 + 21299/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (63 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6323 : BSD_FrobeniusDegreeNonneg_OPEN 6323 := fun r => by
  have hap : (a_p 6323 : ℝ) = 39 := by exact_mod_cast BSD_ap_p6323
  have key : r ^ 2 - (a_p 6323 : ℝ) * r + ((6323 : ℕ) : ℝ) =
      (r - 39/2) ^ 2 + 23771/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (39 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6329 : BSD_FrobeniusDegreeNonneg_OPEN 6329 := fun r => by
  have hap : (a_p 6329 : ℝ) = 22 := by exact_mod_cast BSD_ap_p6329
  have key : r ^ 2 - (a_p 6329 : ℝ) * r + ((6329 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 24832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6337 : BSD_FrobeniusDegreeNonneg_OPEN 6337 := fun r => by
  have hap : (a_p 6337 : ℝ) = -66 := by exact_mod_cast BSD_ap_p6337
  have key : r ^ 2 - (a_p 6337 : ℝ) * r + ((6337 : ℕ) : ℝ) =
      (r + 66/2) ^ 2 + 20992/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (66 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6343 : BSD_FrobeniusDegreeNonneg_OPEN 6343 := fun r => by
  have hap : (a_p 6343 : ℝ) = -96 := by exact_mod_cast BSD_ap_p6343
  have key : r ^ 2 - (a_p 6343 : ℝ) * r + ((6343 : ℕ) : ℝ) =
      (r + 96/2) ^ 2 + 16156/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (96 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6353 : BSD_FrobeniusDegreeNonneg_OPEN 6353 := fun r => by
  have hap : (a_p 6353 : ℝ) = -30 := by exact_mod_cast BSD_ap_p6353
  have key : r ^ 2 - (a_p 6353 : ℝ) * r + ((6353 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 24512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6359 : BSD_FrobeniusDegreeNonneg_OPEN 6359 := fun r => by
  have hap : (a_p 6359 : ℝ) = -120 := by exact_mod_cast BSD_ap_p6359
  have key : r ^ 2 - (a_p 6359 : ℝ) * r + ((6359 : ℕ) : ℝ) =
      (r + 120/2) ^ 2 + 11036/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (120 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6361 : BSD_FrobeniusDegreeNonneg_OPEN 6361 := fun r => by
  have hap : (a_p 6361 : ℝ) = -106 := by exact_mod_cast BSD_ap_p6361
  have key : r ^ 2 - (a_p 6361 : ℝ) * r + ((6361 : ℕ) : ℝ) =
      (r + 106/2) ^ 2 + 14208/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (106 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6367 : BSD_FrobeniusDegreeNonneg_OPEN 6367 := fun r => by
  have hap : (a_p 6367 : ℝ) = -32 := by exact_mod_cast BSD_ap_p6367
  have key : r ^ 2 - (a_p 6367 : ℝ) * r + ((6367 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 24444/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6373 : BSD_FrobeniusDegreeNonneg_OPEN 6373 := fun r => by
  have hap : (a_p 6373 : ℝ) = -82 := by exact_mod_cast BSD_ap_p6373
  have key : r ^ 2 - (a_p 6373 : ℝ) * r + ((6373 : ℕ) : ℝ) =
      (r + 82/2) ^ 2 + 18768/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (82 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6379 : BSD_FrobeniusDegreeNonneg_OPEN 6379 := fun r => by
  have hap : (a_p 6379 : ℝ) = -54 := by exact_mod_cast BSD_ap_p6379
  have key : r ^ 2 - (a_p 6379 : ℝ) * r + ((6379 : ℕ) : ℝ) =
      (r + 54/2) ^ 2 + 22600/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6389 : BSD_FrobeniusDegreeNonneg_OPEN 6389 := fun r => by
  have hap : (a_p 6389 : ℝ) = 99 := by exact_mod_cast BSD_ap_p6389
  have key : r ^ 2 - (a_p 6389 : ℝ) * r + ((6389 : ℕ) : ℝ) =
      (r - 99/2) ^ 2 + 15755/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (99 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6397 : BSD_FrobeniusDegreeNonneg_OPEN 6397 := fun r => by
  have hap : (a_p 6397 : ℝ) = -92 := by exact_mod_cast BSD_ap_p6397
  have key : r ^ 2 - (a_p 6397 : ℝ) * r + ((6397 : ℕ) : ℝ) =
      (r + 92/2) ^ 2 + 17124/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (92 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6421 : BSD_FrobeniusDegreeNonneg_OPEN 6421 := fun r => by
  have hap : (a_p 6421 : ℝ) = 32 := by exact_mod_cast BSD_ap_p6421
  have key : r ^ 2 - (a_p 6421 : ℝ) * r + ((6421 : ℕ) : ℝ) =
      (r - 32/2) ^ 2 + 24660/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6427 : BSD_FrobeniusDegreeNonneg_OPEN 6427 := fun r => by
  have hap : (a_p 6427 : ℝ) = 29 := by exact_mod_cast BSD_ap_p6427
  have key : r ^ 2 - (a_p 6427 : ℝ) * r + ((6427 : ℕ) : ℝ) =
      (r - 29/2) ^ 2 + 24867/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (29 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6449 : BSD_FrobeniusDegreeNonneg_OPEN 6449 := fun r => by
  have hap : (a_p 6449 : ℝ) = 25 := by exact_mod_cast BSD_ap_p6449
  have key : r ^ 2 - (a_p 6449 : ℝ) * r + ((6449 : ℕ) : ℝ) =
      (r - 25/2) ^ 2 + 25171/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (25 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6451 : BSD_FrobeniusDegreeNonneg_OPEN 6451 := fun r => by
  have hap : (a_p 6451 : ℝ) = -12 := by exact_mod_cast BSD_ap_p6451
  have key : r ^ 2 - (a_p 6451 : ℝ) * r + ((6451 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 25660/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6469 : BSD_FrobeniusDegreeNonneg_OPEN 6469 := fun r => by
  have hap : (a_p 6469 : ℝ) = 31 := by exact_mod_cast BSD_ap_p6469
  have key : r ^ 2 - (a_p 6469 : ℝ) * r + ((6469 : ℕ) : ℝ) =
      (r - 31/2) ^ 2 + 24915/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (31 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6473 : BSD_FrobeniusDegreeNonneg_OPEN 6473 := fun r => by
  have hap : (a_p 6473 : ℝ) = 33 := by exact_mod_cast BSD_ap_p6473
  have key : r ^ 2 - (a_p 6473 : ℝ) * r + ((6473 : ℕ) : ℝ) =
      (r - 33/2) ^ 2 + 24803/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (33 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6481 : BSD_FrobeniusDegreeNonneg_OPEN 6481 := fun r => by
  have hap : (a_p 6481 : ℝ) = 146 := by exact_mod_cast BSD_ap_p6481
  have key : r ^ 2 - (a_p 6481 : ℝ) * r + ((6481 : ℕ) : ℝ) =
      (r - 146/2) ^ 2 + 4608/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (146 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6491 : BSD_FrobeniusDegreeNonneg_OPEN 6491 := fun r => by
  have hap : (a_p 6491 : ℝ) = -75 := by exact_mod_cast BSD_ap_p6491
  have key : r ^ 2 - (a_p 6491 : ℝ) * r + ((6491 : ℕ) : ℝ) =
      (r + 75/2) ^ 2 + 20339/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (75 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6521 : BSD_FrobeniusDegreeNonneg_OPEN 6521 := fun r => by
  have hap : (a_p 6521 : ℝ) = -9 := by exact_mod_cast BSD_ap_p6521
  have key : r ^ 2 - (a_p 6521 : ℝ) * r + ((6521 : ℕ) : ℝ) =
      (r + 9/2) ^ 2 + 26003/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (9 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6529 : BSD_FrobeniusDegreeNonneg_OPEN 6529 := fun r => by
  have hap : (a_p 6529 : ℝ) = -14 := by exact_mod_cast BSD_ap_p6529
  have key : r ^ 2 - (a_p 6529 : ℝ) * r + ((6529 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 25920/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6547 : BSD_FrobeniusDegreeNonneg_OPEN 6547 := fun r => by
  have hap : (a_p 6547 : ℝ) = -58 := by exact_mod_cast BSD_ap_p6547
  have key : r ^ 2 - (a_p 6547 : ℝ) * r + ((6547 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 22824/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6551 : BSD_FrobeniusDegreeNonneg_OPEN 6551 := fun r => by
  have hap : (a_p 6551 : ℝ) = -86 := by exact_mod_cast BSD_ap_p6551
  have key : r ^ 2 - (a_p 6551 : ℝ) * r + ((6551 : ℕ) : ℝ) =
      (r + 86/2) ^ 2 + 18808/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (86 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6553 : BSD_FrobeniusDegreeNonneg_OPEN 6553 := fun r => by
  have hap : (a_p 6553 : ℝ) = -20 := by exact_mod_cast BSD_ap_p6553
  have key : r ^ 2 - (a_p 6553 : ℝ) * r + ((6553 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 25812/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6563 : BSD_FrobeniusDegreeNonneg_OPEN 6563 := fun r => by
  have hap : (a_p 6563 : ℝ) = 100 := by exact_mod_cast BSD_ap_p6563
  have key : r ^ 2 - (a_p 6563 : ℝ) * r + ((6563 : ℕ) : ℝ) =
      (r - 100/2) ^ 2 + 16252/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (100 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6569 : BSD_FrobeniusDegreeNonneg_OPEN 6569 := fun r => by
  have hap : (a_p 6569 : ℝ) = 18 := by exact_mod_cast BSD_ap_p6569
  have key : r ^ 2 - (a_p 6569 : ℝ) * r + ((6569 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 25952/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6571 : BSD_FrobeniusDegreeNonneg_OPEN 6571 := fun r => by
  have hap : (a_p 6571 : ℝ) = 20 := by exact_mod_cast BSD_ap_p6571
  have key : r ^ 2 - (a_p 6571 : ℝ) * r + ((6571 : ℕ) : ℝ) =
      (r - 20/2) ^ 2 + 25884/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6577 : BSD_FrobeniusDegreeNonneg_OPEN 6577 := fun r => by
  have hap : (a_p 6577 : ℝ) = -82 := by exact_mod_cast BSD_ap_p6577
  have key : r ^ 2 - (a_p 6577 : ℝ) * r + ((6577 : ℕ) : ℝ) =
      (r + 82/2) ^ 2 + 19584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (82 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6581 : BSD_FrobeniusDegreeNonneg_OPEN 6581 := fun r => by
  have hap : (a_p 6581 : ℝ) = -129 := by exact_mod_cast BSD_ap_p6581
  have key : r ^ 2 - (a_p 6581 : ℝ) * r + ((6581 : ℕ) : ℝ) =
      (r + 129/2) ^ 2 + 9683/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (129 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6599 : BSD_FrobeniusDegreeNonneg_OPEN 6599 := fun r => by
  have hap : (a_p 6599 : ℝ) = -38 := by exact_mod_cast BSD_ap_p6599
  have key : r ^ 2 - (a_p 6599 : ℝ) * r + ((6599 : ℕ) : ℝ) =
      (r + 38/2) ^ 2 + 24952/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6607 : BSD_FrobeniusDegreeNonneg_OPEN 6607 := fun r => by
  have hap : (a_p 6607 : ℝ) = 98 := by exact_mod_cast BSD_ap_p6607
  have key : r ^ 2 - (a_p 6607 : ℝ) * r + ((6607 : ℕ) : ℝ) =
      (r - 98/2) ^ 2 + 16824/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (98 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6619 : BSD_FrobeniusDegreeNonneg_OPEN 6619 := fun r => by
  have hap : (a_p 6619 : ℝ) = -110 := by exact_mod_cast BSD_ap_p6619
  have key : r ^ 2 - (a_p 6619 : ℝ) * r + ((6619 : ℕ) : ℝ) =
      (r + 110/2) ^ 2 + 14376/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (110 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6637 : BSD_FrobeniusDegreeNonneg_OPEN 6637 := fun r => by
  have hap : (a_p 6637 : ℝ) = -118 := by exact_mod_cast BSD_ap_p6637
  have key : r ^ 2 - (a_p 6637 : ℝ) * r + ((6637 : ℕ) : ℝ) =
      (r + 118/2) ^ 2 + 12624/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (118 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6653 : BSD_FrobeniusDegreeNonneg_OPEN 6653 := fun r => by
  have hap : (a_p 6653 : ℝ) = 65 := by exact_mod_cast BSD_ap_p6653
  have key : r ^ 2 - (a_p 6653 : ℝ) * r + ((6653 : ℕ) : ℝ) =
      (r - 65/2) ^ 2 + 22387/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (65 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6659 : BSD_FrobeniusDegreeNonneg_OPEN 6659 := fun r => by
  have hap : (a_p 6659 : ℝ) = 69 := by exact_mod_cast BSD_ap_p6659
  have key : r ^ 2 - (a_p 6659 : ℝ) * r + ((6659 : ℕ) : ℝ) =
      (r - 69/2) ^ 2 + 21875/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (69 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6661 : BSD_FrobeniusDegreeNonneg_OPEN 6661 := fun r => by
  have hap : (a_p 6661 : ℝ) = 110 := by exact_mod_cast BSD_ap_p6661
  have key : r ^ 2 - (a_p 6661 : ℝ) * r + ((6661 : ℕ) : ℝ) =
      (r - 110/2) ^ 2 + 14544/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (110 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6673 : BSD_FrobeniusDegreeNonneg_OPEN 6673 := fun r => by
  have hap : (a_p 6673 : ℝ) = -156 := by exact_mod_cast BSD_ap_p6673
  have key : r ^ 2 - (a_p 6673 : ℝ) * r + ((6673 : ℕ) : ℝ) =
      (r + 156/2) ^ 2 + 2356/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (156 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6679 : BSD_FrobeniusDegreeNonneg_OPEN 6679 := fun r => by
  have hap : (a_p 6679 : ℝ) = -118 := by exact_mod_cast BSD_ap_p6679
  have key : r ^ 2 - (a_p 6679 : ℝ) * r + ((6679 : ℕ) : ℝ) =
      (r + 118/2) ^ 2 + 12792/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (118 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6689 : BSD_FrobeniusDegreeNonneg_OPEN 6689 := fun r => by
  have hap : (a_p 6689 : ℝ) = 109 := by exact_mod_cast BSD_ap_p6689
  have key : r ^ 2 - (a_p 6689 : ℝ) * r + ((6689 : ℕ) : ℝ) =
      (r - 109/2) ^ 2 + 14875/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (109 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6691 : BSD_FrobeniusDegreeNonneg_OPEN 6691 := fun r => by
  have hap : (a_p 6691 : ℝ) = 13 := by exact_mod_cast BSD_ap_p6691
  have key : r ^ 2 - (a_p 6691 : ℝ) * r + ((6691 : ℕ) : ℝ) =
      (r - 13/2) ^ 2 + 26595/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (13 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6701 : BSD_FrobeniusDegreeNonneg_OPEN 6701 := fun r => by
  have hap : (a_p 6701 : ℝ) = 40 := by exact_mod_cast BSD_ap_p6701
  have key : r ^ 2 - (a_p 6701 : ℝ) * r + ((6701 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 25204/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6703 : BSD_FrobeniusDegreeNonneg_OPEN 6703 := fun r => by
  have hap : (a_p 6703 : ℝ) = 71 := by exact_mod_cast BSD_ap_p6703
  have key : r ^ 2 - (a_p 6703 : ℝ) * r + ((6703 : ℕ) : ℝ) =
      (r - 71/2) ^ 2 + 21771/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (71 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6709 : BSD_FrobeniusDegreeNonneg_OPEN 6709 := fun r => by
  have hap : (a_p 6709 : ℝ) = 122 := by exact_mod_cast BSD_ap_p6709
  have key : r ^ 2 - (a_p 6709 : ℝ) * r + ((6709 : ℕ) : ℝ) =
      (r - 122/2) ^ 2 + 11952/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (122 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6719 : BSD_FrobeniusDegreeNonneg_OPEN 6719 := fun r => by
  have hap : (a_p 6719 : ℝ) = 132 := by exact_mod_cast BSD_ap_p6719
  have key : r ^ 2 - (a_p 6719 : ℝ) * r + ((6719 : ℕ) : ℝ) =
      (r - 132/2) ^ 2 + 9452/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (132 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6733 : BSD_FrobeniusDegreeNonneg_OPEN 6733 := fun r => by
  have hap : (a_p 6733 : ℝ) = 137 := by exact_mod_cast BSD_ap_p6733
  have key : r ^ 2 - (a_p 6733 : ℝ) * r + ((6733 : ℕ) : ℝ) =
      (r - 137/2) ^ 2 + 8163/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (137 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6737 : BSD_FrobeniusDegreeNonneg_OPEN 6737 := fun r => by
  have hap : (a_p 6737 : ℝ) = 46 := by exact_mod_cast BSD_ap_p6737
  have key : r ^ 2 - (a_p 6737 : ℝ) * r + ((6737 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 24832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6761 : BSD_FrobeniusDegreeNonneg_OPEN 6761 := fun r => by
  have hap : (a_p 6761 : ℝ) = -76 := by exact_mod_cast BSD_ap_p6761
  have key : r ^ 2 - (a_p 6761 : ℝ) * r + ((6761 : ℕ) : ℝ) =
      (r + 76/2) ^ 2 + 21268/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (76 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6763 : BSD_FrobeniusDegreeNonneg_OPEN 6763 := fun r => by
  have hap : (a_p 6763 : ℝ) = -3 := by exact_mod_cast BSD_ap_p6763
  have key : r ^ 2 - (a_p 6763 : ℝ) * r + ((6763 : ℕ) : ℝ) =
      (r + 3/2) ^ 2 + 27043/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (3 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6779 : BSD_FrobeniusDegreeNonneg_OPEN 6779 := fun r => by
  have hap : (a_p 6779 : ℝ) = -20 := by exact_mod_cast BSD_ap_p6779
  have key : r ^ 2 - (a_p 6779 : ℝ) * r + ((6779 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 26716/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6781 : BSD_FrobeniusDegreeNonneg_OPEN 6781 := fun r => by
  have hap : (a_p 6781 : ℝ) = -43 := by exact_mod_cast BSD_ap_p6781
  have key : r ^ 2 - (a_p 6781 : ℝ) * r + ((6781 : ℕ) : ℝ) =
      (r + 43/2) ^ 2 + 25275/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (43 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6791 : BSD_FrobeniusDegreeNonneg_OPEN 6791 := fun r => by
  have hap : (a_p 6791 : ℝ) = -5 := by exact_mod_cast BSD_ap_p6791
  have key : r ^ 2 - (a_p 6791 : ℝ) * r + ((6791 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 27139/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6793 : BSD_FrobeniusDegreeNonneg_OPEN 6793 := fun r => by
  have hap : (a_p 6793 : ℝ) = 62 := by exact_mod_cast BSD_ap_p6793
  have key : r ^ 2 - (a_p 6793 : ℝ) * r + ((6793 : ℕ) : ℝ) =
      (r - 62/2) ^ 2 + 23328/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (62 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6803 : BSD_FrobeniusDegreeNonneg_OPEN 6803 := fun r => by
  have hap : (a_p 6803 : ℝ) = 57 := by exact_mod_cast BSD_ap_p6803
  have key : r ^ 2 - (a_p 6803 : ℝ) * r + ((6803 : ℕ) : ℝ) =
      (r - 57/2) ^ 2 + 23963/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (57 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6823 : BSD_FrobeniusDegreeNonneg_OPEN 6823 := fun r => by
  have hap : (a_p 6823 : ℝ) = 88 := by exact_mod_cast BSD_ap_p6823
  have key : r ^ 2 - (a_p 6823 : ℝ) * r + ((6823 : ℕ) : ℝ) =
      (r - 88/2) ^ 2 + 19548/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (88 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6827 : BSD_FrobeniusDegreeNonneg_OPEN 6827 := fun r => by
  have hap : (a_p 6827 : ℝ) = -52 := by exact_mod_cast BSD_ap_p6827
  have key : r ^ 2 - (a_p 6827 : ℝ) * r + ((6827 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 24604/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6829 : BSD_FrobeniusDegreeNonneg_OPEN 6829 := fun r => by
  have hap : (a_p 6829 : ℝ) = 61 := by exact_mod_cast BSD_ap_p6829
  have key : r ^ 2 - (a_p 6829 : ℝ) * r + ((6829 : ℕ) : ℝ) =
      (r - 61/2) ^ 2 + 23595/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (61 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6833 : BSD_FrobeniusDegreeNonneg_OPEN 6833 := fun r => by
  have hap : (a_p 6833 : ℝ) = 6 := by exact_mod_cast BSD_ap_p6833
  have key : r ^ 2 - (a_p 6833 : ℝ) * r + ((6833 : ℕ) : ℝ) =
      (r - 6/2) ^ 2 + 27296/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6841 : BSD_FrobeniusDegreeNonneg_OPEN 6841 := fun r => by
  have hap : (a_p 6841 : ℝ) = -84 := by exact_mod_cast BSD_ap_p6841
  have key : r ^ 2 - (a_p 6841 : ℝ) * r + ((6841 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 20308/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6857 : BSD_FrobeniusDegreeNonneg_OPEN 6857 := fun r => by
  have hap : (a_p 6857 : ℝ) = 27 := by exact_mod_cast BSD_ap_p6857
  have key : r ^ 2 - (a_p 6857 : ℝ) * r + ((6857 : ℕ) : ℝ) =
      (r - 27/2) ^ 2 + 26699/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (27 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6863 : BSD_FrobeniusDegreeNonneg_OPEN 6863 := fun r => by
  have hap : (a_p 6863 : ℝ) = -84 := by exact_mod_cast BSD_ap_p6863
  have key : r ^ 2 - (a_p 6863 : ℝ) * r + ((6863 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 20396/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6869 : BSD_FrobeniusDegreeNonneg_OPEN 6869 := fun r => by
  have hap : (a_p 6869 : ℝ) = -25 := by exact_mod_cast BSD_ap_p6869
  have key : r ^ 2 - (a_p 6869 : ℝ) * r + ((6869 : ℕ) : ℝ) =
      (r + 25/2) ^ 2 + 26851/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (25 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6871 : BSD_FrobeniusDegreeNonneg_OPEN 6871 := fun r => by
  have hap : (a_p 6871 : ℝ) = -4 := by exact_mod_cast BSD_ap_p6871
  have key : r ^ 2 - (a_p 6871 : ℝ) * r + ((6871 : ℕ) : ℝ) =
      (r + 4/2) ^ 2 + 27468/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (4 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6883 : BSD_FrobeniusDegreeNonneg_OPEN 6883 := fun r => by
  have hap : (a_p 6883 : ℝ) = 126 := by exact_mod_cast BSD_ap_p6883
  have key : r ^ 2 - (a_p 6883 : ℝ) * r + ((6883 : ℕ) : ℝ) =
      (r - 126/2) ^ 2 + 11656/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (126 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6899 : BSD_FrobeniusDegreeNonneg_OPEN 6899 := fun r => by
  have hap : (a_p 6899 : ℝ) = 10 := by exact_mod_cast BSD_ap_p6899
  have key : r ^ 2 - (a_p 6899 : ℝ) * r + ((6899 : ℕ) : ℝ) =
      (r - 10/2) ^ 2 + 27496/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (10 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6907 : BSD_FrobeniusDegreeNonneg_OPEN 6907 := fun r => by
  have hap : (a_p 6907 : ℝ) = 154 := by exact_mod_cast BSD_ap_p6907
  have key : r ^ 2 - (a_p 6907 : ℝ) * r + ((6907 : ℕ) : ℝ) =
      (r - 154/2) ^ 2 + 3912/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (154 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6911 : BSD_FrobeniusDegreeNonneg_OPEN 6911 := fun r => by
  have hap : (a_p 6911 : ℝ) = -8 := by exact_mod_cast BSD_ap_p6911
  have key : r ^ 2 - (a_p 6911 : ℝ) * r + ((6911 : ℕ) : ℝ) =
      (r + 8/2) ^ 2 + 27580/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (8 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6917 : BSD_FrobeniusDegreeNonneg_OPEN 6917 := fun r => by
  have hap : (a_p 6917 : ℝ) = 38 := by exact_mod_cast BSD_ap_p6917
  have key : r ^ 2 - (a_p 6917 : ℝ) * r + ((6917 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 26224/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6947 : BSD_FrobeniusDegreeNonneg_OPEN 6947 := fun r => by
  have hap : (a_p 6947 : ℝ) = 66 := by exact_mod_cast BSD_ap_p6947
  have key : r ^ 2 - (a_p 6947 : ℝ) * r + ((6947 : ℕ) : ℝ) =
      (r - 66/2) ^ 2 + 23432/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (66 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6949 : BSD_FrobeniusDegreeNonneg_OPEN 6949 := fun r => by
  have hap : (a_p 6949 : ℝ) = -88 := by exact_mod_cast BSD_ap_p6949
  have key : r ^ 2 - (a_p 6949 : ℝ) * r + ((6949 : ℕ) : ℝ) =
      (r + 88/2) ^ 2 + 20052/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (88 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6959 : BSD_FrobeniusDegreeNonneg_OPEN 6959 := fun r => by
  have hap : (a_p 6959 : ℝ) = -72 := by exact_mod_cast BSD_ap_p6959
  have key : r ^ 2 - (a_p 6959 : ℝ) * r + ((6959 : ℕ) : ℝ) =
      (r + 72/2) ^ 2 + 22652/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (72 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6961 : BSD_FrobeniusDegreeNonneg_OPEN 6961 := fun r => by
  have hap : (a_p 6961 : ℝ) = -66 := by exact_mod_cast BSD_ap_p6961
  have key : r ^ 2 - (a_p 6961 : ℝ) * r + ((6961 : ℕ) : ℝ) =
      (r + 66/2) ^ 2 + 23488/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (66 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6967 : BSD_FrobeniusDegreeNonneg_OPEN 6967 := fun r => by
  have hap : (a_p 6967 : ℝ) = 16 := by exact_mod_cast BSD_ap_p6967
  have key : r ^ 2 - (a_p 6967 : ℝ) * r + ((6967 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 27612/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6971 : BSD_FrobeniusDegreeNonneg_OPEN 6971 := fun r => by
  have hap : (a_p 6971 : ℝ) = 82 := by exact_mod_cast BSD_ap_p6971
  have key : r ^ 2 - (a_p 6971 : ℝ) * r + ((6971 : ℕ) : ℝ) =
      (r - 82/2) ^ 2 + 21160/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (82 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6977 : BSD_FrobeniusDegreeNonneg_OPEN 6977 := fun r => by
  have hap : (a_p 6977 : ℝ) = 135 := by exact_mod_cast BSD_ap_p6977
  have key : r ^ 2 - (a_p 6977 : ℝ) * r + ((6977 : ℕ) : ℝ) =
      (r - 135/2) ^ 2 + 9683/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (135 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6983 : BSD_FrobeniusDegreeNonneg_OPEN 6983 := fun r => by
  have hap : (a_p 6983 : ℝ) = -111 := by exact_mod_cast BSD_ap_p6983
  have key : r ^ 2 - (a_p 6983 : ℝ) * r + ((6983 : ℕ) : ℝ) =
      (r + 111/2) ^ 2 + 15611/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (111 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6991 : BSD_FrobeniusDegreeNonneg_OPEN 6991 := fun r => by
  have hap : (a_p 6991 : ℝ) = -106 := by exact_mod_cast BSD_ap_p6991
  have key : r ^ 2 - (a_p 6991 : ℝ) * r + ((6991 : ℕ) : ℝ) =
      (r + 106/2) ^ 2 + 16728/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (106 : ℝ)/2)]

theorem BSD_DegreeNonneg_p6997 : BSD_FrobeniusDegreeNonneg_OPEN 6997 := fun r => by
  have hap : (a_p 6997 : ℝ) = 135 := by exact_mod_cast BSD_ap_p6997
  have key : r ^ 2 - (a_p 6997 : ℝ) * r + ((6997 : ℕ) : ℝ) =
      (r - 135/2) ^ 2 + 9763/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (135 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7001 : BSD_FrobeniusDegreeNonneg_OPEN 7001 := fun r => by
  have hap : (a_p 7001 : ℝ) = -22 := by exact_mod_cast BSD_ap_p7001
  have key : r ^ 2 - (a_p 7001 : ℝ) * r + ((7001 : ℕ) : ℝ) =
      (r + 22/2) ^ 2 + 27520/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7013 : BSD_FrobeniusDegreeNonneg_OPEN 7013 := fun r => by
  have hap : (a_p 7013 : ℝ) = -18 := by exact_mod_cast BSD_ap_p7013
  have key : r ^ 2 - (a_p 7013 : ℝ) * r + ((7013 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 27728/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7019 : BSD_FrobeniusDegreeNonneg_OPEN 7019 := fun r => by
  have hap : (a_p 7019 : ℝ) = -20 := by exact_mod_cast BSD_ap_p7019
  have key : r ^ 2 - (a_p 7019 : ℝ) * r + ((7019 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 27676/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7027 : BSD_FrobeniusDegreeNonneg_OPEN 7027 := fun r => by
  have hap : (a_p 7027 : ℝ) = 33 := by exact_mod_cast BSD_ap_p7027
  have key : r ^ 2 - (a_p 7027 : ℝ) * r + ((7027 : ℕ) : ℝ) =
      (r - 33/2) ^ 2 + 27019/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (33 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7039 : BSD_FrobeniusDegreeNonneg_OPEN 7039 := fun r => by
  have hap : (a_p 7039 : ℝ) = 66 := by exact_mod_cast BSD_ap_p7039
  have key : r ^ 2 - (a_p 7039 : ℝ) * r + ((7039 : ℕ) : ℝ) =
      (r - 66/2) ^ 2 + 23800/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (66 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7043 : BSD_FrobeniusDegreeNonneg_OPEN 7043 := fun r => by
  have hap : (a_p 7043 : ℝ) = -100 := by exact_mod_cast BSD_ap_p7043
  have key : r ^ 2 - (a_p 7043 : ℝ) * r + ((7043 : ℕ) : ℝ) =
      (r + 100/2) ^ 2 + 18172/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (100 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7057 : BSD_FrobeniusDegreeNonneg_OPEN 7057 := fun r => by
  have hap : (a_p 7057 : ℝ) = -32 := by exact_mod_cast BSD_ap_p7057
  have key : r ^ 2 - (a_p 7057 : ℝ) * r + ((7057 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 27204/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7069 : BSD_FrobeniusDegreeNonneg_OPEN 7069 := fun r => by
  have hap : (a_p 7069 : ℝ) = -124 := by exact_mod_cast BSD_ap_p7069
  have key : r ^ 2 - (a_p 7069 : ℝ) * r + ((7069 : ℕ) : ℝ) =
      (r + 124/2) ^ 2 + 12900/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (124 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7079 : BSD_FrobeniusDegreeNonneg_OPEN 7079 := fun r => by
  have hap : (a_p 7079 : ℝ) = 18 := by exact_mod_cast BSD_ap_p7079
  have key : r ^ 2 - (a_p 7079 : ℝ) * r + ((7079 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 27992/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7103 : BSD_FrobeniusDegreeNonneg_OPEN 7103 := fun r => by
  have hap : (a_p 7103 : ℝ) = -2 := by exact_mod_cast BSD_ap_p7103
  have key : r ^ 2 - (a_p 7103 : ℝ) * r + ((7103 : ℕ) : ℝ) =
      (r + 2/2) ^ 2 + 28408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (2 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7109 : BSD_FrobeniusDegreeNonneg_OPEN 7109 := fun r => by
  have hap : (a_p 7109 : ℝ) = -31 := by exact_mod_cast BSD_ap_p7109
  have key : r ^ 2 - (a_p 7109 : ℝ) * r + ((7109 : ℕ) : ℝ) =
      (r + 31/2) ^ 2 + 27475/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (31 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7121 : BSD_FrobeniusDegreeNonneg_OPEN 7121 := fun r => by
  have hap : (a_p 7121 : ℝ) = -87 := by exact_mod_cast BSD_ap_p7121
  have key : r ^ 2 - (a_p 7121 : ℝ) * r + ((7121 : ℕ) : ℝ) =
      (r + 87/2) ^ 2 + 20915/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (87 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7127 : BSD_FrobeniusDegreeNonneg_OPEN 7127 := fun r => by
  have hap : (a_p 7127 : ℝ) = 90 := by exact_mod_cast BSD_ap_p7127
  have key : r ^ 2 - (a_p 7127 : ℝ) * r + ((7127 : ℕ) : ℝ) =
      (r - 90/2) ^ 2 + 20408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (90 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7129 : BSD_FrobeniusDegreeNonneg_OPEN 7129 := fun r => by
  have hap : (a_p 7129 : ℝ) = 125 := by exact_mod_cast BSD_ap_p7129
  have key : r ^ 2 - (a_p 7129 : ℝ) * r + ((7129 : ℕ) : ℝ) =
      (r - 125/2) ^ 2 + 12891/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (125 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7151 : BSD_FrobeniusDegreeNonneg_OPEN 7151 := fun r => by
  have hap : (a_p 7151 : ℝ) = -45 := by exact_mod_cast BSD_ap_p7151
  have key : r ^ 2 - (a_p 7151 : ℝ) * r + ((7151 : ℕ) : ℝ) =
      (r + 45/2) ^ 2 + 26579/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (45 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7159 : BSD_FrobeniusDegreeNonneg_OPEN 7159 := fun r => by
  have hap : (a_p 7159 : ℝ) = 7 := by exact_mod_cast BSD_ap_p7159
  have key : r ^ 2 - (a_p 7159 : ℝ) * r + ((7159 : ℕ) : ℝ) =
      (r - 7/2) ^ 2 + 28587/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7177 : BSD_FrobeniusDegreeNonneg_OPEN 7177 := fun r => by
  have hap : (a_p 7177 : ℝ) = -30 := by exact_mod_cast BSD_ap_p7177
  have key : r ^ 2 - (a_p 7177 : ℝ) * r + ((7177 : ℕ) : ℝ) =
      (r + 30/2) ^ 2 + 27808/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7187 : BSD_FrobeniusDegreeNonneg_OPEN 7187 := fun r => by
  have hap : (a_p 7187 : ℝ) = -93 := by exact_mod_cast BSD_ap_p7187
  have key : r ^ 2 - (a_p 7187 : ℝ) * r + ((7187 : ℕ) : ℝ) =
      (r + 93/2) ^ 2 + 20099/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (93 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7193 : BSD_FrobeniusDegreeNonneg_OPEN 7193 := fun r => by
  have hap : (a_p 7193 : ℝ) = -42 := by exact_mod_cast BSD_ap_p7193
  have key : r ^ 2 - (a_p 7193 : ℝ) * r + ((7193 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 27008/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7207 : BSD_FrobeniusDegreeNonneg_OPEN 7207 := fun r => by
  have hap : (a_p 7207 : ℝ) = 100 := by exact_mod_cast BSD_ap_p7207
  have key : r ^ 2 - (a_p 7207 : ℝ) * r + ((7207 : ℕ) : ℝ) =
      (r - 100/2) ^ 2 + 18828/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (100 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7211 : BSD_FrobeniusDegreeNonneg_OPEN 7211 := fun r => by
  have hap : (a_p 7211 : ℝ) = 108 := by exact_mod_cast BSD_ap_p7211
  have key : r ^ 2 - (a_p 7211 : ℝ) * r + ((7211 : ℕ) : ℝ) =
      (r - 108/2) ^ 2 + 17180/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (108 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7213 : BSD_FrobeniusDegreeNonneg_OPEN 7213 := fun r => by
  have hap : (a_p 7213 : ℝ) = 52 := by exact_mod_cast BSD_ap_p7213
  have key : r ^ 2 - (a_p 7213 : ℝ) * r + ((7213 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 26148/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7219 : BSD_FrobeniusDegreeNonneg_OPEN 7219 := fun r => by
  have hap : (a_p 7219 : ℝ) = 97 := by exact_mod_cast BSD_ap_p7219
  have key : r ^ 2 - (a_p 7219 : ℝ) * r + ((7219 : ℕ) : ℝ) =
      (r - 97/2) ^ 2 + 19467/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (97 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7229 : BSD_FrobeniusDegreeNonneg_OPEN 7229 := fun r => by
  have hap : (a_p 7229 : ℝ) = -102 := by exact_mod_cast BSD_ap_p7229
  have key : r ^ 2 - (a_p 7229 : ℝ) * r + ((7229 : ℕ) : ℝ) =
      (r + 102/2) ^ 2 + 18512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (102 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7237 : BSD_FrobeniusDegreeNonneg_OPEN 7237 := fun r => by
  have hap : (a_p 7237 : ℝ) = 40 := by exact_mod_cast BSD_ap_p7237
  have key : r ^ 2 - (a_p 7237 : ℝ) * r + ((7237 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 27348/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7243 : BSD_FrobeniusDegreeNonneg_OPEN 7243 := fun r => by
  have hap : (a_p 7243 : ℝ) = -43 := by exact_mod_cast BSD_ap_p7243
  have key : r ^ 2 - (a_p 7243 : ℝ) * r + ((7243 : ℕ) : ℝ) =
      (r + 43/2) ^ 2 + 27123/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (43 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7247 : BSD_FrobeniusDegreeNonneg_OPEN 7247 := fun r => by
  have hap : (a_p 7247 : ℝ) = 37 := by exact_mod_cast BSD_ap_p7247
  have key : r ^ 2 - (a_p 7247 : ℝ) * r + ((7247 : ℕ) : ℝ) =
      (r - 37/2) ^ 2 + 27619/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (37 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7253 : BSD_FrobeniusDegreeNonneg_OPEN 7253 := fun r => by
  have hap : (a_p 7253 : ℝ) = -97 := by exact_mod_cast BSD_ap_p7253
  have key : r ^ 2 - (a_p 7253 : ℝ) * r + ((7253 : ℕ) : ℝ) =
      (r + 97/2) ^ 2 + 19603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (97 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7283 : BSD_FrobeniusDegreeNonneg_OPEN 7283 := fun r => by
  have hap : (a_p 7283 : ℝ) = -29 := by exact_mod_cast BSD_ap_p7283
  have key : r ^ 2 - (a_p 7283 : ℝ) * r + ((7283 : ℕ) : ℝ) =
      (r + 29/2) ^ 2 + 28291/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (29 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7297 : BSD_FrobeniusDegreeNonneg_OPEN 7297 := fun r => by
  have hap : (a_p 7297 : ℝ) = -130 := by exact_mod_cast BSD_ap_p7297
  have key : r ^ 2 - (a_p 7297 : ℝ) * r + ((7297 : ℕ) : ℝ) =
      (r + 130/2) ^ 2 + 12288/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (130 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7307 : BSD_FrobeniusDegreeNonneg_OPEN 7307 := fun r => by
  have hap : (a_p 7307 : ℝ) = -155 := by exact_mod_cast BSD_ap_p7307
  have key : r ^ 2 - (a_p 7307 : ℝ) * r + ((7307 : ℕ) : ℝ) =
      (r + 155/2) ^ 2 + 5203/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (155 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7309 : BSD_FrobeniusDegreeNonneg_OPEN 7309 := fun r => by
  have hap : (a_p 7309 : ℝ) = 95 := by exact_mod_cast BSD_ap_p7309
  have key : r ^ 2 - (a_p 7309 : ℝ) * r + ((7309 : ℕ) : ℝ) =
      (r - 95/2) ^ 2 + 20211/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (95 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7321 : BSD_FrobeniusDegreeNonneg_OPEN 7321 := fun r => by
  have hap : (a_p 7321 : ℝ) = -62 := by exact_mod_cast BSD_ap_p7321
  have key : r ^ 2 - (a_p 7321 : ℝ) * r + ((7321 : ℕ) : ℝ) =
      (r + 62/2) ^ 2 + 25440/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (62 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7331 : BSD_FrobeniusDegreeNonneg_OPEN 7331 := fun r => by
  have hap : (a_p 7331 : ℝ) = -20 := by exact_mod_cast BSD_ap_p7331
  have key : r ^ 2 - (a_p 7331 : ℝ) * r + ((7331 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 28924/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7333 : BSD_FrobeniusDegreeNonneg_OPEN 7333 := fun r => by
  have hap : (a_p 7333 : ℝ) = -16 := by exact_mod_cast BSD_ap_p7333
  have key : r ^ 2 - (a_p 7333 : ℝ) * r + ((7333 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 29076/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7349 : BSD_FrobeniusDegreeNonneg_OPEN 7349 := fun r => by
  have hap : (a_p 7349 : ℝ) = -102 := by exact_mod_cast BSD_ap_p7349
  have key : r ^ 2 - (a_p 7349 : ℝ) * r + ((7349 : ℕ) : ℝ) =
      (r + 102/2) ^ 2 + 18992/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (102 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7351 : BSD_FrobeniusDegreeNonneg_OPEN 7351 := fun r => by
  have hap : (a_p 7351 : ℝ) = 112 := by exact_mod_cast BSD_ap_p7351
  have key : r ^ 2 - (a_p 7351 : ℝ) * r + ((7351 : ℕ) : ℝ) =
      (r - 112/2) ^ 2 + 16860/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (112 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7369 : BSD_FrobeniusDegreeNonneg_OPEN 7369 := fun r => by
  have hap : (a_p 7369 : ℝ) = 112 := by exact_mod_cast BSD_ap_p7369
  have key : r ^ 2 - (a_p 7369 : ℝ) * r + ((7369 : ℕ) : ℝ) =
      (r - 112/2) ^ 2 + 16932/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (112 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7393 : BSD_FrobeniusDegreeNonneg_OPEN 7393 := fun r => by
  have hap : (a_p 7393 : ℝ) = -147 := by exact_mod_cast BSD_ap_p7393
  have key : r ^ 2 - (a_p 7393 : ℝ) * r + ((7393 : ℕ) : ℝ) =
      (r + 147/2) ^ 2 + 7963/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (147 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7411 : BSD_FrobeniusDegreeNonneg_OPEN 7411 := fun r => by
  have hap : (a_p 7411 : ℝ) = 116 := by exact_mod_cast BSD_ap_p7411
  have key : r ^ 2 - (a_p 7411 : ℝ) * r + ((7411 : ℕ) : ℝ) =
      (r - 116/2) ^ 2 + 16188/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (116 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7417 : BSD_FrobeniusDegreeNonneg_OPEN 7417 := fun r => by
  have hap : (a_p 7417 : ℝ) = -3 := by exact_mod_cast BSD_ap_p7417
  have key : r ^ 2 - (a_p 7417 : ℝ) * r + ((7417 : ℕ) : ℝ) =
      (r + 3/2) ^ 2 + 29659/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (3 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7433 : BSD_FrobeniusDegreeNonneg_OPEN 7433 := fun r => by
  have hap : (a_p 7433 : ℝ) = -132 := by exact_mod_cast BSD_ap_p7433
  have key : r ^ 2 - (a_p 7433 : ℝ) * r + ((7433 : ℕ) : ℝ) =
      (r + 132/2) ^ 2 + 12308/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (132 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7451 : BSD_FrobeniusDegreeNonneg_OPEN 7451 := fun r => by
  have hap : (a_p 7451 : ℝ) = -156 := by exact_mod_cast BSD_ap_p7451
  have key : r ^ 2 - (a_p 7451 : ℝ) * r + ((7451 : ℕ) : ℝ) =
      (r + 156/2) ^ 2 + 5468/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (156 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7457 : BSD_FrobeniusDegreeNonneg_OPEN 7457 := fun r => by
  have hap : (a_p 7457 : ℝ) = 50 := by exact_mod_cast BSD_ap_p7457
  have key : r ^ 2 - (a_p 7457 : ℝ) * r + ((7457 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 27328/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7459 : BSD_FrobeniusDegreeNonneg_OPEN 7459 := fun r => by
  have hap : (a_p 7459 : ℝ) = -121 := by exact_mod_cast BSD_ap_p7459
  have key : r ^ 2 - (a_p 7459 : ℝ) * r + ((7459 : ℕ) : ℝ) =
      (r + 121/2) ^ 2 + 15195/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (121 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7477 : BSD_FrobeniusDegreeNonneg_OPEN 7477 := fun r => by
  have hap : (a_p 7477 : ℝ) = -50 := by exact_mod_cast BSD_ap_p7477
  have key : r ^ 2 - (a_p 7477 : ℝ) * r + ((7477 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 27408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7481 : BSD_FrobeniusDegreeNonneg_OPEN 7481 := fun r => by
  have hap : (a_p 7481 : ℝ) = -129 := by exact_mod_cast BSD_ap_p7481
  have key : r ^ 2 - (a_p 7481 : ℝ) * r + ((7481 : ℕ) : ℝ) =
      (r + 129/2) ^ 2 + 13283/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (129 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7487 : BSD_FrobeniusDegreeNonneg_OPEN 7487 := fun r => by
  have hap : (a_p 7487 : ℝ) = -102 := by exact_mod_cast BSD_ap_p7487
  have key : r ^ 2 - (a_p 7487 : ℝ) * r + ((7487 : ℕ) : ℝ) =
      (r + 102/2) ^ 2 + 19544/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (102 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7489 : BSD_FrobeniusDegreeNonneg_OPEN 7489 := fun r => by
  have hap : (a_p 7489 : ℝ) = 9 := by exact_mod_cast BSD_ap_p7489
  have key : r ^ 2 - (a_p 7489 : ℝ) * r + ((7489 : ℕ) : ℝ) =
      (r - 9/2) ^ 2 + 29875/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (9 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7499 : BSD_FrobeniusDegreeNonneg_OPEN 7499 := fun r => by
  have hap : (a_p 7499 : ℝ) = 16 := by exact_mod_cast BSD_ap_p7499
  have key : r ^ 2 - (a_p 7499 : ℝ) * r + ((7499 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 29740/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7507 : BSD_FrobeniusDegreeNonneg_OPEN 7507 := fun r => by
  have hap : (a_p 7507 : ℝ) = 71 := by exact_mod_cast BSD_ap_p7507
  have key : r ^ 2 - (a_p 7507 : ℝ) * r + ((7507 : ℕ) : ℝ) =
      (r - 71/2) ^ 2 + 24987/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (71 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7517 : BSD_FrobeniusDegreeNonneg_OPEN 7517 := fun r => by
  have hap : (a_p 7517 : ℝ) = -90 := by exact_mod_cast BSD_ap_p7517
  have key : r ^ 2 - (a_p 7517 : ℝ) * r + ((7517 : ℕ) : ℝ) =
      (r + 90/2) ^ 2 + 21968/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (90 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7523 : BSD_FrobeniusDegreeNonneg_OPEN 7523 := fun r => by
  have hap : (a_p 7523 : ℝ) = 154 := by exact_mod_cast BSD_ap_p7523
  have key : r ^ 2 - (a_p 7523 : ℝ) * r + ((7523 : ℕ) : ℝ) =
      (r - 154/2) ^ 2 + 6376/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (154 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7529 : BSD_FrobeniusDegreeNonneg_OPEN 7529 := fun r => by
  have hap : (a_p 7529 : ℝ) = 27 := by exact_mod_cast BSD_ap_p7529
  have key : r ^ 2 - (a_p 7529 : ℝ) * r + ((7529 : ℕ) : ℝ) =
      (r - 27/2) ^ 2 + 29387/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (27 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7537 : BSD_FrobeniusDegreeNonneg_OPEN 7537 := fun r => by
  have hap : (a_p 7537 : ℝ) = 54 := by exact_mod_cast BSD_ap_p7537
  have key : r ^ 2 - (a_p 7537 : ℝ) * r + ((7537 : ℕ) : ℝ) =
      (r - 54/2) ^ 2 + 27232/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7541 : BSD_FrobeniusDegreeNonneg_OPEN 7541 := fun r => by
  have hap : (a_p 7541 : ℝ) = -32 := by exact_mod_cast BSD_ap_p7541
  have key : r ^ 2 - (a_p 7541 : ℝ) * r + ((7541 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 29140/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7547 : BSD_FrobeniusDegreeNonneg_OPEN 7547 := fun r => by
  have hap : (a_p 7547 : ℝ) = 1 := by exact_mod_cast BSD_ap_p7547
  have key : r ^ 2 - (a_p 7547 : ℝ) * r + ((7547 : ℕ) : ℝ) =
      (r - 1/2) ^ 2 + 30187/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (1 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7549 : BSD_FrobeniusDegreeNonneg_OPEN 7549 := fun r => by
  have hap : (a_p 7549 : ℝ) = -1 := by exact_mod_cast BSD_ap_p7549
  have key : r ^ 2 - (a_p 7549 : ℝ) * r + ((7549 : ℕ) : ℝ) =
      (r + 1/2) ^ 2 + 30195/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (1 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7559 : BSD_FrobeniusDegreeNonneg_OPEN 7559 := fun r => by
  have hap : (a_p 7559 : ℝ) = 42 := by exact_mod_cast BSD_ap_p7559
  have key : r ^ 2 - (a_p 7559 : ℝ) * r + ((7559 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 28472/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7561 : BSD_FrobeniusDegreeNonneg_OPEN 7561 := fun r => by
  have hap : (a_p 7561 : ℝ) = 70 := by exact_mod_cast BSD_ap_p7561
  have key : r ^ 2 - (a_p 7561 : ℝ) * r + ((7561 : ℕ) : ℝ) =
      (r - 70/2) ^ 2 + 25344/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (70 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7573 : BSD_FrobeniusDegreeNonneg_OPEN 7573 := fun r => by
  have hap : (a_p 7573 : ℝ) = -149 := by exact_mod_cast BSD_ap_p7573
  have key : r ^ 2 - (a_p 7573 : ℝ) * r + ((7573 : ℕ) : ℝ) =
      (r + 149/2) ^ 2 + 8091/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (149 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7577 : BSD_FrobeniusDegreeNonneg_OPEN 7577 := fun r => by
  have hap : (a_p 7577 : ℝ) = 18 := by exact_mod_cast BSD_ap_p7577
  have key : r ^ 2 - (a_p 7577 : ℝ) * r + ((7577 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 29984/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7583 : BSD_FrobeniusDegreeNonneg_OPEN 7583 := fun r => by
  have hap : (a_p 7583 : ℝ) = 0 := by exact_mod_cast BSD_ap_p7583
  have key : r ^ 2 - (a_p 7583 : ℝ) * r + ((7583 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 30332/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7589 : BSD_FrobeniusDegreeNonneg_OPEN 7589 := fun r => by
  have hap : (a_p 7589 : ℝ) = -150 := by exact_mod_cast BSD_ap_p7589
  have key : r ^ 2 - (a_p 7589 : ℝ) * r + ((7589 : ℕ) : ℝ) =
      (r + 150/2) ^ 2 + 7856/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (150 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7591 : BSD_FrobeniusDegreeNonneg_OPEN 7591 := fun r => by
  have hap : (a_p 7591 : ℝ) = 31 := by exact_mod_cast BSD_ap_p7591
  have key : r ^ 2 - (a_p 7591 : ℝ) * r + ((7591 : ℕ) : ℝ) =
      (r - 31/2) ^ 2 + 29403/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (31 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7603 : BSD_FrobeniusDegreeNonneg_OPEN 7603 := fun r => by
  have hap : (a_p 7603 : ℝ) = 146 := by exact_mod_cast BSD_ap_p7603
  have key : r ^ 2 - (a_p 7603 : ℝ) * r + ((7603 : ℕ) : ℝ) =
      (r - 146/2) ^ 2 + 9096/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (146 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7607 : BSD_FrobeniusDegreeNonneg_OPEN 7607 := fun r => by
  have hap : (a_p 7607 : ℝ) = 22 := by exact_mod_cast BSD_ap_p7607
  have key : r ^ 2 - (a_p 7607 : ℝ) * r + ((7607 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 29944/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7621 : BSD_FrobeniusDegreeNonneg_OPEN 7621 := fun r => by
  have hap : (a_p 7621 : ℝ) = -142 := by exact_mod_cast BSD_ap_p7621
  have key : r ^ 2 - (a_p 7621 : ℝ) * r + ((7621 : ℕ) : ℝ) =
      (r + 142/2) ^ 2 + 10320/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (142 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7639 : BSD_FrobeniusDegreeNonneg_OPEN 7639 := fun r => by
  have hap : (a_p 7639 : ℝ) = -97 := by exact_mod_cast BSD_ap_p7639
  have key : r ^ 2 - (a_p 7639 : ℝ) * r + ((7639 : ℕ) : ℝ) =
      (r + 97/2) ^ 2 + 21147/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (97 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7643 : BSD_FrobeniusDegreeNonneg_OPEN 7643 := fun r => by
  have hap : (a_p 7643 : ℝ) = -33 := by exact_mod_cast BSD_ap_p7643
  have key : r ^ 2 - (a_p 7643 : ℝ) * r + ((7643 : ℕ) : ℝ) =
      (r + 33/2) ^ 2 + 29483/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (33 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7649 : BSD_FrobeniusDegreeNonneg_OPEN 7649 := fun r => by
  have hap : (a_p 7649 : ℝ) = 98 := by exact_mod_cast BSD_ap_p7649
  have key : r ^ 2 - (a_p 7649 : ℝ) * r + ((7649 : ℕ) : ℝ) =
      (r - 98/2) ^ 2 + 20992/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (98 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7669 : BSD_FrobeniusDegreeNonneg_OPEN 7669 := fun r => by
  have hap : (a_p 7669 : ℝ) = 84 := by exact_mod_cast BSD_ap_p7669
  have key : r ^ 2 - (a_p 7669 : ℝ) * r + ((7669 : ℕ) : ℝ) =
      (r - 84/2) ^ 2 + 23620/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (84 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7673 : BSD_FrobeniusDegreeNonneg_OPEN 7673 := fun r => by
  have hap : (a_p 7673 : ℝ) = 96 := by exact_mod_cast BSD_ap_p7673
  have key : r ^ 2 - (a_p 7673 : ℝ) * r + ((7673 : ℕ) : ℝ) =
      (r - 96/2) ^ 2 + 21476/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (96 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7681 : BSD_FrobeniusDegreeNonneg_OPEN 7681 := fun r => by
  have hap : (a_p 7681 : ℝ) = 105 := by exact_mod_cast BSD_ap_p7681
  have key : r ^ 2 - (a_p 7681 : ℝ) * r + ((7681 : ℕ) : ℝ) =
      (r - 105/2) ^ 2 + 19699/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (105 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7687 : BSD_FrobeniusDegreeNonneg_OPEN 7687 := fun r => by
  have hap : (a_p 7687 : ℝ) = -5 := by exact_mod_cast BSD_ap_p7687
  have key : r ^ 2 - (a_p 7687 : ℝ) * r + ((7687 : ℕ) : ℝ) =
      (r + 5/2) ^ 2 + 30723/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (5 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7691 : BSD_FrobeniusDegreeNonneg_OPEN 7691 := fun r => by
  have hap : (a_p 7691 : ℝ) = -42 := by exact_mod_cast BSD_ap_p7691
  have key : r ^ 2 - (a_p 7691 : ℝ) * r + ((7691 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 29000/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7699 : BSD_FrobeniusDegreeNonneg_OPEN 7699 := fun r => by
  have hap : (a_p 7699 : ℝ) = -70 := by exact_mod_cast BSD_ap_p7699
  have key : r ^ 2 - (a_p 7699 : ℝ) * r + ((7699 : ℕ) : ℝ) =
      (r + 70/2) ^ 2 + 25896/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (70 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7703 : BSD_FrobeniusDegreeNonneg_OPEN 7703 := fun r => by
  have hap : (a_p 7703 : ℝ) = -69 := by exact_mod_cast BSD_ap_p7703
  have key : r ^ 2 - (a_p 7703 : ℝ) * r + ((7703 : ℕ) : ℝ) =
      (r + 69/2) ^ 2 + 26051/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (69 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7717 : BSD_FrobeniusDegreeNonneg_OPEN 7717 := fun r => by
  have hap : (a_p 7717 : ℝ) = -32 := by exact_mod_cast BSD_ap_p7717
  have key : r ^ 2 - (a_p 7717 : ℝ) * r + ((7717 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 29844/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7723 : BSD_FrobeniusDegreeNonneg_OPEN 7723 := fun r => by
  have hap : (a_p 7723 : ℝ) = 29 := by exact_mod_cast BSD_ap_p7723
  have key : r ^ 2 - (a_p 7723 : ℝ) * r + ((7723 : ℕ) : ℝ) =
      (r - 29/2) ^ 2 + 30051/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (29 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7727 : BSD_FrobeniusDegreeNonneg_OPEN 7727 := fun r => by
  have hap : (a_p 7727 : ℝ) = 147 := by exact_mod_cast BSD_ap_p7727
  have key : r ^ 2 - (a_p 7727 : ℝ) * r + ((7727 : ℕ) : ℝ) =
      (r - 147/2) ^ 2 + 9299/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (147 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7741 : BSD_FrobeniusDegreeNonneg_OPEN 7741 := fun r => by
  have hap : (a_p 7741 : ℝ) = 76 := by exact_mod_cast BSD_ap_p7741
  have key : r ^ 2 - (a_p 7741 : ℝ) * r + ((7741 : ℕ) : ℝ) =
      (r - 76/2) ^ 2 + 25188/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (76 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7753 : BSD_FrobeniusDegreeNonneg_OPEN 7753 := fun r => by
  have hap : (a_p 7753 : ℝ) = 77 := by exact_mod_cast BSD_ap_p7753
  have key : r ^ 2 - (a_p 7753 : ℝ) * r + ((7753 : ℕ) : ℝ) =
      (r - 77/2) ^ 2 + 25083/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (77 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7757 : BSD_FrobeniusDegreeNonneg_OPEN 7757 := fun r => by
  have hap : (a_p 7757 : ℝ) = -126 := by exact_mod_cast BSD_ap_p7757
  have key : r ^ 2 - (a_p 7757 : ℝ) * r + ((7757 : ℕ) : ℝ) =
      (r + 126/2) ^ 2 + 15152/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (126 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7759 : BSD_FrobeniusDegreeNonneg_OPEN 7759 := fun r => by
  have hap : (a_p 7759 : ℝ) = -167 := by exact_mod_cast BSD_ap_p7759
  have key : r ^ 2 - (a_p 7759 : ℝ) * r + ((7759 : ℕ) : ℝ) =
      (r + 167/2) ^ 2 + 3147/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (167 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7789 : BSD_FrobeniusDegreeNonneg_OPEN 7789 := fun r => by
  have hap : (a_p 7789 : ℝ) = -18 := by exact_mod_cast BSD_ap_p7789
  have key : r ^ 2 - (a_p 7789 : ℝ) * r + ((7789 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 30832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7793 : BSD_FrobeniusDegreeNonneg_OPEN 7793 := fun r => by
  have hap : (a_p 7793 : ℝ) = -39 := by exact_mod_cast BSD_ap_p7793
  have key : r ^ 2 - (a_p 7793 : ℝ) * r + ((7793 : ℕ) : ℝ) =
      (r + 39/2) ^ 2 + 29651/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (39 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7817 : BSD_FrobeniusDegreeNonneg_OPEN 7817 := fun r => by
  have hap : (a_p 7817 : ℝ) = 140 := by exact_mod_cast BSD_ap_p7817
  have key : r ^ 2 - (a_p 7817 : ℝ) * r + ((7817 : ℕ) : ℝ) =
      (r - 140/2) ^ 2 + 11668/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (140 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7823 : BSD_FrobeniusDegreeNonneg_OPEN 7823 := fun r => by
  have hap : (a_p 7823 : ℝ) = 108 := by exact_mod_cast BSD_ap_p7823
  have key : r ^ 2 - (a_p 7823 : ℝ) * r + ((7823 : ℕ) : ℝ) =
      (r - 108/2) ^ 2 + 19628/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (108 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7829 : BSD_FrobeniusDegreeNonneg_OPEN 7829 := fun r => by
  have hap : (a_p 7829 : ℝ) = 72 := by exact_mod_cast BSD_ap_p7829
  have key : r ^ 2 - (a_p 7829 : ℝ) * r + ((7829 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 26132/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7841 : BSD_FrobeniusDegreeNonneg_OPEN 7841 := fun r => by
  have hap : (a_p 7841 : ℝ) = -69 := by exact_mod_cast BSD_ap_p7841
  have key : r ^ 2 - (a_p 7841 : ℝ) * r + ((7841 : ℕ) : ℝ) =
      (r + 69/2) ^ 2 + 26603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (69 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7853 : BSD_FrobeniusDegreeNonneg_OPEN 7853 := fun r => by
  have hap : (a_p 7853 : ℝ) = -6 := by exact_mod_cast BSD_ap_p7853
  have key : r ^ 2 - (a_p 7853 : ℝ) * r + ((7853 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 31376/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7867 : BSD_FrobeniusDegreeNonneg_OPEN 7867 := fun r => by
  have hap : (a_p 7867 : ℝ) = -68 := by exact_mod_cast BSD_ap_p7867
  have key : r ^ 2 - (a_p 7867 : ℝ) * r + ((7867 : ℕ) : ℝ) =
      (r + 68/2) ^ 2 + 26844/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (68 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7873 : BSD_FrobeniusDegreeNonneg_OPEN 7873 := fun r => by
  have hap : (a_p 7873 : ℝ) = -112 := by exact_mod_cast BSD_ap_p7873
  have key : r ^ 2 - (a_p 7873 : ℝ) * r + ((7873 : ℕ) : ℝ) =
      (r + 112/2) ^ 2 + 18948/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (112 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7877 : BSD_FrobeniusDegreeNonneg_OPEN 7877 := fun r => by
  have hap : (a_p 7877 : ℝ) = 114 := by exact_mod_cast BSD_ap_p7877
  have key : r ^ 2 - (a_p 7877 : ℝ) * r + ((7877 : ℕ) : ℝ) =
      (r - 114/2) ^ 2 + 18512/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (114 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7879 : BSD_FrobeniusDegreeNonneg_OPEN 7879 := fun r => by
  have hap : (a_p 7879 : ℝ) = 79 := by exact_mod_cast BSD_ap_p7879
  have key : r ^ 2 - (a_p 7879 : ℝ) * r + ((7879 : ℕ) : ℝ) =
      (r - 79/2) ^ 2 + 25275/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (79 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7883 : BSD_FrobeniusDegreeNonneg_OPEN 7883 := fun r => by
  have hap : (a_p 7883 : ℝ) = 22 := by exact_mod_cast BSD_ap_p7883
  have key : r ^ 2 - (a_p 7883 : ℝ) * r + ((7883 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 31048/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7901 : BSD_FrobeniusDegreeNonneg_OPEN 7901 := fun r => by
  have hap : (a_p 7901 : ℝ) = -1 := by exact_mod_cast BSD_ap_p7901
  have key : r ^ 2 - (a_p 7901 : ℝ) * r + ((7901 : ℕ) : ℝ) =
      (r + 1/2) ^ 2 + 31603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (1 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7907 : BSD_FrobeniusDegreeNonneg_OPEN 7907 := fun r => by
  have hap : (a_p 7907 : ℝ) = 17 := by exact_mod_cast BSD_ap_p7907
  have key : r ^ 2 - (a_p 7907 : ℝ) * r + ((7907 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 31339/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7919 : BSD_FrobeniusDegreeNonneg_OPEN 7919 := fun r => by
  have hap : (a_p 7919 : ℝ) = 130 := by exact_mod_cast BSD_ap_p7919
  have key : r ^ 2 - (a_p 7919 : ℝ) * r + ((7919 : ℕ) : ℝ) =
      (r - 130/2) ^ 2 + 14776/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (130 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7927 : BSD_FrobeniusDegreeNonneg_OPEN 7927 := fun r => by
  have hap : (a_p 7927 : ℝ) = -174 := by exact_mod_cast BSD_ap_p7927
  have key : r ^ 2 - (a_p 7927 : ℝ) * r + ((7927 : ℕ) : ℝ) =
      (r + 174/2) ^ 2 + 1432/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (174 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7933 : BSD_FrobeniusDegreeNonneg_OPEN 7933 := fun r => by
  have hap : (a_p 7933 : ℝ) = 132 := by exact_mod_cast BSD_ap_p7933
  have key : r ^ 2 - (a_p 7933 : ℝ) * r + ((7933 : ℕ) : ℝ) =
      (r - 132/2) ^ 2 + 14308/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (132 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7937 : BSD_FrobeniusDegreeNonneg_OPEN 7937 := fun r => by
  have hap : (a_p 7937 : ℝ) = 162 := by exact_mod_cast BSD_ap_p7937
  have key : r ^ 2 - (a_p 7937 : ℝ) * r + ((7937 : ℕ) : ℝ) =
      (r - 162/2) ^ 2 + 5504/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (162 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7949 : BSD_FrobeniusDegreeNonneg_OPEN 7949 := fun r => by
  have hap : (a_p 7949 : ℝ) = 90 := by exact_mod_cast BSD_ap_p7949
  have key : r ^ 2 - (a_p 7949 : ℝ) * r + ((7949 : ℕ) : ℝ) =
      (r - 90/2) ^ 2 + 23696/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (90 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7951 : BSD_FrobeniusDegreeNonneg_OPEN 7951 := fun r => by
  have hap : (a_p 7951 : ℝ) = -16 := by exact_mod_cast BSD_ap_p7951
  have key : r ^ 2 - (a_p 7951 : ℝ) * r + ((7951 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 31548/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7963 : BSD_FrobeniusDegreeNonneg_OPEN 7963 := fun r => by
  have hap : (a_p 7963 : ℝ) = -92 := by exact_mod_cast BSD_ap_p7963
  have key : r ^ 2 - (a_p 7963 : ℝ) * r + ((7963 : ℕ) : ℝ) =
      (r + 92/2) ^ 2 + 23388/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (92 : ℝ)/2)]

theorem BSD_DegreeNonneg_p7993 : BSD_FrobeniusDegreeNonneg_OPEN 7993 := fun r => by
  have hap : (a_p 7993 : ℝ) = 74 := by exact_mod_cast BSD_ap_p7993
  have key : r ^ 2 - (a_p 7993 : ℝ) * r + ((7993 : ℕ) : ℝ) =
      (r - 74/2) ^ 2 + 26496/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (74 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8009 : BSD_FrobeniusDegreeNonneg_OPEN 8009 := fun r => by
  have hap : (a_p 8009 : ℝ) = 109 := by exact_mod_cast BSD_ap_p8009
  have key : r ^ 2 - (a_p 8009 : ℝ) * r + ((8009 : ℕ) : ℝ) =
      (r - 109/2) ^ 2 + 20155/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (109 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8011 : BSD_FrobeniusDegreeNonneg_OPEN 8011 := fun r => by
  have hap : (a_p 8011 : ℝ) = -23 := by exact_mod_cast BSD_ap_p8011
  have key : r ^ 2 - (a_p 8011 : ℝ) * r + ((8011 : ℕ) : ℝ) =
      (r + 23/2) ^ 2 + 31515/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (23 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8017 : BSD_FrobeniusDegreeNonneg_OPEN 8017 := fun r => by
  have hap : (a_p 8017 : ℝ) = -6 := by exact_mod_cast BSD_ap_p8017
  have key : r ^ 2 - (a_p 8017 : ℝ) * r + ((8017 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 32032/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8039 : BSD_FrobeniusDegreeNonneg_OPEN 8039 := fun r => by
  have hap : (a_p 8039 : ℝ) = -53 := by exact_mod_cast BSD_ap_p8039
  have key : r ^ 2 - (a_p 8039 : ℝ) * r + ((8039 : ℕ) : ℝ) =
      (r + 53/2) ^ 2 + 29347/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (53 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8053 : BSD_FrobeniusDegreeNonneg_OPEN 8053 := fun r => by
  have hap : (a_p 8053 : ℝ) = 94 := by exact_mod_cast BSD_ap_p8053
  have key : r ^ 2 - (a_p 8053 : ℝ) * r + ((8053 : ℕ) : ℝ) =
      (r - 94/2) ^ 2 + 23376/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (94 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8059 : BSD_FrobeniusDegreeNonneg_OPEN 8059 := fun r => by
  have hap : (a_p 8059 : ℝ) = 0 := by exact_mod_cast BSD_ap_p8059
  have key : r ^ 2 - (a_p 8059 : ℝ) * r + ((8059 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 32236/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8069 : BSD_FrobeniusDegreeNonneg_OPEN 8069 := fun r => by
  have hap : (a_p 8069 : ℝ) = -92 := by exact_mod_cast BSD_ap_p8069
  have key : r ^ 2 - (a_p 8069 : ℝ) * r + ((8069 : ℕ) : ℝ) =
      (r + 92/2) ^ 2 + 23812/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (92 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8081 : BSD_FrobeniusDegreeNonneg_OPEN 8081 := fun r => by
  have hap : (a_p 8081 : ℝ) = -110 := by exact_mod_cast BSD_ap_p8081
  have key : r ^ 2 - (a_p 8081 : ℝ) * r + ((8081 : ℕ) : ℝ) =
      (r + 110/2) ^ 2 + 20224/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (110 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8087 : BSD_FrobeniusDegreeNonneg_OPEN 8087 := fun r => by
  have hap : (a_p 8087 : ℝ) = -110 := by exact_mod_cast BSD_ap_p8087
  have key : r ^ 2 - (a_p 8087 : ℝ) * r + ((8087 : ℕ) : ℝ) =
      (r + 110/2) ^ 2 + 20248/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (110 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8089 : BSD_FrobeniusDegreeNonneg_OPEN 8089 := fun r => by
  have hap : (a_p 8089 : ℝ) = 99 := by exact_mod_cast BSD_ap_p8089
  have key : r ^ 2 - (a_p 8089 : ℝ) * r + ((8089 : ℕ) : ℝ) =
      (r - 99/2) ^ 2 + 22555/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (99 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8093 : BSD_FrobeniusDegreeNonneg_OPEN 8093 := fun r => by
  have hap : (a_p 8093 : ℝ) = 88 := by exact_mod_cast BSD_ap_p8093
  have key : r ^ 2 - (a_p 8093 : ℝ) * r + ((8093 : ℕ) : ℝ) =
      (r - 88/2) ^ 2 + 24628/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (88 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8101 : BSD_FrobeniusDegreeNonneg_OPEN 8101 := fun r => by
  have hap : (a_p 8101 : ℝ) = -113 := by exact_mod_cast BSD_ap_p8101
  have key : r ^ 2 - (a_p 8101 : ℝ) * r + ((8101 : ℕ) : ℝ) =
      (r + 113/2) ^ 2 + 19635/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (113 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8111 : BSD_FrobeniusDegreeNonneg_OPEN 8111 := fun r => by
  have hap : (a_p 8111 : ℝ) = -44 := by exact_mod_cast BSD_ap_p8111
  have key : r ^ 2 - (a_p 8111 : ℝ) * r + ((8111 : ℕ) : ℝ) =
      (r + 44/2) ^ 2 + 30508/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (44 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8117 : BSD_FrobeniusDegreeNonneg_OPEN 8117 := fun r => by
  have hap : (a_p 8117 : ℝ) = 72 := by exact_mod_cast BSD_ap_p8117
  have key : r ^ 2 - (a_p 8117 : ℝ) * r + ((8117 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 27284/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8123 : BSD_FrobeniusDegreeNonneg_OPEN 8123 := fun r => by
  have hap : (a_p 8123 : ℝ) = 60 := by exact_mod_cast BSD_ap_p8123
  have key : r ^ 2 - (a_p 8123 : ℝ) * r + ((8123 : ℕ) : ℝ) =
      (r - 60/2) ^ 2 + 28892/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (60 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8147 : BSD_FrobeniusDegreeNonneg_OPEN 8147 := fun r => by
  have hap : (a_p 8147 : ℝ) = -24 := by exact_mod_cast BSD_ap_p8147
  have key : r ^ 2 - (a_p 8147 : ℝ) * r + ((8147 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 32012/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8161 : BSD_FrobeniusDegreeNonneg_OPEN 8161 := fun r => by
  have hap : (a_p 8161 : ℝ) = 88 := by exact_mod_cast BSD_ap_p8161
  have key : r ^ 2 - (a_p 8161 : ℝ) * r + ((8161 : ℕ) : ℝ) =
      (r - 88/2) ^ 2 + 24900/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (88 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8167 : BSD_FrobeniusDegreeNonneg_OPEN 8167 := fun r => by
  have hap : (a_p 8167 : ℝ) = -101 := by exact_mod_cast BSD_ap_p8167
  have key : r ^ 2 - (a_p 8167 : ℝ) * r + ((8167 : ℕ) : ℝ) =
      (r + 101/2) ^ 2 + 22467/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (101 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8171 : BSD_FrobeniusDegreeNonneg_OPEN 8171 := fun r => by
  have hap : (a_p 8171 : ℝ) = -52 := by exact_mod_cast BSD_ap_p8171
  have key : r ^ 2 - (a_p 8171 : ℝ) * r + ((8171 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 29980/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8179 : BSD_FrobeniusDegreeNonneg_OPEN 8179 := fun r => by
  have hap : (a_p 8179 : ℝ) = -140 := by exact_mod_cast BSD_ap_p8179
  have key : r ^ 2 - (a_p 8179 : ℝ) * r + ((8179 : ℕ) : ℝ) =
      (r + 140/2) ^ 2 + 13116/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (140 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8191 : BSD_FrobeniusDegreeNonneg_OPEN 8191 := fun r => by
  have hap : (a_p 8191 : ℝ) = 126 := by exact_mod_cast BSD_ap_p8191
  have key : r ^ 2 - (a_p 8191 : ℝ) * r + ((8191 : ℕ) : ℝ) =
      (r - 126/2) ^ 2 + 16888/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (126 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8209 : BSD_FrobeniusDegreeNonneg_OPEN 8209 := fun r => by
  have hap : (a_p 8209 : ℝ) = 59 := by exact_mod_cast BSD_ap_p8209
  have key : r ^ 2 - (a_p 8209 : ℝ) * r + ((8209 : ℕ) : ℝ) =
      (r - 59/2) ^ 2 + 29355/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (59 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8219 : BSD_FrobeniusDegreeNonneg_OPEN 8219 := fun r => by
  have hap : (a_p 8219 : ℝ) = 22 := by exact_mod_cast BSD_ap_p8219
  have key : r ^ 2 - (a_p 8219 : ℝ) * r + ((8219 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 32392/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8221 : BSD_FrobeniusDegreeNonneg_OPEN 8221 := fun r => by
  have hap : (a_p 8221 : ℝ) = 15 := by exact_mod_cast BSD_ap_p8221
  have key : r ^ 2 - (a_p 8221 : ℝ) * r + ((8221 : ℕ) : ℝ) =
      (r - 15/2) ^ 2 + 32659/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (15 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8231 : BSD_FrobeniusDegreeNonneg_OPEN 8231 := fun r => by
  have hap : (a_p 8231 : ℝ) = 93 := by exact_mod_cast BSD_ap_p8231
  have key : r ^ 2 - (a_p 8231 : ℝ) * r + ((8231 : ℕ) : ℝ) =
      (r - 93/2) ^ 2 + 24275/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (93 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8233 : BSD_FrobeniusDegreeNonneg_OPEN 8233 := fun r => by
  have hap : (a_p 8233 : ℝ) = -11 := by exact_mod_cast BSD_ap_p8233
  have key : r ^ 2 - (a_p 8233 : ℝ) * r + ((8233 : ℕ) : ℝ) =
      (r + 11/2) ^ 2 + 32811/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (11 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8237 : BSD_FrobeniusDegreeNonneg_OPEN 8237 := fun r => by
  have hap : (a_p 8237 : ℝ) = 129 := by exact_mod_cast BSD_ap_p8237
  have key : r ^ 2 - (a_p 8237 : ℝ) * r + ((8237 : ℕ) : ℝ) =
      (r - 129/2) ^ 2 + 16307/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (129 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8243 : BSD_FrobeniusDegreeNonneg_OPEN 8243 := fun r => by
  have hap : (a_p 8243 : ℝ) = -21 := by exact_mod_cast BSD_ap_p8243
  have key : r ^ 2 - (a_p 8243 : ℝ) * r + ((8243 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 32531/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8263 : BSD_FrobeniusDegreeNonneg_OPEN 8263 := fun r => by
  have hap : (a_p 8263 : ℝ) = 116 := by exact_mod_cast BSD_ap_p8263
  have key : r ^ 2 - (a_p 8263 : ℝ) * r + ((8263 : ℕ) : ℝ) =
      (r - 116/2) ^ 2 + 19596/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (116 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8269 : BSD_FrobeniusDegreeNonneg_OPEN 8269 := fun r => by
  have hap : (a_p 8269 : ℝ) = -2 := by exact_mod_cast BSD_ap_p8269
  have key : r ^ 2 - (a_p 8269 : ℝ) * r + ((8269 : ℕ) : ℝ) =
      (r + 2/2) ^ 2 + 33072/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (2 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8273 : BSD_FrobeniusDegreeNonneg_OPEN 8273 := fun r => by
  have hap : (a_p 8273 : ℝ) = -142 := by exact_mod_cast BSD_ap_p8273
  have key : r ^ 2 - (a_p 8273 : ℝ) * r + ((8273 : ℕ) : ℝ) =
      (r + 142/2) ^ 2 + 12928/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (142 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8287 : BSD_FrobeniusDegreeNonneg_OPEN 8287 := fun r => by
  have hap : (a_p 8287 : ℝ) = 48 := by exact_mod_cast BSD_ap_p8287
  have key : r ^ 2 - (a_p 8287 : ℝ) * r + ((8287 : ℕ) : ℝ) =
      (r - 48/2) ^ 2 + 30844/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8291 : BSD_FrobeniusDegreeNonneg_OPEN 8291 := fun r => by
  have hap : (a_p 8291 : ℝ) = -58 := by exact_mod_cast BSD_ap_p8291
  have key : r ^ 2 - (a_p 8291 : ℝ) * r + ((8291 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 29800/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8293 : BSD_FrobeniusDegreeNonneg_OPEN 8293 := fun r => by
  have hap : (a_p 8293 : ℝ) = 134 := by exact_mod_cast BSD_ap_p8293
  have key : r ^ 2 - (a_p 8293 : ℝ) * r + ((8293 : ℕ) : ℝ) =
      (r - 134/2) ^ 2 + 15216/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (134 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8297 : BSD_FrobeniusDegreeNonneg_OPEN 8297 := fun r => by
  have hap : (a_p 8297 : ℝ) = -69 := by exact_mod_cast BSD_ap_p8297
  have key : r ^ 2 - (a_p 8297 : ℝ) * r + ((8297 : ℕ) : ℝ) =
      (r + 69/2) ^ 2 + 28427/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (69 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8311 : BSD_FrobeniusDegreeNonneg_OPEN 8311 := fun r => by
  have hap : (a_p 8311 : ℝ) = -20 := by exact_mod_cast BSD_ap_p8311
  have key : r ^ 2 - (a_p 8311 : ℝ) * r + ((8311 : ℕ) : ℝ) =
      (r + 20/2) ^ 2 + 32844/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (20 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8317 : BSD_FrobeniusDegreeNonneg_OPEN 8317 := fun r => by
  have hap : (a_p 8317 : ℝ) = 34 := by exact_mod_cast BSD_ap_p8317
  have key : r ^ 2 - (a_p 8317 : ℝ) * r + ((8317 : ℕ) : ℝ) =
      (r - 34/2) ^ 2 + 32112/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (34 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8329 : BSD_FrobeniusDegreeNonneg_OPEN 8329 := fun r => by
  have hap : (a_p 8329 : ℝ) = 86 := by exact_mod_cast BSD_ap_p8329
  have key : r ^ 2 - (a_p 8329 : ℝ) * r + ((8329 : ℕ) : ℝ) =
      (r - 86/2) ^ 2 + 25920/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (86 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8353 : BSD_FrobeniusDegreeNonneg_OPEN 8353 := fun r => by
  have hap : (a_p 8353 : ℝ) = 57 := by exact_mod_cast BSD_ap_p8353
  have key : r ^ 2 - (a_p 8353 : ℝ) * r + ((8353 : ℕ) : ℝ) =
      (r - 57/2) ^ 2 + 30163/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (57 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8363 : BSD_FrobeniusDegreeNonneg_OPEN 8363 := fun r => by
  have hap : (a_p 8363 : ℝ) = -136 := by exact_mod_cast BSD_ap_p8363
  have key : r ^ 2 - (a_p 8363 : ℝ) * r + ((8363 : ℕ) : ℝ) =
      (r + 136/2) ^ 2 + 14956/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (136 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8369 : BSD_FrobeniusDegreeNonneg_OPEN 8369 := fun r => by
  have hap : (a_p 8369 : ℝ) = 66 := by exact_mod_cast BSD_ap_p8369
  have key : r ^ 2 - (a_p 8369 : ℝ) * r + ((8369 : ℕ) : ℝ) =
      (r - 66/2) ^ 2 + 29120/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (66 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8377 : BSD_FrobeniusDegreeNonneg_OPEN 8377 := fun r => by
  have hap : (a_p 8377 : ℝ) = -62 := by exact_mod_cast BSD_ap_p8377
  have key : r ^ 2 - (a_p 8377 : ℝ) * r + ((8377 : ℕ) : ℝ) =
      (r + 62/2) ^ 2 + 29664/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (62 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8387 : BSD_FrobeniusDegreeNonneg_OPEN 8387 := fun r => by
  have hap : (a_p 8387 : ℝ) = -12 := by exact_mod_cast BSD_ap_p8387
  have key : r ^ 2 - (a_p 8387 : ℝ) * r + ((8387 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 33404/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8389 : BSD_FrobeniusDegreeNonneg_OPEN 8389 := fun r => by
  have hap : (a_p 8389 : ℝ) = -108 := by exact_mod_cast BSD_ap_p8389
  have key : r ^ 2 - (a_p 8389 : ℝ) * r + ((8389 : ℕ) : ℝ) =
      (r + 108/2) ^ 2 + 21892/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (108 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8419 : BSD_FrobeniusDegreeNonneg_OPEN 8419 := fun r => by
  have hap : (a_p 8419 : ℝ) = 136 := by exact_mod_cast BSD_ap_p8419
  have key : r ^ 2 - (a_p 8419 : ℝ) * r + ((8419 : ℕ) : ℝ) =
      (r - 136/2) ^ 2 + 15180/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (136 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8423 : BSD_FrobeniusDegreeNonneg_OPEN 8423 := fun r => by
  have hap : (a_p 8423 : ℝ) = -52 := by exact_mod_cast BSD_ap_p8423
  have key : r ^ 2 - (a_p 8423 : ℝ) * r + ((8423 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 30988/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8429 : BSD_FrobeniusDegreeNonneg_OPEN 8429 := fun r => by
  have hap : (a_p 8429 : ℝ) = -61 := by exact_mod_cast BSD_ap_p8429
  have key : r ^ 2 - (a_p 8429 : ℝ) * r + ((8429 : ℕ) : ℝ) =
      (r + 61/2) ^ 2 + 29995/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (61 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8431 : BSD_FrobeniusDegreeNonneg_OPEN 8431 := fun r => by
  have hap : (a_p 8431 : ℝ) = 17 := by exact_mod_cast BSD_ap_p8431
  have key : r ^ 2 - (a_p 8431 : ℝ) * r + ((8431 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 33435/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8443 : BSD_FrobeniusDegreeNonneg_OPEN 8443 := fun r => by
  have hap : (a_p 8443 : ℝ) = 116 := by exact_mod_cast BSD_ap_p8443
  have key : r ^ 2 - (a_p 8443 : ℝ) * r + ((8443 : ℕ) : ℝ) =
      (r - 116/2) ^ 2 + 20316/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (116 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8447 : BSD_FrobeniusDegreeNonneg_OPEN 8447 := fun r => by
  have hap : (a_p 8447 : ℝ) = 10 := by exact_mod_cast BSD_ap_p8447
  have key : r ^ 2 - (a_p 8447 : ℝ) * r + ((8447 : ℕ) : ℝ) =
      (r - 10/2) ^ 2 + 33688/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (10 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8461 : BSD_FrobeniusDegreeNonneg_OPEN 8461 := fun r => by
  have hap : (a_p 8461 : ℝ) = -176 := by exact_mod_cast BSD_ap_p8461
  have key : r ^ 2 - (a_p 8461 : ℝ) * r + ((8461 : ℕ) : ℝ) =
      (r + 176/2) ^ 2 + 2868/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (176 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8467 : BSD_FrobeniusDegreeNonneg_OPEN 8467 := fun r => by
  have hap : (a_p 8467 : ℝ) = -70 := by exact_mod_cast BSD_ap_p8467
  have key : r ^ 2 - (a_p 8467 : ℝ) * r + ((8467 : ℕ) : ℝ) =
      (r + 70/2) ^ 2 + 28968/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (70 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8501 : BSD_FrobeniusDegreeNonneg_OPEN 8501 := fun r => by
  have hap : (a_p 8501 : ℝ) = -107 := by exact_mod_cast BSD_ap_p8501
  have key : r ^ 2 - (a_p 8501 : ℝ) * r + ((8501 : ℕ) : ℝ) =
      (r + 107/2) ^ 2 + 22555/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (107 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8513 : BSD_FrobeniusDegreeNonneg_OPEN 8513 := fun r => by
  have hap : (a_p 8513 : ℝ) = -84 := by exact_mod_cast BSD_ap_p8513
  have key : r ^ 2 - (a_p 8513 : ℝ) * r + ((8513 : ℕ) : ℝ) =
      (r + 84/2) ^ 2 + 26996/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (84 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8521 : BSD_FrobeniusDegreeNonneg_OPEN 8521 := fun r => by
  have hap : (a_p 8521 : ℝ) = 14 := by exact_mod_cast BSD_ap_p8521
  have key : r ^ 2 - (a_p 8521 : ℝ) * r + ((8521 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 33888/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8527 : BSD_FrobeniusDegreeNonneg_OPEN 8527 := fun r => by
  have hap : (a_p 8527 : ℝ) = -174 := by exact_mod_cast BSD_ap_p8527
  have key : r ^ 2 - (a_p 8527 : ℝ) * r + ((8527 : ℕ) : ℝ) =
      (r + 174/2) ^ 2 + 3832/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (174 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8537 : BSD_FrobeniusDegreeNonneg_OPEN 8537 := fun r => by
  have hap : (a_p 8537 : ℝ) = 129 := by exact_mod_cast BSD_ap_p8537
  have key : r ^ 2 - (a_p 8537 : ℝ) * r + ((8537 : ℕ) : ℝ) =
      (r - 129/2) ^ 2 + 17507/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (129 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8539 : BSD_FrobeniusDegreeNonneg_OPEN 8539 := fun r => by
  have hap : (a_p 8539 : ℝ) = -85 := by exact_mod_cast BSD_ap_p8539
  have key : r ^ 2 - (a_p 8539 : ℝ) * r + ((8539 : ℕ) : ℝ) =
      (r + 85/2) ^ 2 + 26931/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (85 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8543 : BSD_FrobeniusDegreeNonneg_OPEN 8543 := fun r => by
  have hap : (a_p 8543 : ℝ) = -66 := by exact_mod_cast BSD_ap_p8543
  have key : r ^ 2 - (a_p 8543 : ℝ) * r + ((8543 : ℕ) : ℝ) =
      (r + 66/2) ^ 2 + 29816/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (66 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8563 : BSD_FrobeniusDegreeNonneg_OPEN 8563 := fun r => by
  have hap : (a_p 8563 : ℝ) = 36 := by exact_mod_cast BSD_ap_p8563
  have key : r ^ 2 - (a_p 8563 : ℝ) * r + ((8563 : ℕ) : ℝ) =
      (r - 36/2) ^ 2 + 32956/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (36 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8573 : BSD_FrobeniusDegreeNonneg_OPEN 8573 := fun r => by
  have hap : (a_p 8573 : ℝ) = 78 := by exact_mod_cast BSD_ap_p8573
  have key : r ^ 2 - (a_p 8573 : ℝ) * r + ((8573 : ℕ) : ℝ) =
      (r - 78/2) ^ 2 + 28208/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (78 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8581 : BSD_FrobeniusDegreeNonneg_OPEN 8581 := fun r => by
  have hap : (a_p 8581 : ℝ) = -61 := by exact_mod_cast BSD_ap_p8581
  have key : r ^ 2 - (a_p 8581 : ℝ) * r + ((8581 : ℕ) : ℝ) =
      (r + 61/2) ^ 2 + 30603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (61 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8597 : BSD_FrobeniusDegreeNonneg_OPEN 8597 := fun r => by
  have hap : (a_p 8597 : ℝ) = -76 := by exact_mod_cast BSD_ap_p8597
  have key : r ^ 2 - (a_p 8597 : ℝ) * r + ((8597 : ℕ) : ℝ) =
      (r + 76/2) ^ 2 + 28612/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (76 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8599 : BSD_FrobeniusDegreeNonneg_OPEN 8599 := fun r => by
  have hap : (a_p 8599 : ℝ) = -42 := by exact_mod_cast BSD_ap_p8599
  have key : r ^ 2 - (a_p 8599 : ℝ) * r + ((8599 : ℕ) : ℝ) =
      (r + 42/2) ^ 2 + 32632/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8609 : BSD_FrobeniusDegreeNonneg_OPEN 8609 := fun r => by
  have hap : (a_p 8609 : ℝ) = 4 := by exact_mod_cast BSD_ap_p8609
  have key : r ^ 2 - (a_p 8609 : ℝ) * r + ((8609 : ℕ) : ℝ) =
      (r - 4/2) ^ 2 + 34420/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (4 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8623 : BSD_FrobeniusDegreeNonneg_OPEN 8623 := fun r => by
  have hap : (a_p 8623 : ℝ) = 102 := by exact_mod_cast BSD_ap_p8623
  have key : r ^ 2 - (a_p 8623 : ℝ) * r + ((8623 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 24088/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8627 : BSD_FrobeniusDegreeNonneg_OPEN 8627 := fun r => by
  have hap : (a_p 8627 : ℝ) = -175 := by exact_mod_cast BSD_ap_p8627
  have key : r ^ 2 - (a_p 8627 : ℝ) * r + ((8627 : ℕ) : ℝ) =
      (r + 175/2) ^ 2 + 3883/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (175 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8629 : BSD_FrobeniusDegreeNonneg_OPEN 8629 := fun r => by
  have hap : (a_p 8629 : ℝ) = 133 := by exact_mod_cast BSD_ap_p8629
  have key : r ^ 2 - (a_p 8629 : ℝ) * r + ((8629 : ℕ) : ℝ) =
      (r - 133/2) ^ 2 + 16827/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (133 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8641 : BSD_FrobeniusDegreeNonneg_OPEN 8641 := fun r => by
  have hap : (a_p 8641 : ℝ) = 136 := by exact_mod_cast BSD_ap_p8641
  have key : r ^ 2 - (a_p 8641 : ℝ) * r + ((8641 : ℕ) : ℝ) =
      (r - 136/2) ^ 2 + 16068/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (136 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8647 : BSD_FrobeniusDegreeNonneg_OPEN 8647 := fun r => by
  have hap : (a_p 8647 : ℝ) = -21 := by exact_mod_cast BSD_ap_p8647
  have key : r ^ 2 - (a_p 8647 : ℝ) * r + ((8647 : ℕ) : ℝ) =
      (r + 21/2) ^ 2 + 34147/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (21 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8663 : BSD_FrobeniusDegreeNonneg_OPEN 8663 := fun r => by
  have hap : (a_p 8663 : ℝ) = -142 := by exact_mod_cast BSD_ap_p8663
  have key : r ^ 2 - (a_p 8663 : ℝ) * r + ((8663 : ℕ) : ℝ) =
      (r + 142/2) ^ 2 + 14488/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (142 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8669 : BSD_FrobeniusDegreeNonneg_OPEN 8669 := fun r => by
  have hap : (a_p 8669 : ℝ) = -38 := by exact_mod_cast BSD_ap_p8669
  have key : r ^ 2 - (a_p 8669 : ℝ) * r + ((8669 : ℕ) : ℝ) =
      (r + 38/2) ^ 2 + 33232/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8677 : BSD_FrobeniusDegreeNonneg_OPEN 8677 := fun r => by
  have hap : (a_p 8677 : ℝ) = -58 := by exact_mod_cast BSD_ap_p8677
  have key : r ^ 2 - (a_p 8677 : ℝ) * r + ((8677 : ℕ) : ℝ) =
      (r + 58/2) ^ 2 + 31344/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (58 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8681 : BSD_FrobeniusDegreeNonneg_OPEN 8681 := fun r => by
  have hap : (a_p 8681 : ℝ) = 42 := by exact_mod_cast BSD_ap_p8681
  have key : r ^ 2 - (a_p 8681 : ℝ) * r + ((8681 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 32960/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8689 : BSD_FrobeniusDegreeNonneg_OPEN 8689 := fun r => by
  have hap : (a_p 8689 : ℝ) = 46 := by exact_mod_cast BSD_ap_p8689
  have key : r ^ 2 - (a_p 8689 : ℝ) * r + ((8689 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 32640/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8693 : BSD_FrobeniusDegreeNonneg_OPEN 8693 := fun r => by
  have hap : (a_p 8693 : ℝ) = 106 := by exact_mod_cast BSD_ap_p8693
  have key : r ^ 2 - (a_p 8693 : ℝ) * r + ((8693 : ℕ) : ℝ) =
      (r - 106/2) ^ 2 + 23536/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (106 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8699 : BSD_FrobeniusDegreeNonneg_OPEN 8699 := fun r => by
  have hap : (a_p 8699 : ℝ) = 153 := by exact_mod_cast BSD_ap_p8699
  have key : r ^ 2 - (a_p 8699 : ℝ) * r + ((8699 : ℕ) : ℝ) =
      (r - 153/2) ^ 2 + 11387/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (153 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8707 : BSD_FrobeniusDegreeNonneg_OPEN 8707 := fun r => by
  have hap : (a_p 8707 : ℝ) = 22 := by exact_mod_cast BSD_ap_p8707
  have key : r ^ 2 - (a_p 8707 : ℝ) * r + ((8707 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 34344/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8713 : BSD_FrobeniusDegreeNonneg_OPEN 8713 := fun r => by
  have hap : (a_p 8713 : ℝ) = 91 := by exact_mod_cast BSD_ap_p8713
  have key : r ^ 2 - (a_p 8713 : ℝ) * r + ((8713 : ℕ) : ℝ) =
      (r - 91/2) ^ 2 + 26571/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (91 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8719 : BSD_FrobeniusDegreeNonneg_OPEN 8719 := fun r => by
  have hap : (a_p 8719 : ℝ) = 170 := by exact_mod_cast BSD_ap_p8719
  have key : r ^ 2 - (a_p 8719 : ℝ) * r + ((8719 : ℕ) : ℝ) =
      (r - 170/2) ^ 2 + 5976/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (170 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8731 : BSD_FrobeniusDegreeNonneg_OPEN 8731 := fun r => by
  have hap : (a_p 8731 : ℝ) = 52 := by exact_mod_cast BSD_ap_p8731
  have key : r ^ 2 - (a_p 8731 : ℝ) * r + ((8731 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 32220/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8737 : BSD_FrobeniusDegreeNonneg_OPEN 8737 := fun r => by
  have hap : (a_p 8737 : ℝ) = -90 := by exact_mod_cast BSD_ap_p8737
  have key : r ^ 2 - (a_p 8737 : ℝ) * r + ((8737 : ℕ) : ℝ) =
      (r + 90/2) ^ 2 + 26848/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (90 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8741 : BSD_FrobeniusDegreeNonneg_OPEN 8741 := fun r => by
  have hap : (a_p 8741 : ℝ) = 24 := by exact_mod_cast BSD_ap_p8741
  have key : r ^ 2 - (a_p 8741 : ℝ) * r + ((8741 : ℕ) : ℝ) =
      (r - 24/2) ^ 2 + 34388/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8747 : BSD_FrobeniusDegreeNonneg_OPEN 8747 := fun r => by
  have hap : (a_p 8747 : ℝ) = -170 := by exact_mod_cast BSD_ap_p8747
  have key : r ^ 2 - (a_p 8747 : ℝ) * r + ((8747 : ℕ) : ℝ) =
      (r + 170/2) ^ 2 + 6088/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (170 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8753 : BSD_FrobeniusDegreeNonneg_OPEN 8753 := fun r => by
  have hap : (a_p 8753 : ℝ) = 38 := by exact_mod_cast BSD_ap_p8753
  have key : r ^ 2 - (a_p 8753 : ℝ) * r + ((8753 : ℕ) : ℝ) =
      (r - 38/2) ^ 2 + 33568/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (38 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8761 : BSD_FrobeniusDegreeNonneg_OPEN 8761 := fun r => by
  have hap : (a_p 8761 : ℝ) = -69 := by exact_mod_cast BSD_ap_p8761
  have key : r ^ 2 - (a_p 8761 : ℝ) * r + ((8761 : ℕ) : ℝ) =
      (r + 69/2) ^ 2 + 30283/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (69 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8779 : BSD_FrobeniusDegreeNonneg_OPEN 8779 := fun r => by
  have hap : (a_p 8779 : ℝ) = -65 := by exact_mod_cast BSD_ap_p8779
  have key : r ^ 2 - (a_p 8779 : ℝ) * r + ((8779 : ℕ) : ℝ) =
      (r + 65/2) ^ 2 + 30891/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (65 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8783 : BSD_FrobeniusDegreeNonneg_OPEN 8783 := fun r => by
  have hap : (a_p 8783 : ℝ) = -57 := by exact_mod_cast BSD_ap_p8783
  have key : r ^ 2 - (a_p 8783 : ℝ) * r + ((8783 : ℕ) : ℝ) =
      (r + 57/2) ^ 2 + 31883/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (57 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8803 : BSD_FrobeniusDegreeNonneg_OPEN 8803 := fun r => by
  have hap : (a_p 8803 : ℝ) = 92 := by exact_mod_cast BSD_ap_p8803
  have key : r ^ 2 - (a_p 8803 : ℝ) * r + ((8803 : ℕ) : ℝ) =
      (r - 92/2) ^ 2 + 26748/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (92 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8807 : BSD_FrobeniusDegreeNonneg_OPEN 8807 := fun r => by
  have hap : (a_p 8807 : ℝ) = 124 := by exact_mod_cast BSD_ap_p8807
  have key : r ^ 2 - (a_p 8807 : ℝ) * r + ((8807 : ℕ) : ℝ) =
      (r - 124/2) ^ 2 + 19852/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (124 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8819 : BSD_FrobeniusDegreeNonneg_OPEN 8819 := fun r => by
  have hap : (a_p 8819 : ℝ) = -54 := by exact_mod_cast BSD_ap_p8819
  have key : r ^ 2 - (a_p 8819 : ℝ) * r + ((8819 : ℕ) : ℝ) =
      (r + 54/2) ^ 2 + 32360/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8821 : BSD_FrobeniusDegreeNonneg_OPEN 8821 := fun r => by
  have hap : (a_p 8821 : ℝ) = 10 := by exact_mod_cast BSD_ap_p8821
  have key : r ^ 2 - (a_p 8821 : ℝ) * r + ((8821 : ℕ) : ℝ) =
      (r - 10/2) ^ 2 + 35184/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (10 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8831 : BSD_FrobeniusDegreeNonneg_OPEN 8831 := fun r => by
  have hap : (a_p 8831 : ℝ) = -43 := by exact_mod_cast BSD_ap_p8831
  have key : r ^ 2 - (a_p 8831 : ℝ) * r + ((8831 : ℕ) : ℝ) =
      (r + 43/2) ^ 2 + 33475/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (43 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8837 : BSD_FrobeniusDegreeNonneg_OPEN 8837 := fun r => by
  have hap : (a_p 8837 : ℝ) = 159 := by exact_mod_cast BSD_ap_p8837
  have key : r ^ 2 - (a_p 8837 : ℝ) * r + ((8837 : ℕ) : ℝ) =
      (r - 159/2) ^ 2 + 10067/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (159 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8839 : BSD_FrobeniusDegreeNonneg_OPEN 8839 := fun r => by
  have hap : (a_p 8839 : ℝ) = 18 := by exact_mod_cast BSD_ap_p8839
  have key : r ^ 2 - (a_p 8839 : ℝ) * r + ((8839 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 35032/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8849 : BSD_FrobeniusDegreeNonneg_OPEN 8849 := fun r => by
  have hap : (a_p 8849 : ℝ) = -6 := by exact_mod_cast BSD_ap_p8849
  have key : r ^ 2 - (a_p 8849 : ℝ) * r + ((8849 : ℕ) : ℝ) =
      (r + 6/2) ^ 2 + 35360/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8861 : BSD_FrobeniusDegreeNonneg_OPEN 8861 := fun r => by
  have hap : (a_p 8861 : ℝ) = 72 := by exact_mod_cast BSD_ap_p8861
  have key : r ^ 2 - (a_p 8861 : ℝ) * r + ((8861 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 30260/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8863 : BSD_FrobeniusDegreeNonneg_OPEN 8863 := fun r => by
  have hap : (a_p 8863 : ℝ) = 52 := by exact_mod_cast BSD_ap_p8863
  have key : r ^ 2 - (a_p 8863 : ℝ) * r + ((8863 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 32748/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8867 : BSD_FrobeniusDegreeNonneg_OPEN 8867 := fun r => by
  have hap : (a_p 8867 : ℝ) = 47 := by exact_mod_cast BSD_ap_p8867
  have key : r ^ 2 - (a_p 8867 : ℝ) * r + ((8867 : ℕ) : ℝ) =
      (r - 47/2) ^ 2 + 33259/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (47 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8887 : BSD_FrobeniusDegreeNonneg_OPEN 8887 := fun r => by
  have hap : (a_p 8887 : ℝ) = -132 := by exact_mod_cast BSD_ap_p8887
  have key : r ^ 2 - (a_p 8887 : ℝ) * r + ((8887 : ℕ) : ℝ) =
      (r + 132/2) ^ 2 + 18124/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (132 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8893 : BSD_FrobeniusDegreeNonneg_OPEN 8893 := fun r => by
  have hap : (a_p 8893 : ℝ) = 146 := by exact_mod_cast BSD_ap_p8893
  have key : r ^ 2 - (a_p 8893 : ℝ) * r + ((8893 : ℕ) : ℝ) =
      (r - 146/2) ^ 2 + 14256/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (146 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8923 : BSD_FrobeniusDegreeNonneg_OPEN 8923 := fun r => by
  have hap : (a_p 8923 : ℝ) = 50 := by exact_mod_cast BSD_ap_p8923
  have key : r ^ 2 - (a_p 8923 : ℝ) * r + ((8923 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 33192/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8929 : BSD_FrobeniusDegreeNonneg_OPEN 8929 := fun r => by
  have hap : (a_p 8929 : ℝ) = 106 := by exact_mod_cast BSD_ap_p8929
  have key : r ^ 2 - (a_p 8929 : ℝ) * r + ((8929 : ℕ) : ℝ) =
      (r - 106/2) ^ 2 + 24480/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (106 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8933 : BSD_FrobeniusDegreeNonneg_OPEN 8933 := fun r => by
  have hap : (a_p 8933 : ℝ) = -69 := by exact_mod_cast BSD_ap_p8933
  have key : r ^ 2 - (a_p 8933 : ℝ) * r + ((8933 : ℕ) : ℝ) =
      (r + 69/2) ^ 2 + 30971/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (69 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8941 : BSD_FrobeniusDegreeNonneg_OPEN 8941 := fun r => by
  have hap : (a_p 8941 : ℝ) = 87 := by exact_mod_cast BSD_ap_p8941
  have key : r ^ 2 - (a_p 8941 : ℝ) * r + ((8941 : ℕ) : ℝ) =
      (r - 87/2) ^ 2 + 28195/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (87 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8951 : BSD_FrobeniusDegreeNonneg_OPEN 8951 := fun r => by
  have hap : (a_p 8951 : ℝ) = 98 := by exact_mod_cast BSD_ap_p8951
  have key : r ^ 2 - (a_p 8951 : ℝ) * r + ((8951 : ℕ) : ℝ) =
      (r - 98/2) ^ 2 + 26200/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (98 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8963 : BSD_FrobeniusDegreeNonneg_OPEN 8963 := fun r => by
  have hap : (a_p 8963 : ℝ) = -177 := by exact_mod_cast BSD_ap_p8963
  have key : r ^ 2 - (a_p 8963 : ℝ) * r + ((8963 : ℕ) : ℝ) =
      (r + 177/2) ^ 2 + 4523/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (177 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8969 : BSD_FrobeniusDegreeNonneg_OPEN 8969 := fun r => by
  have hap : (a_p 8969 : ℝ) = 79 := by exact_mod_cast BSD_ap_p8969
  have key : r ^ 2 - (a_p 8969 : ℝ) * r + ((8969 : ℕ) : ℝ) =
      (r - 79/2) ^ 2 + 29635/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (79 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8971 : BSD_FrobeniusDegreeNonneg_OPEN 8971 := fun r => by
  have hap : (a_p 8971 : ℝ) = 42 := by exact_mod_cast BSD_ap_p8971
  have key : r ^ 2 - (a_p 8971 : ℝ) * r + ((8971 : ℕ) : ℝ) =
      (r - 42/2) ^ 2 + 34120/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (42 : ℝ)/2)]

theorem BSD_DegreeNonneg_p8999 : BSD_FrobeniusDegreeNonneg_OPEN 8999 := fun r => by
  have hap : (a_p 8999 : ℝ) = -23 := by exact_mod_cast BSD_ap_p8999
  have key : r ^ 2 - (a_p 8999 : ℝ) * r + ((8999 : ℕ) : ℝ) =
      (r + 23/2) ^ 2 + 35467/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (23 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9001 : BSD_FrobeniusDegreeNonneg_OPEN 9001 := fun r => by
  have hap : (a_p 9001 : ℝ) = 51 := by exact_mod_cast BSD_ap_p9001
  have key : r ^ 2 - (a_p 9001 : ℝ) * r + ((9001 : ℕ) : ℝ) =
      (r - 51/2) ^ 2 + 33403/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (51 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9007 : BSD_FrobeniusDegreeNonneg_OPEN 9007 := fun r => by
  have hap : (a_p 9007 : ℝ) = 143 := by exact_mod_cast BSD_ap_p9007
  have key : r ^ 2 - (a_p 9007 : ℝ) * r + ((9007 : ℕ) : ℝ) =
      (r - 143/2) ^ 2 + 15579/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (143 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9011 : BSD_FrobeniusDegreeNonneg_OPEN 9011 := fun r => by
  have hap : (a_p 9011 : ℝ) = 96 := by exact_mod_cast BSD_ap_p9011
  have key : r ^ 2 - (a_p 9011 : ℝ) * r + ((9011 : ℕ) : ℝ) =
      (r - 96/2) ^ 2 + 26828/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (96 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9013 : BSD_FrobeniusDegreeNonneg_OPEN 9013 := fun r => by
  have hap : (a_p 9013 : ℝ) = 67 := by exact_mod_cast BSD_ap_p9013
  have key : r ^ 2 - (a_p 9013 : ℝ) * r + ((9013 : ℕ) : ℝ) =
      (r - 67/2) ^ 2 + 31563/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (67 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9029 : BSD_FrobeniusDegreeNonneg_OPEN 9029 := fun r => by
  have hap : (a_p 9029 : ℝ) = 105 := by exact_mod_cast BSD_ap_p9029
  have key : r ^ 2 - (a_p 9029 : ℝ) * r + ((9029 : ℕ) : ℝ) =
      (r - 105/2) ^ 2 + 25091/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (105 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9041 : BSD_FrobeniusDegreeNonneg_OPEN 9041 := fun r => by
  have hap : (a_p 9041 : ℝ) = -12 := by exact_mod_cast BSD_ap_p9041
  have key : r ^ 2 - (a_p 9041 : ℝ) * r + ((9041 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 36020/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9043 : BSD_FrobeniusDegreeNonneg_OPEN 9043 := fun r => by
  have hap : (a_p 9043 : ℝ) = -132 := by exact_mod_cast BSD_ap_p9043
  have key : r ^ 2 - (a_p 9043 : ℝ) * r + ((9043 : ℕ) : ℝ) =
      (r + 132/2) ^ 2 + 18748/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (132 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9049 : BSD_FrobeniusDegreeNonneg_OPEN 9049 := fun r => by
  have hap : (a_p 9049 : ℝ) = 44 := by exact_mod_cast BSD_ap_p9049
  have key : r ^ 2 - (a_p 9049 : ℝ) * r + ((9049 : ℕ) : ℝ) =
      (r - 44/2) ^ 2 + 34260/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (44 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9059 : BSD_FrobeniusDegreeNonneg_OPEN 9059 := fun r => by
  have hap : (a_p 9059 : ℝ) = -54 := by exact_mod_cast BSD_ap_p9059
  have key : r ^ 2 - (a_p 9059 : ℝ) * r + ((9059 : ℕ) : ℝ) =
      (r + 54/2) ^ 2 + 33320/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (54 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9067 : BSD_FrobeniusDegreeNonneg_OPEN 9067 := fun r => by
  have hap : (a_p 9067 : ℝ) = -65 := by exact_mod_cast BSD_ap_p9067
  have key : r ^ 2 - (a_p 9067 : ℝ) * r + ((9067 : ℕ) : ℝ) =
      (r + 65/2) ^ 2 + 32043/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (65 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9091 : BSD_FrobeniusDegreeNonneg_OPEN 9091 := fun r => by
  have hap : (a_p 9091 : ℝ) = 163 := by exact_mod_cast BSD_ap_p9091
  have key : r ^ 2 - (a_p 9091 : ℝ) * r + ((9091 : ℕ) : ℝ) =
      (r - 163/2) ^ 2 + 9795/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (163 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9103 : BSD_FrobeniusDegreeNonneg_OPEN 9103 := fun r => by
  have hap : (a_p 9103 : ℝ) = -66 := by exact_mod_cast BSD_ap_p9103
  have key : r ^ 2 - (a_p 9103 : ℝ) * r + ((9103 : ℕ) : ℝ) =
      (r + 66/2) ^ 2 + 32056/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (66 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9109 : BSD_FrobeniusDegreeNonneg_OPEN 9109 := fun r => by
  have hap : (a_p 9109 : ℝ) = -55 := by exact_mod_cast BSD_ap_p9109
  have key : r ^ 2 - (a_p 9109 : ℝ) * r + ((9109 : ℕ) : ℝ) =
      (r + 55/2) ^ 2 + 33411/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (55 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9127 : BSD_FrobeniusDegreeNonneg_OPEN 9127 := fun r => by
  have hap : (a_p 9127 : ℝ) = -110 := by exact_mod_cast BSD_ap_p9127
  have key : r ^ 2 - (a_p 9127 : ℝ) * r + ((9127 : ℕ) : ℝ) =
      (r + 110/2) ^ 2 + 24408/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (110 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9133 : BSD_FrobeniusDegreeNonneg_OPEN 9133 := fun r => by
  have hap : (a_p 9133 : ℝ) = -107 := by exact_mod_cast BSD_ap_p9133
  have key : r ^ 2 - (a_p 9133 : ℝ) * r + ((9133 : ℕ) : ℝ) =
      (r + 107/2) ^ 2 + 25083/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (107 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9137 : BSD_FrobeniusDegreeNonneg_OPEN 9137 := fun r => by
  have hap : (a_p 9137 : ℝ) = -50 := by exact_mod_cast BSD_ap_p9137
  have key : r ^ 2 - (a_p 9137 : ℝ) * r + ((9137 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 34048/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9151 : BSD_FrobeniusDegreeNonneg_OPEN 9151 := fun r => by
  have hap : (a_p 9151 : ℝ) = 30 := by exact_mod_cast BSD_ap_p9151
  have key : r ^ 2 - (a_p 9151 : ℝ) * r + ((9151 : ℕ) : ℝ) =
      (r - 30/2) ^ 2 + 35704/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (30 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9157 : BSD_FrobeniusDegreeNonneg_OPEN 9157 := fun r => by
  have hap : (a_p 9157 : ℝ) = 105 := by exact_mod_cast BSD_ap_p9157
  have key : r ^ 2 - (a_p 9157 : ℝ) * r + ((9157 : ℕ) : ℝ) =
      (r - 105/2) ^ 2 + 25603/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (105 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9161 : BSD_FrobeniusDegreeNonneg_OPEN 9161 := fun r => by
  have hap : (a_p 9161 : ℝ) = 110 := by exact_mod_cast BSD_ap_p9161
  have key : r ^ 2 - (a_p 9161 : ℝ) * r + ((9161 : ℕ) : ℝ) =
      (r - 110/2) ^ 2 + 24544/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (110 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9173 : BSD_FrobeniusDegreeNonneg_OPEN 9173 := fun r => by
  have hap : (a_p 9173 : ℝ) = 110 := by exact_mod_cast BSD_ap_p9173
  have key : r ^ 2 - (a_p 9173 : ℝ) * r + ((9173 : ℕ) : ℝ) =
      (r - 110/2) ^ 2 + 24592/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (110 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9181 : BSD_FrobeniusDegreeNonneg_OPEN 9181 := fun r => by
  have hap : (a_p 9181 : ℝ) = -150 := by exact_mod_cast BSD_ap_p9181
  have key : r ^ 2 - (a_p 9181 : ℝ) * r + ((9181 : ℕ) : ℝ) =
      (r + 150/2) ^ 2 + 14224/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (150 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9187 : BSD_FrobeniusDegreeNonneg_OPEN 9187 := fun r => by
  have hap : (a_p 9187 : ℝ) = -142 := by exact_mod_cast BSD_ap_p9187
  have key : r ^ 2 - (a_p 9187 : ℝ) * r + ((9187 : ℕ) : ℝ) =
      (r + 142/2) ^ 2 + 16584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (142 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9199 : BSD_FrobeniusDegreeNonneg_OPEN 9199 := fun r => by
  have hap : (a_p 9199 : ℝ) = 16 := by exact_mod_cast BSD_ap_p9199
  have key : r ^ 2 - (a_p 9199 : ℝ) * r + ((9199 : ℕ) : ℝ) =
      (r - 16/2) ^ 2 + 36540/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9203 : BSD_FrobeniusDegreeNonneg_OPEN 9203 := fun r => by
  have hap : (a_p 9203 : ℝ) = 44 := by exact_mod_cast BSD_ap_p9203
  have key : r ^ 2 - (a_p 9203 : ℝ) * r + ((9203 : ℕ) : ℝ) =
      (r - 44/2) ^ 2 + 34876/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (44 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9209 : BSD_FrobeniusDegreeNonneg_OPEN 9209 := fun r => by
  have hap : (a_p 9209 : ℝ) = -12 := by exact_mod_cast BSD_ap_p9209
  have key : r ^ 2 - (a_p 9209 : ℝ) * r + ((9209 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 36692/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9221 : BSD_FrobeniusDegreeNonneg_OPEN 9221 := fun r => by
  have hap : (a_p 9221 : ℝ) = -79 := by exact_mod_cast BSD_ap_p9221
  have key : r ^ 2 - (a_p 9221 : ℝ) * r + ((9221 : ℕ) : ℝ) =
      (r + 79/2) ^ 2 + 30643/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (79 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9227 : BSD_FrobeniusDegreeNonneg_OPEN 9227 := fun r => by
  have hap : (a_p 9227 : ℝ) = 0 := by exact_mod_cast BSD_ap_p9227
  have key : r ^ 2 - (a_p 9227 : ℝ) * r + ((9227 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 36908/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9239 : BSD_FrobeniusDegreeNonneg_OPEN 9239 := fun r => by
  have hap : (a_p 9239 : ℝ) = 12 := by exact_mod_cast BSD_ap_p9239
  have key : r ^ 2 - (a_p 9239 : ℝ) * r + ((9239 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 36812/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9241 : BSD_FrobeniusDegreeNonneg_OPEN 9241 := fun r => by
  have hap : (a_p 9241 : ℝ) = -39 := by exact_mod_cast BSD_ap_p9241
  have key : r ^ 2 - (a_p 9241 : ℝ) * r + ((9241 : ℕ) : ℝ) =
      (r + 39/2) ^ 2 + 35443/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (39 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9257 : BSD_FrobeniusDegreeNonneg_OPEN 9257 := fun r => by
  have hap : (a_p 9257 : ℝ) = 118 := by exact_mod_cast BSD_ap_p9257
  have key : r ^ 2 - (a_p 9257 : ℝ) * r + ((9257 : ℕ) : ℝ) =
      (r - 118/2) ^ 2 + 23104/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (118 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9277 : BSD_FrobeniusDegreeNonneg_OPEN 9277 := fun r => by
  have hap : (a_p 9277 : ℝ) = 17 := by exact_mod_cast BSD_ap_p9277
  have key : r ^ 2 - (a_p 9277 : ℝ) * r + ((9277 : ℕ) : ℝ) =
      (r - 17/2) ^ 2 + 36819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (17 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9281 : BSD_FrobeniusDegreeNonneg_OPEN 9281 := fun r => by
  have hap : (a_p 9281 : ℝ) = -156 := by exact_mod_cast BSD_ap_p9281
  have key : r ^ 2 - (a_p 9281 : ℝ) * r + ((9281 : ℕ) : ℝ) =
      (r + 156/2) ^ 2 + 12788/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (156 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9283 : BSD_FrobeniusDegreeNonneg_OPEN 9283 := fun r => by
  have hap : (a_p 9283 : ℝ) = -94 := by exact_mod_cast BSD_ap_p9283
  have key : r ^ 2 - (a_p 9283 : ℝ) * r + ((9283 : ℕ) : ℝ) =
      (r + 94/2) ^ 2 + 28296/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (94 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9293 : BSD_FrobeniusDegreeNonneg_OPEN 9293 := fun r => by
  have hap : (a_p 9293 : ℝ) = 14 := by exact_mod_cast BSD_ap_p9293
  have key : r ^ 2 - (a_p 9293 : ℝ) * r + ((9293 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 36976/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9311 : BSD_FrobeniusDegreeNonneg_OPEN 9311 := fun r => by
  have hap : (a_p 9311 : ℝ) = 131 := by exact_mod_cast BSD_ap_p9311
  have key : r ^ 2 - (a_p 9311 : ℝ) * r + ((9311 : ℕ) : ℝ) =
      (r - 131/2) ^ 2 + 20083/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (131 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9319 : BSD_FrobeniusDegreeNonneg_OPEN 9319 := fun r => by
  have hap : (a_p 9319 : ℝ) = -98 := by exact_mod_cast BSD_ap_p9319
  have key : r ^ 2 - (a_p 9319 : ℝ) * r + ((9319 : ℕ) : ℝ) =
      (r + 98/2) ^ 2 + 27672/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (98 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9323 : BSD_FrobeniusDegreeNonneg_OPEN 9323 := fun r => by
  have hap : (a_p 9323 : ℝ) = 134 := by exact_mod_cast BSD_ap_p9323
  have key : r ^ 2 - (a_p 9323 : ℝ) * r + ((9323 : ℕ) : ℝ) =
      (r - 134/2) ^ 2 + 19336/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (134 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9337 : BSD_FrobeniusDegreeNonneg_OPEN 9337 := fun r => by
  have hap : (a_p 9337 : ℝ) = 113 := by exact_mod_cast BSD_ap_p9337
  have key : r ^ 2 - (a_p 9337 : ℝ) * r + ((9337 : ℕ) : ℝ) =
      (r - 113/2) ^ 2 + 24579/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (113 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9341 : BSD_FrobeniusDegreeNonneg_OPEN 9341 := fun r => by
  have hap : (a_p 9341 : ℝ) = 106 := by exact_mod_cast BSD_ap_p9341
  have key : r ^ 2 - (a_p 9341 : ℝ) * r + ((9341 : ℕ) : ℝ) =
      (r - 106/2) ^ 2 + 26128/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (106 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9343 : BSD_FrobeniusDegreeNonneg_OPEN 9343 := fun r => by
  have hap : (a_p 9343 : ℝ) = -183 := by exact_mod_cast BSD_ap_p9343
  have key : r ^ 2 - (a_p 9343 : ℝ) * r + ((9343 : ℕ) : ℝ) =
      (r + 183/2) ^ 2 + 3883/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (183 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9349 : BSD_FrobeniusDegreeNonneg_OPEN 9349 := fun r => by
  have hap : (a_p 9349 : ℝ) = -136 := by exact_mod_cast BSD_ap_p9349
  have key : r ^ 2 - (a_p 9349 : ℝ) * r + ((9349 : ℕ) : ℝ) =
      (r + 136/2) ^ 2 + 18900/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (136 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9371 : BSD_FrobeniusDegreeNonneg_OPEN 9371 := fun r => by
  have hap : (a_p 9371 : ℝ) = -12 := by exact_mod_cast BSD_ap_p9371
  have key : r ^ 2 - (a_p 9371 : ℝ) * r + ((9371 : ℕ) : ℝ) =
      (r + 12/2) ^ 2 + 37340/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9377 : BSD_FrobeniusDegreeNonneg_OPEN 9377 := fun r => by
  have hap : (a_p 9377 : ℝ) = 70 := by exact_mod_cast BSD_ap_p9377
  have key : r ^ 2 - (a_p 9377 : ℝ) * r + ((9377 : ℕ) : ℝ) =
      (r - 70/2) ^ 2 + 32608/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (70 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9391 : BSD_FrobeniusDegreeNonneg_OPEN 9391 := fun r => by
  have hap : (a_p 9391 : ℝ) = -14 := by exact_mod_cast BSD_ap_p9391
  have key : r ^ 2 - (a_p 9391 : ℝ) * r + ((9391 : ℕ) : ℝ) =
      (r + 14/2) ^ 2 + 37368/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9397 : BSD_FrobeniusDegreeNonneg_OPEN 9397 := fun r => by
  have hap : (a_p 9397 : ℝ) = 177 := by exact_mod_cast BSD_ap_p9397
  have key : r ^ 2 - (a_p 9397 : ℝ) * r + ((9397 : ℕ) : ℝ) =
      (r - 177/2) ^ 2 + 6259/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (177 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9403 : BSD_FrobeniusDegreeNonneg_OPEN 9403 := fun r => by
  have hap : (a_p 9403 : ℝ) = 55 := by exact_mod_cast BSD_ap_p9403
  have key : r ^ 2 - (a_p 9403 : ℝ) * r + ((9403 : ℕ) : ℝ) =
      (r - 55/2) ^ 2 + 34587/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (55 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9413 : BSD_FrobeniusDegreeNonneg_OPEN 9413 := fun r => by
  have hap : (a_p 9413 : ℝ) = -106 := by exact_mod_cast BSD_ap_p9413
  have key : r ^ 2 - (a_p 9413 : ℝ) * r + ((9413 : ℕ) : ℝ) =
      (r + 106/2) ^ 2 + 26416/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (106 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9419 : BSD_FrobeniusDegreeNonneg_OPEN 9419 := fun r => by
  have hap : (a_p 9419 : ℝ) = 40 := by exact_mod_cast BSD_ap_p9419
  have key : r ^ 2 - (a_p 9419 : ℝ) * r + ((9419 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 36076/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9421 : BSD_FrobeniusDegreeNonneg_OPEN 9421 := fun r => by
  have hap : (a_p 9421 : ℝ) = -114 := by exact_mod_cast BSD_ap_p9421
  have key : r ^ 2 - (a_p 9421 : ℝ) * r + ((9421 : ℕ) : ℝ) =
      (r + 114/2) ^ 2 + 24688/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (114 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9431 : BSD_FrobeniusDegreeNonneg_OPEN 9431 := fun r => by
  have hap : (a_p 9431 : ℝ) = -64 := by exact_mod_cast BSD_ap_p9431
  have key : r ^ 2 - (a_p 9431 : ℝ) * r + ((9431 : ℕ) : ℝ) =
      (r + 64/2) ^ 2 + 33628/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (64 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9433 : BSD_FrobeniusDegreeNonneg_OPEN 9433 := fun r => by
  have hap : (a_p 9433 : ℝ) = -164 := by exact_mod_cast BSD_ap_p9433
  have key : r ^ 2 - (a_p 9433 : ℝ) * r + ((9433 : ℕ) : ℝ) =
      (r + 164/2) ^ 2 + 10836/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (164 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9437 : BSD_FrobeniusDegreeNonneg_OPEN 9437 := fun r => by
  have hap : (a_p 9437 : ℝ) = -52 := by exact_mod_cast BSD_ap_p9437
  have key : r ^ 2 - (a_p 9437 : ℝ) * r + ((9437 : ℕ) : ℝ) =
      (r + 52/2) ^ 2 + 35044/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9439 : BSD_FrobeniusDegreeNonneg_OPEN 9439 := fun r => by
  have hap : (a_p 9439 : ℝ) = 33 := by exact_mod_cast BSD_ap_p9439
  have key : r ^ 2 - (a_p 9439 : ℝ) * r + ((9439 : ℕ) : ℝ) =
      (r - 33/2) ^ 2 + 36667/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (33 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9461 : BSD_FrobeniusDegreeNonneg_OPEN 9461 := fun r => by
  have hap : (a_p 9461 : ℝ) = 170 := by exact_mod_cast BSD_ap_p9461
  have key : r ^ 2 - (a_p 9461 : ℝ) * r + ((9461 : ℕ) : ℝ) =
      (r - 170/2) ^ 2 + 8944/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (170 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9463 : BSD_FrobeniusDegreeNonneg_OPEN 9463 := fun r => by
  have hap : (a_p 9463 : ℝ) = 184 := by exact_mod_cast BSD_ap_p9463
  have key : r ^ 2 - (a_p 9463 : ℝ) * r + ((9463 : ℕ) : ℝ) =
      (r - 184/2) ^ 2 + 3996/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (184 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9467 : BSD_FrobeniusDegreeNonneg_OPEN 9467 := fun r => by
  have hap : (a_p 9467 : ℝ) = -88 := by exact_mod_cast BSD_ap_p9467
  have key : r ^ 2 - (a_p 9467 : ℝ) * r + ((9467 : ℕ) : ℝ) =
      (r + 88/2) ^ 2 + 30124/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (88 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9473 : BSD_FrobeniusDegreeNonneg_OPEN 9473 := fun r => by
  have hap : (a_p 9473 : ℝ) = -44 := by exact_mod_cast BSD_ap_p9473
  have key : r ^ 2 - (a_p 9473 : ℝ) * r + ((9473 : ℕ) : ℝ) =
      (r + 44/2) ^ 2 + 35956/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (44 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9479 : BSD_FrobeniusDegreeNonneg_OPEN 9479 := fun r => by
  have hap : (a_p 9479 : ℝ) = 22 := by exact_mod_cast BSD_ap_p9479
  have key : r ^ 2 - (a_p 9479 : ℝ) * r + ((9479 : ℕ) : ℝ) =
      (r - 22/2) ^ 2 + 37432/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (22 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9491 : BSD_FrobeniusDegreeNonneg_OPEN 9491 := fun r => by
  have hap : (a_p 9491 : ℝ) = -60 := by exact_mod_cast BSD_ap_p9491
  have key : r ^ 2 - (a_p 9491 : ℝ) * r + ((9491 : ℕ) : ℝ) =
      (r + 60/2) ^ 2 + 34364/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (60 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9497 : BSD_FrobeniusDegreeNonneg_OPEN 9497 := fun r => by
  have hap : (a_p 9497 : ℝ) = 115 := by exact_mod_cast BSD_ap_p9497
  have key : r ^ 2 - (a_p 9497 : ℝ) * r + ((9497 : ℕ) : ℝ) =
      (r - 115/2) ^ 2 + 24763/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (115 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9511 : BSD_FrobeniusDegreeNonneg_OPEN 9511 := fun r => by
  have hap : (a_p 9511 : ℝ) = 116 := by exact_mod_cast BSD_ap_p9511
  have key : r ^ 2 - (a_p 9511 : ℝ) * r + ((9511 : ℕ) : ℝ) =
      (r - 116/2) ^ 2 + 24588/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (116 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9521 : BSD_FrobeniusDegreeNonneg_OPEN 9521 := fun r => by
  have hap : (a_p 9521 : ℝ) = -50 := by exact_mod_cast BSD_ap_p9521
  have key : r ^ 2 - (a_p 9521 : ℝ) * r + ((9521 : ℕ) : ℝ) =
      (r + 50/2) ^ 2 + 35584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9533 : BSD_FrobeniusDegreeNonneg_OPEN 9533 := fun r => by
  have hap : (a_p 9533 : ℝ) = 74 := by exact_mod_cast BSD_ap_p9533
  have key : r ^ 2 - (a_p 9533 : ℝ) * r + ((9533 : ℕ) : ℝ) =
      (r - 74/2) ^ 2 + 32656/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (74 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9539 : BSD_FrobeniusDegreeNonneg_OPEN 9539 := fun r => by
  have hap : (a_p 9539 : ℝ) = 0 := by exact_mod_cast BSD_ap_p9539
  have key : r ^ 2 - (a_p 9539 : ℝ) * r + ((9539 : ℕ) : ℝ) =
      (r - 0/2) ^ 2 + 38156/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (0 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9547 : BSD_FrobeniusDegreeNonneg_OPEN 9547 := fun r => by
  have hap : (a_p 9547 : ℝ) = 98 := by exact_mod_cast BSD_ap_p9547
  have key : r ^ 2 - (a_p 9547 : ℝ) * r + ((9547 : ℕ) : ℝ) =
      (r - 98/2) ^ 2 + 28584/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (98 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9551 : BSD_FrobeniusDegreeNonneg_OPEN 9551 := fun r => by
  have hap : (a_p 9551 : ℝ) = 139 := by exact_mod_cast BSD_ap_p9551
  have key : r ^ 2 - (a_p 9551 : ℝ) * r + ((9551 : ℕ) : ℝ) =
      (r - 139/2) ^ 2 + 18883/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (139 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9587 : BSD_FrobeniusDegreeNonneg_OPEN 9587 := fun r => by
  have hap : (a_p 9587 : ℝ) = -60 := by exact_mod_cast BSD_ap_p9587
  have key : r ^ 2 - (a_p 9587 : ℝ) * r + ((9587 : ℕ) : ℝ) =
      (r + 60/2) ^ 2 + 34748/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (60 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9601 : BSD_FrobeniusDegreeNonneg_OPEN 9601 := fun r => by
  have hap : (a_p 9601 : ℝ) = -111 := by exact_mod_cast BSD_ap_p9601
  have key : r ^ 2 - (a_p 9601 : ℝ) * r + ((9601 : ℕ) : ℝ) =
      (r + 111/2) ^ 2 + 26083/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (111 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9613 : BSD_FrobeniusDegreeNonneg_OPEN 9613 := fun r => by
  have hap : (a_p 9613 : ℝ) = -94 := by exact_mod_cast BSD_ap_p9613
  have key : r ^ 2 - (a_p 9613 : ℝ) * r + ((9613 : ℕ) : ℝ) =
      (r + 94/2) ^ 2 + 29616/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (94 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9619 : BSD_FrobeniusDegreeNonneg_OPEN 9619 := fun r => by
  have hap : (a_p 9619 : ℝ) = 72 := by exact_mod_cast BSD_ap_p9619
  have key : r ^ 2 - (a_p 9619 : ℝ) * r + ((9619 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 33292/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9623 : BSD_FrobeniusDegreeNonneg_OPEN 9623 := fun r => by
  have hap : (a_p 9623 : ℝ) = 63 := by exact_mod_cast BSD_ap_p9623
  have key : r ^ 2 - (a_p 9623 : ℝ) * r + ((9623 : ℕ) : ℝ) =
      (r - 63/2) ^ 2 + 34523/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (63 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9629 : BSD_FrobeniusDegreeNonneg_OPEN 9629 := fun r => by
  have hap : (a_p 9629 : ℝ) = 137 := by exact_mod_cast BSD_ap_p9629
  have key : r ^ 2 - (a_p 9629 : ℝ) * r + ((9629 : ℕ) : ℝ) =
      (r - 137/2) ^ 2 + 19747/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (137 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9631 : BSD_FrobeniusDegreeNonneg_OPEN 9631 := fun r => by
  have hap : (a_p 9631 : ℝ) = 18 := by exact_mod_cast BSD_ap_p9631
  have key : r ^ 2 - (a_p 9631 : ℝ) * r + ((9631 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 38200/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9643 : BSD_FrobeniusDegreeNonneg_OPEN 9643 := fun r => by
  have hap : (a_p 9643 : ℝ) = -46 := by exact_mod_cast BSD_ap_p9643
  have key : r ^ 2 - (a_p 9643 : ℝ) * r + ((9643 : ℕ) : ℝ) =
      (r + 46/2) ^ 2 + 36456/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9649 : BSD_FrobeniusDegreeNonneg_OPEN 9649 := fun r => by
  have hap : (a_p 9649 : ℝ) = -28 := by exact_mod_cast BSD_ap_p9649
  have key : r ^ 2 - (a_p 9649 : ℝ) * r + ((9649 : ℕ) : ℝ) =
      (r + 28/2) ^ 2 + 37812/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (28 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9661 : BSD_FrobeniusDegreeNonneg_OPEN 9661 := fun r => by
  have hap : (a_p 9661 : ℝ) = -47 := by exact_mod_cast BSD_ap_p9661
  have key : r ^ 2 - (a_p 9661 : ℝ) * r + ((9661 : ℕ) : ℝ) =
      (r + 47/2) ^ 2 + 36435/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (47 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9677 : BSD_FrobeniusDegreeNonneg_OPEN 9677 := fun r => by
  have hap : (a_p 9677 : ℝ) = -48 := by exact_mod_cast BSD_ap_p9677
  have key : r ^ 2 - (a_p 9677 : ℝ) * r + ((9677 : ℕ) : ℝ) =
      (r + 48/2) ^ 2 + 36404/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (48 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9679 : BSD_FrobeniusDegreeNonneg_OPEN 9679 := fun r => by
  have hap : (a_p 9679 : ℝ) = 40 := by exact_mod_cast BSD_ap_p9679
  have key : r ^ 2 - (a_p 9679 : ℝ) * r + ((9679 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 37116/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9689 : BSD_FrobeniusDegreeNonneg_OPEN 9689 := fun r => by
  have hap : (a_p 9689 : ℝ) = -15 := by exact_mod_cast BSD_ap_p9689
  have key : r ^ 2 - (a_p 9689 : ℝ) * r + ((9689 : ℕ) : ℝ) =
      (r + 15/2) ^ 2 + 38531/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (15 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9697 : BSD_FrobeniusDegreeNonneg_OPEN 9697 := fun r => by
  have hap : (a_p 9697 : ℝ) = 46 := by exact_mod_cast BSD_ap_p9697
  have key : r ^ 2 - (a_p 9697 : ℝ) * r + ((9697 : ℕ) : ℝ) =
      (r - 46/2) ^ 2 + 36672/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (46 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9719 : BSD_FrobeniusDegreeNonneg_OPEN 9719 := fun r => by
  have hap : (a_p 9719 : ℝ) = -124 := by exact_mod_cast BSD_ap_p9719
  have key : r ^ 2 - (a_p 9719 : ℝ) * r + ((9719 : ℕ) : ℝ) =
      (r + 124/2) ^ 2 + 23500/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (124 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9721 : BSD_FrobeniusDegreeNonneg_OPEN 9721 := fun r => by
  have hap : (a_p 9721 : ℝ) = 100 := by exact_mod_cast BSD_ap_p9721
  have key : r ^ 2 - (a_p 9721 : ℝ) * r + ((9721 : ℕ) : ℝ) =
      (r - 100/2) ^ 2 + 28884/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (100 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9733 : BSD_FrobeniusDegreeNonneg_OPEN 9733 := fun r => by
  have hap : (a_p 9733 : ℝ) = -19 := by exact_mod_cast BSD_ap_p9733
  have key : r ^ 2 - (a_p 9733 : ℝ) * r + ((9733 : ℕ) : ℝ) =
      (r + 19/2) ^ 2 + 38571/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (19 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9739 : BSD_FrobeniusDegreeNonneg_OPEN 9739 := fun r => by
  have hap : (a_p 9739 : ℝ) = -101 := by exact_mod_cast BSD_ap_p9739
  have key : r ^ 2 - (a_p 9739 : ℝ) * r + ((9739 : ℕ) : ℝ) =
      (r + 101/2) ^ 2 + 28755/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (101 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9743 : BSD_FrobeniusDegreeNonneg_OPEN 9743 := fun r => by
  have hap : (a_p 9743 : ℝ) = -44 := by exact_mod_cast BSD_ap_p9743
  have key : r ^ 2 - (a_p 9743 : ℝ) * r + ((9743 : ℕ) : ℝ) =
      (r + 44/2) ^ 2 + 37036/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (44 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9749 : BSD_FrobeniusDegreeNonneg_OPEN 9749 := fun r => by
  have hap : (a_p 9749 : ℝ) = 86 := by exact_mod_cast BSD_ap_p9749
  have key : r ^ 2 - (a_p 9749 : ℝ) * r + ((9749 : ℕ) : ℝ) =
      (r - 86/2) ^ 2 + 31600/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (86 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9767 : BSD_FrobeniusDegreeNonneg_OPEN 9767 := fun r => by
  have hap : (a_p 9767 : ℝ) = 18 := by exact_mod_cast BSD_ap_p9767
  have key : r ^ 2 - (a_p 9767 : ℝ) * r + ((9767 : ℕ) : ℝ) =
      (r - 18/2) ^ 2 + 38744/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9769 : BSD_FrobeniusDegreeNonneg_OPEN 9769 := fun r => by
  have hap : (a_p 9769 : ℝ) = 61 := by exact_mod_cast BSD_ap_p9769
  have key : r ^ 2 - (a_p 9769 : ℝ) * r + ((9769 : ℕ) : ℝ) =
      (r - 61/2) ^ 2 + 35355/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (61 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9781 : BSD_FrobeniusDegreeNonneg_OPEN 9781 := fun r => by
  have hap : (a_p 9781 : ℝ) = 88 := by exact_mod_cast BSD_ap_p9781
  have key : r ^ 2 - (a_p 9781 : ℝ) * r + ((9781 : ℕ) : ℝ) =
      (r - 88/2) ^ 2 + 31380/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (88 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9787 : BSD_FrobeniusDegreeNonneg_OPEN 9787 := fun r => by
  have hap : (a_p 9787 : ℝ) = -122 := by exact_mod_cast BSD_ap_p9787
  have key : r ^ 2 - (a_p 9787 : ℝ) * r + ((9787 : ℕ) : ℝ) =
      (r + 122/2) ^ 2 + 24264/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (122 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9791 : BSD_FrobeniusDegreeNonneg_OPEN 9791 := fun r => by
  have hap : (a_p 9791 : ℝ) = -112 := by exact_mod_cast BSD_ap_p9791
  have key : r ^ 2 - (a_p 9791 : ℝ) * r + ((9791 : ℕ) : ℝ) =
      (r + 112/2) ^ 2 + 26620/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (112 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9803 : BSD_FrobeniusDegreeNonneg_OPEN 9803 := fun r => by
  have hap : (a_p 9803 : ℝ) = -24 := by exact_mod_cast BSD_ap_p9803
  have key : r ^ 2 - (a_p 9803 : ℝ) * r + ((9803 : ℕ) : ℝ) =
      (r + 24/2) ^ 2 + 38636/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (24 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9811 : BSD_FrobeniusDegreeNonneg_OPEN 9811 := fun r => by
  have hap : (a_p 9811 : ℝ) = -18 := by exact_mod_cast BSD_ap_p9811
  have key : r ^ 2 - (a_p 9811 : ℝ) * r + ((9811 : ℕ) : ℝ) =
      (r + 18/2) ^ 2 + 38920/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (18 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9817 : BSD_FrobeniusDegreeNonneg_OPEN 9817 := fun r => by
  have hap : (a_p 9817 : ℝ) = 90 := by exact_mod_cast BSD_ap_p9817
  have key : r ^ 2 - (a_p 9817 : ℝ) * r + ((9817 : ℕ) : ℝ) =
      (r - 90/2) ^ 2 + 31168/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (90 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9829 : BSD_FrobeniusDegreeNonneg_OPEN 9829 := fun r => by
  have hap : (a_p 9829 : ℝ) = 14 := by exact_mod_cast BSD_ap_p9829
  have key : r ^ 2 - (a_p 9829 : ℝ) * r + ((9829 : ℕ) : ℝ) =
      (r - 14/2) ^ 2 + 39120/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (14 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9833 : BSD_FrobeniusDegreeNonneg_OPEN 9833 := fun r => by
  have hap : (a_p 9833 : ℝ) = 6 := by exact_mod_cast BSD_ap_p9833
  have key : r ^ 2 - (a_p 9833 : ℝ) * r + ((9833 : ℕ) : ℝ) =
      (r - 6/2) ^ 2 + 39296/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (6 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9839 : BSD_FrobeniusDegreeNonneg_OPEN 9839 := fun r => by
  have hap : (a_p 9839 : ℝ) = -11 := by exact_mod_cast BSD_ap_p9839
  have key : r ^ 2 - (a_p 9839 : ℝ) * r + ((9839 : ℕ) : ℝ) =
      (r + 11/2) ^ 2 + 39235/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (11 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9851 : BSD_FrobeniusDegreeNonneg_OPEN 9851 := fun r => by
  have hap : (a_p 9851 : ℝ) = -66 := by exact_mod_cast BSD_ap_p9851
  have key : r ^ 2 - (a_p 9851 : ℝ) * r + ((9851 : ℕ) : ℝ) =
      (r + 66/2) ^ 2 + 35048/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (66 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9857 : BSD_FrobeniusDegreeNonneg_OPEN 9857 := fun r => by
  have hap : (a_p 9857 : ℝ) = -173 := by exact_mod_cast BSD_ap_p9857
  have key : r ^ 2 - (a_p 9857 : ℝ) * r + ((9857 : ℕ) : ℝ) =
      (r + 173/2) ^ 2 + 9499/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (173 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9859 : BSD_FrobeniusDegreeNonneg_OPEN 9859 := fun r => by
  have hap : (a_p 9859 : ℝ) = -23 := by exact_mod_cast BSD_ap_p9859
  have key : r ^ 2 - (a_p 9859 : ℝ) * r + ((9859 : ℕ) : ℝ) =
      (r + 23/2) ^ 2 + 38907/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (23 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9871 : BSD_FrobeniusDegreeNonneg_OPEN 9871 := fun r => by
  have hap : (a_p 9871 : ℝ) = -16 := by exact_mod_cast BSD_ap_p9871
  have key : r ^ 2 - (a_p 9871 : ℝ) * r + ((9871 : ℕ) : ℝ) =
      (r + 16/2) ^ 2 + 39228/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (16 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9883 : BSD_FrobeniusDegreeNonneg_OPEN 9883 := fun r => by
  have hap : (a_p 9883 : ℝ) = 51 := by exact_mod_cast BSD_ap_p9883
  have key : r ^ 2 - (a_p 9883 : ℝ) * r + ((9883 : ℕ) : ℝ) =
      (r - 51/2) ^ 2 + 36931/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (51 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9887 : BSD_FrobeniusDegreeNonneg_OPEN 9887 := fun r => by
  have hap : (a_p 9887 : ℝ) = -27 := by exact_mod_cast BSD_ap_p9887
  have key : r ^ 2 - (a_p 9887 : ℝ) * r + ((9887 : ℕ) : ℝ) =
      (r + 27/2) ^ 2 + 38819/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (27 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9901 : BSD_FrobeniusDegreeNonneg_OPEN 9901 := fun r => by
  have hap : (a_p 9901 : ℝ) = -118 := by exact_mod_cast BSD_ap_p9901
  have key : r ^ 2 - (a_p 9901 : ℝ) * r + ((9901 : ℕ) : ℝ) =
      (r + 118/2) ^ 2 + 25680/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (118 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9907 : BSD_FrobeniusDegreeNonneg_OPEN 9907 := fun r => by
  have hap : (a_p 9907 : ℝ) = 62 := by exact_mod_cast BSD_ap_p9907
  have key : r ^ 2 - (a_p 9907 : ℝ) * r + ((9907 : ℕ) : ℝ) =
      (r - 62/2) ^ 2 + 35784/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (62 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9923 : BSD_FrobeniusDegreeNonneg_OPEN 9923 := fun r => by
  have hap : (a_p 9923 : ℝ) = 129 := by exact_mod_cast BSD_ap_p9923
  have key : r ^ 2 - (a_p 9923 : ℝ) * r + ((9923 : ℕ) : ℝ) =
      (r - 129/2) ^ 2 + 23051/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (129 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9929 : BSD_FrobeniusDegreeNonneg_OPEN 9929 := fun r => by
  have hap : (a_p 9929 : ℝ) = -146 := by exact_mod_cast BSD_ap_p9929
  have key : r ^ 2 - (a_p 9929 : ℝ) * r + ((9929 : ℕ) : ℝ) =
      (r + 146/2) ^ 2 + 18400/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (146 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9931 : BSD_FrobeniusDegreeNonneg_OPEN 9931 := fun r => by
  have hap : (a_p 9931 : ℝ) = -83 := by exact_mod_cast BSD_ap_p9931
  have key : r ^ 2 - (a_p 9931 : ℝ) * r + ((9931 : ℕ) : ℝ) =
      (r + 83/2) ^ 2 + 32835/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (83 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9941 : BSD_FrobeniusDegreeNonneg_OPEN 9941 := fun r => by
  have hap : (a_p 9941 : ℝ) = 72 := by exact_mod_cast BSD_ap_p9941
  have key : r ^ 2 - (a_p 9941 : ℝ) * r + ((9941 : ℕ) : ℝ) =
      (r - 72/2) ^ 2 + 34580/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (72 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9949 : BSD_FrobeniusDegreeNonneg_OPEN 9949 := fun r => by
  have hap : (a_p 9949 : ℝ) = 102 := by exact_mod_cast BSD_ap_p9949
  have key : r ^ 2 - (a_p 9949 : ℝ) * r + ((9949 : ℕ) : ℝ) =
      (r - 102/2) ^ 2 + 29392/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (102 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9967 : BSD_FrobeniusDegreeNonneg_OPEN 9967 := fun r => by
  have hap : (a_p 9967 : ℝ) = 103 := by exact_mod_cast BSD_ap_p9967
  have key : r ^ 2 - (a_p 9967 : ℝ) * r + ((9967 : ℕ) : ℝ) =
      (r - 103/2) ^ 2 + 29259/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (103 : ℝ)/2)]

theorem BSD_DegreeNonneg_p9973 : BSD_FrobeniusDegreeNonneg_OPEN 9973 := fun r => by
  have hap : (a_p 9973 : ℝ) = -48 := by exact_mod_cast BSD_ap_p9973
  have key : r ^ 2 - (a_p 9973 : ℝ) * r + ((9973 : ℕ) : ℝ) =
      (r + 48/2) ^ 2 + 37588/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (48 : ℝ)/2)]

-- §4 Hasse OPEN via V.5 bridge
theorem BSD_Hasse_OPEN_p251 : BSD_Hasse_OPEN 251 :=
theorem BSD_Hasse_OPEN_p257 : BSD_Hasse_OPEN 257 :=
theorem BSD_Hasse_OPEN_p263 : BSD_Hasse_OPEN 263 :=
theorem BSD_Hasse_OPEN_p269 : BSD_Hasse_OPEN 269 :=
theorem BSD_Hasse_OPEN_p271 : BSD_Hasse_OPEN 271 :=
theorem BSD_Hasse_OPEN_p277 : BSD_Hasse_OPEN 277 :=
theorem BSD_Hasse_OPEN_p281 : BSD_Hasse_OPEN 281 :=
theorem BSD_Hasse_OPEN_p283 : BSD_Hasse_OPEN 283 :=
theorem BSD_Hasse_OPEN_p293 : BSD_Hasse_OPEN 293 :=
theorem BSD_Hasse_OPEN_p307 : BSD_Hasse_OPEN 307 :=
theorem BSD_Hasse_OPEN_p311 : BSD_Hasse_OPEN 311 :=
theorem BSD_Hasse_OPEN_p313 : BSD_Hasse_OPEN 313 :=
theorem BSD_Hasse_OPEN_p317 : BSD_Hasse_OPEN 317 :=
theorem BSD_Hasse_OPEN_p331 : BSD_Hasse_OPEN 331 :=
theorem BSD_Hasse_OPEN_p337 : BSD_Hasse_OPEN 337 :=
theorem BSD_Hasse_OPEN_p347 : BSD_Hasse_OPEN 347 :=
theorem BSD_Hasse_OPEN_p349 : BSD_Hasse_OPEN 349 :=
theorem BSD_Hasse_OPEN_p353 : BSD_Hasse_OPEN 353 :=
theorem BSD_Hasse_OPEN_p359 : BSD_Hasse_OPEN 359 :=
theorem BSD_Hasse_OPEN_p367 : BSD_Hasse_OPEN 367 :=
theorem BSD_Hasse_OPEN_p373 : BSD_Hasse_OPEN 373 :=
theorem BSD_Hasse_OPEN_p379 : BSD_Hasse_OPEN 379 :=
theorem BSD_Hasse_OPEN_p383 : BSD_Hasse_OPEN 383 :=
theorem BSD_Hasse_OPEN_p389 : BSD_Hasse_OPEN 389 :=
theorem BSD_Hasse_OPEN_p397 : BSD_Hasse_OPEN 397 :=
theorem BSD_Hasse_OPEN_p401 : BSD_Hasse_OPEN 401 :=
theorem BSD_Hasse_OPEN_p409 : BSD_Hasse_OPEN 409 :=
theorem BSD_Hasse_OPEN_p419 : BSD_Hasse_OPEN 419 :=
theorem BSD_Hasse_OPEN_p421 : BSD_Hasse_OPEN 421 :=
theorem BSD_Hasse_OPEN_p431 : BSD_Hasse_OPEN 431 :=
theorem BSD_Hasse_OPEN_p433 : BSD_Hasse_OPEN 433 :=
theorem BSD_Hasse_OPEN_p439 : BSD_Hasse_OPEN 439 :=
theorem BSD_Hasse_OPEN_p443 : BSD_Hasse_OPEN 443 :=
theorem BSD_Hasse_OPEN_p449 : BSD_Hasse_OPEN 449 :=
theorem BSD_Hasse_OPEN_p457 : BSD_Hasse_OPEN 457 :=
theorem BSD_Hasse_OPEN_p461 : BSD_Hasse_OPEN 461 :=
theorem BSD_Hasse_OPEN_p463 : BSD_Hasse_OPEN 463 :=
theorem BSD_Hasse_OPEN_p467 : BSD_Hasse_OPEN 467 :=
theorem BSD_Hasse_OPEN_p479 : BSD_Hasse_OPEN 479 :=
theorem BSD_Hasse_OPEN_p487 : BSD_Hasse_OPEN 487 :=
theorem BSD_Hasse_OPEN_p491 : BSD_Hasse_OPEN 491 :=
theorem BSD_Hasse_OPEN_p499 : BSD_Hasse_OPEN 499 :=
theorem BSD_Hasse_OPEN_p503 : BSD_Hasse_OPEN 503 :=
theorem BSD_Hasse_OPEN_p509 : BSD_Hasse_OPEN 509 :=
theorem BSD_Hasse_OPEN_p521 : BSD_Hasse_OPEN 521 :=
theorem BSD_Hasse_OPEN_p523 : BSD_Hasse_OPEN 523 :=
theorem BSD_Hasse_OPEN_p541 : BSD_Hasse_OPEN 541 :=
theorem BSD_Hasse_OPEN_p547 : BSD_Hasse_OPEN 547 :=
theorem BSD_Hasse_OPEN_p557 : BSD_Hasse_OPEN 557 :=
theorem BSD_Hasse_OPEN_p563 : BSD_Hasse_OPEN 563 :=
theorem BSD_Hasse_OPEN_p569 : BSD_Hasse_OPEN 569 :=
theorem BSD_Hasse_OPEN_p571 : BSD_Hasse_OPEN 571 :=
theorem BSD_Hasse_OPEN_p577 : BSD_Hasse_OPEN 577 :=
theorem BSD_Hasse_OPEN_p587 : BSD_Hasse_OPEN 587 :=
theorem BSD_Hasse_OPEN_p593 : BSD_Hasse_OPEN 593 :=
theorem BSD_Hasse_OPEN_p599 : BSD_Hasse_OPEN 599 :=
theorem BSD_Hasse_OPEN_p601 : BSD_Hasse_OPEN 601 :=
theorem BSD_Hasse_OPEN_p607 : BSD_Hasse_OPEN 607 :=
theorem BSD_Hasse_OPEN_p613 : BSD_Hasse_OPEN 613 :=
theorem BSD_Hasse_OPEN_p617 : BSD_Hasse_OPEN 617 :=
theorem BSD_Hasse_OPEN_p619 : BSD_Hasse_OPEN 619 :=
theorem BSD_Hasse_OPEN_p631 : BSD_Hasse_OPEN 631 :=
theorem BSD_Hasse_OPEN_p641 : BSD_Hasse_OPEN 641 :=
theorem BSD_Hasse_OPEN_p643 : BSD_Hasse_OPEN 643 :=
theorem BSD_Hasse_OPEN_p647 : BSD_Hasse_OPEN 647 :=
theorem BSD_Hasse_OPEN_p653 : BSD_Hasse_OPEN 653 :=
theorem BSD_Hasse_OPEN_p659 : BSD_Hasse_OPEN 659 :=
theorem BSD_Hasse_OPEN_p661 : BSD_Hasse_OPEN 661 :=
theorem BSD_Hasse_OPEN_p673 : BSD_Hasse_OPEN 673 :=
theorem BSD_Hasse_OPEN_p677 : BSD_Hasse_OPEN 677 :=
theorem BSD_Hasse_OPEN_p683 : BSD_Hasse_OPEN 683 :=
theorem BSD_Hasse_OPEN_p691 : BSD_Hasse_OPEN 691 :=
theorem BSD_Hasse_OPEN_p701 : BSD_Hasse_OPEN 701 :=
theorem BSD_Hasse_OPEN_p709 : BSD_Hasse_OPEN 709 :=
theorem BSD_Hasse_OPEN_p719 : BSD_Hasse_OPEN 719 :=
theorem BSD_Hasse_OPEN_p727 : BSD_Hasse_OPEN 727 :=
theorem BSD_Hasse_OPEN_p733 : BSD_Hasse_OPEN 733 :=
theorem BSD_Hasse_OPEN_p739 : BSD_Hasse_OPEN 739 :=
theorem BSD_Hasse_OPEN_p743 : BSD_Hasse_OPEN 743 :=
theorem BSD_Hasse_OPEN_p751 : BSD_Hasse_OPEN 751 :=
theorem BSD_Hasse_OPEN_p757 : BSD_Hasse_OPEN 757 :=
theorem BSD_Hasse_OPEN_p761 : BSD_Hasse_OPEN 761 :=
theorem BSD_Hasse_OPEN_p769 : BSD_Hasse_OPEN 769 :=
theorem BSD_Hasse_OPEN_p773 : BSD_Hasse_OPEN 773 :=
theorem BSD_Hasse_OPEN_p787 : BSD_Hasse_OPEN 787 :=
theorem BSD_Hasse_OPEN_p797 : BSD_Hasse_OPEN 797 :=
theorem BSD_Hasse_OPEN_p809 : BSD_Hasse_OPEN 809 :=
theorem BSD_Hasse_OPEN_p811 : BSD_Hasse_OPEN 811 :=
theorem BSD_Hasse_OPEN_p821 : BSD_Hasse_OPEN 821 :=
theorem BSD_Hasse_OPEN_p823 : BSD_Hasse_OPEN 823 :=
theorem BSD_Hasse_OPEN_p827 : BSD_Hasse_OPEN 827 :=
theorem BSD_Hasse_OPEN_p829 : BSD_Hasse_OPEN 829 :=
theorem BSD_Hasse_OPEN_p839 : BSD_Hasse_OPEN 839 :=
theorem BSD_Hasse_OPEN_p853 : BSD_Hasse_OPEN 853 :=
theorem BSD_Hasse_OPEN_p857 : BSD_Hasse_OPEN 857 :=
theorem BSD_Hasse_OPEN_p859 : BSD_Hasse_OPEN 859 :=
theorem BSD_Hasse_OPEN_p863 : BSD_Hasse_OPEN 863 :=
theorem BSD_Hasse_OPEN_p877 : BSD_Hasse_OPEN 877 :=
theorem BSD_Hasse_OPEN_p881 : BSD_Hasse_OPEN 881 :=
theorem BSD_Hasse_OPEN_p883 : BSD_Hasse_OPEN 883 :=
theorem BSD_Hasse_OPEN_p887 : BSD_Hasse_OPEN 887 :=
theorem BSD_Hasse_OPEN_p907 : BSD_Hasse_OPEN 907 :=
theorem BSD_Hasse_OPEN_p911 : BSD_Hasse_OPEN 911 :=
theorem BSD_Hasse_OPEN_p919 : BSD_Hasse_OPEN 919 :=
theorem BSD_Hasse_OPEN_p929 : BSD_Hasse_OPEN 929 :=
theorem BSD_Hasse_OPEN_p937 : BSD_Hasse_OPEN 937 :=
theorem BSD_Hasse_OPEN_p941 : BSD_Hasse_OPEN 941 :=
theorem BSD_Hasse_OPEN_p947 : BSD_Hasse_OPEN 947 :=
theorem BSD_Hasse_OPEN_p953 : BSD_Hasse_OPEN 953 :=
theorem BSD_Hasse_OPEN_p967 : BSD_Hasse_OPEN 967 :=
theorem BSD_Hasse_OPEN_p971 : BSD_Hasse_OPEN 971 :=
theorem BSD_Hasse_OPEN_p977 : BSD_Hasse_OPEN 977 :=
theorem BSD_Hasse_OPEN_p983 : BSD_Hasse_OPEN 983 :=
theorem BSD_Hasse_OPEN_p991 : BSD_Hasse_OPEN 991 :=
theorem BSD_Hasse_OPEN_p997 : BSD_Hasse_OPEN 997 :=
theorem BSD_Hasse_OPEN_p1009 : BSD_Hasse_OPEN 1009 :=
theorem BSD_Hasse_OPEN_p1013 : BSD_Hasse_OPEN 1013 :=
theorem BSD_Hasse_OPEN_p1019 : BSD_Hasse_OPEN 1019 :=
theorem BSD_Hasse_OPEN_p1021 : BSD_Hasse_OPEN 1021 :=
theorem BSD_Hasse_OPEN_p1031 : BSD_Hasse_OPEN 1031 :=
theorem BSD_Hasse_OPEN_p1033 : BSD_Hasse_OPEN 1033 :=
theorem BSD_Hasse_OPEN_p1039 : BSD_Hasse_OPEN 1039 :=
theorem BSD_Hasse_OPEN_p1049 : BSD_Hasse_OPEN 1049 :=
theorem BSD_Hasse_OPEN_p1051 : BSD_Hasse_OPEN 1051 :=
theorem BSD_Hasse_OPEN_p1061 : BSD_Hasse_OPEN 1061 :=
theorem BSD_Hasse_OPEN_p1063 : BSD_Hasse_OPEN 1063 :=
theorem BSD_Hasse_OPEN_p1069 : BSD_Hasse_OPEN 1069 :=
theorem BSD_Hasse_OPEN_p1087 : BSD_Hasse_OPEN 1087 :=
theorem BSD_Hasse_OPEN_p1091 : BSD_Hasse_OPEN 1091 :=
theorem BSD_Hasse_OPEN_p1093 : BSD_Hasse_OPEN 1093 :=
theorem BSD_Hasse_OPEN_p1097 : BSD_Hasse_OPEN 1097 :=
theorem BSD_Hasse_OPEN_p1103 : BSD_Hasse_OPEN 1103 :=
theorem BSD_Hasse_OPEN_p1109 : BSD_Hasse_OPEN 1109 :=
theorem BSD_Hasse_OPEN_p1117 : BSD_Hasse_OPEN 1117 :=
theorem BSD_Hasse_OPEN_p1123 : BSD_Hasse_OPEN 1123 :=
theorem BSD_Hasse_OPEN_p1129 : BSD_Hasse_OPEN 1129 :=
theorem BSD_Hasse_OPEN_p1151 : BSD_Hasse_OPEN 1151 :=
theorem BSD_Hasse_OPEN_p1153 : BSD_Hasse_OPEN 1153 :=
theorem BSD_Hasse_OPEN_p1163 : BSD_Hasse_OPEN 1163 :=
theorem BSD_Hasse_OPEN_p1171 : BSD_Hasse_OPEN 1171 :=
theorem BSD_Hasse_OPEN_p1181 : BSD_Hasse_OPEN 1181 :=
theorem BSD_Hasse_OPEN_p1187 : BSD_Hasse_OPEN 1187 :=
theorem BSD_Hasse_OPEN_p1193 : BSD_Hasse_OPEN 1193 :=
theorem BSD_Hasse_OPEN_p1201 : BSD_Hasse_OPEN 1201 :=
theorem BSD_Hasse_OPEN_p1213 : BSD_Hasse_OPEN 1213 :=
theorem BSD_Hasse_OPEN_p1217 : BSD_Hasse_OPEN 1217 :=
theorem BSD_Hasse_OPEN_p1223 : BSD_Hasse_OPEN 1223 :=
theorem BSD_Hasse_OPEN_p1229 : BSD_Hasse_OPEN 1229 :=
theorem BSD_Hasse_OPEN_p1231 : BSD_Hasse_OPEN 1231 :=
theorem BSD_Hasse_OPEN_p1237 : BSD_Hasse_OPEN 1237 :=
theorem BSD_Hasse_OPEN_p1249 : BSD_Hasse_OPEN 1249 :=
theorem BSD_Hasse_OPEN_p1259 : BSD_Hasse_OPEN 1259 :=
theorem BSD_Hasse_OPEN_p1277 : BSD_Hasse_OPEN 1277 :=
theorem BSD_Hasse_OPEN_p1279 : BSD_Hasse_OPEN 1279 :=
theorem BSD_Hasse_OPEN_p1283 : BSD_Hasse_OPEN 1283 :=
theorem BSD_Hasse_OPEN_p1289 : BSD_Hasse_OPEN 1289 :=
theorem BSD_Hasse_OPEN_p1291 : BSD_Hasse_OPEN 1291 :=
theorem BSD_Hasse_OPEN_p1297 : BSD_Hasse_OPEN 1297 :=
theorem BSD_Hasse_OPEN_p1301 : BSD_Hasse_OPEN 1301 :=
theorem BSD_Hasse_OPEN_p1303 : BSD_Hasse_OPEN 1303 :=
theorem BSD_Hasse_OPEN_p1307 : BSD_Hasse_OPEN 1307 :=
theorem BSD_Hasse_OPEN_p1319 : BSD_Hasse_OPEN 1319 :=
theorem BSD_Hasse_OPEN_p1321 : BSD_Hasse_OPEN 1321 :=
theorem BSD_Hasse_OPEN_p1327 : BSD_Hasse_OPEN 1327 :=
theorem BSD_Hasse_OPEN_p1361 : BSD_Hasse_OPEN 1361 :=
theorem BSD_Hasse_OPEN_p1367 : BSD_Hasse_OPEN 1367 :=
theorem BSD_Hasse_OPEN_p1373 : BSD_Hasse_OPEN 1373 :=
theorem BSD_Hasse_OPEN_p1381 : BSD_Hasse_OPEN 1381 :=
theorem BSD_Hasse_OPEN_p1399 : BSD_Hasse_OPEN 1399 :=
theorem BSD_Hasse_OPEN_p1409 : BSD_Hasse_OPEN 1409 :=
theorem BSD_Hasse_OPEN_p1423 : BSD_Hasse_OPEN 1423 :=
theorem BSD_Hasse_OPEN_p1427 : BSD_Hasse_OPEN 1427 :=
theorem BSD_Hasse_OPEN_p1429 : BSD_Hasse_OPEN 1429 :=
theorem BSD_Hasse_OPEN_p1433 : BSD_Hasse_OPEN 1433 :=
theorem BSD_Hasse_OPEN_p1439 : BSD_Hasse_OPEN 1439 :=
theorem BSD_Hasse_OPEN_p1447 : BSD_Hasse_OPEN 1447 :=
theorem BSD_Hasse_OPEN_p1451 : BSD_Hasse_OPEN 1451 :=
theorem BSD_Hasse_OPEN_p1453 : BSD_Hasse_OPEN 1453 :=
theorem BSD_Hasse_OPEN_p1459 : BSD_Hasse_OPEN 1459 :=
theorem BSD_Hasse_OPEN_p1471 : BSD_Hasse_OPEN 1471 :=
theorem BSD_Hasse_OPEN_p1481 : BSD_Hasse_OPEN 1481 :=
theorem BSD_Hasse_OPEN_p1483 : BSD_Hasse_OPEN 1483 :=
theorem BSD_Hasse_OPEN_p1487 : BSD_Hasse_OPEN 1487 :=
theorem BSD_Hasse_OPEN_p1489 : BSD_Hasse_OPEN 1489 :=
theorem BSD_Hasse_OPEN_p1493 : BSD_Hasse_OPEN 1493 :=
theorem BSD_Hasse_OPEN_p1499 : BSD_Hasse_OPEN 1499 :=
theorem BSD_Hasse_OPEN_p1511 : BSD_Hasse_OPEN 1511 :=
theorem BSD_Hasse_OPEN_p1523 : BSD_Hasse_OPEN 1523 :=
theorem BSD_Hasse_OPEN_p1531 : BSD_Hasse_OPEN 1531 :=
theorem BSD_Hasse_OPEN_p1543 : BSD_Hasse_OPEN 1543 :=
theorem BSD_Hasse_OPEN_p1549 : BSD_Hasse_OPEN 1549 :=
theorem BSD_Hasse_OPEN_p1553 : BSD_Hasse_OPEN 1553 :=
theorem BSD_Hasse_OPEN_p1559 : BSD_Hasse_OPEN 1559 :=
theorem BSD_Hasse_OPEN_p1567 : BSD_Hasse_OPEN 1567 :=
theorem BSD_Hasse_OPEN_p1571 : BSD_Hasse_OPEN 1571 :=
theorem BSD_Hasse_OPEN_p1579 : BSD_Hasse_OPEN 1579 :=
theorem BSD_Hasse_OPEN_p1583 : BSD_Hasse_OPEN 1583 :=
theorem BSD_Hasse_OPEN_p1597 : BSD_Hasse_OPEN 1597 :=
theorem BSD_Hasse_OPEN_p1601 : BSD_Hasse_OPEN 1601 :=
theorem BSD_Hasse_OPEN_p1607 : BSD_Hasse_OPEN 1607 :=
theorem BSD_Hasse_OPEN_p1609 : BSD_Hasse_OPEN 1609 :=
theorem BSD_Hasse_OPEN_p1613 : BSD_Hasse_OPEN 1613 :=
theorem BSD_Hasse_OPEN_p1619 : BSD_Hasse_OPEN 1619 :=
theorem BSD_Hasse_OPEN_p1621 : BSD_Hasse_OPEN 1621 :=
theorem BSD_Hasse_OPEN_p1627 : BSD_Hasse_OPEN 1627 :=
theorem BSD_Hasse_OPEN_p1637 : BSD_Hasse_OPEN 1637 :=
theorem BSD_Hasse_OPEN_p1657 : BSD_Hasse_OPEN 1657 :=
theorem BSD_Hasse_OPEN_p1663 : BSD_Hasse_OPEN 1663 :=
theorem BSD_Hasse_OPEN_p1667 : BSD_Hasse_OPEN 1667 :=
theorem BSD_Hasse_OPEN_p1669 : BSD_Hasse_OPEN 1669 :=
theorem BSD_Hasse_OPEN_p1693 : BSD_Hasse_OPEN 1693 :=
theorem BSD_Hasse_OPEN_p1697 : BSD_Hasse_OPEN 1697 :=
theorem BSD_Hasse_OPEN_p1699 : BSD_Hasse_OPEN 1699 :=
theorem BSD_Hasse_OPEN_p1709 : BSD_Hasse_OPEN 1709 :=
theorem BSD_Hasse_OPEN_p1721 : BSD_Hasse_OPEN 1721 :=
theorem BSD_Hasse_OPEN_p1723 : BSD_Hasse_OPEN 1723 :=
theorem BSD_Hasse_OPEN_p1733 : BSD_Hasse_OPEN 1733 :=
theorem BSD_Hasse_OPEN_p1741 : BSD_Hasse_OPEN 1741 :=
theorem BSD_Hasse_OPEN_p1747 : BSD_Hasse_OPEN 1747 :=
theorem BSD_Hasse_OPEN_p1753 : BSD_Hasse_OPEN 1753 :=
theorem BSD_Hasse_OPEN_p1759 : BSD_Hasse_OPEN 1759 :=
theorem BSD_Hasse_OPEN_p1777 : BSD_Hasse_OPEN 1777 :=
theorem BSD_Hasse_OPEN_p1783 : BSD_Hasse_OPEN 1783 :=
theorem BSD_Hasse_OPEN_p1787 : BSD_Hasse_OPEN 1787 :=
theorem BSD_Hasse_OPEN_p1789 : BSD_Hasse_OPEN 1789 :=
theorem BSD_Hasse_OPEN_p1801 : BSD_Hasse_OPEN 1801 :=
theorem BSD_Hasse_OPEN_p1811 : BSD_Hasse_OPEN 1811 :=
theorem BSD_Hasse_OPEN_p1823 : BSD_Hasse_OPEN 1823 :=
theorem BSD_Hasse_OPEN_p1831 : BSD_Hasse_OPEN 1831 :=
theorem BSD_Hasse_OPEN_p1847 : BSD_Hasse_OPEN 1847 :=
theorem BSD_Hasse_OPEN_p1861 : BSD_Hasse_OPEN 1861 :=
theorem BSD_Hasse_OPEN_p1867 : BSD_Hasse_OPEN 1867 :=
theorem BSD_Hasse_OPEN_p1871 : BSD_Hasse_OPEN 1871 :=
theorem BSD_Hasse_OPEN_p1873 : BSD_Hasse_OPEN 1873 :=
theorem BSD_Hasse_OPEN_p1877 : BSD_Hasse_OPEN 1877 :=
theorem BSD_Hasse_OPEN_p1879 : BSD_Hasse_OPEN 1879 :=
theorem BSD_Hasse_OPEN_p1889 : BSD_Hasse_OPEN 1889 :=
theorem BSD_Hasse_OPEN_p1901 : BSD_Hasse_OPEN 1901 :=
theorem BSD_Hasse_OPEN_p1907 : BSD_Hasse_OPEN 1907 :=
theorem BSD_Hasse_OPEN_p1913 : BSD_Hasse_OPEN 1913 :=
theorem BSD_Hasse_OPEN_p1931 : BSD_Hasse_OPEN 1931 :=
theorem BSD_Hasse_OPEN_p1933 : BSD_Hasse_OPEN 1933 :=
theorem BSD_Hasse_OPEN_p1949 : BSD_Hasse_OPEN 1949 :=
theorem BSD_Hasse_OPEN_p1951 : BSD_Hasse_OPEN 1951 :=
theorem BSD_Hasse_OPEN_p1973 : BSD_Hasse_OPEN 1973 :=
theorem BSD_Hasse_OPEN_p1979 : BSD_Hasse_OPEN 1979 :=
theorem BSD_Hasse_OPEN_p1987 : BSD_Hasse_OPEN 1987 :=
theorem BSD_Hasse_OPEN_p1993 : BSD_Hasse_OPEN 1993 :=
theorem BSD_Hasse_OPEN_p1997 : BSD_Hasse_OPEN 1997 :=
theorem BSD_Hasse_OPEN_p1999 : BSD_Hasse_OPEN 1999 :=
theorem BSD_Hasse_OPEN_p2003 : BSD_Hasse_OPEN 2003 :=
theorem BSD_Hasse_OPEN_p2011 : BSD_Hasse_OPEN 2011 :=
theorem BSD_Hasse_OPEN_p2017 : BSD_Hasse_OPEN 2017 :=
theorem BSD_Hasse_OPEN_p2027 : BSD_Hasse_OPEN 2027 :=
theorem BSD_Hasse_OPEN_p2029 : BSD_Hasse_OPEN 2029 :=
theorem BSD_Hasse_OPEN_p2039 : BSD_Hasse_OPEN 2039 :=
theorem BSD_Hasse_OPEN_p2053 : BSD_Hasse_OPEN 2053 :=
theorem BSD_Hasse_OPEN_p2063 : BSD_Hasse_OPEN 2063 :=
theorem BSD_Hasse_OPEN_p2069 : BSD_Hasse_OPEN 2069 :=
theorem BSD_Hasse_OPEN_p2081 : BSD_Hasse_OPEN 2081 :=
theorem BSD_Hasse_OPEN_p2083 : BSD_Hasse_OPEN 2083 :=
theorem BSD_Hasse_OPEN_p2087 : BSD_Hasse_OPEN 2087 :=
theorem BSD_Hasse_OPEN_p2089 : BSD_Hasse_OPEN 2089 :=
theorem BSD_Hasse_OPEN_p2099 : BSD_Hasse_OPEN 2099 :=
theorem BSD_Hasse_OPEN_p2111 : BSD_Hasse_OPEN 2111 :=
theorem BSD_Hasse_OPEN_p2113 : BSD_Hasse_OPEN 2113 :=
theorem BSD_Hasse_OPEN_p2129 : BSD_Hasse_OPEN 2129 :=
theorem BSD_Hasse_OPEN_p2131 : BSD_Hasse_OPEN 2131 :=
theorem BSD_Hasse_OPEN_p2137 : BSD_Hasse_OPEN 2137 :=
theorem BSD_Hasse_OPEN_p2141 : BSD_Hasse_OPEN 2141 :=
theorem BSD_Hasse_OPEN_p2143 : BSD_Hasse_OPEN 2143 :=
theorem BSD_Hasse_OPEN_p2153 : BSD_Hasse_OPEN 2153 :=
theorem BSD_Hasse_OPEN_p2161 : BSD_Hasse_OPEN 2161 :=
theorem BSD_Hasse_OPEN_p2179 : BSD_Hasse_OPEN 2179 :=
theorem BSD_Hasse_OPEN_p2203 : BSD_Hasse_OPEN 2203 :=
theorem BSD_Hasse_OPEN_p2207 : BSD_Hasse_OPEN 2207 :=
theorem BSD_Hasse_OPEN_p2213 : BSD_Hasse_OPEN 2213 :=
theorem BSD_Hasse_OPEN_p2221 : BSD_Hasse_OPEN 2221 :=
theorem BSD_Hasse_OPEN_p2237 : BSD_Hasse_OPEN 2237 :=
theorem BSD_Hasse_OPEN_p2239 : BSD_Hasse_OPEN 2239 :=
theorem BSD_Hasse_OPEN_p2243 : BSD_Hasse_OPEN 2243 :=
theorem BSD_Hasse_OPEN_p2251 : BSD_Hasse_OPEN 2251 :=
theorem BSD_Hasse_OPEN_p2267 : BSD_Hasse_OPEN 2267 :=
theorem BSD_Hasse_OPEN_p2269 : BSD_Hasse_OPEN 2269 :=
theorem BSD_Hasse_OPEN_p2273 : BSD_Hasse_OPEN 2273 :=
theorem BSD_Hasse_OPEN_p2281 : BSD_Hasse_OPEN 2281 :=
theorem BSD_Hasse_OPEN_p2287 : BSD_Hasse_OPEN 2287 :=
theorem BSD_Hasse_OPEN_p2293 : BSD_Hasse_OPEN 2293 :=
theorem BSD_Hasse_OPEN_p2297 : BSD_Hasse_OPEN 2297 :=
theorem BSD_Hasse_OPEN_p2309 : BSD_Hasse_OPEN 2309 :=
theorem BSD_Hasse_OPEN_p2311 : BSD_Hasse_OPEN 2311 :=
theorem BSD_Hasse_OPEN_p2333 : BSD_Hasse_OPEN 2333 :=
theorem BSD_Hasse_OPEN_p2339 : BSD_Hasse_OPEN 2339 :=
theorem BSD_Hasse_OPEN_p2341 : BSD_Hasse_OPEN 2341 :=
theorem BSD_Hasse_OPEN_p2347 : BSD_Hasse_OPEN 2347 :=
theorem BSD_Hasse_OPEN_p2351 : BSD_Hasse_OPEN 2351 :=
theorem BSD_Hasse_OPEN_p2357 : BSD_Hasse_OPEN 2357 :=
theorem BSD_Hasse_OPEN_p2371 : BSD_Hasse_OPEN 2371 :=
theorem BSD_Hasse_OPEN_p2377 : BSD_Hasse_OPEN 2377 :=
theorem BSD_Hasse_OPEN_p2381 : BSD_Hasse_OPEN 2381 :=
theorem BSD_Hasse_OPEN_p2383 : BSD_Hasse_OPEN 2383 :=
theorem BSD_Hasse_OPEN_p2389 : BSD_Hasse_OPEN 2389 :=
theorem BSD_Hasse_OPEN_p2393 : BSD_Hasse_OPEN 2393 :=
theorem BSD_Hasse_OPEN_p2399 : BSD_Hasse_OPEN 2399 :=
theorem BSD_Hasse_OPEN_p2411 : BSD_Hasse_OPEN 2411 :=
theorem BSD_Hasse_OPEN_p2417 : BSD_Hasse_OPEN 2417 :=
theorem BSD_Hasse_OPEN_p2423 : BSD_Hasse_OPEN 2423 :=
theorem BSD_Hasse_OPEN_p2437 : BSD_Hasse_OPEN 2437 :=
theorem BSD_Hasse_OPEN_p2441 : BSD_Hasse_OPEN 2441 :=
theorem BSD_Hasse_OPEN_p2447 : BSD_Hasse_OPEN 2447 :=
theorem BSD_Hasse_OPEN_p2459 : BSD_Hasse_OPEN 2459 :=
theorem BSD_Hasse_OPEN_p2467 : BSD_Hasse_OPEN 2467 :=
theorem BSD_Hasse_OPEN_p2473 : BSD_Hasse_OPEN 2473 :=
theorem BSD_Hasse_OPEN_p2477 : BSD_Hasse_OPEN 2477 :=
theorem BSD_Hasse_OPEN_p2503 : BSD_Hasse_OPEN 2503 :=
theorem BSD_Hasse_OPEN_p2521 : BSD_Hasse_OPEN 2521 :=
theorem BSD_Hasse_OPEN_p2531 : BSD_Hasse_OPEN 2531 :=
theorem BSD_Hasse_OPEN_p2539 : BSD_Hasse_OPEN 2539 :=
theorem BSD_Hasse_OPEN_p2543 : BSD_Hasse_OPEN 2543 :=
theorem BSD_Hasse_OPEN_p2549 : BSD_Hasse_OPEN 2549 :=
theorem BSD_Hasse_OPEN_p2551 : BSD_Hasse_OPEN 2551 :=
theorem BSD_Hasse_OPEN_p2557 : BSD_Hasse_OPEN 2557 :=
theorem BSD_Hasse_OPEN_p2579 : BSD_Hasse_OPEN 2579 :=
theorem BSD_Hasse_OPEN_p2591 : BSD_Hasse_OPEN 2591 :=
theorem BSD_Hasse_OPEN_p2593 : BSD_Hasse_OPEN 2593 :=
theorem BSD_Hasse_OPEN_p2609 : BSD_Hasse_OPEN 2609 :=
theorem BSD_Hasse_OPEN_p2617 : BSD_Hasse_OPEN 2617 :=
theorem BSD_Hasse_OPEN_p2621 : BSD_Hasse_OPEN 2621 :=
theorem BSD_Hasse_OPEN_p2633 : BSD_Hasse_OPEN 2633 :=
theorem BSD_Hasse_OPEN_p2647 : BSD_Hasse_OPEN 2647 :=
theorem BSD_Hasse_OPEN_p2657 : BSD_Hasse_OPEN 2657 :=
theorem BSD_Hasse_OPEN_p2659 : BSD_Hasse_OPEN 2659 :=
theorem BSD_Hasse_OPEN_p2663 : BSD_Hasse_OPEN 2663 :=
theorem BSD_Hasse_OPEN_p2671 : BSD_Hasse_OPEN 2671 :=
theorem BSD_Hasse_OPEN_p2677 : BSD_Hasse_OPEN 2677 :=
theorem BSD_Hasse_OPEN_p2683 : BSD_Hasse_OPEN 2683 :=
theorem BSD_Hasse_OPEN_p2687 : BSD_Hasse_OPEN 2687 :=
theorem BSD_Hasse_OPEN_p2689 : BSD_Hasse_OPEN 2689 :=
theorem BSD_Hasse_OPEN_p2693 : BSD_Hasse_OPEN 2693 :=
theorem BSD_Hasse_OPEN_p2699 : BSD_Hasse_OPEN 2699 :=
theorem BSD_Hasse_OPEN_p2707 : BSD_Hasse_OPEN 2707 :=
theorem BSD_Hasse_OPEN_p2711 : BSD_Hasse_OPEN 2711 :=
theorem BSD_Hasse_OPEN_p2713 : BSD_Hasse_OPEN 2713 :=
theorem BSD_Hasse_OPEN_p2719 : BSD_Hasse_OPEN 2719 :=
theorem BSD_Hasse_OPEN_p2729 : BSD_Hasse_OPEN 2729 :=
theorem BSD_Hasse_OPEN_p2731 : BSD_Hasse_OPEN 2731 :=
theorem BSD_Hasse_OPEN_p2741 : BSD_Hasse_OPEN 2741 :=
theorem BSD_Hasse_OPEN_p2749 : BSD_Hasse_OPEN 2749 :=
theorem BSD_Hasse_OPEN_p2753 : BSD_Hasse_OPEN 2753 :=
theorem BSD_Hasse_OPEN_p2767 : BSD_Hasse_OPEN 2767 :=
theorem BSD_Hasse_OPEN_p2777 : BSD_Hasse_OPEN 2777 :=
theorem BSD_Hasse_OPEN_p2789 : BSD_Hasse_OPEN 2789 :=
theorem BSD_Hasse_OPEN_p2791 : BSD_Hasse_OPEN 2791 :=
theorem BSD_Hasse_OPEN_p2797 : BSD_Hasse_OPEN 2797 :=
theorem BSD_Hasse_OPEN_p2801 : BSD_Hasse_OPEN 2801 :=
theorem BSD_Hasse_OPEN_p2803 : BSD_Hasse_OPEN 2803 :=
theorem BSD_Hasse_OPEN_p2819 : BSD_Hasse_OPEN 2819 :=
theorem BSD_Hasse_OPEN_p2833 : BSD_Hasse_OPEN 2833 :=
theorem BSD_Hasse_OPEN_p2837 : BSD_Hasse_OPEN 2837 :=
theorem BSD_Hasse_OPEN_p2843 : BSD_Hasse_OPEN 2843 :=
theorem BSD_Hasse_OPEN_p2851 : BSD_Hasse_OPEN 2851 :=
theorem BSD_Hasse_OPEN_p2857 : BSD_Hasse_OPEN 2857 :=
theorem BSD_Hasse_OPEN_p2861 : BSD_Hasse_OPEN 2861 :=
theorem BSD_Hasse_OPEN_p2879 : BSD_Hasse_OPEN 2879 :=
theorem BSD_Hasse_OPEN_p2887 : BSD_Hasse_OPEN 2887 :=
theorem BSD_Hasse_OPEN_p2897 : BSD_Hasse_OPEN 2897 :=
theorem BSD_Hasse_OPEN_p2903 : BSD_Hasse_OPEN 2903 :=
theorem BSD_Hasse_OPEN_p2909 : BSD_Hasse_OPEN 2909 :=
theorem BSD_Hasse_OPEN_p2917 : BSD_Hasse_OPEN 2917 :=
theorem BSD_Hasse_OPEN_p2927 : BSD_Hasse_OPEN 2927 :=
theorem BSD_Hasse_OPEN_p2939 : BSD_Hasse_OPEN 2939 :=
theorem BSD_Hasse_OPEN_p2953 : BSD_Hasse_OPEN 2953 :=
theorem BSD_Hasse_OPEN_p2957 : BSD_Hasse_OPEN 2957 :=
theorem BSD_Hasse_OPEN_p2963 : BSD_Hasse_OPEN 2963 :=
theorem BSD_Hasse_OPEN_p2969 : BSD_Hasse_OPEN 2969 :=
theorem BSD_Hasse_OPEN_p2971 : BSD_Hasse_OPEN 2971 :=
theorem BSD_Hasse_OPEN_p2999 : BSD_Hasse_OPEN 2999 :=
theorem BSD_Hasse_OPEN_p3001 : BSD_Hasse_OPEN 3001 :=
theorem BSD_Hasse_OPEN_p3011 : BSD_Hasse_OPEN 3011 :=
theorem BSD_Hasse_OPEN_p3019 : BSD_Hasse_OPEN 3019 :=
theorem BSD_Hasse_OPEN_p3023 : BSD_Hasse_OPEN 3023 :=
theorem BSD_Hasse_OPEN_p3037 : BSD_Hasse_OPEN 3037 :=
theorem BSD_Hasse_OPEN_p3041 : BSD_Hasse_OPEN 3041 :=
theorem BSD_Hasse_OPEN_p3049 : BSD_Hasse_OPEN 3049 :=
theorem BSD_Hasse_OPEN_p3061 : BSD_Hasse_OPEN 3061 :=
theorem BSD_Hasse_OPEN_p3067 : BSD_Hasse_OPEN 3067 :=
theorem BSD_Hasse_OPEN_p3079 : BSD_Hasse_OPEN 3079 :=
theorem BSD_Hasse_OPEN_p3083 : BSD_Hasse_OPEN 3083 :=
theorem BSD_Hasse_OPEN_p3089 : BSD_Hasse_OPEN 3089 :=
theorem BSD_Hasse_OPEN_p3109 : BSD_Hasse_OPEN 3109 :=
theorem BSD_Hasse_OPEN_p3119 : BSD_Hasse_OPEN 3119 :=
theorem BSD_Hasse_OPEN_p3121 : BSD_Hasse_OPEN 3121 :=
theorem BSD_Hasse_OPEN_p3137 : BSD_Hasse_OPEN 3137 :=
theorem BSD_Hasse_OPEN_p3163 : BSD_Hasse_OPEN 3163 :=
theorem BSD_Hasse_OPEN_p3167 : BSD_Hasse_OPEN 3167 :=
theorem BSD_Hasse_OPEN_p3169 : BSD_Hasse_OPEN 3169 :=
theorem BSD_Hasse_OPEN_p3181 : BSD_Hasse_OPEN 3181 :=
theorem BSD_Hasse_OPEN_p3187 : BSD_Hasse_OPEN 3187 :=
theorem BSD_Hasse_OPEN_p3191 : BSD_Hasse_OPEN 3191 :=
theorem BSD_Hasse_OPEN_p3203 : BSD_Hasse_OPEN 3203 :=
theorem BSD_Hasse_OPEN_p3209 : BSD_Hasse_OPEN 3209 :=
theorem BSD_Hasse_OPEN_p3217 : BSD_Hasse_OPEN 3217 :=
theorem BSD_Hasse_OPEN_p3221 : BSD_Hasse_OPEN 3221 :=
theorem BSD_Hasse_OPEN_p3229 : BSD_Hasse_OPEN 3229 :=
theorem BSD_Hasse_OPEN_p3251 : BSD_Hasse_OPEN 3251 :=
theorem BSD_Hasse_OPEN_p3253 : BSD_Hasse_OPEN 3253 :=
theorem BSD_Hasse_OPEN_p3257 : BSD_Hasse_OPEN 3257 :=
theorem BSD_Hasse_OPEN_p3259 : BSD_Hasse_OPEN 3259 :=
theorem BSD_Hasse_OPEN_p3271 : BSD_Hasse_OPEN 3271 :=
theorem BSD_Hasse_OPEN_p3299 : BSD_Hasse_OPEN 3299 :=
theorem BSD_Hasse_OPEN_p3301 : BSD_Hasse_OPEN 3301 :=
theorem BSD_Hasse_OPEN_p3307 : BSD_Hasse_OPEN 3307 :=
theorem BSD_Hasse_OPEN_p3313 : BSD_Hasse_OPEN 3313 :=
theorem BSD_Hasse_OPEN_p3319 : BSD_Hasse_OPEN 3319 :=
theorem BSD_Hasse_OPEN_p3323 : BSD_Hasse_OPEN 3323 :=
theorem BSD_Hasse_OPEN_p3329 : BSD_Hasse_OPEN 3329 :=
theorem BSD_Hasse_OPEN_p3331 : BSD_Hasse_OPEN 3331 :=
theorem BSD_Hasse_OPEN_p3343 : BSD_Hasse_OPEN 3343 :=
theorem BSD_Hasse_OPEN_p3347 : BSD_Hasse_OPEN 3347 :=
theorem BSD_Hasse_OPEN_p3359 : BSD_Hasse_OPEN 3359 :=
theorem BSD_Hasse_OPEN_p3361 : BSD_Hasse_OPEN 3361 :=
theorem BSD_Hasse_OPEN_p3371 : BSD_Hasse_OPEN 3371 :=
theorem BSD_Hasse_OPEN_p3373 : BSD_Hasse_OPEN 3373 :=
theorem BSD_Hasse_OPEN_p3389 : BSD_Hasse_OPEN 3389 :=
theorem BSD_Hasse_OPEN_p3391 : BSD_Hasse_OPEN 3391 :=
theorem BSD_Hasse_OPEN_p3407 : BSD_Hasse_OPEN 3407 :=
theorem BSD_Hasse_OPEN_p3413 : BSD_Hasse_OPEN 3413 :=
theorem BSD_Hasse_OPEN_p3433 : BSD_Hasse_OPEN 3433 :=
theorem BSD_Hasse_OPEN_p3449 : BSD_Hasse_OPEN 3449 :=
theorem BSD_Hasse_OPEN_p3457 : BSD_Hasse_OPEN 3457 :=
theorem BSD_Hasse_OPEN_p3461 : BSD_Hasse_OPEN 3461 :=
theorem BSD_Hasse_OPEN_p3463 : BSD_Hasse_OPEN 3463 :=
theorem BSD_Hasse_OPEN_p3467 : BSD_Hasse_OPEN 3467 :=
theorem BSD_Hasse_OPEN_p3469 : BSD_Hasse_OPEN 3469 :=
theorem BSD_Hasse_OPEN_p3491 : BSD_Hasse_OPEN 3491 :=
theorem BSD_Hasse_OPEN_p3499 : BSD_Hasse_OPEN 3499 :=
theorem BSD_Hasse_OPEN_p3511 : BSD_Hasse_OPEN 3511 :=
theorem BSD_Hasse_OPEN_p3517 : BSD_Hasse_OPEN 3517 :=
theorem BSD_Hasse_OPEN_p3527 : BSD_Hasse_OPEN 3527 :=
theorem BSD_Hasse_OPEN_p3529 : BSD_Hasse_OPEN 3529 :=
theorem BSD_Hasse_OPEN_p3533 : BSD_Hasse_OPEN 3533 :=
theorem BSD_Hasse_OPEN_p3539 : BSD_Hasse_OPEN 3539 :=
theorem BSD_Hasse_OPEN_p3541 : BSD_Hasse_OPEN 3541 :=
theorem BSD_Hasse_OPEN_p3547 : BSD_Hasse_OPEN 3547 :=
theorem BSD_Hasse_OPEN_p3557 : BSD_Hasse_OPEN 3557 :=
theorem BSD_Hasse_OPEN_p3559 : BSD_Hasse_OPEN 3559 :=
theorem BSD_Hasse_OPEN_p3571 : BSD_Hasse_OPEN 3571 :=
theorem BSD_Hasse_OPEN_p3581 : BSD_Hasse_OPEN 3581 :=
theorem BSD_Hasse_OPEN_p3583 : BSD_Hasse_OPEN 3583 :=
theorem BSD_Hasse_OPEN_p3593 : BSD_Hasse_OPEN 3593 :=
theorem BSD_Hasse_OPEN_p3607 : BSD_Hasse_OPEN 3607 :=
theorem BSD_Hasse_OPEN_p3613 : BSD_Hasse_OPEN 3613 :=
theorem BSD_Hasse_OPEN_p3617 : BSD_Hasse_OPEN 3617 :=
theorem BSD_Hasse_OPEN_p3623 : BSD_Hasse_OPEN 3623 :=
theorem BSD_Hasse_OPEN_p3631 : BSD_Hasse_OPEN 3631 :=
theorem BSD_Hasse_OPEN_p3637 : BSD_Hasse_OPEN 3637 :=
theorem BSD_Hasse_OPEN_p3643 : BSD_Hasse_OPEN 3643 :=
theorem BSD_Hasse_OPEN_p3659 : BSD_Hasse_OPEN 3659 :=
theorem BSD_Hasse_OPEN_p3671 : BSD_Hasse_OPEN 3671 :=
theorem BSD_Hasse_OPEN_p3673 : BSD_Hasse_OPEN 3673 :=
theorem BSD_Hasse_OPEN_p3677 : BSD_Hasse_OPEN 3677 :=
theorem BSD_Hasse_OPEN_p3691 : BSD_Hasse_OPEN 3691 :=
theorem BSD_Hasse_OPEN_p3697 : BSD_Hasse_OPEN 3697 :=
theorem BSD_Hasse_OPEN_p3701 : BSD_Hasse_OPEN 3701 :=
theorem BSD_Hasse_OPEN_p3709 : BSD_Hasse_OPEN 3709 :=
theorem BSD_Hasse_OPEN_p3719 : BSD_Hasse_OPEN 3719 :=
theorem BSD_Hasse_OPEN_p3727 : BSD_Hasse_OPEN 3727 :=
theorem BSD_Hasse_OPEN_p3733 : BSD_Hasse_OPEN 3733 :=
theorem BSD_Hasse_OPEN_p3739 : BSD_Hasse_OPEN 3739 :=
theorem BSD_Hasse_OPEN_p3761 : BSD_Hasse_OPEN 3761 :=
theorem BSD_Hasse_OPEN_p3767 : BSD_Hasse_OPEN 3767 :=
theorem BSD_Hasse_OPEN_p3769 : BSD_Hasse_OPEN 3769 :=
theorem BSD_Hasse_OPEN_p3779 : BSD_Hasse_OPEN 3779 :=
theorem BSD_Hasse_OPEN_p3793 : BSD_Hasse_OPEN 3793 :=
theorem BSD_Hasse_OPEN_p3797 : BSD_Hasse_OPEN 3797 :=
theorem BSD_Hasse_OPEN_p3803 : BSD_Hasse_OPEN 3803 :=
theorem BSD_Hasse_OPEN_p3821 : BSD_Hasse_OPEN 3821 :=
theorem BSD_Hasse_OPEN_p3823 : BSD_Hasse_OPEN 3823 :=
theorem BSD_Hasse_OPEN_p3833 : BSD_Hasse_OPEN 3833 :=
theorem BSD_Hasse_OPEN_p3847 : BSD_Hasse_OPEN 3847 :=
theorem BSD_Hasse_OPEN_p3851 : BSD_Hasse_OPEN 3851 :=
theorem BSD_Hasse_OPEN_p3853 : BSD_Hasse_OPEN 3853 :=
theorem BSD_Hasse_OPEN_p3863 : BSD_Hasse_OPEN 3863 :=
theorem BSD_Hasse_OPEN_p3877 : BSD_Hasse_OPEN 3877 :=
theorem BSD_Hasse_OPEN_p3881 : BSD_Hasse_OPEN 3881 :=
theorem BSD_Hasse_OPEN_p3889 : BSD_Hasse_OPEN 3889 :=
theorem BSD_Hasse_OPEN_p3907 : BSD_Hasse_OPEN 3907 :=
theorem BSD_Hasse_OPEN_p3911 : BSD_Hasse_OPEN 3911 :=
theorem BSD_Hasse_OPEN_p3917 : BSD_Hasse_OPEN 3917 :=
theorem BSD_Hasse_OPEN_p3919 : BSD_Hasse_OPEN 3919 :=
theorem BSD_Hasse_OPEN_p3923 : BSD_Hasse_OPEN 3923 :=
theorem BSD_Hasse_OPEN_p3929 : BSD_Hasse_OPEN 3929 :=
theorem BSD_Hasse_OPEN_p3931 : BSD_Hasse_OPEN 3931 :=
theorem BSD_Hasse_OPEN_p3943 : BSD_Hasse_OPEN 3943 :=
theorem BSD_Hasse_OPEN_p3947 : BSD_Hasse_OPEN 3947 :=
theorem BSD_Hasse_OPEN_p3967 : BSD_Hasse_OPEN 3967 :=
theorem BSD_Hasse_OPEN_p3989 : BSD_Hasse_OPEN 3989 :=
theorem BSD_Hasse_OPEN_p4001 : BSD_Hasse_OPEN 4001 :=
theorem BSD_Hasse_OPEN_p4003 : BSD_Hasse_OPEN 4003 :=
theorem BSD_Hasse_OPEN_p4007 : BSD_Hasse_OPEN 4007 :=
theorem BSD_Hasse_OPEN_p4013 : BSD_Hasse_OPEN 4013 :=
theorem BSD_Hasse_OPEN_p4019 : BSD_Hasse_OPEN 4019 :=
theorem BSD_Hasse_OPEN_p4021 : BSD_Hasse_OPEN 4021 :=
theorem BSD_Hasse_OPEN_p4027 : BSD_Hasse_OPEN 4027 :=
theorem BSD_Hasse_OPEN_p4049 : BSD_Hasse_OPEN 4049 :=
theorem BSD_Hasse_OPEN_p4051 : BSD_Hasse_OPEN 4051 :=
theorem BSD_Hasse_OPEN_p4057 : BSD_Hasse_OPEN 4057 :=
theorem BSD_Hasse_OPEN_p4073 : BSD_Hasse_OPEN 4073 :=
theorem BSD_Hasse_OPEN_p4079 : BSD_Hasse_OPEN 4079 :=
theorem BSD_Hasse_OPEN_p4091 : BSD_Hasse_OPEN 4091 :=
theorem BSD_Hasse_OPEN_p4093 : BSD_Hasse_OPEN 4093 :=
theorem BSD_Hasse_OPEN_p4099 : BSD_Hasse_OPEN 4099 :=
theorem BSD_Hasse_OPEN_p4111 : BSD_Hasse_OPEN 4111 :=
theorem BSD_Hasse_OPEN_p4127 : BSD_Hasse_OPEN 4127 :=
theorem BSD_Hasse_OPEN_p4129 : BSD_Hasse_OPEN 4129 :=
theorem BSD_Hasse_OPEN_p4133 : BSD_Hasse_OPEN 4133 :=
theorem BSD_Hasse_OPEN_p4139 : BSD_Hasse_OPEN 4139 :=
theorem BSD_Hasse_OPEN_p4153 : BSD_Hasse_OPEN 4153 :=
theorem BSD_Hasse_OPEN_p4157 : BSD_Hasse_OPEN 4157 :=
theorem BSD_Hasse_OPEN_p4159 : BSD_Hasse_OPEN 4159 :=
theorem BSD_Hasse_OPEN_p4177 : BSD_Hasse_OPEN 4177 :=
theorem BSD_Hasse_OPEN_p4201 : BSD_Hasse_OPEN 4201 :=
theorem BSD_Hasse_OPEN_p4211 : BSD_Hasse_OPEN 4211 :=
theorem BSD_Hasse_OPEN_p4217 : BSD_Hasse_OPEN 4217 :=
theorem BSD_Hasse_OPEN_p4219 : BSD_Hasse_OPEN 4219 :=
theorem BSD_Hasse_OPEN_p4229 : BSD_Hasse_OPEN 4229 :=
theorem BSD_Hasse_OPEN_p4231 : BSD_Hasse_OPEN 4231 :=
theorem BSD_Hasse_OPEN_p4241 : BSD_Hasse_OPEN 4241 :=
theorem BSD_Hasse_OPEN_p4243 : BSD_Hasse_OPEN 4243 :=
theorem BSD_Hasse_OPEN_p4253 : BSD_Hasse_OPEN 4253 :=
theorem BSD_Hasse_OPEN_p4259 : BSD_Hasse_OPEN 4259 :=
theorem BSD_Hasse_OPEN_p4261 : BSD_Hasse_OPEN 4261 :=
theorem BSD_Hasse_OPEN_p4271 : BSD_Hasse_OPEN 4271 :=
theorem BSD_Hasse_OPEN_p4273 : BSD_Hasse_OPEN 4273 :=
theorem BSD_Hasse_OPEN_p4283 : BSD_Hasse_OPEN 4283 :=
theorem BSD_Hasse_OPEN_p4289 : BSD_Hasse_OPEN 4289 :=
theorem BSD_Hasse_OPEN_p4297 : BSD_Hasse_OPEN 4297 :=
theorem BSD_Hasse_OPEN_p4327 : BSD_Hasse_OPEN 4327 :=
theorem BSD_Hasse_OPEN_p4337 : BSD_Hasse_OPEN 4337 :=
theorem BSD_Hasse_OPEN_p4339 : BSD_Hasse_OPEN 4339 :=
theorem BSD_Hasse_OPEN_p4349 : BSD_Hasse_OPEN 4349 :=
theorem BSD_Hasse_OPEN_p4357 : BSD_Hasse_OPEN 4357 :=
theorem BSD_Hasse_OPEN_p4363 : BSD_Hasse_OPEN 4363 :=
theorem BSD_Hasse_OPEN_p4373 : BSD_Hasse_OPEN 4373 :=
theorem BSD_Hasse_OPEN_p4391 : BSD_Hasse_OPEN 4391 :=
theorem BSD_Hasse_OPEN_p4397 : BSD_Hasse_OPEN 4397 :=
theorem BSD_Hasse_OPEN_p4409 : BSD_Hasse_OPEN 4409 :=
theorem BSD_Hasse_OPEN_p4421 : BSD_Hasse_OPEN 4421 :=
theorem BSD_Hasse_OPEN_p4423 : BSD_Hasse_OPEN 4423 :=
theorem BSD_Hasse_OPEN_p4441 : BSD_Hasse_OPEN 4441 :=
theorem BSD_Hasse_OPEN_p4447 : BSD_Hasse_OPEN 4447 :=
theorem BSD_Hasse_OPEN_p4451 : BSD_Hasse_OPEN 4451 :=
theorem BSD_Hasse_OPEN_p4457 : BSD_Hasse_OPEN 4457 :=
theorem BSD_Hasse_OPEN_p4463 : BSD_Hasse_OPEN 4463 :=
theorem BSD_Hasse_OPEN_p4481 : BSD_Hasse_OPEN 4481 :=
theorem BSD_Hasse_OPEN_p4483 : BSD_Hasse_OPEN 4483 :=
theorem BSD_Hasse_OPEN_p4493 : BSD_Hasse_OPEN 4493 :=
theorem BSD_Hasse_OPEN_p4507 : BSD_Hasse_OPEN 4507 :=
theorem BSD_Hasse_OPEN_p4513 : BSD_Hasse_OPEN 4513 :=
theorem BSD_Hasse_OPEN_p4517 : BSD_Hasse_OPEN 4517 :=
theorem BSD_Hasse_OPEN_p4519 : BSD_Hasse_OPEN 4519 :=
theorem BSD_Hasse_OPEN_p4523 : BSD_Hasse_OPEN 4523 :=
theorem BSD_Hasse_OPEN_p4547 : BSD_Hasse_OPEN 4547 :=
theorem BSD_Hasse_OPEN_p4549 : BSD_Hasse_OPEN 4549 :=
theorem BSD_Hasse_OPEN_p4561 : BSD_Hasse_OPEN 4561 :=
theorem BSD_Hasse_OPEN_p4567 : BSD_Hasse_OPEN 4567 :=
theorem BSD_Hasse_OPEN_p4583 : BSD_Hasse_OPEN 4583 :=
theorem BSD_Hasse_OPEN_p4591 : BSD_Hasse_OPEN 4591 :=
theorem BSD_Hasse_OPEN_p4597 : BSD_Hasse_OPEN 4597 :=
theorem BSD_Hasse_OPEN_p4603 : BSD_Hasse_OPEN 4603 :=
theorem BSD_Hasse_OPEN_p4621 : BSD_Hasse_OPEN 4621 :=
theorem BSD_Hasse_OPEN_p4637 : BSD_Hasse_OPEN 4637 :=
theorem BSD_Hasse_OPEN_p4639 : BSD_Hasse_OPEN 4639 :=
theorem BSD_Hasse_OPEN_p4643 : BSD_Hasse_OPEN 4643 :=
theorem BSD_Hasse_OPEN_p4649 : BSD_Hasse_OPEN 4649 :=
theorem BSD_Hasse_OPEN_p4651 : BSD_Hasse_OPEN 4651 :=
theorem BSD_Hasse_OPEN_p4657 : BSD_Hasse_OPEN 4657 :=
theorem BSD_Hasse_OPEN_p4663 : BSD_Hasse_OPEN 4663 :=
theorem BSD_Hasse_OPEN_p4673 : BSD_Hasse_OPEN 4673 :=
theorem BSD_Hasse_OPEN_p4679 : BSD_Hasse_OPEN 4679 :=
theorem BSD_Hasse_OPEN_p4691 : BSD_Hasse_OPEN 4691 :=
theorem BSD_Hasse_OPEN_p4703 : BSD_Hasse_OPEN 4703 :=
theorem BSD_Hasse_OPEN_p4721 : BSD_Hasse_OPEN 4721 :=
theorem BSD_Hasse_OPEN_p4723 : BSD_Hasse_OPEN 4723 :=
theorem BSD_Hasse_OPEN_p4729 : BSD_Hasse_OPEN 4729 :=
theorem BSD_Hasse_OPEN_p4733 : BSD_Hasse_OPEN 4733 :=
theorem BSD_Hasse_OPEN_p4751 : BSD_Hasse_OPEN 4751 :=
theorem BSD_Hasse_OPEN_p4759 : BSD_Hasse_OPEN 4759 :=
theorem BSD_Hasse_OPEN_p4783 : BSD_Hasse_OPEN 4783 :=
theorem BSD_Hasse_OPEN_p4787 : BSD_Hasse_OPEN 4787 :=
theorem BSD_Hasse_OPEN_p4789 : BSD_Hasse_OPEN 4789 :=
theorem BSD_Hasse_OPEN_p4793 : BSD_Hasse_OPEN 4793 :=
theorem BSD_Hasse_OPEN_p4799 : BSD_Hasse_OPEN 4799 :=
theorem BSD_Hasse_OPEN_p4801 : BSD_Hasse_OPEN 4801 :=
theorem BSD_Hasse_OPEN_p4813 : BSD_Hasse_OPEN 4813 :=
theorem BSD_Hasse_OPEN_p4817 : BSD_Hasse_OPEN 4817 :=
theorem BSD_Hasse_OPEN_p4831 : BSD_Hasse_OPEN 4831 :=
theorem BSD_Hasse_OPEN_p4861 : BSD_Hasse_OPEN 4861 :=
theorem BSD_Hasse_OPEN_p4871 : BSD_Hasse_OPEN 4871 :=
theorem BSD_Hasse_OPEN_p4877 : BSD_Hasse_OPEN 4877 :=
theorem BSD_Hasse_OPEN_p4889 : BSD_Hasse_OPEN 4889 :=
theorem BSD_Hasse_OPEN_p4903 : BSD_Hasse_OPEN 4903 :=
theorem BSD_Hasse_OPEN_p4909 : BSD_Hasse_OPEN 4909 :=
theorem BSD_Hasse_OPEN_p4919 : BSD_Hasse_OPEN 4919 :=
theorem BSD_Hasse_OPEN_p4931 : BSD_Hasse_OPEN 4931 :=
theorem BSD_Hasse_OPEN_p4933 : BSD_Hasse_OPEN 4933 :=
theorem BSD_Hasse_OPEN_p4937 : BSD_Hasse_OPEN 4937 :=
theorem BSD_Hasse_OPEN_p4943 : BSD_Hasse_OPEN 4943 :=
theorem BSD_Hasse_OPEN_p4951 : BSD_Hasse_OPEN 4951 :=
theorem BSD_Hasse_OPEN_p4957 : BSD_Hasse_OPEN 4957 :=
theorem BSD_Hasse_OPEN_p4967 : BSD_Hasse_OPEN 4967 :=
theorem BSD_Hasse_OPEN_p4969 : BSD_Hasse_OPEN 4969 :=
theorem BSD_Hasse_OPEN_p4973 : BSD_Hasse_OPEN 4973 :=
theorem BSD_Hasse_OPEN_p4987 : BSD_Hasse_OPEN 4987 :=
theorem BSD_Hasse_OPEN_p4993 : BSD_Hasse_OPEN 4993 :=
theorem BSD_Hasse_OPEN_p4999 : BSD_Hasse_OPEN 4999 :=
theorem BSD_Hasse_OPEN_p5003 : BSD_Hasse_OPEN 5003 :=
theorem BSD_Hasse_OPEN_p5009 : BSD_Hasse_OPEN 5009 :=
theorem BSD_Hasse_OPEN_p5011 : BSD_Hasse_OPEN 5011 :=
theorem BSD_Hasse_OPEN_p5021 : BSD_Hasse_OPEN 5021 :=
theorem BSD_Hasse_OPEN_p5023 : BSD_Hasse_OPEN 5023 :=
theorem BSD_Hasse_OPEN_p5039 : BSD_Hasse_OPEN 5039 :=
theorem BSD_Hasse_OPEN_p5051 : BSD_Hasse_OPEN 5051 :=
theorem BSD_Hasse_OPEN_p5059 : BSD_Hasse_OPEN 5059 :=
theorem BSD_Hasse_OPEN_p5077 : BSD_Hasse_OPEN 5077 :=
theorem BSD_Hasse_OPEN_p5081 : BSD_Hasse_OPEN 5081 :=
theorem BSD_Hasse_OPEN_p5087 : BSD_Hasse_OPEN 5087 :=
theorem BSD_Hasse_OPEN_p5099 : BSD_Hasse_OPEN 5099 :=
theorem BSD_Hasse_OPEN_p5101 : BSD_Hasse_OPEN 5101 :=
theorem BSD_Hasse_OPEN_p5107 : BSD_Hasse_OPEN 5107 :=
theorem BSD_Hasse_OPEN_p5113 : BSD_Hasse_OPEN 5113 :=
theorem BSD_Hasse_OPEN_p5119 : BSD_Hasse_OPEN 5119 :=
theorem BSD_Hasse_OPEN_p5147 : BSD_Hasse_OPEN 5147 :=
theorem BSD_Hasse_OPEN_p5153 : BSD_Hasse_OPEN 5153 :=
theorem BSD_Hasse_OPEN_p5167 : BSD_Hasse_OPEN 5167 :=
theorem BSD_Hasse_OPEN_p5171 : BSD_Hasse_OPEN 5171 :=
theorem BSD_Hasse_OPEN_p5179 : BSD_Hasse_OPEN 5179 :=
theorem BSD_Hasse_OPEN_p5189 : BSD_Hasse_OPEN 5189 :=
theorem BSD_Hasse_OPEN_p5197 : BSD_Hasse_OPEN 5197 :=
theorem BSD_Hasse_OPEN_p5209 : BSD_Hasse_OPEN 5209 :=
theorem BSD_Hasse_OPEN_p5227 : BSD_Hasse_OPEN 5227 :=
theorem BSD_Hasse_OPEN_p5231 : BSD_Hasse_OPEN 5231 :=
theorem BSD_Hasse_OPEN_p5233 : BSD_Hasse_OPEN 5233 :=
theorem BSD_Hasse_OPEN_p5237 : BSD_Hasse_OPEN 5237 :=
theorem BSD_Hasse_OPEN_p5261 : BSD_Hasse_OPEN 5261 :=
theorem BSD_Hasse_OPEN_p5273 : BSD_Hasse_OPEN 5273 :=
theorem BSD_Hasse_OPEN_p5279 : BSD_Hasse_OPEN 5279 :=
theorem BSD_Hasse_OPEN_p5281 : BSD_Hasse_OPEN 5281 :=
theorem BSD_Hasse_OPEN_p5297 : BSD_Hasse_OPEN 5297 :=
theorem BSD_Hasse_OPEN_p5303 : BSD_Hasse_OPEN 5303 :=
theorem BSD_Hasse_OPEN_p5309 : BSD_Hasse_OPEN 5309 :=
theorem BSD_Hasse_OPEN_p5323 : BSD_Hasse_OPEN 5323 :=
theorem BSD_Hasse_OPEN_p5333 : BSD_Hasse_OPEN 5333 :=
theorem BSD_Hasse_OPEN_p5347 : BSD_Hasse_OPEN 5347 :=
theorem BSD_Hasse_OPEN_p5351 : BSD_Hasse_OPEN 5351 :=
theorem BSD_Hasse_OPEN_p5381 : BSD_Hasse_OPEN 5381 :=
theorem BSD_Hasse_OPEN_p5387 : BSD_Hasse_OPEN 5387 :=
theorem BSD_Hasse_OPEN_p5393 : BSD_Hasse_OPEN 5393 :=
theorem BSD_Hasse_OPEN_p5399 : BSD_Hasse_OPEN 5399 :=
theorem BSD_Hasse_OPEN_p5407 : BSD_Hasse_OPEN 5407 :=
theorem BSD_Hasse_OPEN_p5413 : BSD_Hasse_OPEN 5413 :=
theorem BSD_Hasse_OPEN_p5417 : BSD_Hasse_OPEN 5417 :=
theorem BSD_Hasse_OPEN_p5419 : BSD_Hasse_OPEN 5419 :=
theorem BSD_Hasse_OPEN_p5431 : BSD_Hasse_OPEN 5431 :=
theorem BSD_Hasse_OPEN_p5437 : BSD_Hasse_OPEN 5437 :=
theorem BSD_Hasse_OPEN_p5441 : BSD_Hasse_OPEN 5441 :=
theorem BSD_Hasse_OPEN_p5443 : BSD_Hasse_OPEN 5443 :=
theorem BSD_Hasse_OPEN_p5449 : BSD_Hasse_OPEN 5449 :=
theorem BSD_Hasse_OPEN_p5471 : BSD_Hasse_OPEN 5471 :=
theorem BSD_Hasse_OPEN_p5477 : BSD_Hasse_OPEN 5477 :=
theorem BSD_Hasse_OPEN_p5479 : BSD_Hasse_OPEN 5479 :=
theorem BSD_Hasse_OPEN_p5483 : BSD_Hasse_OPEN 5483 :=
theorem BSD_Hasse_OPEN_p5501 : BSD_Hasse_OPEN 5501 :=
theorem BSD_Hasse_OPEN_p5503 : BSD_Hasse_OPEN 5503 :=
theorem BSD_Hasse_OPEN_p5507 : BSD_Hasse_OPEN 5507 :=
theorem BSD_Hasse_OPEN_p5519 : BSD_Hasse_OPEN 5519 :=
theorem BSD_Hasse_OPEN_p5521 : BSD_Hasse_OPEN 5521 :=
theorem BSD_Hasse_OPEN_p5527 : BSD_Hasse_OPEN 5527 :=
theorem BSD_Hasse_OPEN_p5531 : BSD_Hasse_OPEN 5531 :=
theorem BSD_Hasse_OPEN_p5557 : BSD_Hasse_OPEN 5557 :=
theorem BSD_Hasse_OPEN_p5563 : BSD_Hasse_OPEN 5563 :=
theorem BSD_Hasse_OPEN_p5569 : BSD_Hasse_OPEN 5569 :=
theorem BSD_Hasse_OPEN_p5573 : BSD_Hasse_OPEN 5573 :=
theorem BSD_Hasse_OPEN_p5581 : BSD_Hasse_OPEN 5581 :=
theorem BSD_Hasse_OPEN_p5591 : BSD_Hasse_OPEN 5591 :=
theorem BSD_Hasse_OPEN_p5623 : BSD_Hasse_OPEN 5623 :=
theorem BSD_Hasse_OPEN_p5639 : BSD_Hasse_OPEN 5639 :=
theorem BSD_Hasse_OPEN_p5641 : BSD_Hasse_OPEN 5641 :=
theorem BSD_Hasse_OPEN_p5647 : BSD_Hasse_OPEN 5647 :=
theorem BSD_Hasse_OPEN_p5651 : BSD_Hasse_OPEN 5651 :=
theorem BSD_Hasse_OPEN_p5653 : BSD_Hasse_OPEN 5653 :=
theorem BSD_Hasse_OPEN_p5657 : BSD_Hasse_OPEN 5657 :=
theorem BSD_Hasse_OPEN_p5659 : BSD_Hasse_OPEN 5659 :=
theorem BSD_Hasse_OPEN_p5669 : BSD_Hasse_OPEN 5669 :=
theorem BSD_Hasse_OPEN_p5683 : BSD_Hasse_OPEN 5683 :=
theorem BSD_Hasse_OPEN_p5689 : BSD_Hasse_OPEN 5689 :=
theorem BSD_Hasse_OPEN_p5693 : BSD_Hasse_OPEN 5693 :=
theorem BSD_Hasse_OPEN_p5701 : BSD_Hasse_OPEN 5701 :=
theorem BSD_Hasse_OPEN_p5711 : BSD_Hasse_OPEN 5711 :=
theorem BSD_Hasse_OPEN_p5717 : BSD_Hasse_OPEN 5717 :=
theorem BSD_Hasse_OPEN_p5737 : BSD_Hasse_OPEN 5737 :=
theorem BSD_Hasse_OPEN_p5741 : BSD_Hasse_OPEN 5741 :=
theorem BSD_Hasse_OPEN_p5743 : BSD_Hasse_OPEN 5743 :=
theorem BSD_Hasse_OPEN_p5749 : BSD_Hasse_OPEN 5749 :=
theorem BSD_Hasse_OPEN_p5779 : BSD_Hasse_OPEN 5779 :=
theorem BSD_Hasse_OPEN_p5783 : BSD_Hasse_OPEN 5783 :=
theorem BSD_Hasse_OPEN_p5791 : BSD_Hasse_OPEN 5791 :=
theorem BSD_Hasse_OPEN_p5801 : BSD_Hasse_OPEN 5801 :=
theorem BSD_Hasse_OPEN_p5807 : BSD_Hasse_OPEN 5807 :=
theorem BSD_Hasse_OPEN_p5813 : BSD_Hasse_OPEN 5813 :=
theorem BSD_Hasse_OPEN_p5821 : BSD_Hasse_OPEN 5821 :=
theorem BSD_Hasse_OPEN_p5827 : BSD_Hasse_OPEN 5827 :=
theorem BSD_Hasse_OPEN_p5839 : BSD_Hasse_OPEN 5839 :=
theorem BSD_Hasse_OPEN_p5843 : BSD_Hasse_OPEN 5843 :=
theorem BSD_Hasse_OPEN_p5849 : BSD_Hasse_OPEN 5849 :=
theorem BSD_Hasse_OPEN_p5851 : BSD_Hasse_OPEN 5851 :=
theorem BSD_Hasse_OPEN_p5857 : BSD_Hasse_OPEN 5857 :=
theorem BSD_Hasse_OPEN_p5861 : BSD_Hasse_OPEN 5861 :=
theorem BSD_Hasse_OPEN_p5867 : BSD_Hasse_OPEN 5867 :=
theorem BSD_Hasse_OPEN_p5869 : BSD_Hasse_OPEN 5869 :=
theorem BSD_Hasse_OPEN_p5879 : BSD_Hasse_OPEN 5879 :=
theorem BSD_Hasse_OPEN_p5881 : BSD_Hasse_OPEN 5881 :=
theorem BSD_Hasse_OPEN_p5897 : BSD_Hasse_OPEN 5897 :=
theorem BSD_Hasse_OPEN_p5903 : BSD_Hasse_OPEN 5903 :=
theorem BSD_Hasse_OPEN_p5923 : BSD_Hasse_OPEN 5923 :=
theorem BSD_Hasse_OPEN_p5927 : BSD_Hasse_OPEN 5927 :=
theorem BSD_Hasse_OPEN_p5939 : BSD_Hasse_OPEN 5939 :=
theorem BSD_Hasse_OPEN_p5953 : BSD_Hasse_OPEN 5953 :=
theorem BSD_Hasse_OPEN_p5981 : BSD_Hasse_OPEN 5981 :=
theorem BSD_Hasse_OPEN_p5987 : BSD_Hasse_OPEN 5987 :=
theorem BSD_Hasse_OPEN_p6007 : BSD_Hasse_OPEN 6007 :=
theorem BSD_Hasse_OPEN_p6011 : BSD_Hasse_OPEN 6011 :=
theorem BSD_Hasse_OPEN_p6029 : BSD_Hasse_OPEN 6029 :=
theorem BSD_Hasse_OPEN_p6037 : BSD_Hasse_OPEN 6037 :=
theorem BSD_Hasse_OPEN_p6043 : BSD_Hasse_OPEN 6043 :=
theorem BSD_Hasse_OPEN_p6047 : BSD_Hasse_OPEN 6047 :=
theorem BSD_Hasse_OPEN_p6053 : BSD_Hasse_OPEN 6053 :=
theorem BSD_Hasse_OPEN_p6067 : BSD_Hasse_OPEN 6067 :=
theorem BSD_Hasse_OPEN_p6073 : BSD_Hasse_OPEN 6073 :=
theorem BSD_Hasse_OPEN_p6079 : BSD_Hasse_OPEN 6079 :=
theorem BSD_Hasse_OPEN_p6089 : BSD_Hasse_OPEN 6089 :=
theorem BSD_Hasse_OPEN_p6091 : BSD_Hasse_OPEN 6091 :=
theorem BSD_Hasse_OPEN_p6101 : BSD_Hasse_OPEN 6101 :=
theorem BSD_Hasse_OPEN_p6113 : BSD_Hasse_OPEN 6113 :=
theorem BSD_Hasse_OPEN_p6121 : BSD_Hasse_OPEN 6121 :=
theorem BSD_Hasse_OPEN_p6131 : BSD_Hasse_OPEN 6131 :=
theorem BSD_Hasse_OPEN_p6133 : BSD_Hasse_OPEN 6133 :=
theorem BSD_Hasse_OPEN_p6143 : BSD_Hasse_OPEN 6143 :=
theorem BSD_Hasse_OPEN_p6151 : BSD_Hasse_OPEN 6151 :=
theorem BSD_Hasse_OPEN_p6163 : BSD_Hasse_OPEN 6163 :=
theorem BSD_Hasse_OPEN_p6173 : BSD_Hasse_OPEN 6173 :=
theorem BSD_Hasse_OPEN_p6197 : BSD_Hasse_OPEN 6197 :=
theorem BSD_Hasse_OPEN_p6199 : BSD_Hasse_OPEN 6199 :=
theorem BSD_Hasse_OPEN_p6203 : BSD_Hasse_OPEN 6203 :=
theorem BSD_Hasse_OPEN_p6211 : BSD_Hasse_OPEN 6211 :=
theorem BSD_Hasse_OPEN_p6217 : BSD_Hasse_OPEN 6217 :=
theorem BSD_Hasse_OPEN_p6221 : BSD_Hasse_OPEN 6221 :=
theorem BSD_Hasse_OPEN_p6229 : BSD_Hasse_OPEN 6229 :=
theorem BSD_Hasse_OPEN_p6247 : BSD_Hasse_OPEN 6247 :=
theorem BSD_Hasse_OPEN_p6257 : BSD_Hasse_OPEN 6257 :=
theorem BSD_Hasse_OPEN_p6263 : BSD_Hasse_OPEN 6263 :=
theorem BSD_Hasse_OPEN_p6269 : BSD_Hasse_OPEN 6269 :=
theorem BSD_Hasse_OPEN_p6271 : BSD_Hasse_OPEN 6271 :=
theorem BSD_Hasse_OPEN_p6277 : BSD_Hasse_OPEN 6277 :=
theorem BSD_Hasse_OPEN_p6287 : BSD_Hasse_OPEN 6287 :=
theorem BSD_Hasse_OPEN_p6299 : BSD_Hasse_OPEN 6299 :=
theorem BSD_Hasse_OPEN_p6301 : BSD_Hasse_OPEN 6301 :=
theorem BSD_Hasse_OPEN_p6311 : BSD_Hasse_OPEN 6311 :=
theorem BSD_Hasse_OPEN_p6317 : BSD_Hasse_OPEN 6317 :=
theorem BSD_Hasse_OPEN_p6323 : BSD_Hasse_OPEN 6323 :=
theorem BSD_Hasse_OPEN_p6329 : BSD_Hasse_OPEN 6329 :=
theorem BSD_Hasse_OPEN_p6337 : BSD_Hasse_OPEN 6337 :=
theorem BSD_Hasse_OPEN_p6343 : BSD_Hasse_OPEN 6343 :=
theorem BSD_Hasse_OPEN_p6353 : BSD_Hasse_OPEN 6353 :=
theorem BSD_Hasse_OPEN_p6359 : BSD_Hasse_OPEN 6359 :=
theorem BSD_Hasse_OPEN_p6361 : BSD_Hasse_OPEN 6361 :=
theorem BSD_Hasse_OPEN_p6367 : BSD_Hasse_OPEN 6367 :=
theorem BSD_Hasse_OPEN_p6373 : BSD_Hasse_OPEN 6373 :=
theorem BSD_Hasse_OPEN_p6379 : BSD_Hasse_OPEN 6379 :=
theorem BSD_Hasse_OPEN_p6389 : BSD_Hasse_OPEN 6389 :=
theorem BSD_Hasse_OPEN_p6397 : BSD_Hasse_OPEN 6397 :=
theorem BSD_Hasse_OPEN_p6421 : BSD_Hasse_OPEN 6421 :=
theorem BSD_Hasse_OPEN_p6427 : BSD_Hasse_OPEN 6427 :=
theorem BSD_Hasse_OPEN_p6449 : BSD_Hasse_OPEN 6449 :=
theorem BSD_Hasse_OPEN_p6451 : BSD_Hasse_OPEN 6451 :=
theorem BSD_Hasse_OPEN_p6469 : BSD_Hasse_OPEN 6469 :=
theorem BSD_Hasse_OPEN_p6473 : BSD_Hasse_OPEN 6473 :=
theorem BSD_Hasse_OPEN_p6481 : BSD_Hasse_OPEN 6481 :=
theorem BSD_Hasse_OPEN_p6491 : BSD_Hasse_OPEN 6491 :=
theorem BSD_Hasse_OPEN_p6521 : BSD_Hasse_OPEN 6521 :=
theorem BSD_Hasse_OPEN_p6529 : BSD_Hasse_OPEN 6529 :=
theorem BSD_Hasse_OPEN_p6547 : BSD_Hasse_OPEN 6547 :=
theorem BSD_Hasse_OPEN_p6551 : BSD_Hasse_OPEN 6551 :=
theorem BSD_Hasse_OPEN_p6553 : BSD_Hasse_OPEN 6553 :=
theorem BSD_Hasse_OPEN_p6563 : BSD_Hasse_OPEN 6563 :=
theorem BSD_Hasse_OPEN_p6569 : BSD_Hasse_OPEN 6569 :=
theorem BSD_Hasse_OPEN_p6571 : BSD_Hasse_OPEN 6571 :=
theorem BSD_Hasse_OPEN_p6577 : BSD_Hasse_OPEN 6577 :=
theorem BSD_Hasse_OPEN_p6581 : BSD_Hasse_OPEN 6581 :=
theorem BSD_Hasse_OPEN_p6599 : BSD_Hasse_OPEN 6599 :=
theorem BSD_Hasse_OPEN_p6607 : BSD_Hasse_OPEN 6607 :=
theorem BSD_Hasse_OPEN_p6619 : BSD_Hasse_OPEN 6619 :=
theorem BSD_Hasse_OPEN_p6637 : BSD_Hasse_OPEN 6637 :=
theorem BSD_Hasse_OPEN_p6653 : BSD_Hasse_OPEN 6653 :=
theorem BSD_Hasse_OPEN_p6659 : BSD_Hasse_OPEN 6659 :=
theorem BSD_Hasse_OPEN_p6661 : BSD_Hasse_OPEN 6661 :=
theorem BSD_Hasse_OPEN_p6673 : BSD_Hasse_OPEN 6673 :=
theorem BSD_Hasse_OPEN_p6679 : BSD_Hasse_OPEN 6679 :=
theorem BSD_Hasse_OPEN_p6689 : BSD_Hasse_OPEN 6689 :=
theorem BSD_Hasse_OPEN_p6691 : BSD_Hasse_OPEN 6691 :=
theorem BSD_Hasse_OPEN_p6701 : BSD_Hasse_OPEN 6701 :=
theorem BSD_Hasse_OPEN_p6703 : BSD_Hasse_OPEN 6703 :=
theorem BSD_Hasse_OPEN_p6709 : BSD_Hasse_OPEN 6709 :=
theorem BSD_Hasse_OPEN_p6719 : BSD_Hasse_OPEN 6719 :=
theorem BSD_Hasse_OPEN_p6733 : BSD_Hasse_OPEN 6733 :=
theorem BSD_Hasse_OPEN_p6737 : BSD_Hasse_OPEN 6737 :=
theorem BSD_Hasse_OPEN_p6761 : BSD_Hasse_OPEN 6761 :=
theorem BSD_Hasse_OPEN_p6763 : BSD_Hasse_OPEN 6763 :=
theorem BSD_Hasse_OPEN_p6779 : BSD_Hasse_OPEN 6779 :=
theorem BSD_Hasse_OPEN_p6781 : BSD_Hasse_OPEN 6781 :=
theorem BSD_Hasse_OPEN_p6791 : BSD_Hasse_OPEN 6791 :=
theorem BSD_Hasse_OPEN_p6793 : BSD_Hasse_OPEN 6793 :=
theorem BSD_Hasse_OPEN_p6803 : BSD_Hasse_OPEN 6803 :=
theorem BSD_Hasse_OPEN_p6823 : BSD_Hasse_OPEN 6823 :=
theorem BSD_Hasse_OPEN_p6827 : BSD_Hasse_OPEN 6827 :=
theorem BSD_Hasse_OPEN_p6829 : BSD_Hasse_OPEN 6829 :=
theorem BSD_Hasse_OPEN_p6833 : BSD_Hasse_OPEN 6833 :=
theorem BSD_Hasse_OPEN_p6841 : BSD_Hasse_OPEN 6841 :=
theorem BSD_Hasse_OPEN_p6857 : BSD_Hasse_OPEN 6857 :=
theorem BSD_Hasse_OPEN_p6863 : BSD_Hasse_OPEN 6863 :=
theorem BSD_Hasse_OPEN_p6869 : BSD_Hasse_OPEN 6869 :=
theorem BSD_Hasse_OPEN_p6871 : BSD_Hasse_OPEN 6871 :=
theorem BSD_Hasse_OPEN_p6883 : BSD_Hasse_OPEN 6883 :=
theorem BSD_Hasse_OPEN_p6899 : BSD_Hasse_OPEN 6899 :=
theorem BSD_Hasse_OPEN_p6907 : BSD_Hasse_OPEN 6907 :=
theorem BSD_Hasse_OPEN_p6911 : BSD_Hasse_OPEN 6911 :=
theorem BSD_Hasse_OPEN_p6917 : BSD_Hasse_OPEN 6917 :=
theorem BSD_Hasse_OPEN_p6947 : BSD_Hasse_OPEN 6947 :=
theorem BSD_Hasse_OPEN_p6949 : BSD_Hasse_OPEN 6949 :=
theorem BSD_Hasse_OPEN_p6959 : BSD_Hasse_OPEN 6959 :=
theorem BSD_Hasse_OPEN_p6961 : BSD_Hasse_OPEN 6961 :=
theorem BSD_Hasse_OPEN_p6967 : BSD_Hasse_OPEN 6967 :=
theorem BSD_Hasse_OPEN_p6971 : BSD_Hasse_OPEN 6971 :=
theorem BSD_Hasse_OPEN_p6977 : BSD_Hasse_OPEN 6977 :=
theorem BSD_Hasse_OPEN_p6983 : BSD_Hasse_OPEN 6983 :=
theorem BSD_Hasse_OPEN_p6991 : BSD_Hasse_OPEN 6991 :=
theorem BSD_Hasse_OPEN_p6997 : BSD_Hasse_OPEN 6997 :=
theorem BSD_Hasse_OPEN_p7001 : BSD_Hasse_OPEN 7001 :=
theorem BSD_Hasse_OPEN_p7013 : BSD_Hasse_OPEN 7013 :=
theorem BSD_Hasse_OPEN_p7019 : BSD_Hasse_OPEN 7019 :=
theorem BSD_Hasse_OPEN_p7027 : BSD_Hasse_OPEN 7027 :=
theorem BSD_Hasse_OPEN_p7039 : BSD_Hasse_OPEN 7039 :=
theorem BSD_Hasse_OPEN_p7043 : BSD_Hasse_OPEN 7043 :=
theorem BSD_Hasse_OPEN_p7057 : BSD_Hasse_OPEN 7057 :=
theorem BSD_Hasse_OPEN_p7069 : BSD_Hasse_OPEN 7069 :=
theorem BSD_Hasse_OPEN_p7079 : BSD_Hasse_OPEN 7079 :=
theorem BSD_Hasse_OPEN_p7103 : BSD_Hasse_OPEN 7103 :=
theorem BSD_Hasse_OPEN_p7109 : BSD_Hasse_OPEN 7109 :=
theorem BSD_Hasse_OPEN_p7121 : BSD_Hasse_OPEN 7121 :=
theorem BSD_Hasse_OPEN_p7127 : BSD_Hasse_OPEN 7127 :=
theorem BSD_Hasse_OPEN_p7129 : BSD_Hasse_OPEN 7129 :=
theorem BSD_Hasse_OPEN_p7151 : BSD_Hasse_OPEN 7151 :=
theorem BSD_Hasse_OPEN_p7159 : BSD_Hasse_OPEN 7159 :=
theorem BSD_Hasse_OPEN_p7177 : BSD_Hasse_OPEN 7177 :=
theorem BSD_Hasse_OPEN_p7187 : BSD_Hasse_OPEN 7187 :=
theorem BSD_Hasse_OPEN_p7193 : BSD_Hasse_OPEN 7193 :=
theorem BSD_Hasse_OPEN_p7207 : BSD_Hasse_OPEN 7207 :=
theorem BSD_Hasse_OPEN_p7211 : BSD_Hasse_OPEN 7211 :=
theorem BSD_Hasse_OPEN_p7213 : BSD_Hasse_OPEN 7213 :=
theorem BSD_Hasse_OPEN_p7219 : BSD_Hasse_OPEN 7219 :=
theorem BSD_Hasse_OPEN_p7229 : BSD_Hasse_OPEN 7229 :=
theorem BSD_Hasse_OPEN_p7237 : BSD_Hasse_OPEN 7237 :=
theorem BSD_Hasse_OPEN_p7243 : BSD_Hasse_OPEN 7243 :=
theorem BSD_Hasse_OPEN_p7247 : BSD_Hasse_OPEN 7247 :=
theorem BSD_Hasse_OPEN_p7253 : BSD_Hasse_OPEN 7253 :=
theorem BSD_Hasse_OPEN_p7283 : BSD_Hasse_OPEN 7283 :=
theorem BSD_Hasse_OPEN_p7297 : BSD_Hasse_OPEN 7297 :=
theorem BSD_Hasse_OPEN_p7307 : BSD_Hasse_OPEN 7307 :=
theorem BSD_Hasse_OPEN_p7309 : BSD_Hasse_OPEN 7309 :=
theorem BSD_Hasse_OPEN_p7321 : BSD_Hasse_OPEN 7321 :=
theorem BSD_Hasse_OPEN_p7331 : BSD_Hasse_OPEN 7331 :=
theorem BSD_Hasse_OPEN_p7333 : BSD_Hasse_OPEN 7333 :=
theorem BSD_Hasse_OPEN_p7349 : BSD_Hasse_OPEN 7349 :=
theorem BSD_Hasse_OPEN_p7351 : BSD_Hasse_OPEN 7351 :=
theorem BSD_Hasse_OPEN_p7369 : BSD_Hasse_OPEN 7369 :=
theorem BSD_Hasse_OPEN_p7393 : BSD_Hasse_OPEN 7393 :=
theorem BSD_Hasse_OPEN_p7411 : BSD_Hasse_OPEN 7411 :=
theorem BSD_Hasse_OPEN_p7417 : BSD_Hasse_OPEN 7417 :=
theorem BSD_Hasse_OPEN_p7433 : BSD_Hasse_OPEN 7433 :=
theorem BSD_Hasse_OPEN_p7451 : BSD_Hasse_OPEN 7451 :=
theorem BSD_Hasse_OPEN_p7457 : BSD_Hasse_OPEN 7457 :=
theorem BSD_Hasse_OPEN_p7459 : BSD_Hasse_OPEN 7459 :=
theorem BSD_Hasse_OPEN_p7477 : BSD_Hasse_OPEN 7477 :=
theorem BSD_Hasse_OPEN_p7481 : BSD_Hasse_OPEN 7481 :=
theorem BSD_Hasse_OPEN_p7487 : BSD_Hasse_OPEN 7487 :=
theorem BSD_Hasse_OPEN_p7489 : BSD_Hasse_OPEN 7489 :=
theorem BSD_Hasse_OPEN_p7499 : BSD_Hasse_OPEN 7499 :=
theorem BSD_Hasse_OPEN_p7507 : BSD_Hasse_OPEN 7507 :=
theorem BSD_Hasse_OPEN_p7517 : BSD_Hasse_OPEN 7517 :=
theorem BSD_Hasse_OPEN_p7523 : BSD_Hasse_OPEN 7523 :=
theorem BSD_Hasse_OPEN_p7529 : BSD_Hasse_OPEN 7529 :=
theorem BSD_Hasse_OPEN_p7537 : BSD_Hasse_OPEN 7537 :=
theorem BSD_Hasse_OPEN_p7541 : BSD_Hasse_OPEN 7541 :=
theorem BSD_Hasse_OPEN_p7547 : BSD_Hasse_OPEN 7547 :=
theorem BSD_Hasse_OPEN_p7549 : BSD_Hasse_OPEN 7549 :=
theorem BSD_Hasse_OPEN_p7559 : BSD_Hasse_OPEN 7559 :=
theorem BSD_Hasse_OPEN_p7561 : BSD_Hasse_OPEN 7561 :=
theorem BSD_Hasse_OPEN_p7573 : BSD_Hasse_OPEN 7573 :=
theorem BSD_Hasse_OPEN_p7577 : BSD_Hasse_OPEN 7577 :=
theorem BSD_Hasse_OPEN_p7583 : BSD_Hasse_OPEN 7583 :=
theorem BSD_Hasse_OPEN_p7589 : BSD_Hasse_OPEN 7589 :=
theorem BSD_Hasse_OPEN_p7591 : BSD_Hasse_OPEN 7591 :=
theorem BSD_Hasse_OPEN_p7603 : BSD_Hasse_OPEN 7603 :=
theorem BSD_Hasse_OPEN_p7607 : BSD_Hasse_OPEN 7607 :=
theorem BSD_Hasse_OPEN_p7621 : BSD_Hasse_OPEN 7621 :=
theorem BSD_Hasse_OPEN_p7639 : BSD_Hasse_OPEN 7639 :=
theorem BSD_Hasse_OPEN_p7643 : BSD_Hasse_OPEN 7643 :=
theorem BSD_Hasse_OPEN_p7649 : BSD_Hasse_OPEN 7649 :=
theorem BSD_Hasse_OPEN_p7669 : BSD_Hasse_OPEN 7669 :=
theorem BSD_Hasse_OPEN_p7673 : BSD_Hasse_OPEN 7673 :=
theorem BSD_Hasse_OPEN_p7681 : BSD_Hasse_OPEN 7681 :=
theorem BSD_Hasse_OPEN_p7687 : BSD_Hasse_OPEN 7687 :=
theorem BSD_Hasse_OPEN_p7691 : BSD_Hasse_OPEN 7691 :=
theorem BSD_Hasse_OPEN_p7699 : BSD_Hasse_OPEN 7699 :=
theorem BSD_Hasse_OPEN_p7703 : BSD_Hasse_OPEN 7703 :=
theorem BSD_Hasse_OPEN_p7717 : BSD_Hasse_OPEN 7717 :=
theorem BSD_Hasse_OPEN_p7723 : BSD_Hasse_OPEN 7723 :=
theorem BSD_Hasse_OPEN_p7727 : BSD_Hasse_OPEN 7727 :=
theorem BSD_Hasse_OPEN_p7741 : BSD_Hasse_OPEN 7741 :=
theorem BSD_Hasse_OPEN_p7753 : BSD_Hasse_OPEN 7753 :=
theorem BSD_Hasse_OPEN_p7757 : BSD_Hasse_OPEN 7757 :=
theorem BSD_Hasse_OPEN_p7759 : BSD_Hasse_OPEN 7759 :=
theorem BSD_Hasse_OPEN_p7789 : BSD_Hasse_OPEN 7789 :=
theorem BSD_Hasse_OPEN_p7793 : BSD_Hasse_OPEN 7793 :=
theorem BSD_Hasse_OPEN_p7817 : BSD_Hasse_OPEN 7817 :=
theorem BSD_Hasse_OPEN_p7823 : BSD_Hasse_OPEN 7823 :=
theorem BSD_Hasse_OPEN_p7829 : BSD_Hasse_OPEN 7829 :=
theorem BSD_Hasse_OPEN_p7841 : BSD_Hasse_OPEN 7841 :=
theorem BSD_Hasse_OPEN_p7853 : BSD_Hasse_OPEN 7853 :=
theorem BSD_Hasse_OPEN_p7867 : BSD_Hasse_OPEN 7867 :=
theorem BSD_Hasse_OPEN_p7873 : BSD_Hasse_OPEN 7873 :=
theorem BSD_Hasse_OPEN_p7877 : BSD_Hasse_OPEN 7877 :=
theorem BSD_Hasse_OPEN_p7879 : BSD_Hasse_OPEN 7879 :=
theorem BSD_Hasse_OPEN_p7883 : BSD_Hasse_OPEN 7883 :=
theorem BSD_Hasse_OPEN_p7901 : BSD_Hasse_OPEN 7901 :=
theorem BSD_Hasse_OPEN_p7907 : BSD_Hasse_OPEN 7907 :=
theorem BSD_Hasse_OPEN_p7919 : BSD_Hasse_OPEN 7919 :=
theorem BSD_Hasse_OPEN_p7927 : BSD_Hasse_OPEN 7927 :=
theorem BSD_Hasse_OPEN_p7933 : BSD_Hasse_OPEN 7933 :=
theorem BSD_Hasse_OPEN_p7937 : BSD_Hasse_OPEN 7937 :=
theorem BSD_Hasse_OPEN_p7949 : BSD_Hasse_OPEN 7949 :=
theorem BSD_Hasse_OPEN_p7951 : BSD_Hasse_OPEN 7951 :=
theorem BSD_Hasse_OPEN_p7963 : BSD_Hasse_OPEN 7963 :=
theorem BSD_Hasse_OPEN_p7993 : BSD_Hasse_OPEN 7993 :=
theorem BSD_Hasse_OPEN_p8009 : BSD_Hasse_OPEN 8009 :=
theorem BSD_Hasse_OPEN_p8011 : BSD_Hasse_OPEN 8011 :=
theorem BSD_Hasse_OPEN_p8017 : BSD_Hasse_OPEN 8017 :=
theorem BSD_Hasse_OPEN_p8039 : BSD_Hasse_OPEN 8039 :=
theorem BSD_Hasse_OPEN_p8053 : BSD_Hasse_OPEN 8053 :=
theorem BSD_Hasse_OPEN_p8059 : BSD_Hasse_OPEN 8059 :=
theorem BSD_Hasse_OPEN_p8069 : BSD_Hasse_OPEN 8069 :=
theorem BSD_Hasse_OPEN_p8081 : BSD_Hasse_OPEN 8081 :=
theorem BSD_Hasse_OPEN_p8087 : BSD_Hasse_OPEN 8087 :=
theorem BSD_Hasse_OPEN_p8089 : BSD_Hasse_OPEN 8089 :=
theorem BSD_Hasse_OPEN_p8093 : BSD_Hasse_OPEN 8093 :=
theorem BSD_Hasse_OPEN_p8101 : BSD_Hasse_OPEN 8101 :=
theorem BSD_Hasse_OPEN_p8111 : BSD_Hasse_OPEN 8111 :=
theorem BSD_Hasse_OPEN_p8117 : BSD_Hasse_OPEN 8117 :=
theorem BSD_Hasse_OPEN_p8123 : BSD_Hasse_OPEN 8123 :=
theorem BSD_Hasse_OPEN_p8147 : BSD_Hasse_OPEN 8147 :=
theorem BSD_Hasse_OPEN_p8161 : BSD_Hasse_OPEN 8161 :=
theorem BSD_Hasse_OPEN_p8167 : BSD_Hasse_OPEN 8167 :=
theorem BSD_Hasse_OPEN_p8171 : BSD_Hasse_OPEN 8171 :=
theorem BSD_Hasse_OPEN_p8179 : BSD_Hasse_OPEN 8179 :=
theorem BSD_Hasse_OPEN_p8191 : BSD_Hasse_OPEN 8191 :=
theorem BSD_Hasse_OPEN_p8209 : BSD_Hasse_OPEN 8209 :=
theorem BSD_Hasse_OPEN_p8219 : BSD_Hasse_OPEN 8219 :=
theorem BSD_Hasse_OPEN_p8221 : BSD_Hasse_OPEN 8221 :=
theorem BSD_Hasse_OPEN_p8231 : BSD_Hasse_OPEN 8231 :=
theorem BSD_Hasse_OPEN_p8233 : BSD_Hasse_OPEN 8233 :=
theorem BSD_Hasse_OPEN_p8237 : BSD_Hasse_OPEN 8237 :=
theorem BSD_Hasse_OPEN_p8243 : BSD_Hasse_OPEN 8243 :=
theorem BSD_Hasse_OPEN_p8263 : BSD_Hasse_OPEN 8263 :=
theorem BSD_Hasse_OPEN_p8269 : BSD_Hasse_OPEN 8269 :=
theorem BSD_Hasse_OPEN_p8273 : BSD_Hasse_OPEN 8273 :=
theorem BSD_Hasse_OPEN_p8287 : BSD_Hasse_OPEN 8287 :=
theorem BSD_Hasse_OPEN_p8291 : BSD_Hasse_OPEN 8291 :=
theorem BSD_Hasse_OPEN_p8293 : BSD_Hasse_OPEN 8293 :=
theorem BSD_Hasse_OPEN_p8297 : BSD_Hasse_OPEN 8297 :=
theorem BSD_Hasse_OPEN_p8311 : BSD_Hasse_OPEN 8311 :=
theorem BSD_Hasse_OPEN_p8317 : BSD_Hasse_OPEN 8317 :=
theorem BSD_Hasse_OPEN_p8329 : BSD_Hasse_OPEN 8329 :=
theorem BSD_Hasse_OPEN_p8353 : BSD_Hasse_OPEN 8353 :=
theorem BSD_Hasse_OPEN_p8363 : BSD_Hasse_OPEN 8363 :=
theorem BSD_Hasse_OPEN_p8369 : BSD_Hasse_OPEN 8369 :=
theorem BSD_Hasse_OPEN_p8377 : BSD_Hasse_OPEN 8377 :=
theorem BSD_Hasse_OPEN_p8387 : BSD_Hasse_OPEN 8387 :=
theorem BSD_Hasse_OPEN_p8389 : BSD_Hasse_OPEN 8389 :=
theorem BSD_Hasse_OPEN_p8419 : BSD_Hasse_OPEN 8419 :=
theorem BSD_Hasse_OPEN_p8423 : BSD_Hasse_OPEN 8423 :=
theorem BSD_Hasse_OPEN_p8429 : BSD_Hasse_OPEN 8429 :=
theorem BSD_Hasse_OPEN_p8431 : BSD_Hasse_OPEN 8431 :=
theorem BSD_Hasse_OPEN_p8443 : BSD_Hasse_OPEN 8443 :=
theorem BSD_Hasse_OPEN_p8447 : BSD_Hasse_OPEN 8447 :=
theorem BSD_Hasse_OPEN_p8461 : BSD_Hasse_OPEN 8461 :=
theorem BSD_Hasse_OPEN_p8467 : BSD_Hasse_OPEN 8467 :=
theorem BSD_Hasse_OPEN_p8501 : BSD_Hasse_OPEN 8501 :=
theorem BSD_Hasse_OPEN_p8513 : BSD_Hasse_OPEN 8513 :=
theorem BSD_Hasse_OPEN_p8521 : BSD_Hasse_OPEN 8521 :=
theorem BSD_Hasse_OPEN_p8527 : BSD_Hasse_OPEN 8527 :=
theorem BSD_Hasse_OPEN_p8537 : BSD_Hasse_OPEN 8537 :=
theorem BSD_Hasse_OPEN_p8539 : BSD_Hasse_OPEN 8539 :=
theorem BSD_Hasse_OPEN_p8543 : BSD_Hasse_OPEN 8543 :=
theorem BSD_Hasse_OPEN_p8563 : BSD_Hasse_OPEN 8563 :=
theorem BSD_Hasse_OPEN_p8573 : BSD_Hasse_OPEN 8573 :=
theorem BSD_Hasse_OPEN_p8581 : BSD_Hasse_OPEN 8581 :=
theorem BSD_Hasse_OPEN_p8597 : BSD_Hasse_OPEN 8597 :=
theorem BSD_Hasse_OPEN_p8599 : BSD_Hasse_OPEN 8599 :=
theorem BSD_Hasse_OPEN_p8609 : BSD_Hasse_OPEN 8609 :=
theorem BSD_Hasse_OPEN_p8623 : BSD_Hasse_OPEN 8623 :=
theorem BSD_Hasse_OPEN_p8627 : BSD_Hasse_OPEN 8627 :=
theorem BSD_Hasse_OPEN_p8629 : BSD_Hasse_OPEN 8629 :=
theorem BSD_Hasse_OPEN_p8641 : BSD_Hasse_OPEN 8641 :=
theorem BSD_Hasse_OPEN_p8647 : BSD_Hasse_OPEN 8647 :=
theorem BSD_Hasse_OPEN_p8663 : BSD_Hasse_OPEN 8663 :=
theorem BSD_Hasse_OPEN_p8669 : BSD_Hasse_OPEN 8669 :=
theorem BSD_Hasse_OPEN_p8677 : BSD_Hasse_OPEN 8677 :=
theorem BSD_Hasse_OPEN_p8681 : BSD_Hasse_OPEN 8681 :=
theorem BSD_Hasse_OPEN_p8689 : BSD_Hasse_OPEN 8689 :=
theorem BSD_Hasse_OPEN_p8693 : BSD_Hasse_OPEN 8693 :=
theorem BSD_Hasse_OPEN_p8699 : BSD_Hasse_OPEN 8699 :=
theorem BSD_Hasse_OPEN_p8707 : BSD_Hasse_OPEN 8707 :=
theorem BSD_Hasse_OPEN_p8713 : BSD_Hasse_OPEN 8713 :=
theorem BSD_Hasse_OPEN_p8719 : BSD_Hasse_OPEN 8719 :=
theorem BSD_Hasse_OPEN_p8731 : BSD_Hasse_OPEN 8731 :=
theorem BSD_Hasse_OPEN_p8737 : BSD_Hasse_OPEN 8737 :=
theorem BSD_Hasse_OPEN_p8741 : BSD_Hasse_OPEN 8741 :=
theorem BSD_Hasse_OPEN_p8747 : BSD_Hasse_OPEN 8747 :=
theorem BSD_Hasse_OPEN_p8753 : BSD_Hasse_OPEN 8753 :=
theorem BSD_Hasse_OPEN_p8761 : BSD_Hasse_OPEN 8761 :=
theorem BSD_Hasse_OPEN_p8779 : BSD_Hasse_OPEN 8779 :=
theorem BSD_Hasse_OPEN_p8783 : BSD_Hasse_OPEN 8783 :=
theorem BSD_Hasse_OPEN_p8803 : BSD_Hasse_OPEN 8803 :=
theorem BSD_Hasse_OPEN_p8807 : BSD_Hasse_OPEN 8807 :=
theorem BSD_Hasse_OPEN_p8819 : BSD_Hasse_OPEN 8819 :=
theorem BSD_Hasse_OPEN_p8821 : BSD_Hasse_OPEN 8821 :=
theorem BSD_Hasse_OPEN_p8831 : BSD_Hasse_OPEN 8831 :=
theorem BSD_Hasse_OPEN_p8837 : BSD_Hasse_OPEN 8837 :=
theorem BSD_Hasse_OPEN_p8839 : BSD_Hasse_OPEN 8839 :=
theorem BSD_Hasse_OPEN_p8849 : BSD_Hasse_OPEN 8849 :=
theorem BSD_Hasse_OPEN_p8861 : BSD_Hasse_OPEN 8861 :=
theorem BSD_Hasse_OPEN_p8863 : BSD_Hasse_OPEN 8863 :=
theorem BSD_Hasse_OPEN_p8867 : BSD_Hasse_OPEN 8867 :=
theorem BSD_Hasse_OPEN_p8887 : BSD_Hasse_OPEN 8887 :=
theorem BSD_Hasse_OPEN_p8893 : BSD_Hasse_OPEN 8893 :=
theorem BSD_Hasse_OPEN_p8923 : BSD_Hasse_OPEN 8923 :=
theorem BSD_Hasse_OPEN_p8929 : BSD_Hasse_OPEN 8929 :=
theorem BSD_Hasse_OPEN_p8933 : BSD_Hasse_OPEN 8933 :=
theorem BSD_Hasse_OPEN_p8941 : BSD_Hasse_OPEN 8941 :=
theorem BSD_Hasse_OPEN_p8951 : BSD_Hasse_OPEN 8951 :=
theorem BSD_Hasse_OPEN_p8963 : BSD_Hasse_OPEN 8963 :=
theorem BSD_Hasse_OPEN_p8969 : BSD_Hasse_OPEN 8969 :=
theorem BSD_Hasse_OPEN_p8971 : BSD_Hasse_OPEN 8971 :=
theorem BSD_Hasse_OPEN_p8999 : BSD_Hasse_OPEN 8999 :=
theorem BSD_Hasse_OPEN_p9001 : BSD_Hasse_OPEN 9001 :=
theorem BSD_Hasse_OPEN_p9007 : BSD_Hasse_OPEN 9007 :=
theorem BSD_Hasse_OPEN_p9011 : BSD_Hasse_OPEN 9011 :=
theorem BSD_Hasse_OPEN_p9013 : BSD_Hasse_OPEN 9013 :=
theorem BSD_Hasse_OPEN_p9029 : BSD_Hasse_OPEN 9029 :=
theorem BSD_Hasse_OPEN_p9041 : BSD_Hasse_OPEN 9041 :=
theorem BSD_Hasse_OPEN_p9043 : BSD_Hasse_OPEN 9043 :=
theorem BSD_Hasse_OPEN_p9049 : BSD_Hasse_OPEN 9049 :=
theorem BSD_Hasse_OPEN_p9059 : BSD_Hasse_OPEN 9059 :=
theorem BSD_Hasse_OPEN_p9067 : BSD_Hasse_OPEN 9067 :=
theorem BSD_Hasse_OPEN_p9091 : BSD_Hasse_OPEN 9091 :=
theorem BSD_Hasse_OPEN_p9103 : BSD_Hasse_OPEN 9103 :=
theorem BSD_Hasse_OPEN_p9109 : BSD_Hasse_OPEN 9109 :=
theorem BSD_Hasse_OPEN_p9127 : BSD_Hasse_OPEN 9127 :=
theorem BSD_Hasse_OPEN_p9133 : BSD_Hasse_OPEN 9133 :=
theorem BSD_Hasse_OPEN_p9137 : BSD_Hasse_OPEN 9137 :=
theorem BSD_Hasse_OPEN_p9151 : BSD_Hasse_OPEN 9151 :=
theorem BSD_Hasse_OPEN_p9157 : BSD_Hasse_OPEN 9157 :=
theorem BSD_Hasse_OPEN_p9161 : BSD_Hasse_OPEN 9161 :=
theorem BSD_Hasse_OPEN_p9173 : BSD_Hasse_OPEN 9173 :=
theorem BSD_Hasse_OPEN_p9181 : BSD_Hasse_OPEN 9181 :=
theorem BSD_Hasse_OPEN_p9187 : BSD_Hasse_OPEN 9187 :=
theorem BSD_Hasse_OPEN_p9199 : BSD_Hasse_OPEN 9199 :=
theorem BSD_Hasse_OPEN_p9203 : BSD_Hasse_OPEN 9203 :=
theorem BSD_Hasse_OPEN_p9209 : BSD_Hasse_OPEN 9209 :=
theorem BSD_Hasse_OPEN_p9221 : BSD_Hasse_OPEN 9221 :=
theorem BSD_Hasse_OPEN_p9227 : BSD_Hasse_OPEN 9227 :=
theorem BSD_Hasse_OPEN_p9239 : BSD_Hasse_OPEN 9239 :=
theorem BSD_Hasse_OPEN_p9241 : BSD_Hasse_OPEN 9241 :=
theorem BSD_Hasse_OPEN_p9257 : BSD_Hasse_OPEN 9257 :=
theorem BSD_Hasse_OPEN_p9277 : BSD_Hasse_OPEN 9277 :=
theorem BSD_Hasse_OPEN_p9281 : BSD_Hasse_OPEN 9281 :=
theorem BSD_Hasse_OPEN_p9283 : BSD_Hasse_OPEN 9283 :=
theorem BSD_Hasse_OPEN_p9293 : BSD_Hasse_OPEN 9293 :=
theorem BSD_Hasse_OPEN_p9311 : BSD_Hasse_OPEN 9311 :=
theorem BSD_Hasse_OPEN_p9319 : BSD_Hasse_OPEN 9319 :=
theorem BSD_Hasse_OPEN_p9323 : BSD_Hasse_OPEN 9323 :=
theorem BSD_Hasse_OPEN_p9337 : BSD_Hasse_OPEN 9337 :=
theorem BSD_Hasse_OPEN_p9341 : BSD_Hasse_OPEN 9341 :=
theorem BSD_Hasse_OPEN_p9343 : BSD_Hasse_OPEN 9343 :=
theorem BSD_Hasse_OPEN_p9349 : BSD_Hasse_OPEN 9349 :=
theorem BSD_Hasse_OPEN_p9371 : BSD_Hasse_OPEN 9371 :=
theorem BSD_Hasse_OPEN_p9377 : BSD_Hasse_OPEN 9377 :=
theorem BSD_Hasse_OPEN_p9391 : BSD_Hasse_OPEN 9391 :=
theorem BSD_Hasse_OPEN_p9397 : BSD_Hasse_OPEN 9397 :=
theorem BSD_Hasse_OPEN_p9403 : BSD_Hasse_OPEN 9403 :=
theorem BSD_Hasse_OPEN_p9413 : BSD_Hasse_OPEN 9413 :=
theorem BSD_Hasse_OPEN_p9419 : BSD_Hasse_OPEN 9419 :=
theorem BSD_Hasse_OPEN_p9421 : BSD_Hasse_OPEN 9421 :=
theorem BSD_Hasse_OPEN_p9431 : BSD_Hasse_OPEN 9431 :=
theorem BSD_Hasse_OPEN_p9433 : BSD_Hasse_OPEN 9433 :=
theorem BSD_Hasse_OPEN_p9437 : BSD_Hasse_OPEN 9437 :=
theorem BSD_Hasse_OPEN_p9439 : BSD_Hasse_OPEN 9439 :=
theorem BSD_Hasse_OPEN_p9461 : BSD_Hasse_OPEN 9461 :=
theorem BSD_Hasse_OPEN_p9463 : BSD_Hasse_OPEN 9463 :=
theorem BSD_Hasse_OPEN_p9467 : BSD_Hasse_OPEN 9467 :=
theorem BSD_Hasse_OPEN_p9473 : BSD_Hasse_OPEN 9473 :=
theorem BSD_Hasse_OPEN_p9479 : BSD_Hasse_OPEN 9479 :=
theorem BSD_Hasse_OPEN_p9491 : BSD_Hasse_OPEN 9491 :=
theorem BSD_Hasse_OPEN_p9497 : BSD_Hasse_OPEN 9497 :=
theorem BSD_Hasse_OPEN_p9511 : BSD_Hasse_OPEN 9511 :=
theorem BSD_Hasse_OPEN_p9521 : BSD_Hasse_OPEN 9521 :=
theorem BSD_Hasse_OPEN_p9533 : BSD_Hasse_OPEN 9533 :=
theorem BSD_Hasse_OPEN_p9539 : BSD_Hasse_OPEN 9539 :=
theorem BSD_Hasse_OPEN_p9547 : BSD_Hasse_OPEN 9547 :=
theorem BSD_Hasse_OPEN_p9551 : BSD_Hasse_OPEN 9551 :=
theorem BSD_Hasse_OPEN_p9587 : BSD_Hasse_OPEN 9587 :=
theorem BSD_Hasse_OPEN_p9601 : BSD_Hasse_OPEN 9601 :=
theorem BSD_Hasse_OPEN_p9613 : BSD_Hasse_OPEN 9613 :=
theorem BSD_Hasse_OPEN_p9619 : BSD_Hasse_OPEN 9619 :=
theorem BSD_Hasse_OPEN_p9623 : BSD_Hasse_OPEN 9623 :=
theorem BSD_Hasse_OPEN_p9629 : BSD_Hasse_OPEN 9629 :=
theorem BSD_Hasse_OPEN_p9631 : BSD_Hasse_OPEN 9631 :=
theorem BSD_Hasse_OPEN_p9643 : BSD_Hasse_OPEN 9643 :=
theorem BSD_Hasse_OPEN_p9649 : BSD_Hasse_OPEN 9649 :=
theorem BSD_Hasse_OPEN_p9661 : BSD_Hasse_OPEN 9661 :=
theorem BSD_Hasse_OPEN_p9677 : BSD_Hasse_OPEN 9677 :=
theorem BSD_Hasse_OPEN_p9679 : BSD_Hasse_OPEN 9679 :=
theorem BSD_Hasse_OPEN_p9689 : BSD_Hasse_OPEN 9689 :=
theorem BSD_Hasse_OPEN_p9697 : BSD_Hasse_OPEN 9697 :=
theorem BSD_Hasse_OPEN_p9719 : BSD_Hasse_OPEN 9719 :=
theorem BSD_Hasse_OPEN_p9721 : BSD_Hasse_OPEN 9721 :=
theorem BSD_Hasse_OPEN_p9733 : BSD_Hasse_OPEN 9733 :=
theorem BSD_Hasse_OPEN_p9739 : BSD_Hasse_OPEN 9739 :=
theorem BSD_Hasse_OPEN_p9743 : BSD_Hasse_OPEN 9743 :=
theorem BSD_Hasse_OPEN_p9749 : BSD_Hasse_OPEN 9749 :=
theorem BSD_Hasse_OPEN_p9767 : BSD_Hasse_OPEN 9767 :=
theorem BSD_Hasse_OPEN_p9769 : BSD_Hasse_OPEN 9769 :=
theorem BSD_Hasse_OPEN_p9781 : BSD_Hasse_OPEN 9781 :=
theorem BSD_Hasse_OPEN_p9787 : BSD_Hasse_OPEN 9787 :=
theorem BSD_Hasse_OPEN_p9791 : BSD_Hasse_OPEN 9791 :=
theorem BSD_Hasse_OPEN_p9803 : BSD_Hasse_OPEN 9803 :=
theorem BSD_Hasse_OPEN_p9811 : BSD_Hasse_OPEN 9811 :=
theorem BSD_Hasse_OPEN_p9817 : BSD_Hasse_OPEN 9817 :=
theorem BSD_Hasse_OPEN_p9829 : BSD_Hasse_OPEN 9829 :=
theorem BSD_Hasse_OPEN_p9833 : BSD_Hasse_OPEN 9833 :=
theorem BSD_Hasse_OPEN_p9839 : BSD_Hasse_OPEN 9839 :=
theorem BSD_Hasse_OPEN_p9851 : BSD_Hasse_OPEN 9851 :=
theorem BSD_Hasse_OPEN_p9857 : BSD_Hasse_OPEN 9857 :=
theorem BSD_Hasse_OPEN_p9859 : BSD_Hasse_OPEN 9859 :=
theorem BSD_Hasse_OPEN_p9871 : BSD_Hasse_OPEN 9871 :=
theorem BSD_Hasse_OPEN_p9883 : BSD_Hasse_OPEN 9883 :=
theorem BSD_Hasse_OPEN_p9887 : BSD_Hasse_OPEN 9887 :=
theorem BSD_Hasse_OPEN_p9901 : BSD_Hasse_OPEN 9901 :=
theorem BSD_Hasse_OPEN_p9907 : BSD_Hasse_OPEN 9907 :=
theorem BSD_Hasse_OPEN_p9923 : BSD_Hasse_OPEN 9923 :=
theorem BSD_Hasse_OPEN_p9929 : BSD_Hasse_OPEN 9929 :=
theorem BSD_Hasse_OPEN_p9931 : BSD_Hasse_OPEN 9931 :=
theorem BSD_Hasse_OPEN_p9941 : BSD_Hasse_OPEN 9941 :=
theorem BSD_Hasse_OPEN_p9949 : BSD_Hasse_OPEN 9949 :=
theorem BSD_Hasse_OPEN_p9967 : BSD_Hasse_OPEN 9967 :=
theorem BSD_Hasse_OPEN_p9973 : BSD_Hasse_OPEN 9973 :=

end HassePrimeSet

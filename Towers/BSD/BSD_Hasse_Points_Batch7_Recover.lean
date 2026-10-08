/- Batch 7 affine counts. `a_p = p - (E143_Finset p).card`.
   The cardinality is `native_decide` of the Euler sum `affineFastCard`,
   identified with `E143_Finset` by `E143_card_eq_fast`.
   These are the quadratics at these primes. Not Hasse for every prime. No sorry.
-/

import Towers.BSD.BSD_AffineCount_Fast
import Towers.BSD.BSD_Frobenius_Fact_Instances

set_option maxHeartbeats 0

namespace Towers.BSD

theorem BSD_E143_card_p4999 : (E143_Finset 4999).card = 5111 := by  -- recorded card 5112
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5003 : (E143_Finset 5003).card = 5106 := by  -- recorded card 5107
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5009 : (E143_Finset 5009).card = 5002 := by  -- recorded card 5003
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5081 : (E143_Finset 5081).card = 5099 := by  -- recorded card 5100
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5087 : (E143_Finset 5087).card = 5190 := by  -- recorded card 5191
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5099 : (E143_Finset 5099).card = 4987 := by  -- recorded card 4988
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5171 : (E143_Finset 5171).card = 5074 := by  -- recorded card 5075
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5179 : (E143_Finset 5179).card = 5163 := by  -- recorded card 5164
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5189 : (E143_Finset 5189).card = 5225 := by  -- recorded card 5226
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5273 : (E143_Finset 5273).card = 5408 := by  -- recorded card 5409
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5279 : (E143_Finset 5279).card = 5343 := by  -- recorded card 5344
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5281 : (E143_Finset 5281).card = 5264 := by  -- recorded card 5265
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5381 : (E143_Finset 5381).card = 5369 := by  -- recorded card 5370
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5387 : (E143_Finset 5387).card = 5407 := by  -- recorded card 5408
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5393 : (E143_Finset 5393).card = 5414 := by  -- recorded card 5415
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5441 : (E143_Finset 5441).card = 5389 := by  -- recorded card 5390
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5443 : (E143_Finset 5443).card = 5350 := by  -- recorded card 5351
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5449 : (E143_Finset 5449).card = 5324 := by  -- recorded card 5325
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5519 : (E143_Finset 5519).card = 5453 := by  -- recorded card 5454
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5521 : (E143_Finset 5521).card = 5497 := by  -- recorded card 5498
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5527 : (E143_Finset 5527).card = 5547 := by  -- recorded card 5548
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5623 : (E143_Finset 5623).card = 5701 := by  -- recorded card 5702
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5639 : (E143_Finset 5639).card = 5563 := by  -- recorded card 5564
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5641 : (E143_Finset 5641).card = 5672 := by  -- recorded card 5673
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5689 : (E143_Finset 5689).card = 5717 := by  -- recorded card 5718
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5693 : (E143_Finset 5693).card = 5765 := by  -- recorded card 5766
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5701 : (E143_Finset 5701).card = 5626 := by  -- recorded card 5627
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p569 : (E143_Finset 569).card = 601 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p571 : (E143_Finset 571).card = 531 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p577 : (E143_Finset 577).card = 546 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5783 : (E143_Finset 5783).card = 5769 := by  -- recorded card 5770
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5791 : (E143_Finset 5791).card = 5715 := by  -- recorded card 5716
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5801 : (E143_Finset 5801).card = 5751 := by  -- recorded card 5752
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5851 : (E143_Finset 5851).card = 5969 := by  -- recorded card 5970
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5857 : (E143_Finset 5857).card = 5792 := by  -- recorded card 5793
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5861 : (E143_Finset 5861).card = 5867 := by  -- recorded card 5868
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5927 : (E143_Finset 5927).card = 5876 := by  -- recorded card 5877
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5939 : (E143_Finset 5939).card = 5865 := by  -- recorded card 5866
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p5953 : (E143_Finset 5953).card = 5881 := by  -- recorded card 5882
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6047 : (E143_Finset 6047).card = 6007 := by  -- recorded card 6008
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6053 : (E143_Finset 6053).card = 5975 := by  -- recorded card 5976
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6067 : (E143_Finset 6067).card = 6033 := by  -- recorded card 6034
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6131 : (E143_Finset 6131).card = 6136 := by  -- recorded card 6137
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6133 : (E143_Finset 6133).card = 6149 := by  -- recorded card 6150
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6143 : (E143_Finset 6143).card = 6051 := by  -- recorded card 6052
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p619 : (E143_Finset 619).card = 626 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p631 : (E143_Finset 631).card = 658 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p641 : (E143_Finset 641).card = 674 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6217 : (E143_Finset 6217).card = 6275 := by  -- recorded card 6276
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6221 : (E143_Finset 6221).card = 6251 := by  -- recorded card 6252
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6229 : (E143_Finset 6229).card = 6278 := by  -- recorded card 6279
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6299 : (E143_Finset 6299).card = 6269 := by  -- recorded card 6270
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6301 : (E143_Finset 6301).card = 6292 := by  -- recorded card 6293
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6311 : (E143_Finset 6311).card = 6383 := by  -- recorded card 6384
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6361 : (E143_Finset 6361).card = 6467 := by  -- recorded card 6468
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6367 : (E143_Finset 6367).card = 6399 := by  -- recorded card 6400
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6373 : (E143_Finset 6373).card = 6455 := by  -- recorded card 6456
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6469 : (E143_Finset 6469).card = 6438 := by  -- recorded card 6439
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6473 : (E143_Finset 6473).card = 6440 := by  -- recorded card 6441
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p6481 : (E143_Finset 6481).card = 6335 := by  -- recorded card 6336
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide

theorem BSD_ap_p4999 : a_p 4999 = (-112 : ℤ) := by
  have h := BSD_E143_card_p4999; unfold a_p; omega
theorem BSD_ap_p5003 : a_p 5003 = (-103 : ℤ) := by
  have h := BSD_E143_card_p5003; unfold a_p; omega
theorem BSD_ap_p5009 : a_p 5009 = (7 : ℤ) := by
  have h := BSD_E143_card_p5009; unfold a_p; omega
theorem BSD_ap_p5081 : a_p 5081 = (-18 : ℤ) := by
  have h := BSD_E143_card_p5081; unfold a_p; omega
theorem BSD_ap_p5087 : a_p 5087 = (-103 : ℤ) := by
  have h := BSD_E143_card_p5087; unfold a_p; omega
theorem BSD_ap_p5099 : a_p 5099 = (112 : ℤ) := by
  have h := BSD_E143_card_p5099; unfold a_p; omega
theorem BSD_ap_p5171 : a_p 5171 = (97 : ℤ) := by
  have h := BSD_E143_card_p5171; unfold a_p; omega
theorem BSD_ap_p5179 : a_p 5179 = (16 : ℤ) := by
  have h := BSD_E143_card_p5179; unfold a_p; omega
theorem BSD_ap_p5189 : a_p 5189 = (-36 : ℤ) := by
  have h := BSD_E143_card_p5189; unfold a_p; omega
theorem BSD_ap_p5273 : a_p 5273 = (-135 : ℤ) := by
  have h := BSD_E143_card_p5273; unfold a_p; omega
theorem BSD_ap_p5279 : a_p 5279 = (-64 : ℤ) := by
  have h := BSD_E143_card_p5279; unfold a_p; omega
theorem BSD_ap_p5281 : a_p 5281 = (17 : ℤ) := by
  have h := BSD_E143_card_p5281; unfold a_p; omega
theorem BSD_ap_p5381 : a_p 5381 = (12 : ℤ) := by
  have h := BSD_E143_card_p5381; unfold a_p; omega
theorem BSD_ap_p5387 : a_p 5387 = (-20 : ℤ) := by
  have h := BSD_E143_card_p5387; unfold a_p; omega
theorem BSD_ap_p5393 : a_p 5393 = (-21 : ℤ) := by
  have h := BSD_E143_card_p5393; unfold a_p; omega
theorem BSD_ap_p5441 : a_p 5441 = (52 : ℤ) := by
  have h := BSD_E143_card_p5441; unfold a_p; omega
theorem BSD_ap_p5443 : a_p 5443 = (93 : ℤ) := by
  have h := BSD_E143_card_p5443; unfold a_p; omega
theorem BSD_ap_p5449 : a_p 5449 = (125 : ℤ) := by
  have h := BSD_E143_card_p5449; unfold a_p; omega
theorem BSD_ap_p5519 : a_p 5519 = (66 : ℤ) := by
  have h := BSD_E143_card_p5519; unfold a_p; omega
theorem BSD_ap_p5521 : a_p 5521 = (24 : ℤ) := by
  have h := BSD_E143_card_p5521; unfold a_p; omega
theorem BSD_ap_p5527 : a_p 5527 = (-20 : ℤ) := by
  have h := BSD_E143_card_p5527; unfold a_p; omega
theorem BSD_ap_p5623 : a_p 5623 = (-78 : ℤ) := by
  have h := BSD_E143_card_p5623; unfold a_p; omega
theorem BSD_ap_p5639 : a_p 5639 = (76 : ℤ) := by
  have h := BSD_E143_card_p5639; unfold a_p; omega
theorem BSD_ap_p5641 : a_p 5641 = (-31 : ℤ) := by
  have h := BSD_E143_card_p5641; unfold a_p; omega
theorem BSD_ap_p5689 : a_p 5689 = (-28 : ℤ) := by
  have h := BSD_E143_card_p5689; unfold a_p; omega
theorem BSD_ap_p5693 : a_p 5693 = (-72 : ℤ) := by
  have h := BSD_E143_card_p5693; unfold a_p; omega
theorem BSD_ap_p5701 : a_p 5701 = (75 : ℤ) := by
  have h := BSD_E143_card_p5701; unfold a_p; omega
theorem BSD_ap_p569 : a_p 569 = (-32 : ℤ) := by
  have h := BSD_E143_card_p569; unfold a_p; omega
theorem BSD_ap_p571 : a_p 571 = (40 : ℤ) := by
  have h := BSD_E143_card_p571; unfold a_p; omega
theorem BSD_ap_p577 : a_p 577 = (31 : ℤ) := by
  have h := BSD_E143_card_p577; unfold a_p; omega
theorem BSD_ap_p5783 : a_p 5783 = (14 : ℤ) := by
  have h := BSD_E143_card_p5783; unfold a_p; omega
theorem BSD_ap_p5791 : a_p 5791 = (76 : ℤ) := by
  have h := BSD_E143_card_p5791; unfold a_p; omega
theorem BSD_ap_p5801 : a_p 5801 = (50 : ℤ) := by
  have h := BSD_E143_card_p5801; unfold a_p; omega
theorem BSD_ap_p5851 : a_p 5851 = (-118 : ℤ) := by
  have h := BSD_E143_card_p5851; unfold a_p; omega
theorem BSD_ap_p5857 : a_p 5857 = (65 : ℤ) := by
  have h := BSD_E143_card_p5857; unfold a_p; omega
theorem BSD_ap_p5861 : a_p 5861 = (-6 : ℤ) := by
  have h := BSD_E143_card_p5861; unfold a_p; omega
theorem BSD_ap_p5927 : a_p 5927 = (51 : ℤ) := by
  have h := BSD_E143_card_p5927; unfold a_p; omega
theorem BSD_ap_p5939 : a_p 5939 = (74 : ℤ) := by
  have h := BSD_E143_card_p5939; unfold a_p; omega
theorem BSD_ap_p5953 : a_p 5953 = (72 : ℤ) := by
  have h := BSD_E143_card_p5953; unfold a_p; omega
theorem BSD_ap_p6047 : a_p 6047 = (40 : ℤ) := by
  have h := BSD_E143_card_p6047; unfold a_p; omega
theorem BSD_ap_p6053 : a_p 6053 = (78 : ℤ) := by
  have h := BSD_E143_card_p6053; unfold a_p; omega
theorem BSD_ap_p6067 : a_p 6067 = (34 : ℤ) := by
  have h := BSD_E143_card_p6067; unfold a_p; omega
theorem BSD_ap_p6131 : a_p 6131 = (-5 : ℤ) := by
  have h := BSD_E143_card_p6131; unfold a_p; omega
theorem BSD_ap_p6133 : a_p 6133 = (-16 : ℤ) := by
  have h := BSD_E143_card_p6133; unfold a_p; omega
theorem BSD_ap_p6143 : a_p 6143 = (92 : ℤ) := by
  have h := BSD_E143_card_p6143; unfold a_p; omega
theorem BSD_ap_p619 : a_p 619 = (-7 : ℤ) := by
  have h := BSD_E143_card_p619; unfold a_p; omega
theorem BSD_ap_p631 : a_p 631 = (-27 : ℤ) := by
  have h := BSD_E143_card_p631; unfold a_p; omega
theorem BSD_ap_p641 : a_p 641 = (-33 : ℤ) := by
  have h := BSD_E143_card_p641; unfold a_p; omega
theorem BSD_ap_p6217 : a_p 6217 = (-58 : ℤ) := by
  have h := BSD_E143_card_p6217; unfold a_p; omega
theorem BSD_ap_p6221 : a_p 6221 = (-30 : ℤ) := by
  have h := BSD_E143_card_p6221; unfold a_p; omega
theorem BSD_ap_p6229 : a_p 6229 = (-49 : ℤ) := by
  have h := BSD_E143_card_p6229; unfold a_p; omega
theorem BSD_ap_p6299 : a_p 6299 = (30 : ℤ) := by
  have h := BSD_E143_card_p6299; unfold a_p; omega
theorem BSD_ap_p6301 : a_p 6301 = (9 : ℤ) := by
  have h := BSD_E143_card_p6301; unfold a_p; omega
theorem BSD_ap_p6311 : a_p 6311 = (-72 : ℤ) := by
  have h := BSD_E143_card_p6311; unfold a_p; omega
theorem BSD_ap_p6361 : a_p 6361 = (-106 : ℤ) := by
  have h := BSD_E143_card_p6361; unfold a_p; omega
theorem BSD_ap_p6367 : a_p 6367 = (-32 : ℤ) := by
  have h := BSD_E143_card_p6367; unfold a_p; omega
theorem BSD_ap_p6373 : a_p 6373 = (-82 : ℤ) := by
  have h := BSD_E143_card_p6373; unfold a_p; omega
theorem BSD_ap_p6469 : a_p 6469 = (31 : ℤ) := by
  have h := BSD_E143_card_p6469; unfold a_p; omega
theorem BSD_ap_p6473 : a_p 6473 = (33 : ℤ) := by
  have h := BSD_E143_card_p6473; unfold a_p; omega
theorem BSD_ap_p6481 : a_p 6481 = (146 : ℤ) := by
  have h := BSD_E143_card_p6481; unfold a_p; omega

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

theorem BSD_DegreeNonneg_p569 : BSD_FrobeniusDegreeNonneg_OPEN 569 := fun r => by
  have hap : (a_p 569 : ℝ) = -32 := by exact_mod_cast BSD_ap_p569
  have key : r ^ 2 - (a_p 569 : ℝ) * r + ((569 : ℕ) : ℝ) =
      (r + 32/2) ^ 2 + 1252/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (32 : ℝ)/2)]

theorem BSD_DegreeNonneg_p571 : BSD_FrobeniusDegreeNonneg_OPEN 571 := fun r => by
  have hap : (a_p 571 : ℝ) = 40 := by exact_mod_cast BSD_ap_p571
  have key : r ^ 2 - (a_p 571 : ℝ) * r + ((571 : ℕ) : ℝ) =
      (r - 40/2) ^ 2 + 684/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (40 : ℝ)/2)]

theorem BSD_DegreeNonneg_p577 : BSD_FrobeniusDegreeNonneg_OPEN 577 := fun r => by
  have hap : (a_p 577 : ℝ) = 31 := by exact_mod_cast BSD_ap_p577
  have key : r ^ 2 - (a_p 577 : ℝ) * r + ((577 : ℕ) : ℝ) =
      (r - 31/2) ^ 2 + 1347/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (31 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p619 : BSD_FrobeniusDegreeNonneg_OPEN 619 := fun r => by
  have hap : (a_p 619 : ℝ) = -7 := by exact_mod_cast BSD_ap_p619
  have key : r ^ 2 - (a_p 619 : ℝ) * r + ((619 : ℕ) : ℝ) =
      (r + 7/2) ^ 2 + 2427/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (7 : ℝ)/2)]

theorem BSD_DegreeNonneg_p631 : BSD_FrobeniusDegreeNonneg_OPEN 631 := fun r => by
  have hap : (a_p 631 : ℝ) = -27 := by exact_mod_cast BSD_ap_p631
  have key : r ^ 2 - (a_p 631 : ℝ) * r + ((631 : ℕ) : ℝ) =
      (r + 27/2) ^ 2 + 1795/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (27 : ℝ)/2)]

theorem BSD_DegreeNonneg_p641 : BSD_FrobeniusDegreeNonneg_OPEN 641 := fun r => by
  have hap : (a_p 641 : ℝ) = -33 := by exact_mod_cast BSD_ap_p641
  have key : r ^ 2 - (a_p 641 : ℝ) * r + ((641 : ℕ) : ℝ) =
      (r + 33/2) ^ 2 + 1475/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (33 : ℝ)/2)]

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

end Towers.BSD

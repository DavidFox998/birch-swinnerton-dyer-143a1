/- Batch 9 affine counts. `a_p = p - (E143_Finset p).card`.
   The cardinality is `native_decide` of the Euler sum `affineFastCard`,
   identified with `E143_Finset` by `E143_card_eq_fast`.
   These are the quadratics at these primes. Not Hasse for every prime. No sorry.
-/

import Towers.BSD.BSD_AffineCount_Fast
import Towers.BSD.BSD_Frobenius_Fact_Instances

set_option maxHeartbeats 0

namespace Towers.BSD

theorem BSD_E143_card_p8209 : (E143_Finset 8209).card = 8150 := by  -- recorded card 8151
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8219 : (E143_Finset 8219).card = 8197 := by  -- recorded card 8198
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8221 : (E143_Finset 8221).card = 8206 := by  -- recorded card 8207
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p827 : (E143_Finset 827).card = 777 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p829 : (E143_Finset 829).card = 800 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p839 : (E143_Finset 839).card = 786 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8287 : (E143_Finset 8287).card = 8239 := by  -- recorded card 8240
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8291 : (E143_Finset 8291).card = 8349 := by  -- recorded card 8350
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8293 : (E143_Finset 8293).card = 8159 := by  -- recorded card 8160
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8377 : (E143_Finset 8377).card = 8439 := by  -- recorded card 8440
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8387 : (E143_Finset 8387).card = 8399 := by  -- recorded card 8400
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8389 : (E143_Finset 8389).card = 8497 := by  -- recorded card 8498
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8467 : (E143_Finset 8467).card = 8537 := by  -- recorded card 8538
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8501 : (E143_Finset 8501).card = 8608 := by  -- recorded card 8609
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8513 : (E143_Finset 8513).card = 8597 := by  -- recorded card 8598
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8581 : (E143_Finset 8581).card = 8642 := by  -- recorded card 8643
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8597 : (E143_Finset 8597).card = 8673 := by  -- recorded card 8674
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8599 : (E143_Finset 8599).card = 8641 := by  -- recorded card 8642
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8669 : (E143_Finset 8669).card = 8707 := by  -- recorded card 8708
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8677 : (E143_Finset 8677).card = 8735 := by  -- recorded card 8736
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8681 : (E143_Finset 8681).card = 8639 := by  -- recorded card 8640
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8737 : (E143_Finset 8737).card = 8827 := by  -- recorded card 8828
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8741 : (E143_Finset 8741).card = 8717 := by  -- recorded card 8718
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8747 : (E143_Finset 8747).card = 8917 := by  -- recorded card 8918
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8821 : (E143_Finset 8821).card = 8811 := by  -- recorded card 8812
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8831 : (E143_Finset 8831).card = 8874 := by  -- recorded card 8875
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8837 : (E143_Finset 8837).card = 8678 := by  -- recorded card 8679
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p887 : (E143_Finset 887).card = 875 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p907 : (E143_Finset 907).card = 855 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p911 : (E143_Finset 911).card = 919 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8923 : (E143_Finset 8923).card = 8873 := by  -- recorded card 8874
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8929 : (E143_Finset 8929).card = 8823 := by  -- recorded card 8824
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p8933 : (E143_Finset 8933).card = 9002 := by  -- recorded card 9003
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9007 : (E143_Finset 9007).card = 8864 := by  -- recorded card 8865
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9011 : (E143_Finset 9011).card = 8915 := by  -- recorded card 8916
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9013 : (E143_Finset 9013).card = 8946 := by  -- recorded card 8947
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9103 : (E143_Finset 9103).card = 9169 := by  -- recorded card 9170
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9109 : (E143_Finset 9109).card = 9164 := by  -- recorded card 9165
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9127 : (E143_Finset 9127).card = 9237 := by  -- recorded card 9238
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9187 : (E143_Finset 9187).card = 9329 := by  -- recorded card 9330
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9199 : (E143_Finset 9199).card = 9183 := by  -- recorded card 9184
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9203 : (E143_Finset 9203).card = 9159 := by  -- recorded card 9160
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9281 : (E143_Finset 9281).card = 9437 := by  -- recorded card 9438
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9283 : (E143_Finset 9283).card = 9377 := by  -- recorded card 9378
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9293 : (E143_Finset 9293).card = 9279 := by  -- recorded card 9280
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9371 : (E143_Finset 9371).card = 9383 := by  -- recorded card 9384
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9377 : (E143_Finset 9377).card = 9307 := by  -- recorded card 9308
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9391 : (E143_Finset 9391).card = 9405 := by  -- recorded card 9406
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9437 : (E143_Finset 9437).card = 9489 := by  -- recorded card 9490
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9439 : (E143_Finset 9439).card = 9406 := by  -- recorded card 9407
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9461 : (E143_Finset 9461).card = 9291 := by  -- recorded card 9292
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9521 : (E143_Finset 9521).card = 9571 := by  -- recorded card 9572
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9533 : (E143_Finset 9533).card = 9459 := by  -- recorded card 9460
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9539 : (E143_Finset 9539).card = 9539 := by  -- recorded card 9540
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9629 : (E143_Finset 9629).card = 9492 := by  -- recorded card 9493
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9631 : (E143_Finset 9631).card = 9613 := by  -- recorded card 9614
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p9643 : (E143_Finset 9643).card = 9689 := by  -- recorded card 9690
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p971 : (E143_Finset 971).card = 1020 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p977 : (E143_Finset 977).card = 986 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide
theorem BSD_E143_card_p983 : (E143_Finset 983).card = 1014 := by
  rw [E143_card_eq_fast (hp := by decide)]
  native_decide

theorem BSD_ap_p8209 : a_p 8209 = (59 : ℤ) := by
  have h := BSD_E143_card_p8209; unfold a_p; omega
theorem BSD_ap_p8219 : a_p 8219 = (22 : ℤ) := by
  have h := BSD_E143_card_p8219; unfold a_p; omega
theorem BSD_ap_p8221 : a_p 8221 = (15 : ℤ) := by
  have h := BSD_E143_card_p8221; unfold a_p; omega
theorem BSD_ap_p827 : a_p 827 = (50 : ℤ) := by
  have h := BSD_E143_card_p827; unfold a_p; omega
theorem BSD_ap_p829 : a_p 829 = (29 : ℤ) := by
  have h := BSD_E143_card_p829; unfold a_p; omega
theorem BSD_ap_p839 : a_p 839 = (53 : ℤ) := by
  have h := BSD_E143_card_p839; unfold a_p; omega
theorem BSD_ap_p8287 : a_p 8287 = (48 : ℤ) := by
  have h := BSD_E143_card_p8287; unfold a_p; omega
theorem BSD_ap_p8291 : a_p 8291 = (-58 : ℤ) := by
  have h := BSD_E143_card_p8291; unfold a_p; omega
theorem BSD_ap_p8293 : a_p 8293 = (134 : ℤ) := by
  have h := BSD_E143_card_p8293; unfold a_p; omega
theorem BSD_ap_p8377 : a_p 8377 = (-62 : ℤ) := by
  have h := BSD_E143_card_p8377; unfold a_p; omega
theorem BSD_ap_p8387 : a_p 8387 = (-12 : ℤ) := by
  have h := BSD_E143_card_p8387; unfold a_p; omega
theorem BSD_ap_p8389 : a_p 8389 = (-108 : ℤ) := by
  have h := BSD_E143_card_p8389; unfold a_p; omega
theorem BSD_ap_p8467 : a_p 8467 = (-70 : ℤ) := by
  have h := BSD_E143_card_p8467; unfold a_p; omega
theorem BSD_ap_p8501 : a_p 8501 = (-107 : ℤ) := by
  have h := BSD_E143_card_p8501; unfold a_p; omega
theorem BSD_ap_p8513 : a_p 8513 = (-84 : ℤ) := by
  have h := BSD_E143_card_p8513; unfold a_p; omega
theorem BSD_ap_p8581 : a_p 8581 = (-61 : ℤ) := by
  have h := BSD_E143_card_p8581; unfold a_p; omega
theorem BSD_ap_p8597 : a_p 8597 = (-76 : ℤ) := by
  have h := BSD_E143_card_p8597; unfold a_p; omega
theorem BSD_ap_p8599 : a_p 8599 = (-42 : ℤ) := by
  have h := BSD_E143_card_p8599; unfold a_p; omega
theorem BSD_ap_p8669 : a_p 8669 = (-38 : ℤ) := by
  have h := BSD_E143_card_p8669; unfold a_p; omega
theorem BSD_ap_p8677 : a_p 8677 = (-58 : ℤ) := by
  have h := BSD_E143_card_p8677; unfold a_p; omega
theorem BSD_ap_p8681 : a_p 8681 = (42 : ℤ) := by
  have h := BSD_E143_card_p8681; unfold a_p; omega
theorem BSD_ap_p8737 : a_p 8737 = (-90 : ℤ) := by
  have h := BSD_E143_card_p8737; unfold a_p; omega
theorem BSD_ap_p8741 : a_p 8741 = (24 : ℤ) := by
  have h := BSD_E143_card_p8741; unfold a_p; omega
theorem BSD_ap_p8747 : a_p 8747 = (-170 : ℤ) := by
  have h := BSD_E143_card_p8747; unfold a_p; omega
theorem BSD_ap_p8821 : a_p 8821 = (10 : ℤ) := by
  have h := BSD_E143_card_p8821; unfold a_p; omega
theorem BSD_ap_p8831 : a_p 8831 = (-43 : ℤ) := by
  have h := BSD_E143_card_p8831; unfold a_p; omega
theorem BSD_ap_p8837 : a_p 8837 = (159 : ℤ) := by
  have h := BSD_E143_card_p8837; unfold a_p; omega
theorem BSD_ap_p887 : a_p 887 = (12 : ℤ) := by
  have h := BSD_E143_card_p887; unfold a_p; omega
theorem BSD_ap_p907 : a_p 907 = (52 : ℤ) := by
  have h := BSD_E143_card_p907; unfold a_p; omega
theorem BSD_ap_p911 : a_p 911 = (-8 : ℤ) := by
  have h := BSD_E143_card_p911; unfold a_p; omega
theorem BSD_ap_p8923 : a_p 8923 = (50 : ℤ) := by
  have h := BSD_E143_card_p8923; unfold a_p; omega
theorem BSD_ap_p8929 : a_p 8929 = (106 : ℤ) := by
  have h := BSD_E143_card_p8929; unfold a_p; omega
theorem BSD_ap_p8933 : a_p 8933 = (-69 : ℤ) := by
  have h := BSD_E143_card_p8933; unfold a_p; omega
theorem BSD_ap_p9007 : a_p 9007 = (143 : ℤ) := by
  have h := BSD_E143_card_p9007; unfold a_p; omega
theorem BSD_ap_p9011 : a_p 9011 = (96 : ℤ) := by
  have h := BSD_E143_card_p9011; unfold a_p; omega
theorem BSD_ap_p9013 : a_p 9013 = (67 : ℤ) := by
  have h := BSD_E143_card_p9013; unfold a_p; omega
theorem BSD_ap_p9103 : a_p 9103 = (-66 : ℤ) := by
  have h := BSD_E143_card_p9103; unfold a_p; omega
theorem BSD_ap_p9109 : a_p 9109 = (-55 : ℤ) := by
  have h := BSD_E143_card_p9109; unfold a_p; omega
theorem BSD_ap_p9127 : a_p 9127 = (-110 : ℤ) := by
  have h := BSD_E143_card_p9127; unfold a_p; omega
theorem BSD_ap_p9187 : a_p 9187 = (-142 : ℤ) := by
  have h := BSD_E143_card_p9187; unfold a_p; omega
theorem BSD_ap_p9199 : a_p 9199 = (16 : ℤ) := by
  have h := BSD_E143_card_p9199; unfold a_p; omega
theorem BSD_ap_p9203 : a_p 9203 = (44 : ℤ) := by
  have h := BSD_E143_card_p9203; unfold a_p; omega
theorem BSD_ap_p9281 : a_p 9281 = (-156 : ℤ) := by
  have h := BSD_E143_card_p9281; unfold a_p; omega
theorem BSD_ap_p9283 : a_p 9283 = (-94 : ℤ) := by
  have h := BSD_E143_card_p9283; unfold a_p; omega
theorem BSD_ap_p9293 : a_p 9293 = (14 : ℤ) := by
  have h := BSD_E143_card_p9293; unfold a_p; omega
theorem BSD_ap_p9371 : a_p 9371 = (-12 : ℤ) := by
  have h := BSD_E143_card_p9371; unfold a_p; omega
theorem BSD_ap_p9377 : a_p 9377 = (70 : ℤ) := by
  have h := BSD_E143_card_p9377; unfold a_p; omega
theorem BSD_ap_p9391 : a_p 9391 = (-14 : ℤ) := by
  have h := BSD_E143_card_p9391; unfold a_p; omega
theorem BSD_ap_p9437 : a_p 9437 = (-52 : ℤ) := by
  have h := BSD_E143_card_p9437; unfold a_p; omega
theorem BSD_ap_p9439 : a_p 9439 = (33 : ℤ) := by
  have h := BSD_E143_card_p9439; unfold a_p; omega
theorem BSD_ap_p9461 : a_p 9461 = (170 : ℤ) := by
  have h := BSD_E143_card_p9461; unfold a_p; omega
theorem BSD_ap_p9521 : a_p 9521 = (-50 : ℤ) := by
  have h := BSD_E143_card_p9521; unfold a_p; omega
theorem BSD_ap_p9533 : a_p 9533 = (74 : ℤ) := by
  have h := BSD_E143_card_p9533; unfold a_p; omega
theorem BSD_ap_p9539 : a_p 9539 = (0 : ℤ) := by
  have h := BSD_E143_card_p9539; unfold a_p; omega
theorem BSD_ap_p9629 : a_p 9629 = (137 : ℤ) := by
  have h := BSD_E143_card_p9629; unfold a_p; omega
theorem BSD_ap_p9631 : a_p 9631 = (18 : ℤ) := by
  have h := BSD_E143_card_p9631; unfold a_p; omega
theorem BSD_ap_p9643 : a_p 9643 = (-46 : ℤ) := by
  have h := BSD_E143_card_p9643; unfold a_p; omega
theorem BSD_ap_p971 : a_p 971 = (-49 : ℤ) := by
  have h := BSD_E143_card_p971; unfold a_p; omega
theorem BSD_ap_p977 : a_p 977 = (-9 : ℤ) := by
  have h := BSD_E143_card_p977; unfold a_p; omega
theorem BSD_ap_p983 : a_p 983 = (-31 : ℤ) := by
  have h := BSD_E143_card_p983; unfold a_p; omega

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

theorem BSD_DegreeNonneg_p827 : BSD_FrobeniusDegreeNonneg_OPEN 827 := fun r => by
  have hap : (a_p 827 : ℝ) = 50 := by exact_mod_cast BSD_ap_p827
  have key : r ^ 2 - (a_p 827 : ℝ) * r + ((827 : ℕ) : ℝ) =
      (r - 50/2) ^ 2 + 808/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (50 : ℝ)/2)]

theorem BSD_DegreeNonneg_p829 : BSD_FrobeniusDegreeNonneg_OPEN 829 := fun r => by
  have hap : (a_p 829 : ℝ) = 29 := by exact_mod_cast BSD_ap_p829
  have key : r ^ 2 - (a_p 829 : ℝ) * r + ((829 : ℕ) : ℝ) =
      (r - 29/2) ^ 2 + 2475/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (29 : ℝ)/2)]

theorem BSD_DegreeNonneg_p839 : BSD_FrobeniusDegreeNonneg_OPEN 839 := fun r => by
  have hap : (a_p 839 : ℝ) = 53 := by exact_mod_cast BSD_ap_p839
  have key : r ^ 2 - (a_p 839 : ℝ) * r + ((839 : ℕ) : ℝ) =
      (r - 53/2) ^ 2 + 547/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (53 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p887 : BSD_FrobeniusDegreeNonneg_OPEN 887 := fun r => by
  have hap : (a_p 887 : ℝ) = 12 := by exact_mod_cast BSD_ap_p887
  have key : r ^ 2 - (a_p 887 : ℝ) * r + ((887 : ℕ) : ℝ) =
      (r - 12/2) ^ 2 + 3404/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (12 : ℝ)/2)]

theorem BSD_DegreeNonneg_p907 : BSD_FrobeniusDegreeNonneg_OPEN 907 := fun r => by
  have hap : (a_p 907 : ℝ) = 52 := by exact_mod_cast BSD_ap_p907
  have key : r ^ 2 - (a_p 907 : ℝ) * r + ((907 : ℕ) : ℝ) =
      (r - 52/2) ^ 2 + 924/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (52 : ℝ)/2)]

theorem BSD_DegreeNonneg_p911 : BSD_FrobeniusDegreeNonneg_OPEN 911 := fun r => by
  have hap : (a_p 911 : ℝ) = -8 := by exact_mod_cast BSD_ap_p911
  have key : r ^ 2 - (a_p 911 : ℝ) * r + ((911 : ℕ) : ℝ) =
      (r + 8/2) ^ 2 + 3580/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (8 : ℝ)/2)]

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

theorem BSD_DegreeNonneg_p971 : BSD_FrobeniusDegreeNonneg_OPEN 971 := fun r => by
  have hap : (a_p 971 : ℝ) = -49 := by exact_mod_cast BSD_ap_p971
  have key : r ^ 2 - (a_p 971 : ℝ) * r + ((971 : ℕ) : ℝ) =
      (r + 49/2) ^ 2 + 1483/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (49 : ℝ)/2)]

theorem BSD_DegreeNonneg_p977 : BSD_FrobeniusDegreeNonneg_OPEN 977 := fun r => by
  have hap : (a_p 977 : ℝ) = -9 := by exact_mod_cast BSD_ap_p977
  have key : r ^ 2 - (a_p 977 : ℝ) * r + ((977 : ℕ) : ℝ) =
      (r + 9/2) ^ 2 + 3827/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (9 : ℝ)/2)]

theorem BSD_DegreeNonneg_p983 : BSD_FrobeniusDegreeNonneg_OPEN 983 := fun r => by
  have hap : (a_p 983 : ℝ) = -31 := by exact_mod_cast BSD_ap_p983
  have key : r ^ 2 - (a_p 983 : ℝ) * r + ((983 : ℕ) : ℝ) =
      (r + 31/2) ^ 2 + 2971/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (31 : ℝ)/2)]

end Towers.BSD

/- Finite affine counts for the Batch 5 primes whose assessed props were `True`.
   `a_p` is the clean definition `(p : ℤ) - (E143_Finset p).card`.
   The hasseprimset card theorems for the primes above 1000 are one larger
   than this count, so those card literals are not used.
   `BSD_ap_pN` in hasseprimset equals this `p - card`.
   Each cardinality below is checked by `native_decide`.
   These are the quadratic forms at these primes. Not Hasse for every prime.
   No sorry.
-/

import Towers.BSD.BSD_Frobenius_Certificate_Clean

set_option maxHeartbeats 0

namespace Towers.BSD

instance instFact_prime_2113 : Fact (Nat.Prime 2113) := ⟨by native_decide⟩
instance instFact_prime_2129 : Fact (Nat.Prime 2129) := ⟨by native_decide⟩
instance instFact_prime_2131 : Fact (Nat.Prime 2131) := ⟨by native_decide⟩
instance instFact_prime_2207 : Fact (Nat.Prime 2207) := ⟨by native_decide⟩
instance instFact_prime_2213 : Fact (Nat.Prime 2213) := ⟨by native_decide⟩
instance instFact_prime_2221 : Fact (Nat.Prime 2221) := ⟨by native_decide⟩
instance instFact_prime_2281 : Fact (Nat.Prime 2281) := ⟨by native_decide⟩
instance instFact_prime_2287 : Fact (Nat.Prime 2287) := ⟨by native_decide⟩
instance instFact_prime_2293 : Fact (Nat.Prime 2293) := ⟨by native_decide⟩
instance instFact_prime_2351 : Fact (Nat.Prime 2351) := ⟨by native_decide⟩
instance instFact_prime_2357 : Fact (Nat.Prime 2357) := ⟨by native_decide⟩
instance instFact_prime_2371 : Fact (Nat.Prime 2371) := ⟨by native_decide⟩
instance instFact_prime_2417 : Fact (Nat.Prime 2417) := ⟨by native_decide⟩
instance instFact_prime_2423 : Fact (Nat.Prime 2423) := ⟨by native_decide⟩
instance instFact_prime_2437 : Fact (Nat.Prime 2437) := ⟨by native_decide⟩
instance instFact_prime_2521 : Fact (Nat.Prime 2521) := ⟨by native_decide⟩
instance instFact_prime_2531 : Fact (Nat.Prime 2531) := ⟨by native_decide⟩
instance instFact_prime_2539 : Fact (Nat.Prime 2539) := ⟨by native_decide⟩
instance instFact_prime_2609 : Fact (Nat.Prime 2609) := ⟨by native_decide⟩
instance instFact_prime_2617 : Fact (Nat.Prime 2617) := ⟨by native_decide⟩
instance instFact_prime_2621 : Fact (Nat.Prime 2621) := ⟨by native_decide⟩
instance instFact_prime_2683 : Fact (Nat.Prime 2683) := ⟨by native_decide⟩
instance instFact_prime_2687 : Fact (Nat.Prime 2687) := ⟨by native_decide⟩
instance instFact_prime_2689 : Fact (Nat.Prime 2689) := ⟨by native_decide⟩
instance instFact_prime_2731 : Fact (Nat.Prime 2731) := ⟨by native_decide⟩
instance instFact_prime_2741 : Fact (Nat.Prime 2741) := ⟨by native_decide⟩
instance instFact_prime_2749 : Fact (Nat.Prime 2749) := ⟨by native_decide⟩
instance instFact_prime_2803 : Fact (Nat.Prime 2803) := ⟨by native_decide⟩
instance instFact_prime_2819 : Fact (Nat.Prime 2819) := ⟨by native_decide⟩
instance instFact_prime_2833 : Fact (Nat.Prime 2833) := ⟨by native_decide⟩
instance instFact_prime_2897 : Fact (Nat.Prime 2897) := ⟨by native_decide⟩
instance instFact_prime_2903 : Fact (Nat.Prime 2903) := ⟨by native_decide⟩
instance instFact_prime_2909 : Fact (Nat.Prime 2909) := ⟨by native_decide⟩
instance instFact_prime_2971 : Fact (Nat.Prime 2971) := ⟨by native_decide⟩
instance instFact_prime_2999 : Fact (Nat.Prime 2999) := ⟨by native_decide⟩
instance instFact_prime_3001 : Fact (Nat.Prime 3001) := ⟨by native_decide⟩
instance instFact_prime_3067 : Fact (Nat.Prime 3067) := ⟨by native_decide⟩
instance instFact_prime_3079 : Fact (Nat.Prime 3079) := ⟨by native_decide⟩
instance instFact_prime_3083 : Fact (Nat.Prime 3083) := ⟨by native_decide⟩
instance instFact_prime_311 : Fact (Nat.Prime 311) := ⟨by native_decide⟩
instance instFact_prime_313 : Fact (Nat.Prime 313) := ⟨by native_decide⟩
instance instFact_prime_317 : Fact (Nat.Prime 317) := ⟨by native_decide⟩
instance instFact_prime_3169 : Fact (Nat.Prime 3169) := ⟨by native_decide⟩
instance instFact_prime_3181 : Fact (Nat.Prime 3181) := ⟨by native_decide⟩
instance instFact_prime_3187 : Fact (Nat.Prime 3187) := ⟨by native_decide⟩
instance instFact_prime_3253 : Fact (Nat.Prime 3253) := ⟨by native_decide⟩
instance instFact_prime_3257 : Fact (Nat.Prime 3257) := ⟨by native_decide⟩
instance instFact_prime_3259 : Fact (Nat.Prime 3259) := ⟨by native_decide⟩
instance instFact_prime_3329 : Fact (Nat.Prime 3329) := ⟨by native_decide⟩
instance instFact_prime_3331 : Fact (Nat.Prime 3331) := ⟨by native_decide⟩
instance instFact_prime_3343 : Fact (Nat.Prime 3343) := ⟨by native_decide⟩
instance instFact_prime_3407 : Fact (Nat.Prime 3407) := ⟨by native_decide⟩
instance instFact_prime_3413 : Fact (Nat.Prime 3413) := ⟨by native_decide⟩
instance instFact_prime_3433 : Fact (Nat.Prime 3433) := ⟨by native_decide⟩
instance instFact_prime_3499 : Fact (Nat.Prime 3499) := ⟨by native_decide⟩
instance instFact_prime_3511 : Fact (Nat.Prime 3511) := ⟨by native_decide⟩
instance instFact_prime_3517 : Fact (Nat.Prime 3517) := ⟨by native_decide⟩

theorem BSD_E143_card_p2113 : (E143_Finset 2113).card = 2067 := by native_decide
theorem BSD_E143_card_p2129 : (E143_Finset 2129).card = 2195 := by native_decide
theorem BSD_E143_card_p2131 : (E143_Finset 2131).card = 2105 := by native_decide
theorem BSD_E143_card_p2207 : (E143_Finset 2207).card = 2129 := by native_decide
theorem BSD_E143_card_p2213 : (E143_Finset 2213).card = 2161 := by native_decide
theorem BSD_E143_card_p2221 : (E143_Finset 2221).card = 2159 := by native_decide
theorem BSD_E143_card_p2281 : (E143_Finset 2281).card = 2280 := by native_decide
theorem BSD_E143_card_p2287 : (E143_Finset 2287).card = 2301 := by native_decide
theorem BSD_E143_card_p2293 : (E143_Finset 2293).card = 2322 := by native_decide
theorem BSD_E143_card_p2351 : (E143_Finset 2351).card = 2297 := by native_decide
theorem BSD_E143_card_p2357 : (E143_Finset 2357).card = 2290 := by native_decide
theorem BSD_E143_card_p2371 : (E143_Finset 2371).card = 2341 := by native_decide
theorem BSD_E143_card_p2417 : (E143_Finset 2417).card = 2441 := by native_decide
theorem BSD_E143_card_p2423 : (E143_Finset 2423).card = 2348 := by native_decide
theorem BSD_E143_card_p2437 : (E143_Finset 2437).card = 2397 := by native_decide
theorem BSD_E143_card_p2521 : (E143_Finset 2521).card = 2571 := by native_decide
theorem BSD_E143_card_p2531 : (E143_Finset 2531).card = 2534 := by native_decide
theorem BSD_E143_card_p2539 : (E143_Finset 2539).card = 2543 := by native_decide
theorem BSD_E143_card_p2609 : (E143_Finset 2609).card = 2529 := by native_decide
theorem BSD_E143_card_p2617 : (E143_Finset 2617).card = 2635 := by native_decide
theorem BSD_E143_card_p2621 : (E143_Finset 2621).card = 2699 := by native_decide
theorem BSD_E143_card_p2683 : (E143_Finset 2683).card = 2735 := by native_decide
theorem BSD_E143_card_p2687 : (E143_Finset 2687).card = 2680 := by native_decide
theorem BSD_E143_card_p2689 : (E143_Finset 2689).card = 2766 := by native_decide
theorem BSD_E143_card_p2731 : (E143_Finset 2731).card = 2799 := by native_decide
theorem BSD_E143_card_p2741 : (E143_Finset 2741).card = 2719 := by native_decide
theorem BSD_E143_card_p2749 : (E143_Finset 2749).card = 2723 := by native_decide
theorem BSD_E143_card_p2803 : (E143_Finset 2803).card = 2775 := by native_decide
theorem BSD_E143_card_p2819 : (E143_Finset 2819).card = 2834 := by native_decide
theorem BSD_E143_card_p2833 : (E143_Finset 2833).card = 2807 := by native_decide
theorem BSD_E143_card_p2897 : (E143_Finset 2897).card = 2871 := by native_decide
theorem BSD_E143_card_p2903 : (E143_Finset 2903).card = 2877 := by native_decide
theorem BSD_E143_card_p2909 : (E143_Finset 2909).card = 2934 := by native_decide
theorem BSD_E143_card_p2971 : (E143_Finset 2971).card = 2958 := by native_decide
theorem BSD_E143_card_p2999 : (E143_Finset 2999).card = 3035 := by native_decide
theorem BSD_E143_card_p3001 : (E143_Finset 3001).card = 3000 := by native_decide
theorem BSD_E143_card_p3067 : (E143_Finset 3067).card = 3074 := by native_decide
theorem BSD_E143_card_p3079 : (E143_Finset 3079).card = 3117 := by native_decide
theorem BSD_E143_card_p3083 : (E143_Finset 3083).card = 3080 := by native_decide
theorem BSD_E143_card_p311 : (E143_Finset 311).card = 303 := by native_decide
theorem BSD_E143_card_p313 : (E143_Finset 313).card = 310 := by native_decide
theorem BSD_E143_card_p317 : (E143_Finset 317).card = 318 := by native_decide
theorem BSD_E143_card_p3169 : (E143_Finset 3169).card = 3176 := by native_decide
theorem BSD_E143_card_p3181 : (E143_Finset 3181).card = 3193 := by native_decide
theorem BSD_E143_card_p3187 : (E143_Finset 3187).card = 3267 := by native_decide
theorem BSD_E143_card_p3253 : (E143_Finset 3253).card = 3189 := by native_decide
theorem BSD_E143_card_p3257 : (E143_Finset 3257).card = 3339 := by native_decide
theorem BSD_E143_card_p3259 : (E143_Finset 3259).card = 3263 := by native_decide
theorem BSD_E143_card_p3329 : (E143_Finset 3329).card = 3271 := by native_decide
theorem BSD_E143_card_p3331 : (E143_Finset 3331).card = 3218 := by native_decide
theorem BSD_E143_card_p3343 : (E143_Finset 3343).card = 3301 := by native_decide
theorem BSD_E143_card_p3407 : (E143_Finset 3407).card = 3313 := by native_decide
theorem BSD_E143_card_p3413 : (E143_Finset 3413).card = 3322 := by native_decide
theorem BSD_E143_card_p3433 : (E143_Finset 3433).card = 3419 := by native_decide
theorem BSD_E143_card_p3499 : (E143_Finset 3499).card = 3591 := by native_decide
theorem BSD_E143_card_p3511 : (E143_Finset 3511).card = 3543 := by native_decide
theorem BSD_E143_card_p3517 : (E143_Finset 3517).card = 3499 := by native_decide

theorem BSD_ap_p2113 : a_p 2113 = (46 : ℤ) := by
  have h := BSD_E143_card_p2113; unfold a_p; omega
theorem BSD_ap_p2129 : a_p 2129 = (-66 : ℤ) := by
  have h := BSD_E143_card_p2129; unfold a_p; omega
theorem BSD_ap_p2131 : a_p 2131 = (26 : ℤ) := by
  have h := BSD_E143_card_p2131; unfold a_p; omega
theorem BSD_ap_p2207 : a_p 2207 = (78 : ℤ) := by
  have h := BSD_E143_card_p2207; unfold a_p; omega
theorem BSD_ap_p2213 : a_p 2213 = (52 : ℤ) := by
  have h := BSD_E143_card_p2213; unfold a_p; omega
theorem BSD_ap_p2221 : a_p 2221 = (62 : ℤ) := by
  have h := BSD_E143_card_p2221; unfold a_p; omega
theorem BSD_ap_p2281 : a_p 2281 = (1 : ℤ) := by
  have h := BSD_E143_card_p2281; unfold a_p; omega
theorem BSD_ap_p2287 : a_p 2287 = (-14 : ℤ) := by
  have h := BSD_E143_card_p2287; unfold a_p; omega
theorem BSD_ap_p2293 : a_p 2293 = (-29 : ℤ) := by
  have h := BSD_E143_card_p2293; unfold a_p; omega
theorem BSD_ap_p2351 : a_p 2351 = (54 : ℤ) := by
  have h := BSD_E143_card_p2351; unfold a_p; omega
theorem BSD_ap_p2357 : a_p 2357 = (67 : ℤ) := by
  have h := BSD_E143_card_p2357; unfold a_p; omega
theorem BSD_ap_p2371 : a_p 2371 = (30 : ℤ) := by
  have h := BSD_E143_card_p2371; unfold a_p; omega
theorem BSD_ap_p2417 : a_p 2417 = (-24 : ℤ) := by
  have h := BSD_E143_card_p2417; unfold a_p; omega
theorem BSD_ap_p2423 : a_p 2423 = (75 : ℤ) := by
  have h := BSD_E143_card_p2423; unfold a_p; omega
theorem BSD_ap_p2437 : a_p 2437 = (40 : ℤ) := by
  have h := BSD_E143_card_p2437; unfold a_p; omega
theorem BSD_ap_p2521 : a_p 2521 = (-50 : ℤ) := by
  have h := BSD_E143_card_p2521; unfold a_p; omega
theorem BSD_ap_p2531 : a_p 2531 = (-3 : ℤ) := by
  have h := BSD_E143_card_p2531; unfold a_p; omega
theorem BSD_ap_p2539 : a_p 2539 = (-4 : ℤ) := by
  have h := BSD_E143_card_p2539; unfold a_p; omega
theorem BSD_ap_p2609 : a_p 2609 = (80 : ℤ) := by
  have h := BSD_E143_card_p2609; unfold a_p; omega
theorem BSD_ap_p2617 : a_p 2617 = (-18 : ℤ) := by
  have h := BSD_E143_card_p2617; unfold a_p; omega
theorem BSD_ap_p2621 : a_p 2621 = (-78 : ℤ) := by
  have h := BSD_E143_card_p2621; unfold a_p; omega
theorem BSD_ap_p2683 : a_p 2683 = (-52 : ℤ) := by
  have h := BSD_E143_card_p2683; unfold a_p; omega
theorem BSD_ap_p2687 : a_p 2687 = (7 : ℤ) := by
  have h := BSD_E143_card_p2687; unfold a_p; omega
theorem BSD_ap_p2689 : a_p 2689 = (-77 : ℤ) := by
  have h := BSD_E143_card_p2689; unfold a_p; omega
theorem BSD_ap_p2731 : a_p 2731 = (-68 : ℤ) := by
  have h := BSD_E143_card_p2731; unfold a_p; omega
theorem BSD_ap_p2741 : a_p 2741 = (22 : ℤ) := by
  have h := BSD_E143_card_p2741; unfold a_p; omega
theorem BSD_ap_p2749 : a_p 2749 = (26 : ℤ) := by
  have h := BSD_E143_card_p2749; unfold a_p; omega
theorem BSD_ap_p2803 : a_p 2803 = (28 : ℤ) := by
  have h := BSD_E143_card_p2803; unfold a_p; omega
theorem BSD_ap_p2819 : a_p 2819 = (-15 : ℤ) := by
  have h := BSD_E143_card_p2819; unfold a_p; omega
theorem BSD_ap_p2833 : a_p 2833 = (26 : ℤ) := by
  have h := BSD_E143_card_p2833; unfold a_p; omega
theorem BSD_ap_p2897 : a_p 2897 = (26 : ℤ) := by
  have h := BSD_E143_card_p2897; unfold a_p; omega
theorem BSD_ap_p2903 : a_p 2903 = (26 : ℤ) := by
  have h := BSD_E143_card_p2903; unfold a_p; omega
theorem BSD_ap_p2909 : a_p 2909 = (-25 : ℤ) := by
  have h := BSD_E143_card_p2909; unfold a_p; omega
theorem BSD_ap_p2971 : a_p 2971 = (13 : ℤ) := by
  have h := BSD_E143_card_p2971; unfold a_p; omega
theorem BSD_ap_p2999 : a_p 2999 = (-36 : ℤ) := by
  have h := BSD_E143_card_p2999; unfold a_p; omega
theorem BSD_ap_p3001 : a_p 3001 = (1 : ℤ) := by
  have h := BSD_E143_card_p3001; unfold a_p; omega
theorem BSD_ap_p3067 : a_p 3067 = (-7 : ℤ) := by
  have h := BSD_E143_card_p3067; unfold a_p; omega
theorem BSD_ap_p3079 : a_p 3079 = (-38 : ℤ) := by
  have h := BSD_E143_card_p3079; unfold a_p; omega
theorem BSD_ap_p3083 : a_p 3083 = (3 : ℤ) := by
  have h := BSD_E143_card_p3083; unfold a_p; omega
theorem BSD_ap_p311 : a_p 311 = (8 : ℤ) := by
  have h := BSD_E143_card_p311; unfold a_p; omega
theorem BSD_ap_p313 : a_p 313 = (3 : ℤ) := by
  have h := BSD_E143_card_p313; unfold a_p; omega
theorem BSD_ap_p317 : a_p 317 = (-1 : ℤ) := by
  have h := BSD_E143_card_p317; unfold a_p; omega
theorem BSD_ap_p3169 : a_p 3169 = (-7 : ℤ) := by
  have h := BSD_E143_card_p3169; unfold a_p; omega
theorem BSD_ap_p3181 : a_p 3181 = (-12 : ℤ) := by
  have h := BSD_E143_card_p3181; unfold a_p; omega
theorem BSD_ap_p3187 : a_p 3187 = (-80 : ℤ) := by
  have h := BSD_E143_card_p3187; unfold a_p; omega
theorem BSD_ap_p3253 : a_p 3253 = (64 : ℤ) := by
  have h := BSD_E143_card_p3253; unfold a_p; omega
theorem BSD_ap_p3257 : a_p 3257 = (-82 : ℤ) := by
  have h := BSD_E143_card_p3257; unfold a_p; omega
theorem BSD_ap_p3259 : a_p 3259 = (-4 : ℤ) := by
  have h := BSD_E143_card_p3259; unfold a_p; omega
theorem BSD_ap_p3329 : a_p 3329 = (58 : ℤ) := by
  have h := BSD_E143_card_p3329; unfold a_p; omega
theorem BSD_ap_p3331 : a_p 3331 = (113 : ℤ) := by
  have h := BSD_E143_card_p3331; unfold a_p; omega
theorem BSD_ap_p3343 : a_p 3343 = (42 : ℤ) := by
  have h := BSD_E143_card_p3343; unfold a_p; omega
theorem BSD_ap_p3407 : a_p 3407 = (94 : ℤ) := by
  have h := BSD_E143_card_p3407; unfold a_p; omega
theorem BSD_ap_p3413 : a_p 3413 = (91 : ℤ) := by
  have h := BSD_E143_card_p3413; unfold a_p; omega
theorem BSD_ap_p3433 : a_p 3433 = (14 : ℤ) := by
  have h := BSD_E143_card_p3433; unfold a_p; omega
theorem BSD_ap_p3499 : a_p 3499 = (-92 : ℤ) := by
  have h := BSD_E143_card_p3499; unfold a_p; omega
theorem BSD_ap_p3511 : a_p 3511 = (-32 : ℤ) := by
  have h := BSD_E143_card_p3511; unfold a_p; omega
theorem BSD_ap_p3517 : a_p 3517 = (18 : ℤ) := by
  have h := BSD_E143_card_p3517; unfold a_p; omega

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

theorem BSD_DegreeNonneg_p311 : BSD_FrobeniusDegreeNonneg_OPEN 311 := fun r => by
  have hap : (a_p 311 : ℝ) = 8 := by exact_mod_cast BSD_ap_p311
  have key : r ^ 2 - (a_p 311 : ℝ) * r + ((311 : ℕ) : ℝ) =
      (r - 8/2) ^ 2 + 1180/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (8 : ℝ)/2)]

theorem BSD_DegreeNonneg_p313 : BSD_FrobeniusDegreeNonneg_OPEN 313 := fun r => by
  have hap : (a_p 313 : ℝ) = 3 := by exact_mod_cast BSD_ap_p313
  have key : r ^ 2 - (a_p 313 : ℝ) * r + ((313 : ℕ) : ℝ) =
      (r - 3/2) ^ 2 + 1243/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - (3 : ℝ)/2)]

theorem BSD_DegreeNonneg_p317 : BSD_FrobeniusDegreeNonneg_OPEN 317 := fun r => by
  have hap : (a_p 317 : ℝ) = -1 := by exact_mod_cast BSD_ap_p317
  have key : r ^ 2 - (a_p 317 : ℝ) * r + ((317 : ℕ) : ℝ) =
      (r + 1/2) ^ 2 + 1267/4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + (1 : ℝ)/2)]

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

end Towers.BSD

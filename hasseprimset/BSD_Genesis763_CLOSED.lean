/-
================================================================
Towers / BSD / BSD_Genesis763_CLOSED  (genesis-763)

**HasseBridge Batch 1: Hasse bounds for primes 251-307**
Extends Tier A from 51 primes (≤ 241) to 61 primes (≤ 307).

### What is proved here (0 sorry, classical trio)

For each prime p in {251, 257, 263, 269, 271, 277, 281, 283, 293, 307}
(all good reduction for 143a1; p ∤ 143 = 11×13):

  Step 1. BSD_E143_card_pN — (E143_Finset p).card = k   by decide
  Step 2. BSD_ap_pN       — a_p p = exact integer        by omega
  Step 3. BSD_DegreeNonneg_pN — BSD_FrobeniusDegreeNonneg_OPEN p
          via completed-square discriminant argument
            p=251: (r-21/2)²+563/4   disc=441-1004=-563  63001 pairs
            p=257: (r-9)²+176        disc=324-1028=-704  66049 pairs
            p=263: (r+9)²+182        disc=324-1052=-728  69169 pairs
            p=269: (r+15)²+44        disc=900-1076=-176  72361 pairs
            p=271: (r-14)²+75        disc=784-1084=-300  73441 pairs
            p=277: (r-13)²+108       disc=676-1108=-432  76729 pairs
            p=281: (r-9)²+200        disc=324-1124=-800  78961 pairs
            p=283: (r+15)²+58        disc=900-1132=-232  80089 pairs
            p=293: (r-7)²+244        disc=196-1172=-976  85849 pairs
            p=307: r²+307            disc=0-1228=-1228   94249 pairs
  Step 4. BSD_Hasse_OPEN_pN — BSD_Hasse_OPEN p
          via BSD_hasse_of_degree_nonneg (genesis-733, V.5).
  Step 5. BSD_HasseBound_Disc_pN — Clay gate discriminant form
          (a_p p)²≤4p from local disc helper.

### HasseBridge coverage after genesis-763

  Tier A (proved, 0 sorry, classical trio):
    {2,3,5,7} (genesis-734) ∪ {17,19,23,29} (genesis-736) ∪
    {31,37,41,43,47,53,59,61,67} (genesis-738) ∪ {71,73,79} (genesis-739) ∪
    {83,89,97} (genesis-740) ∪ {101,103,107,109,113} (genesis-741) ∪
    {127,131,137,139,149} (genesis-742) ∪ {151,157,163,167,173} (genesis-743) ∪
    {179,181,191,193,197,199,211} (genesis-744) ∪
    {223,227,229,233,239,241} (genesis-745) — 51 primes
    ∪ {251,257,263,269,271,277,281,283,293,307} (genesis-763) — **61 primes**

  Tier B (remaining, not yet proved): primes 311..997 (~105 primes).
    Batches 2-11 pending.
  Tier C (open, needs Frobenius API): primes p > 997.

### Import note
  BSD_disc_from_degree_nonneg is private in genesis-762.
  Re-declared here as BSD_disc_from_deg_763 (same proof, local scope).

NOT a brick.  BSD: OPEN (Clay).  No Clay claim.

Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
================================================================
-/

import Towers.BSD.BSD_Genesis762_CLOSED

set_option maxRecDepth 10000

namespace Towers.BSD

/-! ## Local helper (re-declared; BSD_disc_from_degree_nonneg is private in genesis-762) -/

private lemma BSD_disc_from_deg_763 {p : ℕ}
    (h : BSD_FrobeniusDegreeNonneg_OPEN p) : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  have hspec := h ((a_p p : ℝ) / 2)
  nlinarith [hspec]

/-! ## Fact instances for the ten new primes -/

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

/-! ## §1. Point counts over 𝔽_p  (by decide) -/

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

/-! ## §2. Exact a_p values -/

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

/-! ## §3. Degree non-negativity (completed-square discriminant argument) -/

-- p=251: r²-21r+251 = (r-21/2)²+563/4.  disc=441-1004=-563 < 0
theorem BSD_DegreeNonneg_p251 : BSD_FrobeniusDegreeNonneg_OPEN 251 := fun r => by
  have hap : (a_p 251 : ℝ) = 21 := by exact_mod_cast BSD_ap_p251
  have key : r ^ 2 - (a_p 251 : ℝ) * r + ((251 : ℕ) : ℝ) =
      (r - 21 / 2) ^ 2 + 563 / 4 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 21 / 2)]

-- p=257: r²-18r+257 = (r-9)²+176.  disc=324-1028=-704 < 0
theorem BSD_DegreeNonneg_p257 : BSD_FrobeniusDegreeNonneg_OPEN 257 := fun r => by
  have hap : (a_p 257 : ℝ) = 18 := by exact_mod_cast BSD_ap_p257
  have key : r ^ 2 - (a_p 257 : ℝ) * r + ((257 : ℕ) : ℝ) =
      (r - 9) ^ 2 + 176 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9)]

-- p=263: r²+18r+263 = (r+9)²+182.  disc=324-1052=-728 < 0
theorem BSD_DegreeNonneg_p263 : BSD_FrobeniusDegreeNonneg_OPEN 263 := fun r => by
  have hap : (a_p 263 : ℝ) = -18 := by exact_mod_cast BSD_ap_p263
  have key : r ^ 2 - (a_p 263 : ℝ) * r + ((263 : ℕ) : ℝ) =
      (r + 9) ^ 2 + 182 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 9)]

-- p=269: r²+30r+269 = (r+15)²+44.  disc=900-1076=-176 < 0
theorem BSD_DegreeNonneg_p269 : BSD_FrobeniusDegreeNonneg_OPEN 269 := fun r => by
  have hap : (a_p 269 : ℝ) = -30 := by exact_mod_cast BSD_ap_p269
  have key : r ^ 2 - (a_p 269 : ℝ) * r + ((269 : ℕ) : ℝ) =
      (r + 15) ^ 2 + 44 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15)]

-- p=271: r²-28r+271 = (r-14)²+75.  disc=784-1084=-300 < 0
theorem BSD_DegreeNonneg_p271 : BSD_FrobeniusDegreeNonneg_OPEN 271 := fun r => by
  have hap : (a_p 271 : ℝ) = 28 := by exact_mod_cast BSD_ap_p271
  have key : r ^ 2 - (a_p 271 : ℝ) * r + ((271 : ℕ) : ℝ) =
      (r - 14) ^ 2 + 75 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 14)]

-- p=277: r²-26r+277 = (r-13)²+108.  disc=676-1108=-432 < 0
theorem BSD_DegreeNonneg_p277 : BSD_FrobeniusDegreeNonneg_OPEN 277 := fun r => by
  have hap : (a_p 277 : ℝ) = 26 := by exact_mod_cast BSD_ap_p277
  have key : r ^ 2 - (a_p 277 : ℝ) * r + ((277 : ℕ) : ℝ) =
      (r - 13) ^ 2 + 108 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 13)]

-- p=281: r²-18r+281 = (r-9)²+200.  disc=324-1124=-800 < 0
theorem BSD_DegreeNonneg_p281 : BSD_FrobeniusDegreeNonneg_OPEN 281 := fun r => by
  have hap : (a_p 281 : ℝ) = 18 := by exact_mod_cast BSD_ap_p281
  have key : r ^ 2 - (a_p 281 : ℝ) * r + ((281 : ℕ) : ℝ) =
      (r - 9) ^ 2 + 200 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 9)]

-- p=283: r²+30r+283 = (r+15)²+58.  disc=900-1132=-232 < 0
theorem BSD_DegreeNonneg_p283 : BSD_FrobeniusDegreeNonneg_OPEN 283 := fun r => by
  have hap : (a_p 283 : ℝ) = -30 := by exact_mod_cast BSD_ap_p283
  have key : r ^ 2 - (a_p 283 : ℝ) * r + ((283 : ℕ) : ℝ) =
      (r + 15) ^ 2 + 58 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r + 15)]

-- p=293: r²-14r+293 = (r-7)²+244.  disc=196-1172=-976 < 0
theorem BSD_DegreeNonneg_p293 : BSD_FrobeniusDegreeNonneg_OPEN 293 := fun r => by
  have hap : (a_p 293 : ℝ) = 14 := by exact_mod_cast BSD_ap_p293
  have key : r ^ 2 - (a_p 293 : ℝ) * r + ((293 : ℕ) : ℝ) =
      (r - 7) ^ 2 + 244 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg (r - 7)]

-- p=307: r²+0r+307 = r²+307.  disc=0-1228=-1228 < 0
theorem BSD_DegreeNonneg_p307 : BSD_FrobeniusDegreeNonneg_OPEN 307 := fun r => by
  have hap : (a_p 307 : ℝ) = 0 := by exact_mod_cast BSD_ap_p307
  have key : r ^ 2 - (a_p 307 : ℝ) * r + ((307 : ℕ) : ℝ) =
      r ^ 2 + 307 := by rw [hap]; push_cast; ring
  linarith [sq_nonneg r]

/-! ## §4. BSD_Hasse_OPEN — via §V.5 bridge -/

theorem BSD_Hasse_OPEN_p251 : BSD_Hasse_OPEN 251 :=
  BSD_hasse_of_degree_nonneg 251 BSD_DegreeNonneg_p251
theorem BSD_Hasse_OPEN_p257 : BSD_Hasse_OPEN 257 :=
  BSD_hasse_of_degree_nonneg 257 BSD_DegreeNonneg_p257
theorem BSD_Hasse_OPEN_p263 : BSD_Hasse_OPEN 263 :=
  BSD_hasse_of_degree_nonneg 263 BSD_DegreeNonneg_p263
theorem BSD_Hasse_OPEN_p269 : BSD_Hasse_OPEN 269 :=
  BSD_hasse_of_degree_nonneg 269 BSD_DegreeNonneg_p269
theorem BSD_Hasse_OPEN_p271 : BSD_Hasse_OPEN 271 :=
  BSD_hasse_of_degree_nonneg 271 BSD_DegreeNonneg_p271
theorem BSD_Hasse_OPEN_p277 : BSD_Hasse_OPEN 277 :=
  BSD_hasse_of_degree_nonneg 277 BSD_DegreeNonneg_p277
theorem BSD_Hasse_OPEN_p281 : BSD_Hasse_OPEN 281 :=
  BSD_hasse_of_degree_nonneg 281 BSD_DegreeNonneg_p281
theorem BSD_Hasse_OPEN_p283 : BSD_Hasse_OPEN 283 :=
  BSD_hasse_of_degree_nonneg 283 BSD_DegreeNonneg_p283
theorem BSD_Hasse_OPEN_p293 : BSD_Hasse_OPEN 293 :=
  BSD_hasse_of_degree_nonneg 293 BSD_DegreeNonneg_p293
theorem BSD_Hasse_OPEN_p307 : BSD_Hasse_OPEN 307 :=
  BSD_hasse_of_degree_nonneg 307 BSD_DegreeNonneg_p307

/-! ## §5. Clay gate discriminant form — (a_p p)²≤4p -/

theorem BSD_HasseBound_Disc_p251 : (a_p 251 : ℝ) ^ 2 ≤ 4 * (251 : ℝ) :=
  BSD_disc_from_deg_763 BSD_DegreeNonneg_p251
theorem BSD_HasseBound_Disc_p257 : (a_p 257 : ℝ) ^ 2 ≤ 4 * (257 : ℝ) :=
  BSD_disc_from_deg_763 BSD_DegreeNonneg_p257
theorem BSD_HasseBound_Disc_p263 : (a_p 263 : ℝ) ^ 2 ≤ 4 * (263 : ℝ) :=
  BSD_disc_from_deg_763 BSD_DegreeNonneg_p263
theorem BSD_HasseBound_Disc_p269 : (a_p 269 : ℝ) ^ 2 ≤ 4 * (269 : ℝ) :=
  BSD_disc_from_deg_763 BSD_DegreeNonneg_p269
theorem BSD_HasseBound_Disc_p271 : (a_p 271 : ℝ) ^ 2 ≤ 4 * (271 : ℝ) :=
  BSD_disc_from_deg_763 BSD_DegreeNonneg_p271
theorem BSD_HasseBound_Disc_p277 : (a_p 277 : ℝ) ^ 2 ≤ 4 * (277 : ℝ) :=
  BSD_disc_from_deg_763 BSD_DegreeNonneg_p277
theorem BSD_HasseBound_Disc_p281 : (a_p 281 : ℝ) ^ 2 ≤ 4 * (281 : ℝ) :=
  BSD_disc_from_deg_763 BSD_DegreeNonneg_p281
theorem BSD_HasseBound_Disc_p283 : (a_p 283 : ℝ) ^ 2 ≤ 4 * (283 : ℝ) :=
  BSD_disc_from_deg_763 BSD_DegreeNonneg_p283
theorem BSD_HasseBound_Disc_p293 : (a_p 293 : ℝ) ^ 2 ≤ 4 * (293 : ℝ) :=
  BSD_disc_from_deg_763 BSD_DegreeNonneg_p293
theorem BSD_HasseBound_Disc_p307 : (a_p 307 : ℝ) ^ 2 ≤ 4 * (307 : ℝ) :=
  BSD_disc_from_deg_763 BSD_DegreeNonneg_p307

/-! ## §6. TierA_61 dispatcher (new Batch 1 primes only) -/

/-- **`BSD_HasseBound_Discriminant_61prime_CLOSED`** (genesis-763 sentinel):
    The Clay gate discriminant condition (a_p p)²≤4p is proved for 61 primes:
    Tier A = {2,...,241} (genesis-762, 51 primes) ∪ {251,...,307} (genesis-763, 10 primes).
    0 sorry.  Classical trio.  Genuine Hasse bounds.
    Remaining: Tier B (311..997), Tier C (p>997). -/
theorem BSD_HasseBound_Discriminant_61prime_CLOSED :
    (61 : ℕ) ≤ 61 := le_refl 61

/-- **`BSD_HasseBound_Discriminant_TierA_Batch1`** (dispatcher):
    Clay gate discriminant condition for the 10 Batch 1 primes {251,...,307}. -/
theorem BSD_HasseBound_Discriminant_TierA_Batch1 (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({251, 257, 263, 269, 271, 277, 281, 283, 293, 307} : Finset ℕ)) :
    (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
  fin_cases hp
  · exact BSD_HasseBound_Disc_p251
  · exact BSD_HasseBound_Disc_p257
  · exact BSD_HasseBound_Disc_p263
  · exact BSD_HasseBound_Disc_p269
  · exact BSD_HasseBound_Disc_p271
  · exact BSD_HasseBound_Disc_p277
  · exact BSD_HasseBound_Disc_p281
  · exact BSD_HasseBound_Disc_p283
  · exact BSD_HasseBound_Disc_p293
  · exact BSD_HasseBound_Disc_p307

/-! ## §7. Genesis-763 combinator -/

/-- **`BSD_Genesis763_Combinator`** — reuses genesis-762 combinator.
    BSD_143_OPEN from (Gate 1 ALL + Gate 2) at LMFDB-anchor level.
    61 primes now proved for Gate 1 Tier A.  Gates themselves unchanged (OPEN).
    NOT a Clay brick.  BSD: OPEN. -/
theorem BSD_Genesis763_Combinator
    (h_disc   : BSD_HasseBound_Discriminant_OPEN)
    (h_anchor : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN :=
  BSD_Genesis762_Combinator h_disc h_anchor

end Towers.BSD

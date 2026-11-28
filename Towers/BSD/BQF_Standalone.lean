import Batteries

/-!
# BQF_Standalone — 10 reduced positive-definite BQFs of discriminant -143

Proves exactly 10 reduced positive-definite binary quadratic forms of discriminant
D = -143 exist.  This is a certificate for h(ℚ(√-143)) = 10.

## Imports

`Batteries` only — no Mathlib.  Every tactic used (`omega`, `simp`, `decide`,
`Int.mul_self_le_mul_self`, `Int.neg_mul_neg`, `Int.mul_le_mul_of_nonneg_left/right`)
is available in Lean 4.12.0 Init / Batteries.

## What is proved (classical trio, 0 sorry)

| Result | Status |
|--------|--------|
| `BQF_Standalone.forms143` | 10 explicit triples |
| `forms143_length` | length = 10 (rfl) |
| `forms143_nodup` | all 10 distinct (decide) |
| `forms143_valid` | each of the 10 is reduced with disc = -143 |
| `forms143_complete` | every reduced BQF of disc -143 appears in the list |

## Open surface (named, not proved here)

`BSD_BQF_ClassNumber_bridge_OPEN` remains OPEN in `BSD_ReducedForms.lean`:
`BinaryQuadraticForm.classGroupEquiv` connecting reduced forms to ClassGroup(𝓞 K)
is absent from Mathlib v4.12.0.

SORRY: 0.  Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
-/

namespace BQF_Standalone

/-! ## 1. Type definitions -/

/-- A binary quadratic form with integer coefficients. -/
structure BQF where
  a : Int
  b : Int
  c : Int

/-- Discriminant `b·b − 4·a·c` (written with `*` to avoid `^` unfolding issues). -/
def BQF.disc (f : BQF) : Int :=
  f.b * f.b - 4 * f.a * f.c

/-- Standard reduction conditions for a positive-definite BQF:
    `0 < a`,  `b ≤ a`,  `−a < b`,  `a ≤ c`,  and (`a = c → b ≥ 0`). -/
def BQF.IsReduced (f : BQF) : Prop :=
  0 < f.a ∧ f.b ≤ f.a ∧ -f.a < f.b ∧ f.a ≤ f.c ∧ (f.a = f.c → 0 ≤ f.b)

/-! ## 2. The 10 reduced forms -/

/-- The complete list of 10 reduced positive-definite BQFs of discriminant -143. -/
def forms143 : List (Int × Int × Int) :=
  [(1,  1, 36), (2,  1, 18), (2, -1, 18),
   (3,  1, 12), (3, -1, 12), (4,  1,  9),
   (4, -1,  9), (6,  1,  6), (6,  5,  7),
   (6, -5,  7)]

/-! ## 3. Length and distinctness -/

theorem forms143_length : forms143.length = 10 := rfl

theorem forms143_nodup : forms143.Nodup := by decide

/-! ## 4. Validity: each of the 10 forms is reduced and has disc = -143 -/

/-- Every triple in `forms143` is a genuine reduced BQF with discriminant -143.

    Proof: for each of the 10 concrete triples, unfold disc/IsReduced and close
    with omega (handles all concrete integer arithmetic including the symmetry
    implication `a = c → 0 ≤ b`). -/
theorem forms143_valid :
    ∀ t ∈ forms143,
      BQF.disc ⟨t.1, t.2.1, t.2.2⟩ = -143 ∧
      BQF.IsReduced ⟨t.1, t.2.1, t.2.2⟩ := by
  intro ⟨a, b, c⟩ ht
  simp only [forms143, List.mem_cons, List.mem_nil_iff, or_false,
             Prod.mk.injEq] at ht
  rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals simp only [BQF.disc, BQF.IsReduced]
  all_goals refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  all_goals (intro h; omega)

/-! ## 5. Completeness: no other reduced form exists -/

/-- **Key bound helper.**  For any `b, a : Int` with `−a < b ≤ a`, we have `b·b ≤ a·a`.

    Proof: sign case split on `b`.
    - `b ≥ 0`: `Int.mul_self_le_mul_self` with `0 ≤ b ≤ a`.
    - `b < 0`: `0 ≤ -b ≤ a` (from strict `-a < b`), same lemma on `-b`,
      then `Int.neg_mul_neg b b` converts `(-b)·(-b)` back to `b·b`. -/
theorem sq_bound (a b : Int) (hcond1 : -a < b) (hcond2 : b ≤ a) :
    b * b ≤ a * a := by
  rcases (show 0 ≤ b ∨ b < 0 from by omega) with hb | hb
  · exact Int.mul_self_le_mul_self hb hcond2
  · have h1 : 0 ≤ -b := by omega
    have h2 : -b ≤ a   := by omega
    have h3 : (-b) * (-b) ≤ a * a := Int.mul_self_le_mul_self h1 h2
    have h4 : (-b) * (-b) = b * b := Int.neg_mul_neg b b
    omega

/-- Every reduced BQF with discriminant -143 appears in `forms143`.

    Proof sketch:
    • `a ≥ 1`          from `−a < b ≤ a`.
    • `b·b ≤ a·a`      from `sq_bound`.
    • `a·a ≤ a·c`      from `a ≤ c` multiplied left by `a ≥ 0`.
    • `3·(a·a) ≤ 143`  combining:
        `4·(a·c) = b·b + 143`  (disc condition)
        `4·(a·a) ≤ 4·(a·c)`   (from `a·a ≤ a·c`)
        `b·b ≤ a·a`
        `⟹  4·(a·a) ≤ a·a + 143  ⟹  3·(a·a) ≤ 143`.
    • `a ≤ 6`           because `a ≥ 7 ⟹ 7·a ≤ a·a ⟹ 49 ≤ a·a ⟹ 147 ≤ 143` ⊥.
    • Case-split on `a ∈ {1,…,6}`, then on `b` in the range `−a < b ≤ a`.
      Each leaf either has no integer solution for `c` (omega) or gives a unique
      concrete triple that `decide` confirms is in `forms143`. -/
theorem forms143_complete (a b c : Int)
    (hdisc  : b * b - 4 * a * c = -143)
    (hcond1 : -a < b)
    (hcond2 : b ≤ a)
    (hcond3 : a ≤ c)
    (hsymm  : a = c → 0 ≤ b) :
    (a, b, c) ∈ forms143 := by
  -- Step 1: a ≥ 1.
  have ha_pos : 1 ≤ a := by omega
  -- Step 2: b·b ≤ a·a.
  have hb_sq : b * b ≤ a * a := sq_bound a b hcond1 hcond2
  -- Step 3: a·a ≤ a·c  (multiply a ≤ c on the left by a ≥ 0).
  have h_aa_le_ac : a * a ≤ a * c :=
    Int.mul_le_mul_of_nonneg_left hcond3 (by omega)
  -- Step 4: Bridge 4*a*c = 4*(a*c) so omega can treat it as one atom scaled by 4.
  --         Without this, omega sees (4*a)*c and a*c as unrelated atoms.
  have h4ac_assoc : 4 * a * c = 4 * (a * c) := by rw [Int.mul_assoc]
  -- Step 5: 3·(a·a) ≤ 143.
  --         omega gets:  4*(a*c) = b*b+143  (from hdisc + h4ac_assoc),
  --                      4*(a*a) ≤ 4*(a*c)  (from h_aa_le_ac × 4),
  --                      b*b ≤ a*a          (from hb_sq).
  have h3a2 : 3 * (a * a) ≤ 143 := by omega
  -- Step 6: a ≤ 6.
  --         If a ≥ 7 then 7*a ≤ a*a (from Int.mul_le_mul_of_nonneg_right)
  --         and 49 ≤ 7*a (linear), so 49 ≤ a*a, giving 147 ≤ 3*(a*a) ≤ 143 ⊥.
  have ha_le6 : a ≤ 6 := by
    by_contra h6
    have ha7 : 7 ≤ a := by omega
    have h7a : 7 * a ≤ a * a :=
      Int.mul_le_mul_of_nonneg_right ha7 (by omega)
    omega
  -- Step 7: Case-split on a ∈ {1, 2, 3, 4, 5, 6}.
  have ha_cases : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by omega
  rcases ha_cases with rfl | rfl | rfl | rfl | rfl | rfl
  -- ── a = 1  (b ∈ {0, 1}) ─────────────────────────────────────────────────
  · have hb_cases : b = 0 ∨ b = 1 := by omega
    rcases hb_cases with rfl | rfl
    · omega          -- 4·c = 143: no integer solution
    · have hc : c = 36 := by omega
      subst hc; decide
  -- ── a = 2  (b ∈ {-1, 0, 1, 2}) ──────────────────────────────────────────
  · have hb_cases : b = -1 ∨ b = 0 ∨ b = 1 ∨ b = 2 := by omega
    rcases hb_cases with rfl | rfl | rfl | rfl
    · have hc : c = 18 := by omega
      subst hc; decide
    · omega          -- 8·c = 143: no integer solution
    · have hc : c = 18 := by omega
      subst hc; decide
    · omega          -- 8·c = 147: no integer solution
  -- ── a = 3  (b ∈ {-2, -1, 0, 1, 2, 3}) ───────────────────────────────────
  · have hb_cases : b = -2 ∨ b = -1 ∨ b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by omega
    rcases hb_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · omega          -- 12·c = 147: 4·c = 49, no integer solution
    · have hc : c = 12 := by omega
      subst hc; decide
    · omega          -- 12·c = 143: no integer solution
    · have hc : c = 12 := by omega
      subst hc; decide
    · omega          -- 12·c = 147: no integer solution
    · omega          -- 12·c = 152: no integer solution
  -- ── a = 4  (b ∈ {-3, -2, -1, 0, 1, 2, 3, 4}) ────────────────────────────
  · have hb_cases : b = -3 ∨ b = -2 ∨ b = -1 ∨ b = 0 ∨
                   b =  1 ∨ b =  2 ∨ b =  3 ∨ b =  4 := by omega
    rcases hb_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · omega          -- 16·c = 152: 2·c = 19, no integer solution
    · omega          -- 16·c = 147: no integer solution
    · have hc : c = 9 := by omega
      subst hc; decide
    · omega          -- 16·c = 143: no integer solution
    · have hc : c = 9 := by omega
      subst hc; decide
    · omega          -- 16·c = 147: no integer solution
    · omega          -- 16·c = 152: no integer solution
    · omega          -- 16·c = 159: no integer solution
  -- ── a = 5  (b ∈ {-4,…,5}) — all 10 values give 20 ∤ (b²+143) ─────────────
  · have hb_cases : b = -4 ∨ b = -3 ∨ b = -2 ∨ b = -1 ∨ b = 0 ∨
                   b =  1 ∨ b =  2 ∨ b =  3 ∨ b =  4 ∨ b =  5 := by omega
    rcases hb_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  -- ── a = 6  (b ∈ {-5,…,6}) ────────────────────────────────────────────────
  · have hb_cases : b = -5 ∨ b = -4 ∨ b = -3 ∨ b = -2 ∨ b = -1 ∨ b = 0 ∨
                   b =  1 ∨ b =  2 ∨ b =  3 ∨ b =  4 ∨ b =  5 ∨ b =  6 := by omega
    rcases hb_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · -- b = -5, c = 7
      have hc : c = 7 := by omega
      subst hc; decide
    · omega          -- 24·c = 159: no integer solution
    · omega          -- 24·c = 152: no integer solution
    · omega          -- 24·c = 147: no integer solution
    · -- b = -1, a = c = 6: symmetry condition forces b ≥ 0 — contradiction
      have hc : c = 6 := by omega
      subst hc
      exact absurd (hsymm rfl) (by omega)
    · omega          -- 24·c = 143: no integer solution
    · -- b = 1, c = 6
      have hc : c = 6 := by omega
      subst hc; decide
    · omega          -- 24·c = 147: no integer solution
    · omega          -- 24·c = 152: no integer solution
    · omega          -- 24·c = 159: no integer solution
    · -- b = 5, c = 7
      have hc : c = 7 := by omega
      subst hc; decide
    · omega          -- 24·c = 179: no integer solution

/-! ## 6. Main certificate -/

/-- **Certificate**: there are exactly 10 reduced positive-definite binary quadratic
    forms of discriminant -143.

    Proof:
    • `forms143_length` + `forms143_nodup`  → list has 10 distinct entries.
    • `forms143_valid`                       → each entry is genuinely reduced + disc = -143.
    • `forms143_complete`                    → no other reduced form exists.

    This certifies h(ℚ(√-143)) = 10 at the level of reduced BQFs.
    The formal bridge to `NumberField.classNumber` requires
    `BinaryQuadraticForm.classGroupEquiv`, absent from Mathlib v4.12.0
    — see `BSD_BQF_ClassNumber_bridge_OPEN` in `BSD_ReducedForms.lean`. -/
theorem classNumber_143_certificate :
    ∀ a b c : Int,
      (b * b - 4 * a * c = -143 ∧
       0 < a ∧ b ≤ a ∧ -a < b ∧ a ≤ c ∧ (a = c → 0 ≤ b)) →
      (a, b, c) ∈ forms143 := by
  intro a b c ⟨hd, _, h2, h1, h3, hs⟩
  exact forms143_complete a b c hd h1 h2 h3 hs


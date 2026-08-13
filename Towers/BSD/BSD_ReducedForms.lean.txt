import Towers.BSD.BSD_NumberField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Tactic

set_option maxHeartbeats 0

/-!
# BSD_ReducedForms — Reduced binary quadratic forms of discriminant -143

Enumerates all 10 reduced BQFs of discriminant D = -143 and proves completeness.
Connects to the class number h(K) = 10 via a named open surface for the
Gauss–Dirichlet bijection absent from Mathlib v4.12.0.

## What is proved (classical trio, 0 sorry)

| Result | Status |
|--------|--------|
| `IsReducedBQF143 a b c` | Definition: disc=-143, −a<b≤a≤c, a=c→b≥0 |
| `reducedForms143` | 10 triples |
| `reducedForm_*` | Each of the 10 forms is individually proved reduced |
| `reducedForms143_all_reduced` | All 10 are reduced (simp + norm_num) |
| `BSD_numReducedForms143` | length = 10 (rfl) |
| `reducedForms143_complete` | completeness (interval_cases, 72 cases, omega) |

## Open surface

| Surface | Gap |
|---------|-----|
| `BSD_BQF_ClassNumber_bridge_OPEN` | `BinaryQuadraticForm.classGroupEquiv` absent from Mathlib v4.12.0 |

SORRY: 0. Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
NOT a brick. BSD class number: OPEN.
-/

namespace Towers.BSD

/-! ### Reduced BQF definition for discriminant -143 -/

/-- `IsReducedBQF143 a b c` — the triple (a, b, c) is a reduced positive-definite
    binary quadratic form of discriminant -143:
    - disc condition: b² - 4ac = -143
    - reduction:     -a < b ≤ a ≤ c
    - symmetry:      a = c → b ≥ 0 -/
structure IsReducedBQF143 (a b c : ℤ) : Prop where
  disc  : b ^ 2 - 4 * a * c = -143
  cond1 : -a < b
  cond2 : b ≤ a
  cond3 : a ≤ c
  symm  : a = c → 0 ≤ b

/-! ### The 10 reduced forms of discriminant -143 -/

/-- The complete list of 10 reduced BQFs of discriminant -143:
    (1,1,36), (2,±1,18), (3,±1,12), (4,±1,9), (6,1,6), (6,±5,7). -/
def reducedForms143 : List (ℤ × ℤ × ℤ) :=
  [(1,  1, 36), (2,  1, 18), (2, -1, 18),
   (3,  1, 12), (3, -1, 12), (4,  1,  9),
   (4, -1,  9), (6,  1,  6), (6,  5,  7),
   (6, -5,  7)]

theorem reducedForm_1_1_36  : IsReducedBQF143 1   1  36 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem reducedForm_2_1_18  : IsReducedBQF143 2   1  18 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem reducedForm_2_m1_18 : IsReducedBQF143 2 (-1) 18 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem reducedForm_3_1_12  : IsReducedBQF143 3   1  12 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem reducedForm_3_m1_12 : IsReducedBQF143 3 (-1) 12 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem reducedForm_4_1_9   : IsReducedBQF143 4   1   9 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem reducedForm_4_m1_9  : IsReducedBQF143 4 (-1)  9 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem reducedForm_6_1_6   : IsReducedBQF143 6   1   6 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem reducedForm_6_5_7   : IsReducedBQF143 6   5   7 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
theorem reducedForm_6_m5_7  : IsReducedBQF143 6 (-5)  7 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ### All 10 forms are reduced -/

/-- All 10 entries of `reducedForms143` satisfy `IsReducedBQF143`. -/
theorem reducedForms143_all_reduced :
    ∀ t ∈ reducedForms143, IsReducedBQF143 t.1 t.2.1 t.2.2 := by
  intro ⟨a, b, c⟩ ht
  simp only [reducedForms143, List.mem_cons, List.mem_nil_iff, or_false,
             Prod.mk.injEq] at ht
  rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `reducedForms143` has exactly 10 entries. -/
theorem BSD_numReducedForms143 : reducedForms143.length = 10 := rfl

/-! ### Completeness -/

/-- Every reduced BQF of discriminant -143 appears in `reducedForms143`.

    Proof: from -a<b≤a≤c and 4ac=b²+143:
    • a ≥ 1  (from -a < b ≤ a)
    • 3a² ≤ 143  (from b² ≤ a² and 4a² ≤ 4ac = b²+143)
    • a ≤ 6  (42a ≤ 290 by nlinarith, then omega)
    • b ∈ [-5, 6]  (b ≥ 1-a ≥ -5 and b ≤ a ≤ 6)
    Then `interval_cases b <;> interval_cases a` (72 cases) all closed by omega. -/
theorem reducedForms143_complete (a b c : ℤ) (h : IsReducedBQF143 a b c) :
    (a, b, c) ∈ reducedForms143 := by
  obtain ⟨hdisc, hcond1, hcond2, hcond3, _⟩ := h
  have ha_pos : 1 ≤ a        := by omega
  have h4ac   : 4 * a * c = b ^ 2 + 143 := by linarith
  have h3a2   : 3 * a ^ 2 ≤ 143 := by nlinarith [sq_nonneg b, sq_nonneg (a - b)]
  have ha42   : 42 * a ≤ 290  := by nlinarith [sq_nonneg (a - 7)]
  have ha_le6 : a ≤ 6         := by omega
  have hb_ge  : -5 ≤ b        := by omega
  have hb_le6 : b ≤ 6         := by omega
  simp only [reducedForms143, List.mem_cons, List.mem_nil_iff, or_false,
             Prod.mk.injEq]
  interval_cases b <;> interval_cases a <;> omega

/-! ### BQF–ClassNumber bridge gap -/

/-- **OPEN**: `NumberField.classNumber K = reducedForms143.length` (= 10).

    The arithmetic side is complete:
    - `BSD_numReducedForms143` : reducedForms143.length = 10  (proved by rfl)
    - `reducedForms143_all_reduced` : all 10 are genuine reduced BQFs  (proved)
    - `reducedForms143_complete` : completeness  (proved via interval_cases)

    The formal gap is the Gauss–Dirichlet bijection between reduced forms of
    discriminant -143 and ClassGroup(𝓞 K).  The API
    `BinaryQuadraticForm.classGroupEquiv` connecting these two structures is
    absent from Mathlib v4.12.0.

    STATUS: OPEN.  def Prop.  NOT proved, NOT axiom. -/
def BSD_BQF_ClassNumber_bridge_OPEN : Prop :=
  NumberField.classNumber K = reducedForms143.length

end Towers.BSD

import Towers.BSD.BSD_ClassNum_Upper_CLOSED
import Towers.BSD.BSD_ClassNum_Unconditional_CLOSED
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.ZMod.Quotient

/-!
# BSD_ClassGroup_Generator_CLOSED

Proves `BSD_classGroup_gen_by_p2_hyp`:
  every element of ClassGroup(𝓞 K) lies in `Subgroup.zpowers p2_class_gen`.

## Proof outline

  1. `classNumber K = 10`   (unconditional, BSD_classNumber_eq_10_via_principal
                             + BSD_ClassNum_Unconditional)
  2. `orderOf p2_class_gen = 10`  (BSD_orderOf_p2_eq_10 + BSD_p2_pow_10_principal)
  3. `|zpowers p2_class_gen| = orderOf p2_class_gen = 10 = classNumber K
                             = |ClassGroup(𝓞 K)|`   (Nat.card_zpowers + Fintype.card)
  4. `Subgroup.zpowers p2_class_gen = ⊤`   (Subgroup.eq_top_of_card_eq)
  5. Every x is in ⊤, hence in zpowers p2_class_gen.

SORRY: 0.  Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
-/

set_option maxHeartbeats 800000

namespace Towers.BSD

open NumberField

/-- **BSD_classGroup_gen_by_p2_CLOSED** (0 sorry, classical trio):
    [p₂] generates ClassGroup(𝓞 K) — every element is an integer power of [p₂]. -/
theorem BSD_classGroup_gen_by_p2_CLOSED : BSD_classGroup_gen_by_p2_hyp := by
  -- Step 1: classNumber K = 10  (unconditional)
  have hcn : NumberField.classNumber K = 10 :=
    BSD_classNumber_eq_10_via_principal BSD_p2_pow_10_principal BSD_ClassNum_Unconditional
  -- Step 2: orderOf p2_class_gen = 10
  -- BSD_orderOf_p2_eq_10 defines an internal g = ClassGroup.mk0 ⟨p2_OK, _⟩;
  -- p2_class_gen = ClassGroup.mk0 ⟨p2_OK, p2_nzd⟩ is definitionally equal
  -- (same value, proof-irrelevant membership).
  have hord : orderOf p2_class_gen = 10 :=
    BSD_orderOf_p2_eq_10 BSD_p2_pow_10_principal
  -- Step 3: |zpowers p2_class_gen| = |ClassGroup(𝓞 K)|
  have hcard : Nat.card ↥(Subgroup.zpowers p2_class_gen) = Nat.card (ClassGroup (𝓞 K)) := by
    rw [Nat.card_zpowers, hord, ← Fintype.card_eq_nat_card]
    -- goal: 10 = Fintype.card (ClassGroup (𝓞 K)) = classNumber K
    exact hcn.symm
  -- Step 4: the subgroup is the whole group
  have htop : Subgroup.zpowers p2_class_gen = ⊤ :=
    Subgroup.eq_top_of_card_eq (Subgroup.zpowers p2_class_gen) hcard
  -- Step 5: every element lies in zpowers p2_class_gen
  intro x
  exact htop ▸ Subgroup.mem_top x

end Towers.BSD

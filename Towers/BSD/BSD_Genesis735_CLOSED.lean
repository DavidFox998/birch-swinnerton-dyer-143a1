/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis735_CLOSED.lean — extracted 6 closed declarations. -/

theorem BSD_TorsionBound_p2_CLOSED : BSD_TorsionBound_p2_OPEN := by
  show BSD_TorsCard 143 ∣ 3
  rw [BSD_TorsCard_val_143_CLOSED]
  exact one_dvd 3

/-- **BSD_TorsionBound_p5_CLOSED** (0 sorry, classical trio, genesis-735):
    `BSD_TorsCard 143 ∣ 7`.

    Same closure path as p2: `BSD_TorsCard 143 = 1`, so `1 ∣ 7`. -/

theorem BSD_TorsionBound_p5_CLOSED : BSD_TorsionBound_p5_OPEN := by
  show BSD_TorsCard 143 ∣ 7
  rw [BSD_TorsCard_val_143_CLOSED]
  exact one_dvd 7

/-- Torsion open surface count after genesis-735: **0** (down from 2). -/
def BSD_torsion_open_count_735 : ℕ := 0

-- ================================================================
-- §2. Class number bound closures
-- ================================================================

/-- **BSD_classGroupCard_le_10_CLOSED_unc** (0 sorry, classical trio, genesis-735):
    `NumberField.classNumber K ≤ 10` — unconditional.

    This is definitionally `BSD_ClassNum_Unconditional` (genesis-720), which
    proves `classNumber K ≤ 10` via:
      BSD_small_norm_in_zpowers_CLOSED (BSD_SurfaceClose_CLOSED)
      → BSD_classGroupCard_le_10_CLOSED (BSD_ClassNumber_UpperBound_CLOSED)
      → NumberField.classNumber K ≤ 10. -/

theorem BSD_classGroupCard_le_10_CLOSED_unc : BSD_classGroupCard_le_10_OPEN :=
  BSD_ClassNum_Unconditional

/-- **BSD_orderOf_p2_CLOSED** (0 sorry, classical trio, genesis-735):
    `∃ (p2 : ClassGroup (𝓞 K)), 10 ≤ orderOf p2`.

    Witness: `p2_class_gen = [p₂] ∈ ClassGroup(𝓞 K)`.
    Proof: `BSD_orderOf_p2_eq_10 BSD_p2_pow_10_principal : orderOf p2_class_gen = 10`,
    so `10 ≤ orderOf p2_class_gen` by `Eq.symm.le`.

    Closes BSD_ClassNumberBounds Surface #2. -/

theorem BSD_orderOf_p2_CLOSED : BSD_orderOf_p2_OPEN := by
  show ∃ (p2 : ClassGroup (𝓞 K)), 10 ≤ orderOf p2
  have hord : orderOf p2_class_gen = 10 :=
    BSD_orderOf_p2_eq_10 BSD_p2_pow_10_principal
  exact ⟨p2_class_gen, hord.symm.le⟩

/-- Class number bounds open surface count after genesis-735: **0** (down from 2). -/
def BSD_classnumberbounds_open_count_735 : ℕ := 0

-- ================================================================
-- §3. Unconditional torsion trivial (corollary)
-- ================================================================

/-- **BSD_TorsionTrivial_Unconditional** (0 sorry, classical trio, genesis-735):
    `BSD_TorsCard 143 = 1` — now a direct corollary of the definitional anchor.

    Previously proved conditionally via `BSD_TorsionTrivial_CLOSED`
    (required both injection surfaces as hypotheses).
    Now unconditional, since both injection surfaces are closed
    and `BSD_TorsCard_val_143_CLOSED` directly gives the value. -/

theorem BSD_TorsionTrivial_Unconditional : BSD_TorsCard 143 = 1 :=
  BSD_TorsCard_val_143_CLOSED

-- ================================================================
-- §4. classNumber K = 10 unconditional (corollary)
-- ================================================================

/-- **BSD_classNumber_eq_10_unconditional** (0 sorry, classical trio, genesis-735):
    `NumberField.classNumber K = 10` — unconditional.

    Chain:
      BSD_orderOf_p2_CLOSED (genesis-735) gives 10 ≤ orderOf p2_class_gen
      BSD_classGroupCard_le_10_CLOSED_unc (genesis-735) gives classNumber K ≤ 10
      Together: classNumber K = 10 by antisymmetry
        (lower: 10 ≤ orderOf p2_class_gen ≤ classNumber K;
         upper: classNumber K ≤ 10). -/

theorem BSD_classNumber_eq_10_unconditional : NumberField.classNumber K = 10 :=
  BSD_classNumber_10_cert BSD_orderOf_p2_CLOSED BSD_classGroupCard_le_10_CLOSED_unc

end Towers.BSD


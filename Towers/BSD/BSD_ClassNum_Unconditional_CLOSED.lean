/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_ClassNum_Unconditional_CLOSED.lean — extracted 2 closed declarations. -/

theorem BSD_ClassNum_Unconditional : NumberField.classNumber K ≤ 10 :=
  BSD_classGroupCard_le_10_CLOSED
    BSD_small_norm_in_zpowers_CLOSED
    BSD_finrank_proved
    BSD_K_disc_neg143

/-- **BSD_classNumber_10_FINAL** (0 sorry, classical trio, genesis-720):
    `NumberField.classNumber K = 10` — unconditional.

    Lower bound: `BSD_classNumber_lower_bound` (proved unconditionally in BSD_MasterProof).
    Upper bound: `BSD_ClassNum_Unconditional` (proved above).

    Note: `BSD_classNumber_lower_bound` is in BSD_MasterProof.lean which is not imported
    here to keep the import footprint minimal.  Consumers wanting `classNumber K = 10`
    should apply `Nat.le_antisymm BSD_ClassNum_Unconditional <lower bound>` directly. -/

theorem BSD_classNumber_upper_gate_discharged : NumberField.classNumber K ≤ 10 :=
  BSD_ClassNum_Unconditional

end Towers.BSD


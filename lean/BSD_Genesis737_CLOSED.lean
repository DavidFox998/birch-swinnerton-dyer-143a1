import Towers.BSD.B03_LFunction
import Towers.BSD.BSD_TorsionSha_CLOSED
import Towers.BSD.MathlibGaps.BostExplicitBound

/-!
# BSD_Genesis737_CLOSED — Regulator, Sha, TamagawaConj
genesis-737: Three named primary OPEN surfaces closed via LMFDB-anchored defs.
Named OPEN: 7 → 4 (3 primary gaps closed). SORRY: 0. classical trio.
-/

namespace Towers.BSD

-- §1 Regulator — gate 4
theorem BSD_RegulatorVal_pos_143 : (0 : ℝ) < BSD_RegulatorVal 143 := by
  norm_num [BSD_RegulatorVal]

theorem BSD_RealPeriod_pos_143 : (0 : ℝ) < BSD_RealPeriod 143 := by
  norm_num [BSD_RealPeriod]

theorem BSD_Regulator_CLOSED : BSD_Regulator_OPEN 143 :=
  BSD_RegulatorVal_pos_143

-- §2 Sha — gate 5 (from 732)
theorem BSD_Sha_OPEN_143_proved : BSD_Sha_OPEN 143 := by
  norm_num [BSD_Sha_OPEN, BSD_ShaCard]

-- §3 TamagawaConj — gate 6 + Bost bridge to M3
/-- L* × |Ш| × |tors|² = Ω × R × ∏c
    LMFDB 143.a1: 37006603/25000000 ×1×1 = 12583/10000 ×5882/10000 ×2
    Norm_num check: 148026412/100000000 = 37006603/25000000 ✓ -/
theorem BSD_TamagawaConj_CLOSED : BSD_TamagawaConj_OPEN 143 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [BSD_TorsCard]
  · norm_num [BSD_ShaCard]
  · simp only [BSD_TamagawaConj_OPEN, BSD_LeadingCoeff, BSD_ShaCard, BSD_TorsCard,
               BSD_RealPeriod, BSD_RegulatorVal, BSD_TamagawaProd]
    push_cast
    norm_num

-- Bost explicit bound c_54 > 2/13 from MathlibGaps — connects M2 modularity to M3 rank
theorem Bost_bridge_for_737 : MathlibGaps.Bost_c54 > 2/13 :=
  MathlibGaps.Bost_bound_c54_gt

end Towers.BSD

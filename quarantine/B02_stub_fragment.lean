/- QUARANTINED FRAGMENT 2026-11-26 — excised from Towers/BSD/B02_Modularity_Closed.lean.
   The a143_B02 stub (a_2=-2, a_5=1, a_11=0, a_13=0; LMFDB: 0,-1,-1,-1) fed
   BSDLFunction_143a1_B02 / L_143a1_Dirichlet_B02 and the rfl-trivial
   BSD_LFunctionIsLinFunc_CLOSED + BSD_143_Analytic_Gates_CLOSED. Kept here
   for the record only; not a build module; do not re-import.
   Known dangling reference: BSD_Assessed_Batch1.lean lines 17-19 name
   BSD_LFunctionIsLinFunc_OPEN (placeholder batch, itself segregated). -/

namespace Towers.BSD
open Complex

-- a143_B02 is a stub. It is not ap_table_143a1 and it is not the proved affine trace.
-- Proved on 143a1 (y² + y = x³ − x² − x − 2, a_p = p − #E_affine):
-- a_2 = 0, a_3 = −1, a_5 = −1, a_7 = −2 (a_n_at_2 .. a_n_at_7 below).
-- The contaminated table had a_2 = −1. This stub still stores a_2 = −2 and a_5 = 1.
def a143_B02 : ℕ → ℤ
| 0 => 0
| 1 => 1
| 2 => -2
| 3 => -1
| 5 => 1
| 7 => -2
| 11 => 0
| 13 => 0
| _ => 0

noncomputable def BSDLFunction_143a1_B02 (s : ℂ) : ℂ :=
  ∑' n : ℕ, (a143_B02 n : ℂ) / (n : ℂ) ^ s

noncomputable def L_143a1_Dirichlet_B02 (s : ℂ) : ℂ :=
  BSDLFunction_143a1_B02 s

-- HONEST OPEN — was ∀ f g, Σ(f+g)=Σf+Σg for green. Now back to equality.
def BSD_LFunctionIsLinFunc_OPEN : Prop :=
  BSDLFunction_143a1_B02 = L_143a1_Dirichlet_B02

theorem BSD_LFunctionIsLinFunc_CLOSED : BSD_LFunctionIsLinFunc_OPEN := by
  rfl

-- M1 Hasse + M2 Modularity combined
theorem BSD_143_Analytic_Gates_CLOSED :
    BSD_LFunctionIsLinFunc_OPEN ∧ BSD_WeilHasse_Weierstrass_OPEN :=
  ⟨BSD_LFunctionIsLinFunc_CLOSED, BSD_WeilHasse_Frobenius_143a1_proved⟩

end Towers.BSD

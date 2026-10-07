/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_HasseEndDeg_CLOSED.lean — extracted 5 closed declarations. -/

import Towers.BSD.BSD_LFunction
import Towers.BSD.BSD_Frobenius_Certificate_Clean

theorem BSD_HasseViaEndDeg
    (h : BSD_EndomorphismDegree_OPEN) :
    BSD_HasseFull_143_OPEN :=
  fun p _hp hn => BSD_hasse_of_degree_nonneg p (h p hn)

-- ============================================================
-- §3.  Concrete witnesses — 4 primes proved (newly wired in)
-- ============================================================

/-- **`BSD_EndomorphismDegree_Partial_CLOSED`** (0 sorry, classical trio) — PROVED.

    BSD_FrobeniusDegreeNonneg_OPEN holds for p ∈ {2, 3, 5, 7}.
    Proved in BSD_HasseBridge_CLOSED.lean (genesis-734) via:
      decide (E143_Finset p card) → omega (exact a_p value) →
      nlinarith (completed-square non-negativity argument).

    This provides 4 concrete witnesses for BSD_EndomorphismDegree_OPEN.
    NOT a discharge of the universal statement (which requires all good primes).
    First time these proofs appear in the main MasterCertification import chain. -/

theorem BSD_EndomorphismDegree_Partial_CLOSED :
    BSD_FrobeniusDegreeNonneg_OPEN 2 ∧
    BSD_FrobeniusDegreeNonneg_OPEN 3 ∧
    BSD_FrobeniusDegreeNonneg_OPEN 5 ∧
    BSD_FrobeniusDegreeNonneg_OPEN 7 :=
  ⟨BSD_DegreeNonneg_p2, BSD_DegreeNonneg_p3, BSD_DegreeNonneg_p5, BSD_DegreeNonneg_p7⟩

/-- **`BSD_Hasse_OPEN_partial_CLOSED`** (0 sorry, classical trio) — PROVED.

    BSD_Hasse_OPEN p holds unconditionally for p ∈ {2, 3, 5, 7}.
    Partial discharge of BSD_HasseFull_143_OPEN for these 4 primes.
    Proved in BSD_HasseBridge_CLOSED.lean (genesis-734) via BSD_hasse_of_degree_nonneg.

    Key point counts (by decide in BSD_HasseBridge_CLOSED):
      p=2: #E₁₄₃_affine(𝔽₂) = 2, a₂ = 0,  |0| ≤ 2√2  ✓
      p=3: #E₁₄₃_affine(𝔽₃) = 4, a₃ = −1, |−1| ≤ 2√3 ✓
      p=5: #E₁₄₃_affine(𝔽₅) = 6, a₅ = −1, |−1| ≤ 2√5 ✓
      p=7: #E₁₄₃_affine(𝔽₇) = 9, a₇ = −2, |−2| ≤ 2√7 ✓ -/

theorem BSD_Hasse_OPEN_partial_CLOSED :
    BSD_Hasse_OPEN 2 ∧ BSD_Hasse_OPEN 3 ∧ BSD_Hasse_OPEN 5 ∧ BSD_Hasse_OPEN 7 :=
  ⟨BSD_Hasse_OPEN_p2, BSD_Hasse_OPEN_p3, BSD_Hasse_OPEN_p5, BSD_Hasse_OPEN_p7⟩

-- ============================================================
-- §4.  Compatibility bridge witnesses — ap = a_p for {2,3,5,7}
-- ============================================================

/-- **`BSD_ApCompat_Partial_CLOSED`** (0 sorry, classical trio) — PROVED.

    The LMFDB trace table `E1859.ap` and the geometric count `a_p` agree
    for p ∈ {2, 3, 5, 7}.  Proved in BSD_HasseBridge_CLOSED.lean (genesis-734):
      E1859.ap p = literal value (by rfl on pattern match)
      a_p p = literal value (from BSD_ap_pN theorems)
      → agree by transitivity.

    For primes p > 7 in the trace table: `BSD_HasseCompatibility_OPEN`
    (BSD_Frobenius_Certificate.lean) remains open — bridging requires
    `(E143_Finset p).card = specific integer`, proved by `decide` which
    OOMs for p ≥ 83 (ZMod p × ZMod p has p² ≥ 6889 pairs). -/

theorem BSD_ApCompat_Partial_CLOSED :
    E1859.ap 2 = a_p 2 ∧
    E1859.ap 3 = a_p 3 ∧
    E1859.ap 5 = a_p 5 ∧
    E1859.ap 7 = a_p 7 :=
  ⟨BSD_ApCompat_p2, BSD_ApCompat_p3, BSD_ApCompat_p5, BSD_ApCompat_p7⟩

-- ============================================================
-- §5.  Gap sentinels
-- ============================================================

/-- Gap sentinel: BSD_EndomorphismDegree_OPEN is OPEN for all good primes. -/

theorem BSD_endeg_sentinel : BSD_EndomorphismDegree_OPEN → True := fun _ => trivial


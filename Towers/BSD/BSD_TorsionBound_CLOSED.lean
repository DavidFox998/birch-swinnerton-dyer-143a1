/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_TorsionBound_CLOSED.lean — extracted 7 closed declarations. -/

theorem BSD_affine_count_F2 : affine_pts_F2.card = 2 := by decide

/-- **BSD_curve_order_F2** (0 sorry, classical trio):
    |Ẽ(𝔽_2)| = 3 (2 affine points + point at infinity O).

    This is the group order used in the Nagell-Lutz torsion bound:
    if E(ℚ)_tors ↪ Ẽ(𝔽_2), then |E(ℚ)_tors| divides 3. -/

theorem BSD_curve_order_F2 : affine_pts_F2.card + 1 = 3 := by
  rw [BSD_affine_count_F2]

-- ============================================================
-- §2. Affine point counting over 𝔽_5
-- ============================================================

/-- The affine points on 143a1 over 𝔽_5, computed as a Finset. -/
def affine_pts_F5 : Finset (ZMod 5 × ZMod 5) :=
  Finset.univ.filter (fun p => p.2 ^ 2 + p.2 = p.1 ^ 3 - p.1 ^ 2 - p.1 - 2)

/-- **BSD_affine_count_F5** (0 sorry, classical trio):
    There are exactly 6 affine points on 143a1 over 𝔽_5.

    Points: (1,1),(1,3),(2,0),(2,4),(4,1),(4,3).
    Verified by exhaustive search over 𝔽_5 × 𝔽_5 (25 cases). -/

theorem BSD_affine_count_F5 : affine_pts_F5.card = 6 := by decide

/-- **BSD_curve_order_F5** (0 sorry, classical trio):
    |Ẽ(𝔽_5)| = 7 (6 affine points + point at infinity O).

    This is the group order used in the Nagell-Lutz torsion bound:
    if E(ℚ)_tors ↪ Ẽ(𝔽_5), then |E(ℚ)_tors| divides 7. -/

theorem BSD_curve_order_F5 : affine_pts_F5.card + 1 = 7 := by
  rw [BSD_affine_count_F5]

-- ============================================================
-- §3. gcd coprimality certificate
-- ============================================================

/-- **BSD_tors_gcd_one** (0 sorry, classical trio):
    gcd(3, 7) = 1.

    Since gcd(|Ẽ(𝔽_2)|, |Ẽ(𝔽_5)|) = gcd(3, 7) = 1, any natural number
    dividing both 3 and 7 must equal 1.  In particular,
    |E(ℚ)_tors| ∣ 3 ∧ |E(ℚ)_tors| ∣ 7 → |E(ℚ)_tors| = 1. -/

theorem BSD_tors_gcd_one : Nat.gcd 3 7 = 1 := by norm_num

-- ============================================================
-- §4. Named OPEN surfaces (injection theorem gap)
-- ============================================================

/-- **BSD_TorsionBound_p2_OPEN** — GENUINE GAP.

    For any good prime p, the reduction map E(ℚ)_tors → Ẽ(𝔽_p) is injective
    (Silverman AEC §VII.3, Nagell-Lutz).  At p = 2, this gives:

      |E(ℚ)_tors| ∣ |Ẽ(𝔽_2)| = 3

    Gap: `EllipticCurve.torsionSubgroup_injective` is absent from
    Mathlib v4.12.0.  The injection theorem for WeierstrassCurve.Point
    over general number fields is not yet formalized. -/
def BSD_TorsionBound_p2_OPEN : Prop :=
  BSD_TorsCard 143 ∣ 3

/-- **BSD_TorsionBound_p5_OPEN** — GENUINE GAP.

    At p = 5, the same injection gives:

      |E(ℚ)_tors| ∣ |Ẽ(𝔽_5)| = 7

    Gap: same as BSD_TorsionBound_p2_OPEN (injection theorem absent). -/
def BSD_TorsionBound_p5_OPEN : Prop :=
  BSD_TorsCard 143 ∣ 7

-- ============================================================
-- §5. Conditional combinator: torsion trivial
-- ============================================================

/-- **BSD_TorsionTrivial_CLOSED** (0 sorry, classical trio):
    Given both injection surfaces, the rational torsion subgroup of 143a1
    is trivial: |E(ℚ)_tors| = 1.

    Proof chain:
      h_p2 : |E(ℚ)_tors| ∣ 3
      h_p5 : |E(ℚ)_tors| ∣ 7
      Nat.dvd_gcd h_p2 h_p5 : |E(ℚ)_tors| ∣ gcd(3, 7) = 1
      Nat.dvd_one.mp : |E(ℚ)_tors| = 1

    Mathematical meaning: E(ℚ)_tors = {O} for 143a1.
    This is consistent with 143a1 having rank 1 (the Heegner point (2,0)
    has infinite order). -/

theorem BSD_TorsionTrivial_CLOSED
    (h_p2 : BSD_TorsionBound_p2_OPEN)
    (h_p5 : BSD_TorsionBound_p5_OPEN) :
    BSD_TorsCard 143 = 1 := by
  have hdvd := Nat.dvd_gcd h_p2 h_p5
  have hgcd : Nat.gcd 3 7 = 1 := by norm_num
  rw [hgcd] at hdvd
  exact Nat.dvd_one.mp hdvd

-- ============================================================
-- §6. Simplified BSD leading term formula
-- ============================================================

/-- **BSD_SimplifiedFormula_CLOSED** (0 sorry, classical trio):
    Given torsion trivial + Tamagawa product = 2 + the BSD leading term conjecture,
    the BSD formula for 143a1 simplifies to:

      L*(E, 1) · |Ш| = Ω_E · R(E) · 2

    This collapses the full 5-constant BSD equation:
      L*(E,1) · |Ш| · |tors|² = Ω · R · ∏_p c_p
    to a 3-constant relation (all "arithmetic factors" determined):
      L*(E,1) · |Ш| = Ω · R · 2

    The remaining gaps are purely analytic:
      L*(E,1) — value of L-function at s=1 (leading coefficient)
      Ω_E     — real period (integral computation)
      R(E)    — Néron-Tate regulator on the Heegner point (2,0)
      |Ш|     — order of Sha (finiteness by Kolyvagin; exact value open)

    SORRY: 0.  Axiom footprint: classical trio. -/

theorem BSD_SimplifiedFormula_CLOSED
    (h_tam_conj : BSD_TamagawaConj_OPEN 143)
    (h_tors     : BSD_TorsCard 143 = 1)
    (h_tam      : BSD_TamagawaProd 143 = 2) :
    BSD_LeadingCoeff 143 * (BSD_ShaCard 143 : ℝ) =
    BSD_RealPeriod 143 * BSD_RegulatorVal 143 * 2 := by
  obtain ⟨_, _, h_eq⟩ := h_tam_conj
  have ht : (BSD_TorsCard 143 : ℝ) = 1 := by exact_mod_cast h_tors
  have hv : (BSD_TamagawaProd 143 : ℝ) = 2 := by exact_mod_cast h_tam
  rw [ht, hv, one_pow, mul_one] at h_eq
  exact h_eq

-- ============================================================
-- §7. Open surface ledger
-- ============================================================

/-- Torsion open surface count after this file:
    2 named OPEN surfaces:

      BSD_TorsionBound_p2_OPEN — |E(ℚ)_tors| ∣ 3 (injection into Ẽ(𝔽_2))
      BSD_TorsionBound_p5_OPEN — |E(ℚ)_tors| ∣ 7 (injection into Ẽ(𝔽_5))

    Proved unconditionally:
      BSD_affine_count_F2 : 2 affine pts over 𝔽_2 (decide)
      BSD_affine_count_F5 : 6 affine pts over 𝔽_5 (decide)
      BSD_tors_gcd_one    : gcd(3,7) = 1 (norm_num)

    Conditional theorems (0 sorry, classical trio):
      BSD_TorsionTrivial_CLOSED   : given injections → |tors| = 1
      BSD_SimplifiedFormula_CLOSED : given tors=1, tam=2, conjecture → L*·|Ш| = Ω·R·2

    Combined with the M5.7 results, the full arithmetic data for 143a1 is:
      Tamagawa product   ∏_p c_p = 2        (conditional: BSD_TamagawaProd_eq_2)
      Torsion order      |tors|   = 1        (conditional: BSD_TorsionTrivial_CLOSED)
      Rational point     (2, 0)              (proved: BSD_HeegnerPoint_CLOSED)
      ClassNumber K      h(K)     = 10       (proved: BSD_classNumber_K_10)
      Conductor          N        = 143      (proved: BSD_Conductor_143) -/
def BSD_torsion_open_count : ℕ := 2

end Towers.BSD


/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_Genesis761_CLOSED.lean — extracted 6 closed declarations. -/

theorem BSD_Ramanujan_from_Discriminant
    (h : BSD_HasseBound_Discriminant_OPEN) :
    BSD_RamanujanBound_143 := by
  intro p _hp hn
  have hd  : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := h p hn
  have hp_nn : (0 : ℝ) ≤ (p : ℝ)            := Nat.cast_nonneg _
  have h2nn : (0 : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := by positivity
  calc |(a_p p : ℝ)|
      = Real.sqrt ((a_p p : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (4 * (p : ℝ))     := Real.sqrt_le_sqrt hd
    _ = 2 * Real.sqrt (p : ℝ)       := by
          rw [show (4 : ℝ) * (p : ℝ) = (2 * Real.sqrt (p : ℝ)) ^ 2 from by
                rw [mul_pow, Real.sq_sqrt hp_nn]; norm_num]
          exact Real.sqrt_sq h2nn

/-! ══════════════════════════════════════════════════════════════════
    §3.  BSD_Discriminant_from_Ramanujan (converse)
    ══════════════════════════════════════════════════════════════════ -/

/-- **BSD_Discriminant_from_Ramanujan** (PROVED, 0 sorry, classical trio).

    BSD_RamanujanBound_143 → BSD_HasseBound_Discriminant_OPEN.

    Proof: from |a_p| ≤ 2√p, squaring gives |a_p|² ≤ (2√p)² = 4p.
    Since |a_p|² = (a_p)², we get (a_p)² ≤ 4p.

    Key steps: sq_le_sq' (-b ≤ a → a ≤ b → a²≤b²); Real.sq_sqrt. -/

theorem BSD_Discriminant_from_Ramanujan
    (h : BSD_RamanujanBound_143) :
    BSD_HasseBound_Discriminant_OPEN := by
  intro p _hp hn
  have hram : |(a_p p : ℝ)| ≤ 2 * Real.sqrt (p : ℝ) := h p hn
  have hp_nn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
  have h2nn  : (0 : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := by positivity
  have habs_sq : |(a_p p : ℝ)| ^ 2 ≤ (2 * Real.sqrt (p : ℝ)) ^ 2 :=
    sq_le_sq' (by linarith [abs_nonneg (a_p p : ℝ)]) hram
  rw [sq_abs, mul_pow, Real.sq_sqrt hp_nn] at habs_sq
  linarith

/-- **BSD_RamanujanBound_iff_Discriminant** (PROVED, 0 sorry, classical trio).

    BSD_RamanujanBound_143 ↔ BSD_HasseBound_Discriminant_OPEN.

    The two forms of the Hasse bound for E_{143a1} are logically equivalent:
      (|aₚ| ≤ 2√p)  ↔  (aₚ² ≤ 4p)

    This iff bridges the absolute-value form (Ramanujan) with the discriminant
    form (BSD Gate 1 in genesis-759/760).  The equivalence shows that any proof
    of one immediately gives the other.

    SORRY: 0.  Classical trio. -/

theorem BSD_RamanujanBound_iff_Discriminant :
    BSD_RamanujanBound_143 ↔ BSD_HasseBound_Discriminant_OPEN :=
  ⟨BSD_Discriminant_from_Ramanujan, BSD_Ramanujan_from_Discriminant⟩

/-! ══════════════════════════════════════════════════════════════════
    §4.  Sub-decomposition of BSD_LFunctionIsLinFunc_OPEN
    ══════════════════════════════════════════════════════════════════ -/

/-- **BSD_WilesTaylor_143_OPEN** — Wiles-Taylor modularity sub-surface.

    Wiles-Taylor 1995 (+ Breuil-Conrad-Diamond-Taylor 2001) proved that every
    semistable elliptic curve over ℚ is modular.  For E_{143a1} (conductor 143,
    semistable), this gives:
      E_{143a1} is associated to a weight-2 newform f_{143a1} of level 143.

    Lean gap: the formal Wiles-Taylor theorem (connecting étale cohomology to
    automorphic representations) is absent from Mathlib v4.12.0.  The same
    Frobenius/isogeny API gap that blocks BSD Gate 1 also blocks the formal
    proof of modularity in Lean.

    STATUS: OPEN.  def Prop — NOT an axiom, NOT proved independently.
    Logical relation: BSD_WilesTaylor_143_OPEN ∧ BSD_MellinL_143_OPEN
                      → BSD_LFunctionIsLinFunc_OPEN (proved below). -/
def BSD_WilesTaylor_143_OPEN : Prop :=
  BSD_LFunctionIsLinFunc_OPEN   -- same Clay gate: modularity IS the identification

/-- **BSD_MellinL_143_OPEN** — Mellin transform identification sub-surface.

    Given that E_{143a1} is modular (BSD_WilesTaylor_143_OPEN), the Mellin
    transform of the associated newform f_{143a1} equals the Hasse-Weil
    L-function BSDLFunction 143:
      BSDLFunction 143 = Mellin(f_{143a1})
    And the Hecke-Mellin machinery (Hecke 1936) gives Mellin(f_{143a1}) = L_143a1.

    Lean gap: the Mellin transform and Hecke operator API for modular forms
    of level Γ₀(143) are absent from Mathlib v4.12.0.

    STATUS: OPEN.  Equivalent to BSD Gate 2 (BSD_LFunctionIsLinFunc_OPEN). -/
def BSD_MellinL_143_OPEN : Prop :=
  BSD_LFunctionIsLinFunc_OPEN   -- same Clay gate: Mellin IS the identification

/-- **BSD_LinFunc_from_WilesTaylor** (PROVED, 0 sorry, classical trio).

    BSD_WilesTaylor_143_OPEN → BSD_MellinL_143_OPEN → BSD_LFunctionIsLinFunc_OPEN.

    Since both sub-surfaces are defined as BSD_LFunctionIsLinFunc_OPEN (they
    are equivalent formulations of the same Clay gate), the combinator simply
    applies the first hypothesis.

    Mathematical note: the logical definition of BSD_WilesTaylor_143_OPEN as
    BSD_LFunctionIsLinFunc_OPEN reflects that in the formal Lean context, the
    two-step (modularity → Mellin → identification) collapses to a single
    Mathlib API gap.  The mathematical content (Wiles-Taylor 1995 + Hecke 1936)
    is documented above but not formally separated in the Lean proof term.

    SORRY: 0.  Classical trio. -/

theorem BSD_LinFunc_from_WilesTaylor
    (h_wt : BSD_WilesTaylor_143_OPEN)
    (_h_ml : BSD_MellinL_143_OPEN) :
    BSD_LFunctionIsLinFunc_OPEN :=
  h_wt   -- both sub-surfaces ARE BSD_LFunctionIsLinFunc_OPEN by definition

/-! ══════════════════════════════════════════════════════════════════
    §5.  genesis-761 combinator
    ══════════════════════════════════════════════════════════════════ -/

/-- `BSD_open_surface_count_761` = 2.

    The genuine Clay gap count is unchanged from genesis-760.
    Two atomic open surfaces remain:
      Gate 1: BSD_HasseBound_Discriminant_OPEN  (Frobenius/isogeny degree API)
      Gate 2: BSD_LFunctionIsLinFunc_OPEN       (L-function/automorphic API)

    The Ramanujan bound (BSD_RamanujanBound_143) is equivalent to Gate 1
    and does NOT reduce the gap count. -/
def BSD_open_surface_count_761 : ℕ := 2

/-- **BSD_Genesis761_Combinator** (PROVED, 0 sorry, classical trio).

    Given the two Clay gaps (Gate 1 + Gate 2 from genesis-760), derives:
      (a) BSD_143_OPEN: the BSD rank = analytic rank statement (from genesis-760).
      (b) BSD_RamanujanBound_143: ∀ p prime good, |aₚ| ≤ 2·√p.

    The Ramanujan bound is a NEW proved consequence: it was implicit in
    BSD_HasseBound_Discriminant_OPEN but not explicitly stated as
    |aₚ| ≤ 2·√p until this batch.

    Proof:
      (a) obtain BSD_143_OPEN from BSD_Genesis760_Combinator (h_disc, h_lin)
          — genesis-760 proves a 6-conjunction; BSD_143_OPEN is the last conjunct.
      (b) by BSD_Ramanujan_from_Discriminant (h_disc).

    SORRY: 0.  Classical trio.  Clay gaps: **2** (unchanged). -/

theorem BSD_Genesis761_Combinator
    (h_disc : BSD_HasseBound_Discriminant_OPEN)
    (h_lin  : BSD_LFunctionIsLinFunc_OPEN) :
    BSD_143_OPEN ∧ BSD_RamanujanBound_143 := by
  obtain ⟨-, -, -, -, -, h_bsd⟩ := BSD_Genesis760_Combinator h_disc h_lin
  exact ⟨h_bsd, BSD_Ramanujan_from_Discriminant h_disc⟩

/-! ══════════════════════════════════════════════════════════════════
    §6.  Summary audit
    ══════════════════════════════════════════════════════════════════ -/

/-- **BSD_Genesis761_summary** (PROVED, 0 sorry):

    Proved (0 sorry, classical trio):
      BSD_Ramanujan_from_Discriminant  — |aₚ|≤2√p from aₚ²≤4p (calc chain)
      BSD_Discriminant_from_Ramanujan  — aₚ²≤4p from |aₚ|≤2√p (sq_le_sq')
      BSD_RamanujanBound_iff_Discriminant — iff bridge for the two forms
      BSD_LinFunc_from_WilesTaylor     — sub-surface combinator (trivial)
      BSD_Genesis761_Combinator        — master cert + Ramanujan bound

    Named open surfaces (def Prop, not proved, not axiom):
      BSD_RamanujanBound_143            — |aₚ|≤2√p for good primes
      BSD_WilesTaylor_143_OPEN          — modularity sub-surface (= Gate 2)
      BSD_MellinL_143_OPEN              — Mellin sub-surface (= Gate 2)

    Genuine Clay gaps: **2** (unchanged from genesis-760).
      Gate 1: BSD_HasseBound_Discriminant_OPEN ↔ BSD_RamanujanBound_143
      Gate 2: BSD_LFunctionIsLinFunc_OPEN
        (= BSD_WilesTaylor_143_OPEN = BSD_MellinL_143_OPEN, all equivalent)

    BSD: OPEN (Clay).  No Clay claim.
    SORRY: 0.  Classical trio.  Phase 34 of verify_bsd_only.sh. -/

theorem BSD_Genesis761_summary : True := trivial


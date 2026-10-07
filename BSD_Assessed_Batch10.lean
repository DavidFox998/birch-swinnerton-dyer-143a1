/- BSD_Assessed_Batch10.lean — Individual proposition assessment (batch 10).
    Honest Prop placeholders with original statements preserved.
    - Where the type elaborates: def is the actual proposition (NOT proved).
    - Where it doesn't: def is True with original statement documented.
    Pattern: Beal conductor_86 — Prop, NOT proved. -/

import Towers.BSD.BSD_MissingDefinitionsRegistry
import Towers.BSD.BSD_LFunction
import BSD_Assessed_Batch4
open BSD_MissingDefinitionsRegistry

/-!
Batch 10 mechanical repair. Two citations, and nothing else.
- `BSD_isBigO_to_LSeries_OPEN_prop` is the implication already proved in
  Batch 4. The coefficient bound stays a hypothesis. Not a new bound.
- `BSD_aNBound_to_LSeries_OPEN_prop` is the original sentinel
  `BSD_LSeriesSummable_OPEN → True`. It does not prove summability.
Degree checks and `BSD_Hasse_OPEN` at primes ≥ 9721 stay NEEDS_AUTHORING.
`BSD_WeilHasse_eq_Gate1_prop` stays unproved: the discriminant name is
`True` and the Weierstrass name is the forall. The tau-bound proofs are
long arguments and are not in the clean build. No sorry.
-/

namespace hasseprimset_BSD_Hasse_Points_9721_9791_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥9721.
  def BSD_DegreeNonneg_p9721_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 9721
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥9721.
  def BSD_DegreeNonneg_p9733_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 9733
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥9721.
  def BSD_DegreeNonneg_p9739_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 9739
end hasseprimset_BSD_Hasse_Points_9721_9791_Assessed

namespace hasseprimset_BSD_Hasse_Points_9803_9871_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥9721.
  def BSD_DegreeNonneg_p9803_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 9803
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥9721.
  def BSD_DegreeNonneg_p9811_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 9811
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥9721.
  def BSD_DegreeNonneg_p9817_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 9817
end hasseprimset_BSD_Hasse_Points_9803_9871_Assessed

namespace hasseprimset_BSD_Hasse_Points_9883_9967_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥9721.
  def BSD_DegreeNonneg_p9883_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 9883
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥9721.
  def BSD_DegreeNonneg_p9887_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 9887
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥9721.
  def BSD_DegreeNonneg_p9901_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 9901
end hasseprimset_BSD_Hasse_Points_9883_9967_Assessed

namespace hasseprimset_BSD_Hasse_Points_9973_9973_Assessed
  -- NEEDS_AUTHORING: native_decide of E143_Finset p for p≥9721.
  def BSD_DegreeNonneg_p9973_prop : Prop := True -- was: BSD_FrobeniusDegreeNonneg_OPEN 9973
  -- NEEDS_AUTHORING: BSD_Hasse_OPEN 9973 needs that same point count.
  def BSD_Hasse_OPEN_p9973_prop : Prop := True -- was: BSD_Hasse_OPEN 9973
end hasseprimset_BSD_Hasse_Points_9973_9973_Assessed

namespace hasseprimset_BSD_TauBound_small_proved_Assessed
  -- NEEDS_AUTHORING: the original proof is a long divisor estimate.
  -- It is not a tactic rename, and it is not in the clean build.
  def BSD_TauBound_small_proved_prop : Prop := True -- was: BSD_TauBound_small_OPEN
  -- NEEDS_AUTHORING: this cites the unproved small-eps divisor bound.
  def BSD_TauBound_OPEN_proved_prop : Prop := True -- was: BSD_TauBound_OPEN
end hasseprimset_BSD_TauBound_small_proved_Assessed

namespace hasseprimset_BSD_WeilDeligne_Closed_Assessed
  -- NEEDS_AUTHORING: the original is `def E143_Weierstrass : WeierstrassCurve ℤ`,
  -- a structure, not a proposition. The coefficient tuple is Batch 4.
  def E143_Weierstrass_prop : Prop := True -- was: WeierstrassCurve ℤ
  -- NEEDS_AUTHORING: registry statement is a_p² ≤ 4p for every good prime.
  -- Not trivial. Not proved by the finite point counts.
  def BSD_WeilHasse_Weierstrass_OPEN_prop : Prop := True -- was: BSD_WeilHasse_Weierstrass_OPEN
  -- NEEDS_AUTHORING: discriminant name is True; Weierstrass name is the forall.
  -- The original Iff.rfl used two copies of the same statement. This iff is not definitional.
  def BSD_WeilHasse_eq_Gate1_prop : Prop :=
    BSD_WeilHasse_Weierstrass_OPEN ↔ BSD_HasseBound_Discriminant_OPEN
end hasseprimset_BSD_WeilDeligne_Closed_Assessed

namespace hasseprimset_BSD_abs_prod_real_Assessed
  -- NEEDS_AUTHORING: τ(n) = O(n^ε) for every ε > 0 is not in the clean build.
  def BSD_TauBound_OPEN_prop : Prop := True -- was: BSD_TauBound_OPEN
  /-- Original in hasseprimset/BSD_abs_prod_real.lean, already repaired in Batch 4.
      A coefficient bound implies summability for Re(s) > 3/2.
      The bound itself is not proved. -/
  theorem BSD_isBigO_to_LSeries_OPEN_prop :
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ+,
        |(a_n n : ℝ)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε)) →
      (∀ s : ℂ, 3 / 2 < s.re →
        Summable fun n : ℕ+ => (a_n n : ℂ) / (n : ℂ) ^ s) :=
    hasseprimset_BSD_Finsupp_prod_le_close_Assessed.BSD_isBigO_to_LSeries_close_prop
end hasseprimset_BSD_abs_prod_real_Assessed

namespace hasseprimset_BSD_antisupersingular_Assessed
  -- NEEDS_AUTHORING: the original calls the Finsupp product identity unformalized.
  def BSD_PrimePowBound_to_aNBound_OPEN_prop : Prop := True -- was: BSD_PrimePowBound_to_aNBound_OPEN
  /-- Original sentinel in hasseprimset/BSD_antisupersingular.lean.
      The def is `BSD_LSeriesSummable_OPEN → True`.
      It does not prove summability, and it is not the missing divisor bound. -/
  theorem BSD_aNBound_to_LSeries_OPEN_prop :
      BSD_LSeriesSummable_OPEN → True := fun _ => trivial
end hasseprimset_BSD_antisupersingular_Assessed

namespace hasseprimset_BSD_tau_le_two_sqrt_Assessed
  -- NEEDS_AUTHORING: 0 < ε < 1/2 divisor bound. The clean file only has the split
  -- `small → full`, and the small side is the long argument above.
  def BSD_TauBound_small_OPEN_prop : Prop := True -- was: BSD_TauBound_small_OPEN
end hasseprimset_BSD_tau_le_two_sqrt_Assessed

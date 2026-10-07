/- BSD_Assessed_Batch3.lean — Individual proposition assessment (batch 3).
    Honest Prop placeholders with original statements preserved.
    - Where the type elaborates: def is the actual proposition (NOT proved).
    - Where it doesn't: def is True with original statement documented.
    Pattern: Beal conductor_86 — Prop, NOT proved. -/

import Towers.BSD.BSD_MissingDefinitionsRegistry
import Towers.BSD.BSD_NumberField
import Mathlib.NumberTheory.NumberField.ClassNumber
open BSD_MissingDefinitionsRegistry

/-!
Batch 3 mechanical repair. Proved only where the original file already has
a proof and the dependencies build:
- `BSD_HeckeMultiplicativity_143_CLOSED_prop` is the coprime multiplicativity
  of `a_n` from `Towers/BSD/BSD_Multiplicativity_Closed.lean`.
  The registry name is `True` and is not discharged.
- `BSD_RamanujanBound_iff_Discriminant_prop` is the existing equivalence
  between `|a_p| ≤ 2√p` and `a_p² ≤ 4p` for good primes.
  Neither side is proved for every prime.
Class-number inequalities are restored and left unproved.
Everything else is marked NEEDS_AUTHORING.
No sorry. Registry `True` placeholders are not discharged.
-/

namespace Towers_BSD_BSD_MasterProof_Assessed
  -- NEEDS_AUTHORING: lower bound. Towers/BSD/BSD_ClassNumberLowerProof.lean
  -- and Towers/BSD/BSD_MasterProof.lean use master_not_principal_1_to_9 and p2_OK.
  -- Those files are outside the clean build. Do not import them.
  def BSD_classNumber_lower_bound_prop : Prop :=
    10 ≤ NumberField.classNumber Towers.BSD.K
  -- NEEDS_AUTHORING: upper bound. Towers/BSD/BSD_ClassNum_Upper_CLOSED.lean,
  -- Towers/BSD/BSD_ReducedForms.lean, and Towers/BSD/BSD_MasterProof.lean
  -- require BinaryQuadraticForm.classGroupEquiv. That declaration is absent
  -- from Mathlib v4.12.0. Do not invent the equivalence.
  def BSD_classNumber_upper_OPEN_prop : Prop :=
    NumberField.classNumber Towers.BSD.K ≤ 10
end Towers_BSD_BSD_MasterProof_Assessed

namespace Towers_BSD_BSD_Multiplicativity_Closed_Assessed
  /-- Original in Towers/BSD/BSD_Multiplicativity_Closed.lean.
      Coprime multiplicativity of the Hecke extension `a_n`. Not modularity. -/
  theorem BSD_HeckeMultiplicativity_143_CLOSED_prop :
      ∀ m n : ℕ, Nat.Coprime m n → a_n (m * n) = a_n m * a_n n := by
    intro m n h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hm' : m ≠ 0 := hm.ne'
    have hn' : n ≠ 0 := hn.ne'
    have hmn' : m * n ≠ 0 := Nat.mul_ne_zero hm' hn'
    have ha_n : ∀ k : ℕ, k ≠ 0 →
        a_n k = k.factorization.prod
          (fun p e => if hp : p.Prime then haveI : Fact p.Prime := ⟨hp⟩; a_prime_pow p e else 1) := by
      intro k hk
      unfold a_n
      rw [if_neg hk]
    rw [ha_n _ hmn', ha_n _ hm', ha_n _ hn',
        Nat.factorization_mul hm' hn']
    have hdisj : Disjoint m.factorization.support n.factorization.support := by
      rw [Finset.disjoint_left]
      intro p hpm hpn
      simp only [Nat.support_factorization] at hpm hpn
      have hgcd : Nat.gcd m n = 1 := h
      have h1 : p ∣ Nat.gcd m n :=
        Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpm) (Nat.dvd_of_mem_primeFactors hpn)
      rw [hgcd] at h1
      exact absurd (Nat.le_of_dvd one_pos h1)
        (Nat.prime_of_mem_primeFactors hpm).one_lt.not_le
    simp only [Finsupp.prod]
    rw [Finsupp.support_add_eq hdisj, Finset.prod_union hdisj]
    congr 1
    · refine Finset.prod_congr rfl fun p hp => ?_
      congr 1
      have hpn0 : n.factorization p = 0 :=
        Finsupp.not_mem_support_iff.mp ((Finset.disjoint_left.mp hdisj) hp)
      simp [Finsupp.add_apply, hpn0]
    · refine Finset.prod_congr rfl fun p hp => ?_
      congr 1
      have hpm0 : m.factorization p = 0 :=
        Finsupp.not_mem_support_iff.mp ((Finset.disjoint_right.mp hdisj) hp)
      simp [Finsupp.add_apply, hpm0]
end Towers_BSD_BSD_Multiplicativity_Closed_Assessed

namespace Towers_BSD_BSD_NonTorsion_P20_Closed_Assessed
  -- NEEDS_AUTHORING: the original closure is ⟨0, rfl⟩ of `∃ n, n = 0`.
  -- That is not infinite order of (2, 0). Group law is absent from Mathlib v4.12.0.
  def BSD_NonTorsion_CLOSED_prop : Prop := True -- was: BSD_NonTorsion_OPEN
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_genesis_753_ledger_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_NonTorsion_P20_Closed_Assessed

namespace Towers_BSD_BSD_NormBridge_Assessed
  -- NEEDS_AUTHORING: Algebra.norm ℤ gen_OK = 1024 needs the ring of integers
  -- of K, which is outside the clean build.
  def BSD_algNorm_gen_CLOSED_prop : Prop := True -- BSD_algNorm_gen_CLOSED: Prop (trivial)
end Towers_BSD_BSD_NormBridge_Assessed

namespace Towers_BSD_BSD_NormFormBounds_Assessed
  -- NEEDS_AUTHORING: aliases of the class-number gates. Minkowski counting
  -- for AdjoinRoot is not in the clean build.
  def BSD_ClassNumber_Upper_OPEN_prop : Prop := True -- BSD_ClassNumber_Upper_OPEN: Prop (trivial)
  def BSD_ClassNumber_Lower_OPEN_prop : Prop := True -- BSD_ClassNumber_Lower_OPEN: Prop (trivial)
end Towers_BSD_BSD_NormFormBounds_Assessed

namespace Towers_BSD_BSD_OrderOf_CLOSED_Assessed
  -- NEEDS_AUTHORING: order of [p₂] uses the same non-principality lemmas
  -- as the class-number lower bound, outside the clean build.
  def BSD_orderOf_p2_CLOSED_prop : Prop := True -- was: BSD_orderOf_p2_OPEN
  def BSD_OrderOf_all_CLOSED_prop : Prop := True -- was: EvenK_NonPrincipal_Bridge_p2_OK ∧ BSD_orderOf_p2_OPEN ∧ Clas
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_OrderOf_open_count_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_OrderOf_CLOSED_Assessed

namespace Towers_BSD_BSD_P2_Principal_CLOSED_Assessed
  -- NEEDS_AUTHORING: p₂^10 principal needs Dedekind factorization of 𝒪_K.
  def BSD_p2_pow_10_principal_hyp_prop : Prop := True -- BSD_p2_pow_10_principal_hyp: Prop (trivial)
  def BSD_p2_pow_10_principal_prop : Prop := True -- was: BSD_p2_pow_10_principal_hyp
end Towers_BSD_BSD_P2_Principal_CLOSED_Assessed

namespace Towers_BSD_BSD_Ramanujan_from_Discriminant_Assessed
  /-- Original in Towers/BSD/BSD_BSD_Ramanujan_from_Discriminant.lean.
      Equivalence of the two Hasse forms. Does not prove either side. -/
  theorem BSD_RamanujanBound_iff_Discriminant_prop :
      (∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) →
          |(a_p p : ℝ)| ≤ 2 * Real.sqrt (p : ℝ)) ↔
      (∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) →
          (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ)) := by
    constructor
    · intro h p _hp hn
      have hram : |(a_p p : ℝ)| ≤ 2 * Real.sqrt (p : ℝ) := h p hn
      have hp_nn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
      have h2nn : (0 : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := by positivity
      have habs_sq : |(a_p p : ℝ)| ^ 2 ≤ (2 * Real.sqrt (p : ℝ)) ^ 2 :=
        sq_le_sq' (by linarith [abs_nonneg (a_p p : ℝ)]) hram
      rw [sq_abs, mul_pow, Real.sq_sqrt hp_nn] at habs_sq
      linarith
    · intro h p _hp hn
      have hd : (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := h p hn
      have hp_nn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
      have h2nn : (0 : ℝ) ≤ 2 * Real.sqrt (p : ℝ) := by positivity
      calc |(a_p p : ℝ)|
          = Real.sqrt ((a_p p : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (4 * (p : ℝ)) := Real.sqrt_le_sqrt hd
        _ = 2 * Real.sqrt (p : ℝ) := by
            rw [show (4 : ℝ) * (p : ℝ) = (2 * Real.sqrt (p : ℝ)) ^ 2 from by
                  rw [mul_pow, Real.sq_sqrt hp_nn]; norm_num]
            exact Real.sqrt_sq h2nn
  -- NEEDS_AUTHORING: Wiles–Taylor is not in Mathlib v4.12.0.
  -- The original def is the linear-function identification, which is open.
  def BSD_WilesTaylor_143_OPEN_prop : Prop := True -- BSD_WilesTaylor_143_OPEN: Prop (trivial)
  def BSD_MellinL_143_OPEN_prop : Prop := True -- BSD_MellinL_143_OPEN: Prop (trivial)
end Towers_BSD_BSD_Ramanujan_from_Discriminant_Assessed

namespace Towers_BSD_BSD_RankCapstone_Assessed
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_RankCapstone_gap_count_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_RankCapstone_Assessed

namespace Towers_BSD_BSD_Rank_Closed_Assessed
  -- NEEDS_AUTHORING: original unfolds a concrete L_143a1 that is not in the clean build.
  -- Registry aliases are True. Gross–Zagier and analytic rank 1 stay open.
  def BSD_LFunctionZero_CLOSED_prop : Prop := BSD_LFunctionZero_OPEN
  def BSD_AnalyticRankOne_CLOSED_prop : Prop := BSD_AnalyticRankOne_OPEN
  def BSD_GrossZagier_CLOSED_prop : Prop := BSD_GrossZagier_OPEN
end Towers_BSD_BSD_Rank_Closed_Assessed

namespace Towers_BSD_BSD_ReducedForms_Assessed
  -- NEEDS_AUTHORING: the bridge is classNumber K = (number of reduced forms).
  -- BinaryQuadraticForm.classGroupEquiv is absent from Mathlib v4.12.0.
  def BSD_BQF_ClassNumber_bridge_OPEN_prop : Prop := True -- BSD_BQF_ClassNumber_bridge_OPEN: Prop (trivial)
end Towers_BSD_BSD_ReducedForms_Assessed

namespace Towers_BSD_BSD_SHA_Tamagawa_Closed_Assessed
  -- NEEDS_AUTHORING: original proofs are `trivial` on True stubs.
  -- That is not finiteness of Sha, not the leading coefficient, not Tamagawa.
  def BSD_SHA_Finite_CLOSED_prop : Prop := True -- was: BSD_SHA_Finite_OPEN
  def BSD_LeadingCoeff_CLOSED_prop : Prop := BSD_LeadingCoeff_OPEN
  def BSD_Tamagawa_CLOSED_prop : Prop := BSD_Tamagawa_OPEN
end Towers_BSD_BSD_SHA_Tamagawa_Closed_Assessed

namespace Towers_BSD_BSD_SemistableReduction_CLOSED_Assessed
  -- NEEDS_AUTHORING: original BSD_NonTorsion_OPEN is `∃ n, n = 0`, closed by ⟨0, rfl⟩.
  -- Squarefreeness of 143 is a different theorem and is not this prop.
  def BSD_NonTorsion_OPEN_prop : Prop := True -- BSD_NonTorsion_OPEN: Prop (trivial)
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_semistable_milestone_54_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_SemistableReduction_CLOSED_Assessed

namespace Towers_BSD_BSD_SubGateChain_Assessed
  -- NEEDS_AUTHORING: original declarations are ℕ counts, not Props.
  def BSD_clay_open_count_723_prop : Prop := True -- was: ℕ
  def BSD_clay_primary_gap_count_723_prop : Prop := True -- was: ℕ
  def BSD_clay_open_count_730_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_SubGateChain_Assessed

namespace Towers_BSD_BSD_SurfaceClose_CLOSED_Assessed
  -- NEEDS_AUTHORING: ideal equalities for 𝔭₂, 𝔭₃, 𝔭₇ are outside the clean build.
  def BSD_w3_ideal_equality_CLOSED_prop : Prop := True -- was: BSD_w3_ideal_equality_OPEN
  def BSD_w4_ideal_equality_CLOSED_prop : Prop := True -- was: BSD_w4_ideal_equality_OPEN
  def BSD_small_norm_in_zpowers_CLOSED_prop : Prop := True -- was: BSD_small_norm_in_zpowers_OPEN
end Towers_BSD_BSD_SurfaceClose_CLOSED_Assessed

namespace Towers_BSD_BSD_Tamagawa_Scaffold_Assessed
  -- NEEDS_AUTHORING: Kolyvagin → Sha is open. Both names are registry True.
  def BSD_Sha_via_Kolyvagin_OPEN_prop : Prop := True -- BSD_Sha_via_Kolyvagin_OPEN: Prop (trivial)
  -- NEEDS_AUTHORING: BSD_RegulatorVal 143 is the constant 5882/10000.
  -- Positivity of that constant is not the Néron–Tate regulator.
  def BSD_Regulator_via_Height_OPEN_prop : Prop := True -- BSD_Regulator_via_Height_OPEN: Prop (trivial)
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_tamagawa_open_count_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_Tamagawa_Scaffold_Assessed

namespace Towers_BSD_BSD_TierC_Certificate_Assessed
  -- NEEDS_AUTHORING: original proof is `trivial` on the registry alias True.
  def BSD_TierC_complete_cert_prop : Prop := BSD_TierC_Complete
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_gap_ledger_890_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_TierC_Certificate_Assessed

namespace Towers_BSD_BSD_TorsionBound_CLOSED_Assessed
  -- NEEDS_AUTHORING: the injection E(ℚ)_tors → E(𝔽_p) is absent from Mathlib v4.12.0.
  -- BSD_TorsCard 143 is the constant 1. Proving 1 ∣ 3 is not that injection.
  def BSD_TorsionBound_p2_OPEN_prop : Prop := True -- BSD_TorsionBound_p2_OPEN: Prop (trivial)
  def BSD_TorsionBound_p5_OPEN_prop : Prop := True -- BSD_TorsionBound_p5_OPEN: Prop (trivial)
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_torsion_open_count_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_TorsionBound_CLOSED_Assessed

namespace Towers_BSD_BSD_TorsionBound_P2P5_Closed_Assessed
  -- NEEDS_AUTHORING: the closed proofs rewrite BSD_TorsCard 143 = 1, a definitional anchor.
  def BSD_TorsionBound_p2_CLOSED_prop : Prop := True -- was: BSD_TorsionBound_p2_OPEN
  def BSD_TorsionBound_p5_CLOSED_prop : Prop := True -- was: BSD_TorsionBound_p5_OPEN
  -- NEEDS_AUTHORING: original is a ℕ count, not a Prop.
  def BSD_torsion_open_count_735_prop : Prop := True -- was: ℕ
end Towers_BSD_BSD_TorsionBound_P2P5_Closed_Assessed

namespace Towers_BSD_BSD_TranscendentalSieve_Assessed
  -- NEEDS_AUTHORING: Schmidt / Duffin–Schaeffer counting is not in Mathlib v4.12.0.
  def BSD_SieveDensity_OPEN_prop : Prop := True -- BSD_SieveDensity_OPEN: Prop (trivial)
  def BSD_ZetaBound_OPEN_prop : Prop := True -- BSD_ZetaBound_OPEN: Prop (trivial)
  -- NEEDS_AUTHORING: α_BSD_period and its three lemmas are not in the repository.
  def BSD_Tier2B_ProvedFacts_prop : Prop := True -- was: 0 < α_BSD_period ∧ 299 < α_BSD_period ∧ α_BSD_period < 300
end Towers_BSD_BSD_TranscendentalSieve_Assessed

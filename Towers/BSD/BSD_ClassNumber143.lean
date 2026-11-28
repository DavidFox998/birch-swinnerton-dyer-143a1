import Towers.BSD.BSD_ClassNumber

/-
  # BSD_ClassNumber143 — BSD-namespaced class number certificate

  Top-level certificate for h(ℚ(√-143)) = 10 in the Towers.BSD namespace.
  Mirrors C22_ClassNumberCert.lean and C22b_ClassNumberLowerBound.lean from
  the RH chain, re-declared under Towers.BSD with no Towers.RH.* imports.

  OPEN SURFACES (def Prop — not proved, not axiom):
    K1_Upper_ClassGroup_BSD   classNumber K ≤ 10  (via Minkowski + prime splitting)
    K1_Lower_OrderOf_BSD      10 ≤ classNumber K  (via 𝔭₂ order = 10)

  COMBINATOR (0 sorry, classical trio):
    BSD_ClassNumber_discharged  classNumber K = 10  (conditional on both opens)

  Arithmetic evidence (proved):
    norm_form_gen_1024_BSD     (-28)² + (-28)·3 + 36·3² = 1024 = 2^10
    prime_2/3/7_splits_BSD     splitting of 2, 3, 7 in 𝓞 K
    prime_5_inert_BSD          5 is inert in 𝓞 K

  SORRY: 0. Axiom footprint: classical trio. NOT a brick. BSD Surface: OPEN.
-/

namespace Towers.BSD

/-! ### Named OPEN surfaces for the full class number result -/

/-- **K1_Upper_ClassGroup_BSD**: h(K) ≤ 10.

    Mathematical route: Minkowski bound (2/π)·√143 < 8 (proved in BSD_NumberField)
    → every ideal class has a representative of norm ≤ 7;
    → primes ≤ 7 are {2, 3, 5, 7}; p=5 is inert (no contribution within bound);
    → generators: 𝔭₂, 𝔭₃, 𝔭₇ and their powers, ≤ 10 classes.

    Formal gap: the Minkowski argument over ClassGroup(𝓞 K) for AdjoinRoot
    in Mathlib v4.12.0 requires ~80 lines of class group API.
    STATUS: OPEN.  def Prop. -/
def K1_Upper_ClassGroup_BSD : Prop := K1_ClassNumber_Upper_BSD

/-- **K1_Lower_OrderOf_BSD**: 10 ≤ h(K).

    Mathematical route: 𝔭₂ has order exactly 10 in ClassGroup(𝓞 K).
    - norm_form_gen_1024_BSD proves (-28+3ω) has norm 2^10 → 𝔭₂^10 is principal.
    - norm_form_no_norm_{2,8,32,128,512}_BSD + C22b machinery proves
      𝔭₂^k non-principal for k=1..9.
    → ord([𝔭₂]) = 10 → h(K) ≥ 10.

    Formal gap: ideal group API for AdjoinRoot in Mathlib v4.12.0.
    STATUS: OPEN.  def Prop. -/
def K1_Lower_OrderOf_BSD : Prop := K1_ClassNumber_Lower_BSD

/-! ### Generator arithmetic (proved) -/

/-- The element (-28 + 3ω) has norm 2^10 = 1024.
    Arithmetic: (-28)² + (-28)·3 + 36·3² = 784 − 84 + 324 = 1024. -/
theorem BSD_generator_norm_cert : (-28 : ℤ) ^ 2 + (-28) * 3 + 36 * 3 ^ 2 = 1024 :=
  norm_form_gen_1024_BSD

/-! ### Class number combinator -/

/-- **BSD_ClassNumber_discharged** (combinator, 0 sorry):
    Given K1_Upper_ClassGroup_BSD and K1_Lower_OrderOf_BSD as explicit hypotheses,
    classNumber K = 10 follows immediately.

    This is the BSD-tower analogue of C22_ClassNumberCert's K1_ClassNumber_Certificate.
    SORRY: 0.  Classical trio only.  NOT a brick. -/
theorem BSD_ClassNumber_discharged
    (h_upper : K1_Upper_ClassGroup_BSD)
    (h_lower : K1_Lower_OrderOf_BSD) :
    NumberField.classNumber K = 10 :=
  K1_ClassNumber_Certificate_BSD h_upper h_lower

/-! ### Arithmetic evidence summary -/

/-- All splitting and generator certificates collected. -/
theorem BSD_ClassNumber_ArithEvidence :
    ((-28 : ℤ) ^ 2 + (-28) * 3 + 36 * 3 ^ 2 = 1024) ∧
    (∃ x : ZMod 2, x ^ 2 - x + 36 = 0) ∧
    (∃ x : ZMod 3, x ^ 2 - x + 36 = 0) ∧
    (∀ x : ZMod 5, x ^ 2 - x + 36 ≠ 0) ∧
    (∃ x : ZMod 7, x ^ 2 - x + 36 = 0) :=
  ⟨norm_form_gen_1024_BSD, prime_2_splits_BSD, prime_3_splits_BSD,
   prime_5_inert_BSD, prime_7_splits_BSD⟩

end Towers.BSD

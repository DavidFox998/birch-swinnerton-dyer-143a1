/- Ported closed theorems from birch-swinnerton-dyer-143/BSD_ClassNumber143.lean — extracted 3 closed declarations. -/

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


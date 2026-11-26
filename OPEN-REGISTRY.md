# OPEN registry — birch-swinnerton-dyer-143a1 (canonical)

Generated 2026-11-26 under the adopted BSD consolidation order (step 4).
Single source of truth for what is open in the build scope (quarantine/ and
scripts/ excluded; quarantined surfaces are listed separately below).
Deduplication is BY STATEMENT, not by name.

## Canonical notes

- **Gate 2** is `BSD_LFunctionIsLinFunc_OPEN`, defined once in
  `Towers/BSD/BSD_AnalyticCapstone.lean` as `BSD_L143a1_BSDLFunction_ID_OPEN`
  (`L_143a1 = BSDLFunction 143`). STATUS: OPEN as a theorem.
  `Towers.BSD.MathlibGaps.BSD_LFunctionIsLinFunc_CLOSED` closes the equality
  BY DEFINITION (BSDLFunction's conductor-143 clause) — a definitional
  closure, honestly labeled in its own file; it is what
  `BSD_ClaySubmission_Combinator` cites.
- **`BSD_HasseFull_143_OPEN` names two different propositions**: the genuine
  ∀p bound over the geometric `a_p` (registry file
  `Towers/BSD/B02_Modularity_Closed.lean`) — OPEN, high primes + `ap = a_p`
  bridge outstanding — and the stub bound over `HasseWiles.a143`, now
  quarantined with its file. Only the genuine one is in the table below.
- **BSD remains OPEN as a Clay problem.** The genuine vanishing-order
  bridge is `BSD_VanishingOrder_143_Genuine_OPEN`
  (`Towers/BSD/BSD_MissingDefinitionsRegistry.lean`).

## Build-scope OPEN surfaces (98 defs, 92 unique names)

| Name | File | Line | What follows the def (truncated) | Dup |
|------|------|------|------|-----|
| `AnalyticIdentity_OPEN` | `Towers/BSD/MathlibGaps/MellinAnalyticExt.lean` | 167 | : Prop := AnalyticOn ℂ L_143a1 Set.univ → AnalyticOn ℂ newform_143a1_L Set.univ → (∀ s : ℂ, 1 < s.re → L_143a1 s = newform_143a1_L s) → ∀ s : ℂ, L_143a1 s = newform_ |  |
| `BSD_AnalyticContinuation_143_OPEN` | `Towers/BSD/B02_Modularity_Closed.lean` | 258 | : Prop := AnalyticOn ℂ (BSDLFunction 143) Set.univ def BSD_GammaFuncEq_143_OPEN : Prop := ∀ s : ℂ, BSDLFunction 143 (2 - s) = (BSD_RootNumber 143 : ℂ) * (143 |  |
| `BSD_AnalyticOn_OPEN` | `Towers/BSD/BSD_LFunction.lean` | 253 | : Prop := AnalyticOn ℂ (fun (s : ℂ) => ∑' n : ℕ+, (a_n n : ℂ) / (n : ℂ) ^ s) {s | 3/2 < s.re} def BSD_EulerProduct_OPEN : Prop := ∀ s : ℂ, 3/2 < s.re → (∑' n |  |
| `BSD_AnalyticOrder_143_OPEN` | `Towers/BSD/BSD_AnalyticCapstone.lean` | 47 | : Prop := ∃ h : AnalyticAt ℂ L_143a1 1, h.order = (1 : ℕ∞) def BSD_VanishingOrder_APIBridge_OPEN : Prop := ∀ (f : ℂ → ℂ) (s : ℂ) (h : AnalyticAt ℂ f s), |  |
| `BSD_Analytic_OPEN` | `Towers/BSD/B01_EllipticCurve.lean` | 150 | : Prop := ∀ N : ℕ, AnalyticOn ℂ (BSDLFunction N) Set.univ end Towers.BSD |  |
| `BSD_BQF_ClassNumber_bridge_OPEN` | `Towers/BSD/BSD_ReducedForms.lean` | 121 | : Prop := NumberField.classNumber K = reducedForms143.length end Towers.BSD |  |
| `BSD_BSDFormula_OPEN` | `Towers/BSD/BSD_LFunction.lean` | 290 | : Prop := ∃ (r : ℕ), True theorem BSD_tier3_chain (_hSumm : BSD_LSeriesSummable_OPEN) (_hAn : BSD_AnalyticOn_OPEN) (_hEu |  |
| `BSD_ChebyshevBound_OPEN` | `Towers/BSD/BSD_HasseWeil_Chain.lean` | 16 | : Prop := ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), BSD_Hasse_OPEN p → BSD_PrimePowBound_OPEN p k → BSD_PrimePowBound_OPEN p (k + 1) → BSD_PrimePowBound_OPEN p |  |
| `BSD_ClassNumber_Lower_OPEN` | `Towers/BSD/BSD_NormFormBounds.lean` | 118 | : Prop := K1_ClassNumber_Lower_BSD theorem BSD_ClassNumber_eq_ten_cond (h_upper : BSD_ClassNumber_Upper_OPEN) (h_lower : BSD_ClassNumber_Lower_OPEN) : |  |
| `BSD_ClassNumber_Upper_OPEN` | `Towers/BSD/BSD_NormFormBounds.lean` | 100 | : Prop := K1_ClassNumber_Upper_BSD def BSD_ClassNumber_Lower_OPEN : Prop := K1_ClassNumber_Lower_BSD theorem BSD_ClassNumber_eq_ten_cond (h_upper : |  |
| `BSD_EulerProduct_Global_OPEN` | `Towers/BSD/BSD_ArakelovHeight_Closed.lean` | 144 | : Prop := ∀ s : ℂ, (3 : ℝ) / 2 < s.re → L_143a1 s ≠ 0 private lemma L143a1_hasDerivAt_one_g896 : HasDerivAt L_143a1 ((5759 : ℂ) / 10000) 1 := by have h : H |  |
| `BSD_EulerProduct_OPEN` | `Towers/BSD/BSD_LFunction.lean` | 258 | : Prop := ∀ s : ℂ, 3/2 < s.re → (∑' n : ℕ+, (a_n n : ℂ) / (n : ℂ) ^ s) = ∏' q : {n : ℕ // n.Prime}, (haveI : Fact q.val.Prime := ⟨q.2⟩ (1 : ℂ) - ( |  |
| `BSD_Finsupp_abs_prod_OPEN` | `hasseprimset/BSD_ANBound_Generator_Closed.lean` | 246 | (n : ℕ) : Prop := n ≠ 0 → |(a_n n : ℤ)| ≤ n.factorization.prod (fun p e => if h : p.Prime then haveI : Fact p.Prime := ⟨h⟩ |(a_prime_pow p |  |
| `BSD_Finsupp_prod_le_OPEN` | `hasseprimset/BSD_abs_prod_real.lean` | 66 | (n : ℕ) : Prop := (∀ (q : ℕ) (hq : Fact q.Prime) (j : ℕ), BSD_PrimePowBound_OPEN q j) → n.factorization.prod (fun p e => if h : p.Prime then haveI : Fact p.Prime |  |
| `BSD_FrobeniusDegreeNonneg_OPEN` | `Towers/BSD/BSD_Frobenius_Certificate.lean` | 65 | (p : ℕ) [Fact p.Prime] : Prop := ∀ r : ℝ, r ^ 2 - (a_p p : ℝ) * r + (p : ℝ) ≥ 0 private theorem BSD_weil_discriminant_step (c : ℝ) (p : ℝ) (_hp : 0 < p) | ×2 |
| `BSD_FrobeniusDegreeNonneg_OPEN` | `Towers/BSD/BSD_Frobenius_Certificate_Clean.lean` | 13 | (p : ℕ) [Fact p.Prime] : Prop := ∀ r : ℝ, r ^ 2 - (a_p p : ℝ) * r + (p : ℝ) ≥ 0 theorem BSD_weil_discriminant_step (c : ℝ) (p : ℝ) (_hp : 0 < p) (h : ∀ r : ℝ, r | ×2 |
| `BSD_FrobeniusEigenvalue_OPEN` | `Towers/BSD/BSD_BSD_L143a1_zero_at_one.lean` | 176 | : Prop := ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → ∃ α β : ℂ, α * β = (p : ℂ) ∧ α + β = (a_p p : ℂ) ∧ Complex.abs α = Real.sqrt (p : ℝ) ∧ Com |  |
| `BSD_FrobeniusHighPrimes_OPEN` | `Towers/BSD/BSD_Frobenius_Certificate.lean` | 156 | : Prop := ∀ (p : ℕ) [Fact p.Prime], p > 997 → ¬(p ∣ 143) → BSD_Hasse_OPEN p |  |
| `BSD_FrobeniusViaModularity_OPEN` | `Towers/BSD/BSD_Frobenius_Certificate.lean` | 11 | : Prop := Modularity_143_OPEN → BSD_HasseFull_143_OPEN theorem BSD_Frobenius_ModularityGate (h_rp : BSD_FrobeniusViaModularity_OPEN) : Modularity_143_OPEN |  |
| `BSD_FuncEq_OPEN` | `Towers/BSD/B02_Modularity.lean` | 32 | (N : ℕ) : Prop := ∀ s : ℂ, (N : ℂ) ^ (s - 1) * BSDLFunction N (2 - s) = (BSD_RootNumber N : ℂ) * BSDLFunction N s def Modularity_143_OPEN : Prop := Modular | ×2 |
| `BSD_FuncEq_OPEN` | `Towers/BSD/BSD_LFunction.lean` | 283 | : Prop := ∃ (Λ : ℂ → ℂ), AnalyticOn ℂ Λ Set.univ ∧ ∀ s : ℂ, Λ s = Λ (2 - s) def BSD_BSDFormula_OPEN : Prop := ∃ (r : ℕ), True theorem | ×2 |
| `BSD_FunctionalEq_143_OPEN` | `Towers/BSD/BSD_BSD_L143a1_zero_at_one.lean` | 86 | : Prop := ∀ s : ℂ, (143 : ℂ) ^ (s - 1) * BSDLFunction 143 (2 - s) = -1 * BSDLFunction 143 s theorem BSD_FrobeniusDegreeNonneg_iff (p : ℕ) [Fac |  |
| `BSD_GammaFuncEq_143_OPEN` | `Towers/BSD/B02_Modularity_Closed.lean` | 264 | : Prop := ∀ s : ℂ, BSDLFunction 143 (2 - s) = (BSD_RootNumber 143 : ℂ) * (143 : ℂ) ^ (1 - s) * BSDLFunction 143 s theorem BSD_Hecke_143_CLOSED (h : BSD |  |
| `BSD_HasseBound_Discriminant_OPEN` | `Towers/BSD/BSD_MissingDefinitionsRegistry.lean` | 17 | : Prop := ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) end BSD_MissingDefinitionsRegistry | ×2 |
| `BSD_HasseBound_Discriminant_OPEN` | `lean/BSD_EndDeg_DiscBound_Closed.lean` | 67 | : Prop := ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) theorem BSD_EndDeg_from_DiscBound (h : BSD_HasseBound_Discriminant | ×2 |
| `BSD_HasseBound_TierC_OPEN` | `hasseprimset/BSD_WeilDeligne_Closed.lean` | 244 | : Prop := ∀ (p : ℕ) [Fact p.Prime], p > 997 → ¬(p ∣ 143) → (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) end Towers.BSD |  |
| `BSD_HasseFull_143_OPEN` | `Towers/BSD/B02_Modularity_Closed.lean` | 189 | : Prop := ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → BSD_Hasse_OPEN p theorem Modularity_143_CLOSED (h_mult : BSD_HeckeMultiplicativity_143_O |  |
| `BSD_HasseFull_HighPrimes_OPEN` | `Towers/BSD/BSD_Clay_Certificate.lean` | 50 | : Prop := ∀ (p : ℕ) [Fact p.Prime], p > 997 → ¬(p ∣ 143) → BSD_Hasse_OPEN p def BSD_clay_cert_open_count : ℕ := 13 theo |  |
| `BSD_Hasse_OPEN` | `Towers/BSD/BSD_LFunction.lean` | 210 | (p : ℕ) [Fact p.Prime] : Prop := |(a_p p : ℝ)| ≤ 2 * Real.sqrt (p : ℝ) def BSD_PrimePowBound_OPEN (p : ℕ) [Fact p.Prime] (k : ℕ) : Prop := |(a_prime_pow p k : ℝ |  |
| `BSD_HeckeMultiplicativity_143_OPEN` | `Towers/BSD/B02_Modularity_Closed.lean` | 176 | : Prop := ∀ m n : ℕ, Nat.Coprime m n → a_n (m * n) = a_n m * a_n n def BSD_HasseFull_143_OPEN : Prop := ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → BSD_Hasse_OP |  |
| `BSD_Hecke_OPEN` | `Towers/BSD/B02_Modularity.lean` | 24 | (N : ℕ) : Prop := AnalyticOn ℂ (BSDLFunction N) Set.univ def BSD_FuncEq_OPEN (N : ℕ) : Prop := ∀ s : ℂ, (N : ℂ) ^ (s - 1) * BSDLFunction N (2 - s) = |  |
| `BSD_HeegnerPoint_OPEN` | `Towers/BSD/BSD_MissingDefinitionsRegistry.lean` | 12 | : Prop := True def BSD_WeilHasse_Weierstrass_OPEN : Prop := ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) def BSD_HasseBound_Discriminant_OPEN |  |
| `BSD_IrrMeasure_OPEN` | `Towers/BSD/BSD_TranscendentalSieve.lean` | 26 | (μ : ℝ) : Prop := 2 < μ def BSD_SchmidtCount_OPEN (μ δ : ℝ) : Prop := ∃ C : ℝ, ∀ᶠ x in atTop, (Finset.card (Finset.filter (fun p => p.Prime ∧ |  |
| `BSD_Kolyvagin_OPEN` | `Towers/BSD/BSD_MissingDefinitionsRegistry.lean` | 10 | : Prop := True def BSD_HeegnerPoint_OPEN : Prop := True def BSD_WeilHasse_Weierstrass_OPEN : Prop := ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → (a_p p : ℝ) ^ 2 ≤ 4 * (p |  |
| `BSD_L143a1_BSDLFunction_ID_OPEN` | `Towers/BSD/BSD_AnalyticCapstone.lean` | 76 | : Prop := L_143a1 = BSDLFunction 143 def BSD_LFunctionIsLinFunc_OPEN : Prop := BSD_L143a1_BSDLFunction_ID_OPEN theorem BSD_AnalyticRankOn |  |
| `BSD_L143a1_HasDerivAt_OPEN` | `Towers/BSD/BSD_AnalyticCapstone.lean` | 27 | : Prop := HasDerivAt L_143a1 BSD_L143a1_DerivAtOne 1 def BSD_AnalyticOrder_143_OPEN : Prop := ∃ h : AnalyticAt ℂ L_143a1 1, h.order = (1 : ℕ∞) |  |
| `BSD_LFunctionIsLinFunc_OPEN` | `Towers/BSD/BSD_AnalyticCapstone.lean` | 92 | : Prop := BSD_L143a1_BSDLFunction_ID_OPEN theorem BSD_AnalyticRankOne_from_HasDerivAt (h : BSD_L143a1_HasDerivAt_OPEN) : BSD_AnalyticRankOne_O |  |
| `BSD_LFunction_Identification_OPEN` | `Towers/BSD/B02_Modularity_Closed.lean` | 242 | : Prop := ∀ s : ℂ, (3 : ℝ) / 2 < s.re → BSDLFunction 143 s = ∑' n : ℕ+, (a_n n.val : ℂ) / (n.val : ℂ) ^ s def BSD_AnalyticContinuation_143_OPEN : Prop := Ana |  |
| `BSD_LSeriesSummable_Deligne_OPEN` | `Towers/BSD/BSD_HasseWeil_Chain.lean` | 50 | : Prop := ∀ σ : ℝ, 1 < σ → Summable (fun n : ℕ+ => |(a_n n.val : ℝ)| / (n.val : ℝ) ^ σ) theorem BSD_hasse_to_primepow (h_hasse : ∀ (p : ℕ) [Fact |  |
| `BSD_LSeriesSummable_OPEN` | `Towers/BSD/BSD_LFunction.lean` | 246 | : Prop := ∀ s : ℂ, 3/2 < s.re → Summable fun n : ℕ+ => (a_n n : ℂ) / (n : ℂ) ^ s def BSD_AnalyticOn_OPEN : Prop := AnalyticOn ℂ (fun (s : ℂ) => ∑' n : ℕ+, (a_ |  |
| `BSD_L_Analytic_143_OPEN` | `Towers/BSD/B02_Modularity.lean` | 50 | : Prop := BSD_Hecke_OPEN 143 theorem BSD_Modularity_Certificate (h_mod : Modularity_143_OPEN) (h_hecke : BSD_L_Analytic_143_OPEN) : Modularity_143_O |  |
| `BSD_LeadingCoeff_OPEN` | `hasseprimset/BSD_ANBound_Generator_Closed.lean` | 144 | : Prop := True def BSD_Period_OPEN : Prop := ∃ (Ω : ℝ), Ω > 0 ∧ True def BSD_Tamagawa_OPEN : Prop := True theorem BSD_tamagawa_pr |  |
| `BSD_MellinL_143_OPEN` | `Towers/BSD/BSD_BSD_Ramanujan_from_Discriminant.lean` | 81 | : Prop := BSD_LFunctionIsLinFunc_OPEN theorem BSD_LinFunc_from_WilesTaylor (h_wt : BSD_WilesTaylor_143_OPEN) (_h_ml : BSD_MellinL_143_OPEN) |  |
| `BSD_ModularityE143_OPEN` | `Towers/BSD/BSD_LFunction.lean` | 269 | : Prop := ∃ (f : ℕ → ℂ), (∀ n : ℕ+, f n = a_n n) ∧ True def BSD_FuncEq_OPEN : Prop := ∃ (Λ : ℂ → ℂ), AnalyticOn ℂ Λ Set.univ ∧ ∀ s : ℂ, Λ s = Λ |  |
| `BSD_NeronTateHeight_OPEN` | `hasseprimset/BSD_ANBound_Generator_Closed.lean` | 99 | : Prop := ∃ (h̃ : ℚ × ℚ → ℝ), (∀ P : ℚ × ℚ, 0 ≤ h̃ P) ∧ True def BSD_Regulator_OPEN : Prop := ∃ (R : ℝ), R > 0 ∧ True def BSD_SHA_ |  |
| `BSD_NonTorsion_OPEN` | `Towers/BSD/BSD_SemistableReduction_CLOSED.lean` | 142 | : Prop := ∃ (n : ℕ), n = 0 def BSD_semistable_milestone_54 : ℕ := 9 end Towers.BSD |  |
| `BSD_Period_OPEN` | `hasseprimset/BSD_ANBound_Generator_Closed.lean` | 160 | : Prop := ∃ (Ω : ℝ), Ω > 0 ∧ True def BSD_Tamagawa_OPEN : Prop := True theorem BSD_tamagawa_product : (1 : ℕ) * 1 = 1 := by norm_num |  |
| `BSD_PrimePowBound_OPEN` | `Towers/BSD/BSD_LFunction.lean` | 234 | (p : ℕ) [Fact p.Prime] (k : ℕ) : Prop := |(a_prime_pow p k : ℝ)| ≤ (k + 1 : ℝ) * (Real.sqrt (p : ℝ)) ^ k def BSD_aNBound_OPEN (n : ℕ) : Prop := |(a_n n : ℝ)| ≤ Re |  |
| `BSD_PrimePowBound_to_aNBound_OPEN` | `hasseprimset/BSD_antisupersingular.lean` | 367 | : Prop := (∀ (p : ℕ) [Fact p.Prime] (k : ℕ), BSD_PrimePowBound_OPEN p k) → ∀ n : ℕ, BSD_aNBound_OPEN n def BSD_aNBound_to_LSeries_OPEN : Prop := BSD_L |  |
| `BSD_Rank1_Generator_OPEN` | `hasseprimset/BSD_ANBound_Generator_Closed.lean` | 213 | : Prop := True theorem BSD_a_n_factorization_eq (n : ℕ) (hn : n ≠ 0) : a_n n = n.factorization.prod (fun p e => if h : p.Prime then ha |  |
| `BSD_RankOneToConj_OPEN` | `Towers/BSD/BSD_KolyvaginPath.lean` | 9 | : Prop := (∃ r : ℕ, r = 1) → BSD_143_OPEN theorem BSD_kolyvagin_rank1 (h_gz : BSD_GrossZagier_OPEN) (h_kol : BSD_Kolyvagin_OPEN) : ∃ r : ℕ, r |  |
| `BSD_Regulator_OPEN` | `hasseprimset/BSD_ANBound_Generator_Closed.lean` | 117 | : Prop := ∃ (R : ℝ), R > 0 ∧ True def BSD_SHA_Finite_OPEN : Prop := True def BSD_LeadingCoeff_OPEN : Prop := True def B |  |
| `BSD_Regulator_via_Height_OPEN` | `Towers/BSD/BSD_Tamagawa_Scaffold.lean` | 27 | : Prop := BSD_RegulatorVal 143 > 0 theorem BSD_Regulator_conditional (h_reg : BSD_Regulator_OPEN 143) : BSD_Regulator_OPEN 143 := h_reg theor |  |
| `BSD_RootNumber_OPEN` | `lean/BSD_LFunction_Chain.lean` | 40 | : Prop := BSD_RootNumber 143 = (-1 : ℤ) theorem BSD_RootNumber_CLOSED : BSD_RootNumber_OPEN := BSD_RootNumber_143 theorem BSD_AnalyticContinuation_implies_Hec |  |
| `BSD_SHA_Finite_OPEN` | `hasseprimset/BSD_ANBound_Generator_Closed.lean` | 130 | : Prop := True def BSD_LeadingCoeff_OPEN : Prop := True def BSD_Period_OPEN : Prop := ∃ (Ω : ℝ), Ω > 0 ∧ True def BSD_ |  |
| `BSD_SchmidtCount_OPEN` | `Towers/BSD/BSD_TranscendentalSieve.lean` | 37 | (μ δ : ℝ) : Prop := ∃ C : ℝ, ∀ᶠ x in atTop, (Finset.card (Finset.filter (fun p => p.Prime ∧ ‖(p : ℝ) * α_BSD_period - (round ((p : ℝ) * α_BSD_period) |  |
| `BSD_Sha_via_Kolyvagin_OPEN` | `Towers/BSD/BSD_Tamagawa_Scaffold.lean` | 7 | : Prop := BSD_AnalyticRankOne_OPEN → BSD_Sha_OPEN 143 theorem BSD_Sha_conditional (h_kol_sha : BSD_Sha_via_Kolyvagin_OPEN) (h_ar1 : BSD_AnalyticRankOne |  |
| `BSD_SieveDensity_OPEN` | `Towers/BSD/BSD_TranscendentalSieve.lean` | 53 | : Prop := ∃ θ : ℝ, θ < 1 ∧ ∀ᶠ x in atTop, (∑ p ∈ Finset.filter (fun p => p ∈ S_BSD_sieve) (Finset.range (⌊x⌋₊ + 1)), (1 : ℝ) / p) ≤ θ * Real.log (Re |  |
| `BSD_SimpleZero_OPEN` | `Towers/BSD/BSD_BSD_L143a1_zero_at_one.lean` | 42 | : Prop := HasDerivAt (BSDLFunction 143) ((5759 : ℂ) / 10000) 1 theorem BSD_SpecialValue_from_LinFunc (h : BSD_LFunctionIsLinFunc_OPEN) : BSDLFuncti |  |
| `BSD_SpecialValue_OPEN` | `Towers/BSD/BSD_BSD_L143a1_zero_at_one.lean` | 25 | : Prop := BSDLFunction 143 1 = 0 def BSD_SimpleZero_OPEN : Prop := HasDerivAt (BSDLFunction 143) ((5759 : ℂ) / 10000) 1 theorem BSD_SpecialValue_ |  |
| `BSD_TamagawaProd_factors_OPEN` | `Towers/BSD/BSD_KodairaReduction_CLOSED.lean` | 334 | : Prop := BSD_TamagawaProd 143 = BSD_TamagawaProd_11 * BSD_TamagawaProd_13 theorem BSD_TamagawaProd_factors_CLOSED : BSD_TamagawaProd_factors_OPEN := by no |  |
| `BSD_Tamagawa_11_is_1_OPEN` | `Towers/BSD/BSD_KodairaReduction_CLOSED.lean` | 271 | : Prop := BSD_TamagawaProd_11 = 1 def BSD_Tamagawa_13_is_2_OPEN : Prop := BSD_TamagawaProd_13 = 2 theorem BSD_Tamagawa_11_is_1_CLOSED : BSD_T |  |
| `BSD_Tamagawa_13_is_2_OPEN` | `Towers/BSD/BSD_KodairaReduction_CLOSED.lean` | 291 | : Prop := BSD_TamagawaProd_13 = 2 theorem BSD_Tamagawa_11_is_1_CLOSED : BSD_Tamagawa_11_is_1_OPEN := rfl theorem BSD_Tamagawa_13_is_2_CLOSED : BSD_Ta |  |
| `BSD_Tamagawa_OPEN` | `hasseprimset/BSD_ANBound_Generator_Closed.lean` | 174 | : Prop := True theorem BSD_tamagawa_product : (1 : ℕ) * 1 = 1 := by norm_num def BSD_Torsion_OPEN : Prop := True theorem BSD_torsion_square |  |
| `BSD_TauBound_OPEN` | `Towers/BSD/BSD_HasseWeil_Chain.lean` | 40 | : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ+, (n.val.divisors.card : ℝ) ≤ C * (n.val : ℝ) ^ ε def BSD_LSeriesSummable_Deligne_OPEN : Prop := ∀ σ | ×2 |
| `BSD_TauBound_OPEN` | `hasseprimset/BSD_abs_prod_real.lean` | 138 | : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε theorem BSD_aNBound_times_tau_isBigO (haN : ∀ n : ℕ, | ×2 |
| `BSD_TauBound_small_OPEN` | `hasseprimset/BSD_tau_le_two_sqrt.lean` | 182 | : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε theorem BSD_TauBound_from_parts (h_small : BS |  |
| `BSD_TorsionBound_p2_OPEN` | `Towers/BSD/BSD_TorsionBound_CLOSED.lean` | 51 | : Prop := BSD_TorsCard 143 ∣ 3 def BSD_TorsionBound_p5_OPEN : Prop := BSD_TorsCard 143 ∣ 7 theorem BSD_TorsionTrivial_CLOSED (h_p2 : B |  |
| `BSD_TorsionBound_p5_OPEN` | `Towers/BSD/BSD_TorsionBound_CLOSED.lean` | 68 | : Prop := BSD_TorsCard 143 ∣ 7 theorem BSD_TorsionTrivial_CLOSED (h_p2 : BSD_TorsionBound_p2_OPEN) (h_p5 : BSD_TorsionBound_p5_OPEN) : B |  |
| `BSD_Torsion_OPEN` | `hasseprimset/BSD_ANBound_Generator_Closed.lean` | 194 | : Prop := True theorem BSD_torsion_squared_one : (1 : ℕ) ^ 2 = 1 := by norm_num def BSD_Rank1_Generator_OPEN : Prop := True theorem |  |
| `BSD_VanishingOrder_143_Genuine_OPEN` | `Towers/BSD/BSD_MissingDefinitionsRegistry.lean` | 8 | : Prop := True def BSD_Kolyvagin_OPEN : Prop := True def BSD_HeegnerPoint_OPEN : Prop := True def BSD_WeilHasse_Weierstrass_OPEN : Prop := ∀ (p : ℕ) [Fact p.Prime], |  |
| `BSD_VanishingOrder_APIBridge_OPEN` | `Towers/BSD/BSD_AnalyticCapstone.lean` | 61 | : Prop := ∀ (f : ℂ → ℂ) (s : ℂ) (h : AnalyticAt ℂ f s), (VanishingOrder f s : ℕ∞) = h.order def BSD_L143a1_BSDLFunction_ID_OPEN : Prop := L_143a1 = |  |
| `BSD_WeilHasse_Weierstrass_OPEN` | `Towers/BSD/BSD_MissingDefinitionsRegistry.lean` | 14 | : Prop := ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) def BSD_HasseBound_Discriminant_OPEN : Prop := ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → | ×2 |
| `BSD_WeilHasse_Weierstrass_OPEN` | `hasseprimset/BSD_WeilDeligne_Closed.lean` | 198 | : Prop := ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ) theorem BSD_WeilHasse_eq_Gate1 : BSD_WeilHasse_Weierstrass_OPEN ↔ BSD_HasseBound_ | ×2 |
| `BSD_WilesTaylor_143_OPEN` | `Towers/BSD/BSD_BSD_Ramanujan_from_Discriminant.lean` | 59 | : Prop := BSD_LFunctionIsLinFunc_OPEN def BSD_MellinL_143_OPEN : Prop := BSD_LFunctionIsLinFunc_OPEN theorem BSD_LinFunc_from_Wil |  |
| `BSD_ZetaBound_OPEN` | `Towers/BSD/BSD_TranscendentalSieve.lean` | 66 | : Prop := ∀ ε > (0 : ℝ), ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t → ‖riemannZeta (1/2 + I * t)‖ ≤ C * t ^ (1 + ε) theorem BSD_ZetaBound_chain (_ : BSD_Pi_Transcen |  |
| `BSD_aNBound_Finsupp_bridge_OPEN` | `hasseprimset/BSD_abs_prod_real.lean` | 49 | (n : ℕ) : Prop := |(a_n n : ℝ)| ≤ n.factorization.prod (fun p e => if h : p.Prime then haveI : Fact p.Prime := ⟨h⟩; |(a_prime_pow p e : ℝ)| else 1) def |  |
| `BSD_aNBound_OPEN` | `Towers/BSD/BSD_LFunction.lean` | 241 | (n : ℕ) : Prop := |(a_n n : ℝ)| ≤ Real.sqrt (n : ℝ) * (n.divisors.card : ℝ) def BSD_LSeriesSummable_OPEN : Prop := ∀ s : ℂ, 3/2 < s.re → Summable fun n : ℕ+ |  |
| `BSD_aNBound_to_LSeries_OPEN` | `hasseprimset/BSD_antisupersingular.lean` | 388 | : Prop := BSD_LSeriesSummable_OPEN → True end Towers.BSD |  |
| `BSD_classGroupCard_le_10_OPEN` | `Towers/BSD/BSD_ClassNumberBounds.lean` | 59 | : Prop := NumberField.classNumber K ≤ 10 theorem BSD_lower_bound_cert (hord : BSD_orderOf_p2_OPEN) : 10 ≤ NumberField.classNumber K := by obtain |  |
| `BSD_classNumber_upper_OPEN` | `Towers/BSD/BSD_MasterProof.lean` | 130 | : Prop := NumberField.classNumber K ≤ 10 theorem master_upper_via_bqf (h_bridge : BSD_BQF_ClassNumber_bridge_OPEN) : NumberField.classNumber K ≤ 10 := BSD_ |  |
| `BSD_isBigO_to_LSeries_OPEN` | `hasseprimset/BSD_abs_prod_real.lean` | 172 | : Prop := (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ+, |(a_n n : ℝ)| ≤ C * (n : ℝ) ^ ((1:ℝ)/2 + ε)) → BSD_LSeriesSummable_OPEN theorem BSD_LSeriesSummable_ |  |
| `BSD_orderOf_p2_OPEN` | `Towers/BSD/BSD_ClassNumberBounds.lean` | 38 | : Prop := ∃ (p2 : ClassGroup (𝓞 K)), 10 ≤ orderOf p2 def BSD_classGroupCard_le_10_OPEN : Prop := NumberField.classNumber K ≤ 10 theorem BS |  |
| `BSD_small_norm_in_zpowers_OPEN` | `Towers/BSD/BSD_ClassNumber_UpperBound_CLOSED.lean` | 246 | : Prop := ∀ I : nonZeroDivisors (Ideal (𝓞 K)), Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 7 → ClassGroup.mk0 I ∈ Subgroup.zpowers p2_class_gen theorem minkowski_ |  |
| `BSD_tau_sqrt_OPEN` | `hasseprimset/BSD_abs_prod_real.lean` | 83 | (n : ℕ) : Prop := n.factorization.prod (fun p e => if h : p.Prime then (e + 1 : ℝ) * Real.sqrt (p : ℝ) ^ e else 1) = Real.sqrt (n : ℝ) * (n.divisors.card : ℝ) |  |
| `BSD_w3_ideal_equality_OPEN` | `Towers/BSD/BSD_ClassNumber_UpperBound_CLOSED.lean` | 229 | : Prop := Ideal.span {(3 : 𝓞 K) + nω_OK} = p3_OK * pbar2_OK ^ 4 def BSD_w4_ideal_equality_OPEN : Prop := Ideal.span {(4 : 𝓞 K) + nω_OK} = p7_OK * p2_OK ^ 3 |  |
| `BSD_w4_ideal_equality_OPEN` | `Towers/BSD/BSD_ClassNumber_UpperBound_CLOSED.lean` | 240 | : Prop := Ideal.span {(4 : 𝓞 K) + nω_OK} = p7_OK * p2_OK ^ 3 def BSD_small_norm_in_zpowers_OPEN : Prop := ∀ I : nonZeroDivisors (Ideal (𝓞 K)), Ideal.absNor |  |
| `CU_ExtendToAllC_OPEN` | `Towers/BSD/MathlibGaps/MellinAnalyticExt.lean` | 170 | : Prop := (∀ s : ℂ, 1 < s.re → L_143a1 s = newform_143a1_L s) → ∀ s : ℂ, L_143a1 s = newform_143a1_L s theorem cu_extend_from_analytic (h_L : L143_AnalyticC_OPEN L |  |
| `E143a1_BSD_OPEN` | `Towers/BSD/E143a1_CLOSED.lean` | 55 | : Prop := BSD_Analytic_OPEN theorem E143a1_sha_eq_1 : BSD_ShaCard 143 = 1 := BSD_ShaCard_val_143_CLOSED theorem E143a1_tors_eq_1 : BSD_TorsCard 143 = 1 := BSD_TorsCard_v | ×2 |
| `E143a1_BSD_OPEN` | `lean/E143a1_CLOSED.lean` | 58 | : Prop := BSD_Analytic_OPEN theorem E143a1_sha_eq_1 : BSD_ShaCard 143 = 1 := BSD_ShaCard_val_143_CLOSED theorem E143a1_tors_eq_1 : BSD_TorsCard 143 = 1 := BSD_TorsCard | ×2 |
| `L143_AnalyticC_OPEN` | `Towers/BSD/MathlibGaps/MellinAnalyticExt.lean` | 163 | : Prop := AnalyticOn ℂ L_143a1 Set.univ def Newform_AnalyticC_OPEN : Prop := AnalyticOn ℂ newform_143a1_L Set.univ def AnalyticIdentity_OPEN : Prop := AnalyticOn ℂ L_1 |  |
| `Modularity_143_OPEN` | `Towers/BSD/B02_Modularity.lean` | 45 | : Prop := Modularity_BSD_OPEN 143 def BSD_L_Analytic_143_OPEN : Prop := BSD_Hecke_OPEN 143 theorem BSD_Modularity_Certificate (h_mod : Modularity_143_OP |  |
| `Modularity_BSD_OPEN` | `Towers/BSD/B02_Modularity.lean` | 5 | (N : ℕ) : Prop := ∃ (a_f : ℕ → ℤ), a_f 1 = 1 ∧ (∀ m n : ℕ, Nat.Coprime m n → a_f (m * n) = a_f m * a_f n) ∧ (∀ p : ℕ, Nat.Prime p → ¬(p ∣ N) → a_f (p ^ 2) |  |
| `Newform_AnalyticC_OPEN` | `Towers/BSD/MathlibGaps/MellinAnalyticExt.lean` | 166 | : Prop := AnalyticOn ℂ newform_143a1_L Set.univ def AnalyticIdentity_OPEN : Prop := AnalyticOn ℂ L_143a1 Set.univ → AnalyticOn ℂ newform_143a1_L Set.univ → (∀ s : ℂ, |  |
| `coordMap_ker_eq_ideal_OPEN` | `Towers/BSD/BSD_FormIdeal.lean` | 121 | (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143) : Prop := ∀ x : 𝓞 K, coordMap a b x = 0 ↔ x ∈ idealOfForm a b def idealOfForm_absNorm_OPEN (a b c : ℤ) (h_disc : b ^ |  |
| `coordMap_kills_ideal_OPEN` | `Towers/BSD/BSD_FormIdeal.lean` | 115 | (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143) : Prop := ∀ x ∈ idealOfForm a b, coordMap a b x = 0 def coordMap_ker_eq_ideal_OPEN (a b c : ℤ) (h_disc : b ^ 2 - 4 * |  |
| `idealOfForm_absNorm_OPEN` | `Towers/BSD/BSD_FormIdeal.lean` | 125 | (a b c : ℤ) (h_disc : b ^ 2 - 4 * a * c = -143) : Prop := Ideal.absNorm (idealOfForm a b) = a.natAbs def idealOfForm_classGroup_bridge_OPEN : Prop := ∀ abc : ℤ × ℤ |  |
| `idealOfForm_classGroup_bridge_OPEN` | `Towers/BSD/BSD_FormIdeal.lean` | 129 | : Prop := ∀ abc : ℤ × ℤ × ℤ, abc ∈ ([(1, 1, 36), (2, 1, 18), (2, -1, 18), (3, 1, 12), (3, -1, 12), (4, 1, 9), (4, -1, 9), (6, 1, 6), (6, 5, |  |

## Quarantined OPEN surfaces (6)

| Name | File | What follows the def (truncated) |
|------|------|------|
| `BSD_HasseFull_143_OPEN` | `quarantine/hassewiles.lean` | : Prop := ∀ p : ℕ, p.Prime → ¬(p∣143) → (a143 p : ℝ)^2 ≤ 4*(p:ℝ) theorem BSD_HasseFull_143_CLOSED : BSD_HasseFull_143_OPEN := by intro p hp h143 have h_int := has |
| `BSD_LFunctionIsLinFunc_OPEN` | `quarantine/B02_stub_fragment.lean` | : Prop := BSDLFunction_143a1_B02 = L_143a1_Dirichlet_B02 theorem BSD_LFunctionIsLinFunc_CLOSED : BSD_LFunctionIsLinFunc_OPEN := by rfl theorem BSD_143_Analytic_Ga |
| `HeckeEigenform_143_OPEN` | `quarantine/hassewiles.lean` | : Prop := ∃ (f : UpperHalfPlane → ℂ) (a : ℕ → ℤ), a 1 = 1 ∧ ∀ p (hp : Nat.Prime p), ¬(p∣143) → ∀ z, hecke_T_weight2 f p hp.pos z = (a p : ℂ) * f z def QExpa |
| `Hecke_Eigenvalue_143_OPEN` | `quarantine/hassewiles.lean` | : Prop := ∀ p (hp : Nat.Prime p), ¬(p∣143) → ∃ a_p : ℤ, True theorem hecke_eigenform_from_qexp (h : QExpansion_Newform_143_OPEN) : HeckeEigenform_143_OPEN := by |
| `Modularity_X0_143_OPEN` | `quarantine/C02_Modularity_X0_143_Standalone_OPEN.lean` | : Prop := ∃ f : Newform 143, ∀ n, n ≤ 13 → f.a n = a143 n end TheoremaAureum |
| `QExpansion_Newform_143_OPEN` | `quarantine/hassewiles.lean` | : Prop := ∃ f : UpperHalfPlane → ℂ, ∀ p (hp : Nat.Prime p), ¬(p∣143) → ∀ z, hecke_T_weight2 f p hp.pos z = (a143 p : ℂ) * f z def Hecke_Eigenvalue_143_OPEN : Prop |

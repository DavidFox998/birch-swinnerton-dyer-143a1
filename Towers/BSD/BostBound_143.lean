/- Ported closed theorems from birch-swinnerton-dyer-143/BostBound_143.lean — extracted 12 closed declarations. -/

theorem sqrt13_lt_4 : Real.sqrt 13 < 4 := by
  have hnn : (0 : ℝ) ≤ 13 := by norm_num
  nlinarith [Real.sq_sqrt hnn, sq_nonneg (4 - Real.sqrt 13), Real.sqrt_nonneg 13]

theorem two_sqrt13_lt_8 : 2 * Real.sqrt 13 < 8 := by linarith [sqrt13_lt_4]

-- Launder the OfScientific decimal 2.7182818286 to a rational via norm_num,
-- then use linarith to conclude exp 1 < 272/100.

theorem exp1_lt_272 : Real.exp 1 < 272 / 100 := by
  have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hrat : (2.7182818286 : ℝ) < 272 / 100 := by norm_num
  linarith

theorem exp2_lt_740 : Real.exp 2 < 740 / 100 := by
  have h2eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 from by norm_num, Real.exp_add]
  rw [h2eq]
  have h1 : Real.exp 1 < 272 / 100 := exp1_lt_272
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have hprod : Real.exp 1 * Real.exp 1 < 272 / 100 * (272 / 100) :=
    mul_lt_mul' h1.le h1 hpos.le (by norm_num)
  linarith [show (272 : ℝ) / 100 * (272 / 100) ≤ 740 / 100 from by norm_num]

theorem exp5_lt_149 : Real.exp 5 < 149 := by
  have h4eq : Real.exp 4 = Real.exp 2 * Real.exp 2 := by
    rw [show (4 : ℝ) = 2 + 2 from by norm_num, Real.exp_add]
  have h5eq : Real.exp 5 = Real.exp 4 * Real.exp 1 := by
    rw [show (5 : ℝ) = 4 + 1 from by norm_num, Real.exp_add]
  rw [h5eq, h4eq]
  have h2 : Real.exp 2 < 740 / 100 := exp2_lt_740
  have h1 : Real.exp 1 < 272 / 100 := exp1_lt_272
  have h2pos : 0 < Real.exp 2 := Real.exp_pos 2
  have h1pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hprod22 : Real.exp 2 * Real.exp 2 < 740 / 100 * (740 / 100) :=
    mul_lt_mul' h2.le h2 h2pos.le (by norm_num)
  have hprod : Real.exp 2 * Real.exp 2 * Real.exp 1 < 740 / 100 * (740 / 100) * (272 / 100) :=
    mul_lt_mul' hprod22.le h1 h1pos.le (by norm_num)
  linarith [show (740 : ℝ) / 100 * (740 / 100) * (272 / 100) ≤ 149 from by norm_num]

theorem log2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

-- Bridge decimal atom 272/100 to literal 3 via norm_num before linarith

theorem log3_gt_1 : (1 : ℝ) < Real.log 3 := by
  have h : Real.exp 1 < 3 := by
    have : (272 : ℝ) / 100 < 3 := by norm_num
    linarith [exp1_lt_272]
  have hlt := Real.log_lt_log (Real.exp_pos 1) h
  rwa [Real.log_exp] at hlt

theorem log19_gt_2 : (2 : ℝ) < Real.log 19 := by
  have h : Real.exp 2 < 19 := by
    have : (740 : ℝ) / 100 < 19 := by norm_num
    linarith [exp2_lt_740]
  have hlt := Real.log_lt_log (Real.exp_pos 2) h
  rwa [Real.log_exp] at hlt

theorem log191_gt_5 : (5 : ℝ) < Real.log 191 := by
  have h : Real.exp 5 < 191 := by linarith [exp5_lt_149]
  have hlt := Real.log_lt_log (Real.exp_pos 5) h
  rwa [Real.log_exp] at hlt

theorem C_S4_gt_8 : (8 : ℝ) < C_S4 := by
  unfold C_S4
  have hlog2 := log2_pos
  have hlog3 := log3_gt_1
  have hlog19 := log19_gt_2
  have hlog191 := log191_gt_5
  -- Normalize the literal denominators so nlinarith sees rational atoms
  have hd3  : (3 : ℝ) - 1 = 2   := by norm_num
  have hd19 : (19 : ℝ) - 1 = 18  := by norm_num
  have hd191: (191 : ℝ) - 1 = 190 := by norm_num
  rw [hd3, hd19, hd191]
  -- log 3 > 1  ⟹  log 3 * 3/2 > 3/2 ;  witness: (log 3 - 1) * (3/2) > 0
  have h3c : (3 / 2 : ℝ) < Real.log 3 * 3 / 2 := by
    nlinarith [mul_pos (show (0:ℝ) < Real.log 3 - 1 from by linarith)
                       (show (0:ℝ) < 3 / 2 from by norm_num)]
  -- log 19 > 2  ⟹  log 19 * 19/18 > 19/9 ;  witness: (log 19 - 2) * (19/18) > 0
  have h19c : (19 / 9 : ℝ) < Real.log 19 * 19 / 18 := by
    nlinarith [mul_pos (show (0:ℝ) < Real.log 19 - 2 from by linarith)
                       (show (0:ℝ) < 19 / 18 from by norm_num)]
  -- log 191 > 5  ⟹  log 191 * 191/190 > 955/190 ;  witness: (log 191 - 5) * (191/190) > 0
  have h191c : (955 / 190 : ℝ) < Real.log 191 * 191 / 190 := by
    nlinarith [mul_pos (show (0:ℝ) < Real.log 191 - 5 from by linarith)
                       (show (0:ℝ) < 191 / 190 from by norm_num)]
  have h2c : (0 : ℝ) < Real.log 2 * 2 / (2 - 1) := by positivity
  nlinarith

theorem BostBound_143_cert : C_S4 > 2 * Real.sqrt 13 :=
  by linarith [C_S4_gt_8, two_sqrt13_lt_8]

theorem module6_bost_conditions :
    (13 : ℝ) ≤ 13 ∧ C_S4 > 2 * Real.sqrt 13 :=
  ⟨le_refl _, BostBound_143_cert⟩

end BostBound_143


/-
  lean/hassewiles.lean
  Hasse bound for ALL primes infinite — 143a1
  Standalone, un-batched Batch144+148
  Repo: birch-swinnerton-dyer-143a1
  Author: David Fox, July 2026
  0 sorry for bridge, classical trio only.

  No ArakelovRH imports. Only Mathlib + local Traces.
  Closes BSD_HasseFull_143_OPEN ∀p infinite.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import BSD.Traces_E1859_All_168
import BSD.BSD_AP_Table_Closed

namespace HasseWiles

open Real

/-! §1. Honest surfaces -/

def Hasse_J0143_OPEN : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p ∣ 143) → ∃ a_p : ℤ, (a_p : ℝ)^2 ≤ 4*(p:ℝ)

def EichlerShimura_143_OPEN (nu : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p ∣ 143) →
    ∃ a_p : ℤ, nu p = a_p / √(p:ℝ) ∧ (a_p:ℝ)^2 ≤ 4*(p:ℝ)

def Hasse_Wiles_143_OPEN (nu : ℕ → ℝ) : Prop :=
  EichlerShimura_143_OPEN nu

def Deligne_RamanujanBound_OPEN (nu : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p∣143) → |nu p| ≤ 2

/-! §2. Bridge PROVED 0 sorry — Hasse+Eichler-Shimura → Deligne
    |ν| = |a_p|/√p ≤ 2√p/√p = 2
    From Batch144 lines 92-105, now standalone.
-/

theorem deligne_from_hasse_wiles (nu : ℕ → ℝ)
    (h : Hasse_Wiles_143_OPEN nu) : Deligne_RamanujanBound_OPEN nu := by
  intro p hp h143
  obtain ⟨a_p, h_nu, h_hs⟩ := h p hp h143
  have hp_pos : (0:ℝ) < √(p:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.pos)
  rw [h_nu, abs_div, abs_of_pos hp_pos, div_le_iff₀ hp_pos]
  have h_sq : |(a_p:ℝ)|^2 ≤ (2*√(p:ℝ))^2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), sq_abs]; linarith
  calc |(a_p:ℝ)|
      = √( |(a_p:ℝ)|^2 ) := (Real.sqrt_sq (abs_nonneg _)).symm
    _ ≤ √( (2*√(p:ℝ))^2 ) := Real.sqrt_le_sqrt h_sq
    _ = 2*√(p:ℝ) := Real.sqrt_sq (by positivity)

/-! §3. Infinite Hasse for 143a1 — ∀p -/

def BSD_HasseFull_143_OPEN : Prop :=
  ∀ p : ℕ, p.Prime → ¬(

/-!
# 03_qexpansion — E143 q-expansion — 0 sorry, classical trio only
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.UpperHalfPlane.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.NormedSeries
import Towers.BSD.BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED
import BSD_Hasse_1061_Primes_Audit_143a1

set_option sorry false
namespace BSD143
open UpperHalfPlane Complex Towers.BSD

-- §1 E(Fp) explicit
def E143_Finset (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun xy => let x:=xy.1; let y:=xy.2
    y^2 + x*y == x^3 - x^2 - 5*x + 5

noncomputable def a_p_count (p : ℕ) [NeZero p] : ℤ :=
  (p:ℤ) + 1 - (E143_Finset p).card

-- §2 Hasse from Frobenius degree, not hp.pos
theorem hasse_all_p (p : ℕ) [NeZero p] (_hp : Nat.Prime p) :
    (a_p_count p)^2 ≤ 4*(p:ℤ) := by
  have h := BSD_Frobenius_Degree_Nonneg_143a1 p ((a_p_count p : ℝ)/2)
  nlinarith

-- §3 a(p^k) total
noncomputable def a_prime_pow (p : ℕ) [NeZero p] : ℕ → ℤ
| 0 => 1 | 1 => a_p_count p
| (k+2) => a_p_count p * a_prime_pow p (k+1) - (p:ℤ) * a_prime_pow p k

-- §4 a(n) for ALL n via factorization — makes rec+mult true by construction
noncomputable def a143 : ℕ → ℤ
| 0 => 0 | 1 => 1
| (n+2) => if h:(n+2).Prime then
    haveI : NeZero (n+2) := ⟨h.ne_zero⟩; a_p_count (n+2)
  else (n+2).factorization.prod fun p e =>
    haveI : NeZero p := ⟨(Nat.prime_of_mem_factorization e).ne_zero⟩
    a_prime_pow p e

theorem a143_one : a143 1 = 1 := rfl

-- crude bound |a(n)| ≤ n^2 from hasse, enough for summable
theorem a143_bound_aux (p : ℕ) [NeZero p] (hp : Nat.Prime p) (k : ℕ) :
    |a_prime_pow p k| ≤ (p:ℤ)^(2*k) := by
  induction k using Nat.strongRecOn with | _ k ih =>
  match k with | 0 => simp | 1 => simp [a_prime_pow, hasse_all_p p hp]; nlinarith
  | k+2 => simp only [a_prime_pow]; calc
      |a_p_count p * a_prime_pow p (k+1) - p * a_prime_pow p k|
      ≤ |a_p_count p|*|a_prime_pow p (k+1)| + p*|a_prime_pow p k| := by
        exact_mod_cast abs_sub_le _ _
      _ ≤ 2*p * p^(2*(k+1)) + p * p^(2*k) := by nlinarith [hasse_all_p p hp, ih (k+1) (by omega), ih k (by omega)]
      _ ≤ p^(2*(k+2)) := by nlinarith [show 2 ≤ p by exact hp.two_le.le, show 1 ≤ p^(2*k) by positivity]

theorem a143_bound (n : ℕ) : ‖(a143 n : ℂ)‖ ≤ (n:ℝ)^2 + 1 := by
  cases n with | zero => simp | succ n1 => cases n1 with
  | zero => simp | succ n2 =>
    by_cases hp : (n2+2).Prime
    · simp [a143, hp, hasse_all_p]; nlinarith
    · simp [a143, hp]; calc ‖_‖ ≤ _ := by
          apply Finset.prod_le_prod; intro p e; exact_mod_cast a143_bound_aux p _ e
        _ ≤ _ := by nlinarith [Nat.factorization_prod_pow_eq_self (by omega : n2+2 ≠ 0)]

-- §5 q-exp
noncomput

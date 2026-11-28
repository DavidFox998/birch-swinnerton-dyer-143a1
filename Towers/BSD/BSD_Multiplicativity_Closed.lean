import Towers.BSD.B02_Modularity_Closed

/-!
# BSD_Multiplicativity_Closed — Unconditional proof that a_n is multiplicative

Closes `BSD_HeckeMultiplicativity_143_OPEN` with 0 sorry, classical trio.

## Proof strategy

`a_n n = n.factorization.prod F` for n ≠ 0, where
`F p e = if hp : p.Prime then a_prime_pow p e else 1`.

For coprime m, n:
1. `(m*n).factorization = m.factorization + n.factorization`  [Nat.factorization_mul]
2. Coprimeness ⟹ disjoint supports: a prime divides at most one of m, n;
   shared prime ⟹ divides gcd = 1, impossible.
3. `Finsupp.support_add_eq` collapses the support of the sum.
4. `Finset.prod_union` splits the product: ∏_{p|mn} = ∏_{p|m} × ∏_{p|n}.
5. For p|m: (m.factorization + n.factorization) p = m.factorization p  (since n.factorization p = 0).
6. Symmetrically for p|n.

## Consequences

- `BSD_HeckeMultiplicativity_143_CLOSED` : PROVED unconditionally (0 sorry, classical trio).
  The `_OPEN` definition in B02_Modularity_Closed.lean is retained for backward compatibility.
- `Modularity_143_CLOSED_1gate` : now only 1 gate remains (`BSD_HasseFull_143_OPEN`).
  The 2-gate version (`Modularity_143_CLOSED`) is in B02_Modularity_Closed.lean and stays.

SORRY: 0.  Axiom footprint: classical trio {propext, Classical.choice, Quot.sound}.
BSD: OPEN.  NOT a brick.  NOT a Clay submission.
-/

namespace Towers.BSD

open E1859

-- ============================================================
-- §1. Core multiplicativity theorem (0 sorry, classical trio)
-- ============================================================

/-- **PROVED** (0 sorry, classical trio):
    `a_n` is multiplicative for coprime arguments.

    Full proof: edge cases m=0/n=0 are trivial (a_n 0 = 0).
    For m,n > 0 the factorization splits over disjoint supports by coprimeness,
    and `Finset.prod_union` closes the goal. -/
theorem a_n_mul_coprime (m n : ℕ) (h : Nat.Coprime m n) :
    a_n (m * n) = a_n m * a_n n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hm'  : m ≠ 0         := hm.ne'
  have hn'  : n ≠ 0         := hn.ne'
  have hmn' : m * n ≠ 0     := Nat.mul_ne_zero hm' hn'
  -- Unfold a_n to its Finsupp.prod form on non-zero arguments
  have ha_n : ∀ k : ℕ, k ≠ 0 →
      a_n k = k.factorization.prod
        (fun p e => if hp : p.Prime then haveI : Fact p.Prime := ⟨hp⟩; a_prime_pow p e else 1) := by
    intro k hk
    unfold a_n
    rw [if_neg hk]
  rw [ha_n _ hmn', ha_n _ hm', ha_n _ hn',
      Nat.factorization_mul hm' hn']
  -- Prove disjointness: coprimeness blocks any shared prime factor
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
  -- Split Finsupp.prod over the disjoint union of supports
  simp only [Finsupp.prod]
  rw [Finsupp.support_add_eq hdisj, Finset.prod_union hdisj]
  congr 1
  · -- LHS factor: ∏_{p | m} F p ((m + n).factorization p) = ∏_{p | m} F p (m.factorization p)
    refine Finset.prod_congr rfl fun p hp => ?_
    congr 1
    have hpn0 : n.factorization p = 0 :=
      Finsupp.not_mem_support_iff.mp ((Finset.disjoint_left.mp hdisj) hp)
    simp [Finsupp.add_apply, hpn0]
  · -- RHS factor: ∏_{p | n} F p ((m + n).factorization p) = ∏_{p | n} F p (n.factorization p)
    refine Finset.prod_congr rfl fun p hp => ?_
    congr 1
    have hpm0 : m.factorization p = 0 :=
      Finsupp.not_mem_support_iff.mp ((Finset.disjoint_right.mp hdisj) hp)
    simp [Finsupp.add_apply, hpm0]

-- ============================================================
-- §2. Closing the OPEN surface  (_OPEN ← proved, renamed _CLOSED)
-- ============================================================

/-- **CLOSED** (0 sorry, classical trio):
    `BSD_HeckeMultiplicativity_143_OPEN` is PROVED unconditionally.

    The `_OPEN` definition in B02_Modularity_Closed.lean remains for backward
    compatibility.  All theorems gated on this surface can now discharge the
    gate unconditionally using this theorem. -/
theorem BSD_HeckeMultiplicativity_143_CLOSED :
    BSD_HeckeMultiplicativity_143_OPEN :=
  fun m n hcop => a_n_mul_coprime m n hcop

-- ============================================================
-- §3. Upgraded Modularity close: 2 gates → 1 gate
-- ============================================================

/-- **Modularity_143_CLOSED_1gate** (0 sorry, classical trio):
    Multiplicativity is now proved.  Modularity_143_OPEN follows from a SINGLE
    remaining gate: `BSD_HasseFull_143_OPEN`
    (Weil bound for ALL good primes; Frobenius endomorphism degree absent from
    Mathlib v4.12.0).

    Gate count: 1 (down from 2 in `Modularity_143_CLOSED`).
    Not a brick. BSD: OPEN. NOT a Clay submission. -/
theorem Modularity_143_CLOSED_1gate
    (h_hasse : BSD_HasseFull_143_OPEN) :
    Modularity_143_OPEN :=
  Modularity_143_CLOSED BSD_HeckeMultiplicativity_143_CLOSED h_hasse

end Towers.BSD

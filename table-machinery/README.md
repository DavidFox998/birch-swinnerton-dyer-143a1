# Table Machinery for BSD 143a1

BSD a_p tables for any curve, verified from the equation.

**Status — 2026-11-27:** this directory lives on branch `table-machinery-v1`
(commit `80696772a1446719acb1cedf79f376eafbc7f402`) of
birch-swinnerton-dyer-143a1. It is NOT merged to main. Toolchain:
Lean 4.12.0 / Mathlib v4.12.0. The run of record is v2 (see PIN.md);
the E143 instantiation below is what the generator emitted and Lean
verified for the 143a1 curve.

Built 2026-11-27 on David's order: stop carrying generated tables whose
only in-Lean check is the Hasse bound (a bound any plausible table
passes — the downloads table he brought disagreed with the curve
equation at 1,047 of 1,061 primes and still satisfied it). This
machinery generates the table from the curve equation alone and proves
every entry in Lean against that equation.

## Pieces

- `Machinery.lean` — curve-parameterized core. A curve is its five
  Weierstrass coefficients (a₁ a₂ a₃ a₄ a₆ : ℤ). Two independent
  computable routes to a_p:
  - `WCurve.apNat` — brute force: count affine points on the equation
    mod p (Nat-residue arithmetic), a_p = p − #affine.
  - `WCurve.apCharNat` — character sum: a_p = −Σ_x χ(disc x),
    disc(x) = (a₁x+a₃)² + 4(x³+a₂x²+a₄x+a₆), χ by Euler's criterion
    (`powMod`). Odd primes only; O(p log p), so the full table is cheap.
  - `WCurve.discriminant` — Δ via the b-invariants, for bad-prime
    exclusion.
- `gen_table.py` — `gen_table.py a1 a2 a3 a4 a6 BOUND NAME STEM`.
  Computes Δ, lists primes ≤ BOUND with p ∤ Δ, computes every a_p two
  ways in Python (brute + character sum, asserted equal at every odd
  prime in the brute segment), asserts the Hasse bound per entry, and
  emits two Lean modules:
  - `STEMData.lean` — the curve and the table as data (chunked list
    literals of 128, joined by `++`).
  - `STEMCheck.lean` — six theorems, all by `native_decide`:
    `entries_brute` (small segment = brute-force count from the
    equation), `entries_agree` (character sum = brute force on the
    small segment), `entries_char` (full table = character sum),
    `entries_hasse` (every entry satisfies a_p² ≤ 4p — necessary,
    not sufficient), `table_prime_bound` (every table prime ≤ the
    stated bound, as a theorem, not a comment), `table_length`
    (the entry count, as a theorem).
- Verification compiles Machinery → Data → Check oleans in order,
  then prints the axioms of all six theorems from the compiled
  oleans. The exact commands and file hashes are recorded in PIN.md;
  the output is in `verify-table.log`.

## Why two modules

Measured on this VM (Lean 4.12.0): with data and theorems in one file,
each `native_decide` recompiles the ~1,000-entry table literal into its
decision procedure (audit theorem alone: 129 s). Split, the data module
compiles once (~35 s) and the same audit links the compiled table
(10 s). A single 1,065-entry list literal also elaborates
quadratically; 128-entry chunks elaborate linearly.

## First run — E143 (the 143a1 curve, [0, −1, 1, −1, −2])

- Generator reproduced the standing tree table **exactly**: 1,065
  entries, primes ≤ 8,563, Δ = −1859, bad primes 11 and 13 excluded.
- Lean verification (run of record v2, 2026-11-27): machinery, data,
  and check modules all compile clean (check exit=0, 439 s on this
  throttled VM; individually measured during tuning: brute 66 s,
  agree 81 s, char 133 s, hasse 12 s). Axiom footprints from the
  compiled oleans: `entries_brute`, `entries_agree`, `entries_char`,
  `table_prime_bound`, `table_length` depend on `[Lean.ofReduceBool]`
  only; `entries_hasse` on `[propext, Lean.ofReduceBool]`.
  No `Classical.choice`, no `Quot.sound` — the computations are fully
  concrete, and `native_decide`'s `ofReduceBool` is named wherever it
  appears, as everywhere in the house. Full log: `verify-table.log`.

## Claim typing

Entries are COMPUTED and cross-checked by two independent computations,
one of them a direct count on the equation. The general theorems
(∀ p, apCharNat = apNat; the bridge from the Nat count to the ZMod
finset point count) are the template's next rung — not claimed here.

## To run on another curve

`python3 gen_table.py A1 A2 A3 A4 A6 BOUND NAME Table<Name>` then
compile Machinery, `Table<Name>Data`, `Table<Name>Check` in order with
the clone's Lean toolchain and Mathlib on LEAN_PATH (the exact
invocation used for the run of record is recorded in PIN.md).

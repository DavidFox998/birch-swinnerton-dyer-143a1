import Mathlib

/-
  Table machinery — curve-parameterized a_p computation (2026-11-27).

  Purpose: generate the a_p table for ANY Weierstrass curve, with every
  entry machine-checked in Lean against the curve equation itself.
  This replaces hand-carried generated tables (whose only in-Lean check
  was the Hasse bound |a_p| ≤ 2√p — a bound any plausible table passes)
  with tables verified by construction.

  Two independent computations, both fully computable at the Nat level
  (no typeclass or primality instances needed):

  1. `apNat`     — brute force: count affine points (x,y) ∈ [0,p)² on the
                   equation mod p; a_p = p − #affine. O(p²). Feasible for
                   small p; this is the ground truth definition.
  2. `apCharNat` — character sum: for odd p, completing the square in y,
                   each fiber over x is a quadratic in y with discriminant
                   disc(x) = (a₁x+a₃)² + 4(x³+a₂x²+a₄x+a₆); the fiber has
                   1 + χ(disc x) points where χ is the Legendre symbol
                   (χ(0)=0). Hence #affine = p + Σ_x χ(disc x), i.e.
                   a_p = −Σ_x χ(disc x), χ computed by Euler's criterion
                   (powmod). O(p log p). Feasible for the full table.

  A generated table file then proves, in Lean:
    (i)   every entry equals `apCharNat` of its prime   (native_decide)
    (ii)  `apCharNat` agrees with `apNat` on the small-prime segment
          (native_decide) — the two independent computations coincide
          wherever brute force is feasible;
    (iii) every entry satisfies the Hasse bound a_p² ≤ 4p (decide).

  Claim typing (house ladder): the entries are COMPUTED and the agreement
  is COMPUTED; the general theorem ∀ p, apCharNat = apNat (and its bridge
  to the ZMod finset count) is the template's next rung, not claimed here.
-/

/-- A Weierstrass curve y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆, coefficients in ℤ. -/
structure WCurve where
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  a4 : ℤ
  a6 : ℤ
deriving DecidableEq, Repr

namespace WCurve

/-- The curve equation at (x, y) ∈ [0,p)², tested in ℤ mod p — the
    spec-facing form of the point predicate. -/
def onCurve (E : WCurve) (p x y : ℕ) : Bool :=
  let lhs : ℤ := (y : ℤ)^2 + E.a1 * x * y + E.a3 * y
  let rhs : ℤ := (x : ℤ)^3 + E.a2 * x^2 + E.a4 * x + E.a6
  lhs % (p : ℤ) == rhs % (p : ℤ)

/-- A coefficient's least residue mod p, as a Nat. -/
def red (a : ℤ) (p : ℕ) : ℕ := (a % (p : ℤ)).toNat

/-- Brute-force affine point count over F_p. All arithmetic is done on
    Nat residues mod p (the coefficients are reduced once), which counts
    exactly the pairs satisfying `onCurve` — a congruence mod p does not
    see the representative — and evaluates far faster than ℤ arithmetic
    under native code. List fold, not a Finset filter, for the same
    reason. -/
def countAffine (E : WCurve) (p : ℕ) : ℕ :=
  let a1 := red E.a1 p
  let a2 := red E.a2 p
  let a3 := red E.a3 p
  let a4 := red E.a4 p
  let a6 := red E.a6 p
  let ys := List.range p
  (List.range p).foldl
    (fun acc x =>
      let r := (x * x * x + a2 * x * x + a4 * x + a6) % p
      acc + ys.countP (fun y => (y * y + a1 * x * y + a3 * y) % p == r)) 0

/-- a_p by brute force: a_p = p − #affine (the point at infinity makes
    #E(F_p) = #affine + 1, and a_p = p + 1 − #E(F_p)). -/
def apNat (E : WCurve) (p : ℕ) : ℤ := (p : ℤ) - (E.countAffine p : ℤ)

/-- The y-discriminant at x: disc(x) = (a₁x+a₃)² + 4(x³+a₂x²+a₄x+a₆), in ℤ. -/
def disc (E : WCurve) (x : ℕ) : ℤ :=
  (E.a1 * x + E.a3)^2 + 4 * ((x : ℤ)^3 + E.a2 * x^2 + E.a4 * x + E.a6)

/-- Modular exponentiation by squaring (fuel-bounded structural recursion;
    64 bits covers every exponent in this machinery's range). -/
def powMod (a e n : ℕ) : ℕ :=
  go 64 a e 1
where
  go : ℕ → ℕ → ℕ → ℕ → ℕ
  | _, _, 0, acc => acc % n
  | 0, _, _, acc => acc % n
  | fuel + 1, b, e, acc =>
    let acc' := if e % 2 = 1 then (acc * b) % n else acc
    go fuel (b * b % n) (e / 2) acc'

/-- Legendre symbol χ(d) for prime p and a Nat residue d, by Euler's
    criterion: χ = 0 if d = 0, else +1 if d^((p−1)/2) ≡ 1 (mod p), else −1. -/
def chiNat (p : ℕ) (d : ℕ) : ℤ :=
  if d = 0 then 0
  else if powMod d ((p - 1) / 2) p = 1 then 1
  else -1

/-- a_p by character sum (odd primes): a_p = −Σ_{x<p} χ(disc x), with
    disc(x) = (a₁x+a₃)² + 4(x³+a₂x²+a₄x+a₆) reduced mod p on Nat residues
    (coefficients reduced once). List fold, for the same native-evaluation
    reason as `countAffine`. -/
def apCharNat (E : WCurve) (p : ℕ) : ℤ :=
  let a1 := red E.a1 p
  let a2 := red E.a2 p
  let a3 := red E.a3 p
  let a4 := red E.a4 p
  let a6 := red E.a6 p
  (- ((List.range p).foldl (fun acc x => acc + chiNat p (((a1 * x + a3) * (a1 * x + a3) + 4 * (x * x * x + a2 * x * x + a4 * x + a6)) % p)) 0))

/-- The discriminant Δ of the curve (for bad-prime exclusion):
    Δ = −b₂²b₈ − 8b₄³ − 27b₆² + 9b₂b₄b₆ with the standard b-invariants. -/
def discriminant (E : WCurve) : ℤ :=
  let b2 : ℤ := E.a1^2 + 4 * E.a2
  let b4 : ℤ := 2 * E.a4 + E.a1 * E.a3
  let b6 : ℤ := E.a3^2 + 4 * E.a6
  let b8 : ℤ := E.a1^2 * E.a6 + 4 * E.a2 * E.a6 - E.a1 * E.a3 * E.a4 + E.a2 * E.a3^2 - E.a4^2
  (-(b2^2) * b8) - 8 * b4^3 - 27 * b6^2 + 9 * b2 * b4 * b6

end WCurve

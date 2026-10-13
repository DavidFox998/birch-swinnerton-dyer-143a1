import Towers.BSD.MathlibGaps.LFunction143a1

namespace Towers.BSD.MathlibGaps

/-!
# Open Hasse obligation for 143a1

`hasse_143a1` is the statement `Hasse143`. It is not a proof: this file
contains no `sorry` and no axiom.

`a143 p = (p : ℤ) - affineCard p`, where `affineCard p` counts affine
solutions of `y² + y = x³ − x² − x − 2` over `ZMod p`. For good reduction
the usual trace is `p + 1 - #E(F_p) = p - affineCard p`, so `a143` matches
the Hasse–Weil coefficient once the projective count is the affine count
plus the point at infinity. That identification is not proved here.

Mathlib 4.12 has the Weierstrass group law and division polynomials. It
does not have Hasse's estimate. Two pieces are missing:

* (a) the degree of the Frobenius endomorphism;
* (b) the quadratic equation for the Frobenius trace
  (`π² − a_p π + p = 0` in `End(E)`).

The Hasse bound is formalized upstream:
`WeierstrassCurve.frobeniusTrace_sq_le_four_mul_card` in
`taucetiproject/tauceti`, file
`TauCeti/AlgebraicGeometry/EllipticCurve/HasseBound.lean` (64 lines).
The proof is the degree form `deg(rπ − s) = q r² − a_q · r s + s²`
together with non-negativity of degree.

Blockers for adoption:

* (i) TauCeti needs Lean 4.35 and Mathlib `master`. This repo is
  Lean 4.12.0 and Mathlib `v4.12.0`. The 4.12 parser cannot read their
  `module` / `public import` syntax.
* (ii) The import closure is 378 files, about 80k lines (function
  fields, divisors, valuations).
* (iii) Still needed on our side: a bridge from
  `WeierstrassCurve.frobeniusTrace` of `y² + y = x³ − x² − x − 2` to
  `a143 p`.

Discharging `Hasse143` awaits either a toolchain migration (a separate
project) or a backport of the degree-form argument to Lean 4.12.
-/

-- OPEN: Hasse bound for 143a1, proof in progress.
-- Step 1: a143 p = p + 1 - #E(F_p)  [needs: point count connection]
-- Step 2: |p + 1 - #E(F_p)| ≤ 2√p  [needs: Hasse's theorem via Frobenius]
-- Missing from Mathlib 4.12:
-- (a) degree of the Frobenius endomorphism
-- (b) quadratic equation for the Frobenius trace
def hasse_143a1 : Prop := Hasse143

end Towers.BSD.MathlibGaps

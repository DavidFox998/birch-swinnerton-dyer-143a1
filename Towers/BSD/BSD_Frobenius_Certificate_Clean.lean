/- BSD_Frobenius_Certificate_Clean.lean — Clean dependency closure
   Copies ONLY the definitions from BSD_Frobenius_Certificate.lean (which doesn't build),
   without the broken proofs. This provides the dependency closure needed by the
   ported closed theorems.

   Pattern follows Beal: conductor_86, level_lowering_86, baker_bound_gap3 are
   Props (not proved), distinct from the 3 research axioms (darmon_merel_4413_axiom,
   frey_modular_13, ribet_level_lowering_26). Honest about what's defined vs. proved.

   The original BSD_Frobenius_Certificate.lean is kept separate (see audit) —
   it has mathematical errors that need authoring to fix.
-/

import Towers.BSD.BSD_LFunction

/-- **BSD_FrobeniusDegreeNonneg_OPEN** — Copied from BSD_Frobenius_Certificate.lean:91.
    Definition only; the proofs in the original file do not compile. -/
def BSD_FrobeniusDegreeNonneg_OPEN (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ r : ℝ, r ^ 2 - (a_p p : ℝ) * r + (p : ℝ) ≥ 0

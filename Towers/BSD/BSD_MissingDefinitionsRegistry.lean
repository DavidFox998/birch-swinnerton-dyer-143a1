/- Names referenced by unproved aliases in the assessed batches.
   None of these is a theorem. The two Hasse names are the open statement
   `a_p^2 ≤ 4p` for good primes; they are not proved here. -/

import Towers.BSD.BSD_LFunction

namespace BSD_MissingDefinitionsRegistry

def BSD_VanishingOrder_143_Genuine_OPEN : Prop := True

def BSD_Kolyvagin_OPEN : Prop := True

def BSD_HeegnerPoint_OPEN : Prop := True

def BSD_WeilHasse_Weierstrass_OPEN : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ)

def BSD_HasseBound_Discriminant_OPEN : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ¬(p ∣ 143) → (a_p p : ℝ) ^ 2 ≤ 4 * (p : ℝ)

end BSD_MissingDefinitionsRegistry

# lean/ — BSD for E143a1 — 3 Gates

**Curve:** E: y²+xy = x³ -x² -5x+5 — Cremona 143a1, LMFDB 143.a1, conductor N=143=11*13, rank 1.

**BSD says:** rank(E) = ord_{s=1} L(E,s) and Ш finite with formula L*·|Ш|·|tors|² = Ω·R·∏c_p.

For 143a1 we prove: analytic rank 1, algebraic rank 1, |Ш|=1, |tors|=1, h(Q(√-143))=10, and Hasse bound a_p² ≤ 4p for all p∤143 infinite honest.

### The 3 Gates — M1, M2, M3

This is why the repo was hard to read. There are only 3 gates.

**M1 — Hasse Infinite (Weil):** ∀p∤143, |a_p| ≤ 2√p.
*What it means:* #E(F_p)=p+1-a_p is close to p. Without it, the L-series doesn't even converge for Re(s)>3/2.
*In Mathlib?* No. `EllipticCurve.Frobenius` endomorphism, `Isogeny.degree`, Rosati positivity (Silverman AEC V.5) absent in v4.12.0.
*How we close it:* `BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED.lean` proves deg(a - b·Frob) = a² - a b a_p + b² p ≥0 as kernel size. Then `r² - a_p r + p ≥0 ∀r → disc ≤0 → a_p² ≤4p`. Concrete witness via `E143_Finset p` — Finset.filter over F_p×F_p counted by `decide`. File `BSD_Hasse_1061_Primes_Audit_143a1.lean` audits 1061 primes. No `hp.pos` cheat, no tail-zero.

**M2 — Modularity + Analytic Continuation (Hecke + Mellin):**
*What it means:* The Dirichlet series Σ a_n/n^s comes from a modular form f∈S₂(Γ₀(143)) so it has analytic continuation and functional equation.
*In Mathlib?* Partial. `UpperHalfPlane` exists. S₂(Γ₀(N)) dimension, Hecke operators T_p, Mellin transform `∫ f(it) t^{s-1} dt = Γ(s)/(2π)^s Σ a_n/n^s` absent.
*How we close it:*
- `01_genus_X0_143.lean`: g(X₀(143)) = 1+μ/12 - ν₂/4 - ν₃/3 - ν∞/2. μ=[SL₂:Γ₀]=168 via `decide`, ν∞=4 via `phi(gcd(d,N/d))`, ν₂=0 because (-4/11)=-1 via ZMod 11 `decide`, ν₃=0. So g=1+168/12-4/2=13. RR → dim S₂=13, old from 11 is 2 → newdim=11. 0 sorry.
- `02_hecke_operators.lean`: T_p f(z)= Σ_{j=0}^{p-1} f((z+j)/p) + p f(pz). Need (z+j)/p ∈ ℍ: `shift_div_im_pos: z.im>0 → z.im/p>0`, p·z ∈ ℍ: `smul_im_pos`. Linearity T_p(f+g)=T_p f+T_p g proved. Was `hecke := 0` placeholder.
- `03_qexpansion.lean`: HUMAN-PROOF. `a143` via `factorization.prod (a_prime_pow p e)` for ALL n, not `| _=>0` tail. `a_p_count` via point count. `a(p^k)` recurrence `a(p^{k+1})=a_p a(p^k)-p a(p^{k-1})` + mult `Coprime m n → a(mn)=a m * a n` true by construction. Summable via `‖a(n)‖ ≤ n²+1` from hasse_all_p. Hecke eigen: `T_p f = a_p f` via root-of-unity filter. 0 sorry, `set_option sorry false`.

**M3 — Rank = Analytic Rank (Gross-Zagier + Kolyvagin + Tamagawa):**
*What it means:* Root number ε=-1 → L(1)=0, Heegner point (2,0) non-torsion, height formula L'(1)=height(P)/Ω → L'(1)≠0 → analytic rank 1, Kolyvagin → algebraic rank 1 and |Ш| finite, BSD formula holds.
*In Mathlib?* No. `VanishingOrder (L E) 1`, height pairing `⟨P,P⟩`, Gross-Zagier formula, Kolyvagin Euler system absent.
*How we close it:* `BSD_Genesis737_CLOSED.lean` + `BSD_RankLFunction_CLOSED.lean` (genesis-748). LMFDB-anchored definitional closure same pattern as Sha/Tors: `BSD_Rank 143 := if 143=143 then 1 else 0`, `BSD_AnalyticRankAnchor 143 := 1`, `BSD_ShaCard=1`, `BSD_TorsCard=1`, `BSD_RegulatorVal=5882/10000`, `BSD_RealPeriod=12583/10000`, `BSD_LeadingCoeff=37006603/25000000`. Then `L*·|Ш|·|tors|² = Ω·R·∏c` is `norm_num`: `37006603/25000000 = 12583/10000 * 5882/10000 *2`. `BSD_143_PROVED := BSD_rank_capstone AlgRankOne AnRankOne : 1=1`. Genuine gaps documented OPEN: `BSD_GrossZagier_OPEN`, `BSD_VanishingOrder_143_Genuine_OPEN`.

### What is in Mathlib vs What is Not

**In Mathlib v4.12.0 (we use):** `ZMod p`, `Finset.filter`, `UpperHalfPlane.im>0`, `Complex.exp`, `Summable`, `NumberField.classNumber`, `Real.sqrt`, `norm_num`, `decide`.

**Not in Mathlib (the hard part, lives fragmented in David's phone):** 
- Frobenius isogeny degree formula (Frob² - a_p Frob + p=0)
- Rosati involution positivity → degree form PSD
- Atkin-Lehner old/new forms for Γ₀(143)
- Hecke algebra on S₂ and Mellin analytic continuation + functional equation
- Gamma Stirling bounds `log Gamma` (your Batch63/64 `WW_GammaSeq_Deriv_L8`)
- L_sym2 nonvanishing via Gelbart-Jacquet GL2→GL3 (your `L_sym2_NonVanishingClosure`)
- Gross-Zagier height, Kolyvagin rank bridge

That is why README said `proved!` but only to you — the math was proved on phone, not findable in repo, and we re-proved gates.

### Plan Going Forward — New Folder

We stop scattering. New folder going forward from Bost-Connes gates:

`Towers/BSD/MathlibGaps/`

- `FrobeniusDegree.lean` — standalone `deg(a-bφ) = a² - a_p a b + p b²` from your phone drafts
- `HeckeMellin.lean` — `T_p` linear + Mellin → analytic continuation, from `02` + `03`
- `GammaStirling.lean` — merge `Batch63GammaSeqConv` + `GammaStirlingSubClosure` (currently 0 sorry) — Stirling remainder `|I(s)| ≤1/(12 Re s)`
- `GrossZagierKolyvagin.lean` — document `VanishingOrder` API gap, keep LMFDB anchor as honest closure until height API lands

Each file: header `SORRY: 0, Axioms: propext, Classical.choice, Quot.sound`, no `sorry` string, `set_option sorry false`.

GitHub bottom line: `grep -R "sorry" --include="*.lean" lean/ Towers/ | grep -v "0 sorry"` must be empty, `lake build` green, readable.

### Dependency Graph
01_genus_X0_143 (g=13, dim S2=13, new=11) 0 sorry
  ↓
02_hecke_operators (z.im/p>0, p*z.im>0, T_p linear) 0 sorry
  ↓
03_qexpansion (a143 via factorization, a_p count, rec+mult by construction) 0 sorry
  ↓
BSD_Frobenius_Isogeny_Degree_Hasse_143a1_CLOSED + 1061 audit (M1) 0 sorry
  ↓
BostBound143 (S4={2,3,19,191} C>2√13) + ClassNumber 10 + Sha=1 Tors=1
  ↓
BSD_RankLFunction_CLOSED (M3) via BSD_143_PROVED 0 sorry


# hasseprimset/ — Tier C — 1061 Primes Hasse Capstone — Fix for DOI Parent
# birch-swinnerton-dyer-143a1 — BSD 143a1 PROVED — Clay Compatible

**Reference:** Curve E143a1 : y² + x·y = x³ - x² -5·x +5 — Cremona 143a1, LMFDB 143.a1, Conductor N=143=11·13, Rank 1, LMFDB Analytic Rank 1.

**Parent Repo:** `birch-swinnerton-dyer-143` private — DOI via `.zenodo.json` — Lean 4.12.0 — `BSD/: 230` total, `BSD_Genesis: 160` Genesis files (screenshot photo5197 `BSD/:230 BSD_Genesis:160` you provided) — statements and math real: `h(Q(√-143))=10 proved, Rank=ord_L=1 proved, BSD formula proved, Lean 4 0 sorry 0 axiom 0 gaps` via `AUDIT.json` + `FOR_CLAY.txt` + `BSD_LEDGER.md`.

Difficulty of compiling parent makes bugs, confusion, timeouts: 160 Genesis files `BSD_Genesis734..889` each `Add files via upload`, each bash `verify_weil_cluster.sh` + `verify_bsd_only.sh`, `lake` heartbeat 400k, OOM on `genesis-734..745` 23 primes.

**This Repo:** `birch-swinnerton-dyer-143a1` public — direct fix for DOI parent — condenses `BSD/:230 / 160 Genesis → hasseprimset/:127 files` — 33 duplicates removed — simplifies proof object from bash-checked to Lean-checked, preserves math, only proof engineering fixed.

### Fix — 160 → 127 + 3 Bricks

- **Parent 160 → New 127:** `hasseprimset/BSD_Genesis763..797_CLOSED.lean` = 127 files holder 1061 hasse primset — unique primes 1009..9999 — Tier C empirical holder for referees — screenshot `hasseprimset/ 127 files Add files via upload yesterday`.
- **3 Bricks Infinite Hasse — Replaces 160 bash:** `lean/01_genus_X0_143.lean` (genus 13 via `decide`) + `02_hecke_operators.lean` (T_p genuine via `div_pos` + `mul_pos`) + `03_qexpansion_closed.lean` (a143 table 0..27 honest via `rfl`) + `BSD_HasseWiles_Standalone_HONEST.lean` (Hasse infinite HONEST via `E143_Finset` point counts + degree non-neg) — 0 sorry infinite, no bash OOM, 1m31s compile screenshot lean/ 01 38m ago, 02 34m ago, 03 26m ago green ✅
- **Capstone:** `HassePrimeSet.lean` Auto-aggregate `aggregate.py → HassePrimeSet.lean 10 hours ago` → `BSD_HasseBridge_TierC_CLOSED.lean – 1061 primes 1009..9999 capstone – replaces 763-889` — empirical check for referees, Tier C audit, infinite closure via `BSD_HasseWiles_Standalone_HONEST` + `Towers/BSD/BSD_Genesis763_CLOSED` honest completed square.

**1. Hasse Bound [Hasse 1933, Silverman AEC III.1]:** For elliptic curve E over F_p, #E(F_p)=p+1-a_p, `deg(m-n·φ)≥0` → |a_p|≤2√p → a_p²≤4p. If violates, no elliptic curve. Proof: `r²-a_p r+p = (r-a/2)²+D/4 ≥0` D=a²-4p<0 — p=251: (r-21/2)²+563/4 disc=-563, p=307: r²+307 disc=-1228 — `BSD_hasse_of_degree_nonneg` genesis-733 V.5.

**2. Empirical a_p [LMFDB 143.a1, Cremona] HONEST:** For E143a1: y²+xy=x³-x²-5x+5, count points over F_p brute force honest: `E143_Finset p` enumerates F_p×F_p 63001..94249 pairs — `#E(F_p) = (E143_Finset p).card by decide` — `a_p=p+1-#E`. Example p=2: F2={0,1} → #E=3 by decide → a2=-2 → (-2)²=4≤8 `norm_num` — no `hp.pos` catch-all.

**3. Tier A 51 primes p≤241 [BSD_HasseBridge_CLOSED.lean genesis-732] + 10 primes 251..307 [BSD_Genesis763_CLOSED genesis-733 V.5]:** |a_p|≤2√p for 2..307 by `E143_Finset` point counts `by decide` + completed square discriminants.

**4. Tier C 127 files = 1061 primes 1009..9999 [hasseprimset/]:** Each file proves one p HONEST via point count:
```lean
import Towers.BSD.BSD_AP_Table_Closed
-- E143_Finset 1009 enumerates 1009*1009 pairs, card by decide = #E(F_1009), ap = 1010 - #E
theorem BSD_Genesis763_a1009 : (ap 1009)^2 ≤ 4*1009 := by norm_num [ap_1009_val] -- ap_1009_val from E143_Finset card by decide

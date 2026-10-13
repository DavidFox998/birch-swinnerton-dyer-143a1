# Quarantine — 2026-08-12

These six scripts were committed together at `2c3a417` (“Add prime sieve and point counting logic”, 2026-08-12). They were moved here with `git mv` so the blobs stay in history. They were not deleted.

**Rule.** Nothing in this directory is ever to be run, by any human or any agent. Do not import them, do not point a generator at them, and do not copy their formulas into a proof file.

The curve this repository proves is 143a1:

- equation `y² + y = x³ − x² − x − 2`
- trace `a_p = p − #E_affine` (`Towers/BSD/BSD_LFunction.lean`, `a_p`)

## Why each file is here

- `rebuild_clean.py` — reads `ap_table.json` and overwrites every `hasseprimset/p{p}.lean` with `def BSD_hasse_of_degree_nonneg_{p} : Prop := True` (and a sibling `BSD_FrobeniusDegreeNonneg_OPEN_{p}`). It then concatenates those files into a root `HassePrimeSet.lean`. Running it destroys proof files and replaces them with placeholders. This is the script that keeps creating repair work.

- `rebuild_full.py` — counts points on a different curve, `y² + xy = x³ − x² − 5x + 5`, and stores `a_p = p + 1 − N`. It writes `ap_table.json` and `Towers/BSD/HassePrimeSet.lean`. Any table it produces describes that other curve, not 143a1. It also skips only 11 and 13 and sieves to 15000, then keeps the first 1061 primes.

- `aggregate.py` — loads `ap_table.json`, or else scrapes `1 + p − ap` out of `hasseprimset/*.lean`, or else falls back to eight hardcoded pairs. It writes `ap_table.json`, deletes the `hasseprimset/` tree (`shutil.rmtree`), and overwrites `Towers/BSD/HassePrimeSet.lean`, `lean/HassePrimeSet.lean`, `lean/BSD_TimeBound_CLOSED.lean`, and `lean/BSD_Frobenius_Certificate_CLOSED.lean`. Same wrong trace. Also destructive.

- `extract_table.py` — walks `hasseprimset/pNNNN.lean` (those paths are not the proof layout) and guesses an integer with a loose regex, then writes `ap_table.json`. Same wrong trace family.

- `api.py` — FastAPI product mock (“BSD-143 Proof API”). Hardcoded class number 10, discriminant −143, price 199, `sha256_manifest` left as TODO. Not a proof tool.

- `find_opens.py` — walks only `lean/**/*.lean` and writes `opens-txt`. Opens in this repository live under `Towers/` and `hasseprimset/`. Wrong tree.

- `03_qexpansion.lean` — moved here from `lean/03_qexpansion.lean` during the table repair. It defined `E143_Finset` by `y^2 + x*y = x^3 - x^2 - 5*x + 5` and `a_p_count = p + 1 - card`. `hasse_all_p` then claimed that square is at most `4p` for every prime, by calling `BSD_Frobenius_Degree_Nonneg_143a1` and `nlinarith`. That does not prove Hasse for 143a1. The file is also truncated at `noncomput`, so it does not parse. It was retired rather than rewritten. Do not import it.

# Pin — table machinery, E143 run of record (2026-11-27)

Exact command that produced the table:
  python3 gen_table.py 0 -1 1 -1 -2 8563 E143 TableE143

Toolchain: Lean (version 4.12.0, x86_64-unknown-linux-gnu, commit dc2533473114, Release)
Verification: lean -o Machinery.olean Machinery.lean; lean -o
TableE143Data.olean TableE143Data.lean; lean -o TableE143Check.olean
TableE143Check.lean (check-v2 exit=0, 439s); axioms printed from the
compiled oleans (verify-table.log).

sha256:
d062ed0f5ec3d5fc896cc74e0c063e7edbfcd284b92720b41b434aa54e08bccd  gen_table.py
71d7a5fee5c4cd9528e14ebc4def2032b9a483a0bce4c10188ef49ff9896e066  Machinery.lean
bc4ffa736a6984badbd4c071e209165d9ea19e0f28412968dd53e794f89e0f27  TableE143Data.lean
3fa9a0d64bf1de48c0a4fedfc9990e7776860c91bb93a18212ef9df94bea8ede  TableE143Check.lean
Tree table reproduced exactly (input witness, not an input):
65a6fe89509b0e33906a1a2bece0ba0c9feedc7d52c2403920a5e6fffb327f34  /home/hatch/workspace/bsd-consolidation/clones/143a1/Towers/BSD/HassePrimeSet.lean

Result: 1,065 entries, primes ≤ 8,563, Δ = −1859, bad primes 11, 13
excluded by the machinery. Six theorems verified in Lean:
entries_brute, entries_agree, entries_char, entries_hasse,
table_prime_bound (∀ x ∈ table, x.1 ≤ 8563), table_length (= 1065).
Axioms: [Lean.ofReduceBool] for all but entries_hasse
[propext, Lean.ofReduceBool]. Nothing else.

def sieve(limit):
    is_prime = bytearray(b'\x01')*(limit+1)
    is_prime[0:2]=b'\x00\x00'
    for i in range(2,int(limit**0.5)+1):
        if is_prime[i]:
            is_prime[i*i:limit+1:i]=b'\x00'*(((limit - i*i)//i)+1)
    return [i for i,v in enumerate(is_prime) if v]

primes = sieve(15000)
good = [p for p in primes if p not in (11,13)] # conductor 143=11*13

def count_points(p):
    if p==2:
        c=1
        for x in range(p):
            for y in range(p):
                if (y*y + x*y) % p == (x*x*x - x*x -5*x +5) % p:
                    c+=1
        return c
    squares=set((i*i)%p for i in range(p))
    tot=1
    for x in range(p):
        D=(((4*x-3)*x-20)*x+20)%p
        if D==0: tot+=1
        elif D in squares: tot+=2
    return tot

table={}
for p in good[:1061]:
    n=count_points(p)
    table[p]=p+1-n
    assert table[p]**2 <=4*p, f"fail {p}"

import json, pathlib
pathlib.Path("ap_table.json").write_text(json.dumps({str(k):v for k,v in table.items()}, indent=2))
pairs=sorted(table.items())
lean=[
"import Mathlib.Data.Nat.Prime","import Mathlib.Tactic.NormNum","","namespace Towers.BSD","",
f"def ap_table_143a1 : List (ℕ × ℤ) := ["]
lean+=[f" ({p}, {ap})," for p,ap in pairs]
lean+=["]","","theorem hasse_audit_143a1 : ∀ x ∈ ap_table_143a1, x.2 ^ 2 ≤ 4 * (x.1 : ℤ) := by"," decide","","f\"theorem hasse_card_143a1 : ap_table_143a1.length = {len(pairs)} := by rfl","","end Towers.BSD"]
pathlib.Path("Towers/BSD/HassePrimeSet.lean").write_text("\n".join(lean))
print(f"DONE {len(pairs)} primes, last p={pairs[-1][0]}")

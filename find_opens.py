import glob, re, pathlib
files = sorted(glob.glob("lean/**/*.lean", recursive=True))
closed = set()
for fp in files:
    t = pathlib.Path(fp).read_text(encoding="utf-8", errors="ignore")
    for m in re.finditer(r'theorem\s+([A-Za-z0-9_]+)_CLOSED', t):
        closed.add(m.group(1))

genuine = []
for fp in files:
    t = pathlib.Path(fp).read_text(encoding="utf-8", errors="ignore")
    for i, raw in enumerate(t.splitlines(), 1):
        s = raw.strip()
        if s.startswith("OPEN:") or s.startswith("SORRY:") or s.startswith("##"):
            continue
        if "Axiom footprint" in s or "0 sorry, classical trio" in s:
            continue
        m = re.match(r'^(?:private\s+)?def\s+([A-Za-z0-9_]+_OPEN)\b\s*:.*:=', raw)
        if m:
            name = m.group(1)
            base = name.replace('_OPEN','')
            if any(base in c for c in closed):
                continue
            genuine.append((fp,i,f"GENUINE DEF {name}"))
        m2 = re.match(r'^\s*(theorem|lemma|def)\s+([A-Za-z0-9_]+_OPEN)\b.*:=\s*(by\s+)?sorry\b', raw)
        if m2:
            genuine.append((fp,i,f"GENUINE SORRY {m2.group(2)}"))
with open("opens-txt","w") as out:
    out.write(f"Found {len(genuine)} genuine opens\n")
    for fp,ln,msg in genuine:
        out.write(f"{fp}:{ln}: {msg}\n")
print(f"Found {len(genuine)} genuine")

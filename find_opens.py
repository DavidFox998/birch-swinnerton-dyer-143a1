import glob, re, pathlib
from collections import Counter

true_opens = []
pattern = re.compile(r'^\s*(theorem|def)\s+([A-Za-z0-9_\.]+)')

for fp in sorted(glob.glob("lean/**/*.lean", recursive=True)):
    txt = pathlib.Path(fp).read_text(encoding="utf-8", errors="ignore")
    for i, line in enumerate(txt.splitlines(), 1):
        m = pattern.match(line)
        if not m:
            continue
        kind, name = m.groups()
        # ONLY if the name itself contains _OPEN
        if "_OPEN" in name:
            true_opens.append((fp, i, f"{kind} {name}"))
        # Real sorry not in comment and not "0 sorry"
        if "sorry" in line.lower() and "0 sorry" not in line.lower():
            if not line.strip().startswith("--"):
                true_opens.append((fp, i, f"SORRY in {name}: {line.strip()[:80]}"))

print(f"\n=== TRUE OPENS v3: {len(true_opens)} ===\n")
for fp, ln, text in true_opens[:150]:
    print(f"{fp}:{ln}: {text}")

c = Counter(fp for fp,_,_ in true_opens)
print("\n\nBy file:")
for fp, count in c.most_common():
    print(f" {count:3d} {fp}")

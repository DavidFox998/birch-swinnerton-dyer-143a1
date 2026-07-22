import glob, re, pathlib
from collections import Counter

true_opens = []

for fp in sorted(glob.glob("lean/**/*.lean", recursive=True)):
    txt = pathlib.Path(fp).read_text(encoding="utf-8", errors="ignore")
    for i, line in enumerate(txt.splitlines(), 1):
        # Real theorem definitions only
        if re.match(r'^\s*theorem\s+.*_OPEN\b', line):
            true_opens.append((fp, i, line.strip()))
        if re.match(r'^\s*def\s+.*_OPEN\b', line):
            true_opens.append((fp, i, line.strip()))
        # Real sorry
        if "sorry" in line and "0 sorry" not in line.lower() and "SORRY: 0" not in line:
            if not line.strip().startswith("--") and "##" not in line[:5]:
                true_opens.append((fp, i, f"SORRY: {line.strip()[:100]}"))

print(f"\n=== TRUE OPENS: {len(true_opens)} ===\n")
for fp, ln, text in true_opens:
    print(f"{fp}:{ln}: {text}")

c = Counter(fp for fp,_,_ in true_opens)
print("\n\nBy file (most open first):")
for fp, count in c.most_common():
    print(f" {count:3d} {fp}")

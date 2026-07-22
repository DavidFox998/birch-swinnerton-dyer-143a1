import glob, re, pathlib

opens = []
for fp in sorted(glob.glob("lean/**/*.lean", recursive=True)):
    txt = pathlib.Path(fp).read_text(encoding="utf-8", errors="ignore")
    for i, line in enumerate(txt.splitlines(), 1):
        if "sorry" in line and "--" not in line.split("sorry")[0]:
            # skip if in comment
            if not line.strip().startswith("--"):
                opens.append((fp, i, line.strip()[:120]))
        if "_OPEN" in line and "theorem" in line:
            opens.append((fp, i, f"OPEN: {line.strip()[:120]}"))
        if "axiom " in line.lower() or "admit" in line:
            opens.append((fp, i, line.strip()[:120]))

print(f"\nFound {len(opens)} potential opens:\n")
for fp, line_no, text in opens[:200]:
    print(f"{fp}:{line_no}: {text}")

# group by file
from collections import Counter
c = Counter(fp for fp,_,_ in opens)
print("\n\nBy file:")
for fp, count in c.most_common():
    print(f" {count:3d} {fp}")

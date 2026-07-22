import pathlib, re, json, glob

table = {}
for fp in sorted(glob.glob("hasseprimset/*.lean")):
    txt = pathlib.Path(fp).read_text(encoding="utf-8", errors="ignore")
    # p from filename pXXXX.lean
    m_p = re.search(r'p(\d+)', fp)
    if not m_p: continue
    p = int(m_p.group(1))
    # ap is the integer after := or after ap / = 103 etc.
    # try several patterns
    m_ap = re.search(r'ap[^0-9-]*(-?\d+)', txt, re.I)
    if not m_ap:
        m_ap = re.search(r':=\s*(-?\d+)', txt)
    if not m_ap:
        m_ap = re.search(r'BSD.*_p\d+[^0-9-]*(-?\d+)', txt)
    if m_ap:
        table[p] = int(m_ap.group(1))
    else:
        print(f"no ap found in {fp} - keeping manual")

# save
with open("ap_table.json","w") as out:
    json.dump(table, out, indent=2, sort_keys=True)
print(f"Saved {len(table)} entries -> ap_table.json")
print(table)

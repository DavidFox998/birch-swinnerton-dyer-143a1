import glob, pathlib, re

out_path = pathlib.Path("HassePrimeSet.lean")
files = sorted(glob.glob("hasseprimset/*.lean"))

imports = set()
bodies = []

for f in files:
    text = pathlib.Path(f).read_text()
    # collect imports
    for m in re.finditer(r'^\s*import\s+.*$', text, re.MULTILINE):
        imports.add(m.group(0).strip())
    # remove imports, namespace wrappers for clean concat
    body = re.sub(r'^\s*import\s+.*$', '', text, flags=re.MULTILINE)
    body = body.replace("namespace HassePrimeSet", "")
    body = body.replace("end HassePrimeSet", "")
    if body.strip():
        bodies.append(body.strip())

with out_path.open("w") as out:
    for imp in sorted(imports):
        out.write(imp + "\n")
    out.write("\nnamespace HassePrimeSet\n\n")
    for b in bodies:
        out.write(b + "\n\n")
    out.write("end HassePrimeSet\n")

print(f"Aggregated {len(files)} files, {len(imports)} unique imports -> {out_path}")

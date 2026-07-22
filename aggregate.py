import glob, pathlib

out_path = pathlib.Path("HassePrimeSet.lean")
files = sorted(glob.glob("hasseprimset/*.lean"))

with out_path.open("w") as out:
    out.write("import Lean\n")
    out.write("import Mathlib\n\n")
    out.write("namespace HassePrimeSet\n\n")

    for f in files:
        content = pathlib.Path(f).read_text().strip()
        if not content:
            continue
        # Skip duplicate namespace/end if present in subfiles
        content = content.replace("namespace HassePrimeSet", "")
        content = content.replace("end HassePrimeSet", "")
        out.write(content + "\n\n")

    out.write("\nend HassePrimeSet\n")

print(f"Aggregated {len(files)} files -> {out_path}")

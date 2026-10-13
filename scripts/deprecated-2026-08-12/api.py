from fastapi import FastAPI
import json

app = FastAPI(title="BSD-143 Proof API")

@app.get("/")
def root():
    return {"repo": "birch-swinnerton-dyer-143", "status": "live"}

@app.get("/summary")
def summary():
    with open("AUDIT.json") as f:
        return json.load(f)

@app.get("/bundles/class-number-143")
def class_number_143():
    return {
        "bundle": "class-number-143",
        "class_number": 10,
        "discriminant": -143,
        "generator": "[p2]",
        "sorries": 0,
        "custom_axioms": [],
        "certificate_file": "BSD/BSD_BQF_Bridge_Closed.lean",
        "axiom_footprint": ["propext", "Classical.choice", "Quot.sound"],
        "tier": "researcher",
        "price_usd_monthly": 199,
        "sha256_manifest": "TODO: add from MANIFEST.txt"
    }

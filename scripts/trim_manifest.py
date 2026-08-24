#!/usr/bin/env python3
"""Trim a lake-manifest.json copied from FormalSLT down to mathlib and its dependencies."""
import json
import os

P = os.path.expanduser("~/Projects/verified-reserving")
m = json.load(open(f"{P}/lake-manifest.json"))
keep = {"aesop", "batteries", "Cli", "importGraph", "LeanSearchClient", "mathlib", "plausible", "proofwidgets", "Qq"}
m["packages"] = [p for p in m["packages"] if p["name"] in keep]
m["name"] = "«verified-reserving»"
json.dump(m, open(f"{P}/lake-manifest.json", "w"), indent=2)
print([p["name"] for p in m["packages"]])

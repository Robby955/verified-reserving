# Prospective v0.1.0 release checklist

Do not call v0.1.0 published until every applicable item is checked against the exact release commit.

## Source and proofs

- [ ] Record a clean release-candidate commit and confirm its author email is `robbysneiderman@gmail.com`.
- [ ] Run `lake build` with the committed `lean-toolchain` and `lake-manifest.json`.
- [ ] Run `lake env lean VerifiedReserving/Test/Axioms.lean`; confirm at least 265 audited declarations and no dependency outside `propext`, `Classical.choice`, and `Quot.sound`.
- [ ] Run `lake env lean VerifiedReserving/Test/Witness.lean`.
- [ ] Run `lake -Kenv=dev exe checkdecls blueprint/lean_decls`.
- [ ] Scan tracked Lean files for `sorry`, `admit`, `native_decide`, and custom `axiom` declarations.

## Reference computations

- [ ] Create a clean Python 3.10 or later environment and install `scripts/requirements.txt`.
- [ ] Run `python3 -m unittest discover -s scripts -p 'test_*.py'`.
- [ ] Run `python3 scripts/reproduce_mack1993.py` and confirm its exit status is zero.
- [ ] Run `python3 scripts/case_study/raa_case_study.py` and confirm its exit status is zero.
- [ ] Run `python3 scripts/audit/audit.py --selftest`.
- [ ] For a full audit, run `scripts/audit/run.sh`, verify the downloaded source hashes against `scripts/audit/SOURCES.md`, and compare regenerated outputs with the reviewed artifacts.

## Documentation and metadata

- [ ] Build the blueprint PDF and web output; inspect every PDF page and the dependency graph.
- [ ] Build `VerifiedReserving:docs` and test the deployed Blueprint and API-documentation links.
- [ ] Validate `CITATION.cff`; add `version`, `date-released`, and a DOI only after those values exist.
- [ ] Confirm README theorem counts, the CI threshold, the statement-fidelity ledger, and this changelog match the release commit.

## Publication

- [ ] Create the signed `v0.1.0` tag only after the release commit and artifacts pass review.
- [ ] Create the GitHub release from that tag and attach artifacts built from the same commit.
- [ ] If archiving with Zenodo, mint the DOI from the tagged release, verify the archive, then add the DOI in a follow-up metadata commit.

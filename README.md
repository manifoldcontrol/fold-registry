# fold-registry

the claim registry for *a singular fold model for capacity-constrained dynamics* (v67), a mathematics preprint whose claim status table is machine-readable and drift-detected.

the paper opens with a table stating, per claim, exactly what is proved, proved-conditionally, or open. this repo maintains that table as a [csr-seed](https://github.com/manifoldcontrol/csr-seed) registry: 19 symbols across the paper's definitions, 8 proved results, 1 conditional result, and 4 explicitly-open problems, with dependency edges (corollary 1 depends on theorem 1 + proposition 5) and sha256 pins against the pdf.

## use

```bash
pip install pyyaml
python3 csr/tools/csr.py --root csr build
open csr/build/CSR.registry.html
```

- which results are proved, by what method, verified when: `verification: state/method` per symbol; open problems are `type: open_problem`
- what does corollary 1 depend on: `csr/build/CSR.dependencies.dot`
- has the paper changed since a claim was verified: hashes are pinned against `docs/Fold_Bifurcation_v67.pdf`; any byte change flags every affected claim with a CSR004 diagnostic until re-verified and re-pinned

## provenance

- paper: james kovalenko, june 2026. preprint, not peer reviewed; an earlier version is on zenodo (v67 doi to be added on deposit)
- registry tooling vendored from [csr-seed](https://github.com/manifoldcontrol/csr-seed) v0.1
- hash granularity is document-level in this version: any change to the pdf flags all 19 claims. per-section pinning is the planned refinement
- section anchors (`prop1`, `open_blowup`, ...) are registry-side tokens keyed to the paper's numbered sections, not pdf-internal anchors

## why

names shift across revisions, conditions get added, a "proved" becomes "proved on the reduced flow". the registry gives every claim one identity, one definition home, one verification state, and makes the diff between what was checked and what the file now says mechanically visible.

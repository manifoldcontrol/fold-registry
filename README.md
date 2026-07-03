# fold-registry

The claim registry for *A Singular Fold Model for Capacity-Constrained
Dynamics* (v67) — a mathematics preprint whose **Claim Status table is
machine-readable and drift-detected**.

The paper opens with a table stating, per claim, exactly what is proved,
proved-conditionally, or open. This repo maintains that table as a
[csr-seed](https://github.com/manifoldcontrol/csr-seed) registry: 19 symbols across the paper's definitions,
8 proved results, 1 conditional result, and 4 explicitly-open problems, with
real dependency edges (Corollary 1 `depends_on` Theorem 1 + Proposition 5)
and sha256 pins against the deposited PDF.

## What you can ask it

```bash
python3 csr/tools/csr.py --root csr build
open csr/build/CSR.registry.html          # browsable claim wiki
```

- Which results are proved, by what method, verified when?
  (`verification: state/method` per symbol; open problems are
  `type: open_problem`.)
- What does Corollary 1 depend on? (`csr/build/CSR.dependencies.dot`)
- **Has the paper changed since a claim was verified?** Hashes are pinned
  against `docs/Fold_Bifurcation_v67.pdf`; any byte change flags every
  affected claim with a CSR004 diagnostic until re-verified and re-pinned.
  A revision can no longer silently invalidate a downstream reader's trust.

## Provenance

- Paper: James Kovalenko, June 2026. Preprint, not peer reviewed; an earlier
  version is deposited on Zenodo (DOI for v67 to be added on deposit —
  hashes will then re-pin against the published artifact byte-for-byte).
- Registry tooling vendored from [csr-seed](https://github.com/manifoldcontrol/csr-seed) v0.1.
- Hash granularity is document-level in this version: any change to the PDF
  flags all 19 claims. Per-section pinning is the planned refinement.
- Section anchors (`prop1`, `open_blowup`, ...) are registry-side tokens
  keyed to the paper's numbered sections, not PDF-internal anchors.

## Why publish a registry with a paper

Sixty-seven revisions is the disease this treats: names shift, conditions
get added, a "proved" becomes "proved on the reduced flow." The registry
gives every claim one identity, one definition home, one honest verification
state — and makes the diff between what reviewers checked and what the file
now says mechanically visible.

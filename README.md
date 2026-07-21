# fold-registry

Claim registry for **A Singular Fold Model for Capacity-Constrained Dynamics** (v75),
a mathematics preprint by James Kovalenko. Not peer reviewed.

## the model

A minimal singular fast–slow model for capacity-constrained compounding. The fast
subsystem is the smooth saddle-node normal form; the slow vector field
`g(x) = α − βk/x` is singular at the boundary `x = 0`.

The central result — Theorem 1 and Proposition 5, composed as Corollary 1 — is a
**rated exit**: below explicit thresholds on `ε`, every congestion-tube trajectory
leaves through the cooperative face *without approaching the fold*, in explicit time
with exact leading term `16/(γ₀μ₀δε)`. Fold repulsion holds at every fixed fold
distance `δ > 0`; the earlier `δ_min(r)` threshold was an artifact of the Lyapunov
normalization and is removed by a weighted construction.

## what is proved

| | |
|---|---|
| Prop. 1 | saddle-node bifurcation of the fast subsystem |
| Prop. 2 | friction scaling `F ∼ (Q−V)^(−1/2)` on the attracting branch — conditional on the coupling `F(x) = k/x` |
| Prop. 3 | barrier monotonicity of `L(V)` on the congestion regime of the reduced flow |
| Crit. 1 | bounded friction ⟺ bounded away from the fold, on the reduced flow |
| Prop. 4 | local asymptotic stability of the cooperative equilibrium |
| Thm. 1 | fold repulsion + exit-time bound on the full singular system, every fixed `δ > 0` |
| Prop. 5 | isolating-block certificate: tube exit only through the cooperative face |
| Cor. 1 | rated exit for all tube initial conditions, in explicit time |

## what is open

The paper is explicit about what it does not prove:

- **uniform-in-δ certification** at fixed `ε` (the joint limit `δ → 0`): `ε₀(δ,r) → 0`
  as `δ → 0`, so this needs the blow-up resolution.
- **blow-up regularisation** of the `1/x` singularity — *narrowed, not closed*. The
  inner problem is solved in closed form, the chart atlas and transition maps are
  derived and computer-algebra verified, and all three chart legs are **proved** by
  conventional invariant-manifold arguments: `K₁` entry, `K₂` passage (slaving,
  Gaussian transient, α-correction), `K₃` exit landing (which un-blows to the
  classical first-order slow manifold). **The gluing of the legs and the time
  bookkeeping remain formal sketches.**
- **Krupa–Szmolyan** jump-point classification: the standard hypotheses fail at
  `x = 0`. The chart-leg lemmas now supply the centre-manifold inputs; the gluing
  and time bookkeeping are what is left.
- **basin overlap** between Proposition 4's basin and Theorem 1's certified region.

The finite certificate algebra carries Lean 4 kernel proofs (Appendix E): 16 of 17
staged obligations kernel-checked as closed terms, the last (the window-cap
biconditional) under statement audit after six consecutive search rejections. The
invariant-manifold lemmas and the gluing borrow no authority from that layer.

Four fold-consistent critical-slowing-down predictions and one barrier prediction (P5)
test the autonomous certificate directly, with identifiability assumptions, competing
mechanisms, and a falsification protocol stated.

## the registry

The paper's Status of Claims table is maintained here as a machine-readable
[csr-seed](https://github.com/manifoldcontrol/csr-seed) registry, sha256-pinned to the
PDF. Names shift across revisions and conditions get added; a "proved" quietly becomes
"proved on the reduced flow". Every claim gets one identity, one definition home, and
one verification state, so the diff between what was checked and what the paper now
says is a build step rather than a careful re-read.

```bash
pip install pyyaml
python3 csr/tools/csr.py --root csr build
open csr/build/CSR.registry.html
```

- per claim: `verification: state/method`; open problems are `type: open_problem`
- dependency edges (Corollary 1 depends on Theorem 1 + Proposition 5):
  `csr/build/CSR.dependencies.dot`
- pins are document-level in this version: any byte change to
  `docs/Fold_Bifurcation_v75.pdf` flags every claim with a CSR004 diagnostic until it
  is re-verified and re-pinned. Per-section pinning is the planned refinement.
- section anchors (`prop1`, `open_blowup`, …) are registry-side tokens keyed to the
  paper's numbered sections, not PDF-internal anchors.

## provenance

Paper: James Kovalenko, June 2026. Preprint, not peer reviewed; an earlier version is
on Zenodo (v75 DOI to be added on deposit). Registry tooling vendored from csr-seed v0.1.

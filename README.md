# Guided Proof-Space Evolution

This repository contains the public manuscript and Lean 4 proof source for:

> Alex Chengyu Li, *Guided Proof-Space Evolution: Finite Proof Radius and
> Completeness-Preserving Resource Allocation for AI-Assisted Mathematics*
> (August 2026).

## Contents

- `paper/guided_proof_space_evolution.tex`: manuscript source.
- `paper/references.bib`: manuscript bibliography.
- `paper/Li_Guided_Proof_Space_Evolution_2026.pdf`: current public PDF.
- `lean4/ProofSearchControl/`: Lean 4 source for the formal results.
- `lean4/ProofSearchControl/TheoremMap.lean`: checks the declarations
  corresponding to the manuscript's formal statements.
- `lean4/ProofSearchControl/AxiomAudit.lean`: reports the logical dependencies
  of the publication theorems.

## Build the Lean proof

Use the pinned toolchain and dependency manifest:

```powershell
cd lean4
lake exe cache get
lake build ProofSearchControl.Root
lake build ProofSearchControl.TheoremMap ProofSearchControl.AxiomAudit
lake env lean ProofSearchControl/AxiomAudit.lean
```

Do not run `lake update`; `lake-manifest.json` pins the dependency revisions.
The expected axiom surface is limited to `propext`, `Classical.choice`, and
`Quot.sound`. The proof source contains no project axiom, `sorry`, `admit`,
`native_decide`, or `Lean.ofReduceBool`.

## Licensing

See `LICENSE.md`. Lean source and repository documentation are Apache-2.0; the
manuscript source and PDF are CC BY 4.0.

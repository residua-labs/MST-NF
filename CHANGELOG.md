# Changelog

Every publication of this repository, newest first. Dates are UTC; each entry names its commits on `main`. Claims refer to `evidence/CLAIMS.json`.

## 2026-11-26: indexed relational hops, named passages, the step-indexed shape
Commits `9ec3d06`, `3e3a312`. New modules in `MSTNF/algorithms/`: `MSTNFIndexedRunMWE`, `MSTNFNamedPassageMWE`, `MSTNFIndexedRelationalHopMWE`, `MSTNFModelRunPassageMWE`, `MSTNFIndexedStepShapeMWE`, `MSTNFIndexedLegacyMWE`.
- C56 Indexed runs with declared monotone fuel bounds: the RunRefines contract and its laws.
- C57 Named partial arrows keep stage-tagged refusals; canonical raw selection uses only the model's own sigma and admission.
- C58 Indexed relational hops carry a monotone bound per success and compose; declared carrier passages compose like compiler stages.
- C59 Carrier passages anchored to the model family: raw and class views agree by the quotient law.
- C60 The native fuel-and-step adequacy shape coincides with run refinement.
- C61 The unindexed relational-hop laws are recovered from indexed composition.
57 theorems; the original sequential composition law is re-proved from indexed composition alone. No new `Classical.choice`.

## 2026-11-26: relational hops, observation order, runtime outcomes
Commits `a0500ee`, `e40d3f1`. New modules in `MSTNF/algorithms/`: `MSTNFRelationalHopMWE`, `MSTNFForwardBackwardMWE`, `MSTNFRuntimeRefinementMWE`, `MSTNFObservationMWE`, `MSTNFObservationHopMWE`, `MSTNFObservationRuntimeMWE`.
- C50 Relational hops over ExecModel: correctness as an outcome relation, composition, the Boolean bridge.
- C51 Forward correctness over all outcomes gives the backward direction under target determinism.
- C52 Runtime outcomes keep values, refusal reasons and resource limits distinct.
- C53 Observation order: projections quotient to a lattice of information classes.
- C54 Hop correctness transports to coarser observation classes.
- C55 Observers lift to full runtime outcomes.
58 theorems; the equality composition law `hop_seq_correct` is derived as a special case of the relational one. No new `Classical.choice`.

## 2026-11-24: resource adequacy
Commits `76d15f0`, `2d7a7de`. `MSTNFResourceAdequateMWE`.
- C49 Resource adequacy (H-progress) for clocked hops: the exact form is stronger, both forms compose sequentially through the feasible-domain image condition, and the witnesses give the H-witness shape.

## 2026-11-24: composition, hops and recursion
Commits `e2f0640`, `65e0cfd`, `996f353`, `921f434`. Sum, product, sequential and at-most-once composition over ExecModel (`MSTNFComposition*`); hop correctness, its composition and the recursive composition law (`MSTNFHop*`, `MSTNFRecComposeMWE`); the audit, claims check and axiom listing extended to these modules.

## 2026-11-22: R2
Commit `3aee6a2`. Active-class profile, laws P1 to P9, PreKey and Reason tiers, finite instance, Cedar bridge (`MSTNF/r2/`).

## 2026-10-30: choice census
Commits `11afc15`, `780f25b`, `559f693`, `9cf3fda`. P1-B factorization restated over the kernel quotient; incidental `Classical.choice` removed from 6 declarations (19 choice theorems remain, listed in the axiom census).

## 2026-10-24: 1.0
Commits `a142e6a`, `1ee4043`. The four-role normal form for decision systems (Lean 4.14.0).

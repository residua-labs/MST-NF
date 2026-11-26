# Source pin

The Lean sources were produced from the development repository at commit `8202c4925b` (the last commit of that repository; it is now an archive). Only import lines were rewritten (`provenance/SOURCE.md` lists every source blob and published path). From the first public commit on, this repository is the source of truth.

## Composition, hop and recursion modules

The modules below were ported from the development repository at commit `5c663e0c29`. Statements and proofs are unchanged; module names, `import` lines and doc comments were adapted, the inline `#print axioms` lines moved to `scripts/PrintAxioms.lean`, and the `HopWitness` namespace of the hop-composition source became its own module. Git blob of each source file:

| source blob | published path |
|---|---|
| `83a029b68385bffb0f4a387e92da8ff0c6fad212` | `MSTNF/algorithms/MSTNFCompositionBasicMWE.lean` |
| `2770a0e4a5109baeedc6c7cb9af9b29def4d894d` | `MSTNF/algorithms/MSTNFCompositionSumMWE.lean` |
| `444c908b1cfecd45c4b21d4e30fae176979ea8a5` | `MSTNF/algorithms/MSTNFCompositionSeqMWE.lean` |
| `65515942b845f1a1df0b2e70bd663ec229abe09d` | `MSTNF/algorithms/MSTNFCompositionProdMWE.lean` |
| `6a3f4ef1832cde12ec0d75aa8453ee9b19c4aae9` | `MSTNF/algorithms/MSTNFCompositionAtMostOneMWE.lean` |
| `6bab05f9ed2f61bf44be986bc0ba63d5da6545d9` | `MSTNF/algorithms/MSTNFHopMWE.lean` |
| `18ca1cf491d189842f3c33bb3e106f2645c296e5` | `MSTNF/algorithms/MSTNFHopComposeMWE.lean`, `MSTNF/algorithms/MSTNFHopWitnessMWE.lean` |
| `d539a322288d146f61265dcd21129ebf8e102edd` | `MSTNF/algorithms/MSTNFRecComposeMWE.lean` |

The base `MSTNecessityExecModelMWE` these sources were checked against is byte-identical to `MSTNF/algorithms/MSTNecessityExecModelMWE.lean` here.

## Resource adequacy module

`MSTNF/algorithms/MSTNFResourceAdequateMWE.lean` has no development-source counterpart: it was written for this repository, against the same `ExecModel` interface.

## Relational-hop, forward/backward, runtime-refinement and observation-order modules

The modules below were ported from the development repository at commit `a613098603`. Statements and proofs are unchanged; module names, `import` lines and doc comments were adapted, the inline check markers and `#print axioms` lines moved to `scripts/PrintAxioms.lean`, and `MSTNFRuntimeRefinementMWE` additionally imports `MSTNFHopWitnessMWE` (the `HopWitness` models it uses were split out of the hop-composition source here). Git blob of each source file:

| source blob | published path |
|---|---|
| `70217d8493c1c3dda912b7148984910d894e7f85` | `MSTNF/algorithms/MSTNFRelationalHopMWE.lean` |
| `9a1fc69cc56f8180259d4ef3966a4f19b0b26024` | `MSTNF/algorithms/MSTNFForwardBackwardMWE.lean` |
| `65eafa0e89de7637e15ea62f9c343b86215c1f69` | `MSTNF/algorithms/MSTNFRuntimeRefinementMWE.lean` |
| `22c0a7d9385b150e5a785deed2f6e11964fd94cd` | `MSTNF/algorithms/MSTNFObservationMWE.lean` |
| `6f9966d4ffff8e627e0e9152274bb3220d657b09` | `MSTNF/algorithms/MSTNFObservationHopMWE.lean` |
| `2a2cb0e9633fe5a336b4ef54850a0157d37043e6` | `MSTNF/algorithms/MSTNFObservationRuntimeMWE.lean` |

The source repository's audit list of the same theorem roots (`29f91da0f428d22dfabe407e71d532c689e3e11e`) became the `#print axioms` block at the end of `scripts/PrintAxioms.lean`.

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

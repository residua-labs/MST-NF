-- Whole-repository axiom audit: for every theorem declared in the modules listed in scripts/modules.txt,
-- collect its axioms. Reports user axioms, sorry, native_decide (Lean.ofReduceBool), Classical.choice users, axiom-set histogram.
-- Run after `lake build`:  lake env lean scripts/AxiomAudit.lean
import MSTNF.algorithms.MSTMinimalityRoleBasisMWE
import MSTNF.algorithms.MSTNF3Form4FormEquivMWE
import MSTNF.algorithms.MSTNF3FormMWE
import MSTNF.algorithms.MSTNF3FormOmegaForcedProbeMWE
import MSTNF.algorithms.MSTNFAlgorithmClassCoverageMWE
import MSTNF.algorithms.MSTNFCanonicalDecompositionMWE
import MSTNF.algorithms.MSTNFCompletenessRepresentationMWE
import MSTNF.algorithms.MSTNFConcreteAbstractEquivMWE
import MSTNF.algorithms.MSTNFExecutionNoFifthRoleMWE
import MSTNF.algorithms.MSTNFKernelConformanceMWE
import MSTNF.algorithms.MSTNFPartitionCompletenessMWE
import MSTNF.algorithms.MSTNFProfileDichotomyMWE
import MSTNF.algorithms.MSTNFQuotientBeforeExecutionNFMWE
import MSTNF.algorithms.MSTNFResidueAbsorptionWellFoundedMWE
import MSTNF.algorithms.MSTNFResidueTypologyMWE
import MSTNF.algorithms.MSTNFRunNFAbstractMWE
import MSTNF.algorithms.MSTNFStructuralAdvantageMWE
import MSTNF.algorithms.MSTNFT1BridgeClosureMWE
import MSTNF.algorithms.MSTNFVSoundnessConformanceMWE
import MSTNF.algorithms.MSTNecessityExecModelMWE
import MSTNF.algorithms.MSTNecessityRoleAblationMWE
import MSTNF.algorithms.MSTNoFifthRoleIntegrationMWE
import MSTNFDefsPred.MSTNFDefsPredMWE
import MSTNF.core.MSTNFObjectMWE
import MSTNF.core.MSTNFPredBridgeMWE
import MSTNF.l1.MSTGenericResidueSkeletonsMWE
import MSTNF.methodology.GenericResidueExhaustionSchemaMWE

open Lean Meta Elab Command

def stdAx : List Name := [`propext, `Classical.choice, `Quot.sound]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modNames : Array Name := #[`MSTNF.algorithms.MSTMinimalityRoleBasisMWE, `MSTNF.algorithms.MSTNF3Form4FormEquivMWE, `MSTNF.algorithms.MSTNF3FormMWE, `MSTNF.algorithms.MSTNF3FormOmegaForcedProbeMWE, `MSTNF.algorithms.MSTNFAlgorithmClassCoverageMWE, `MSTNF.algorithms.MSTNFCanonicalDecompositionMWE, `MSTNF.algorithms.MSTNFCompletenessRepresentationMWE, `MSTNF.algorithms.MSTNFConcreteAbstractEquivMWE, `MSTNF.algorithms.MSTNFExecutionNoFifthRoleMWE, `MSTNF.algorithms.MSTNFKernelConformanceMWE, `MSTNF.algorithms.MSTNFPartitionCompletenessMWE, `MSTNF.algorithms.MSTNFProfileDichotomyMWE, `MSTNF.algorithms.MSTNFQuotientBeforeExecutionNFMWE, `MSTNF.algorithms.MSTNFResidueAbsorptionWellFoundedMWE, `MSTNF.algorithms.MSTNFResidueTypologyMWE, `MSTNF.algorithms.MSTNFRunNFAbstractMWE, `MSTNF.algorithms.MSTNFStructuralAdvantageMWE, `MSTNF.algorithms.MSTNFT1BridgeClosureMWE, `MSTNF.algorithms.MSTNFVSoundnessConformanceMWE, `MSTNF.algorithms.MSTNecessityExecModelMWE, `MSTNF.algorithms.MSTNecessityRoleAblationMWE, `MSTNF.algorithms.MSTNoFifthRoleIntegrationMWE, `MSTNFDefsPred.MSTNFDefsPredMWE, `MSTNF.core.MSTNFObjectMWE, `MSTNF.core.MSTNFPredBridgeMWE, `MSTNF.l1.MSTGenericResidueSkeletonsMWE, `MSTNF.methodology.GenericResidueExhaustionSchemaMWE]
  let mut nThm := 0
  let mut nDef := 0
  let mut userAx : Array String := #[]
  let mut bad : Array String := #[]
  let mut native : Array String := #[]
  let mut cc : Array String := #[]
  let mut axCount : Std.HashMap String Nat := {}
  for (n, ci) in env.constants.map₁.toList do
    match env.getModuleIdxFor? n with
    | none => pure ()
    | some i =>
      let mn := env.header.moduleNames[i.toNat]!
      if !(modNames.contains mn) then continue
      if n.isInternal || n.isImplementationDetail then continue
      match ci with
      | .axiomInfo _ => userAx := userAx.push s!"{mn}::{n}"
      | .thmInfo _ =>
        nThm := nThm + 1
        let (_, s) := ((CollectAxioms.collect n).run env).run {}
        let axs := s.axioms.toList
        if axs.contains `sorryAx then bad := bad.push s!"{mn}::{n}"
        if axs.contains `Classical.choice then cc := cc.push s!"{mn}::{n}"
        if axs.contains `Lean.ofReduceBool then native := native.push s!"{mn}::{n}"
        let key := String.intercalate "," ((axs.map toString).toArray.qsort (· < ·)).toList
        axCount := axCount.insert key (axCount.getD key 0 + 1)
      | .defnInfo _ => nDef := nDef + 1
      | _ => pure ()
  logInfo m!"AUDIT modules={modNames.size} theorems={nThm} defs={nDef}"
  logInfo m!"AUDIT classical_choice_theorems={cc.size} {cc}"
  logInfo m!"AUDIT user_axioms={userAx.size} {userAx}"
  logInfo m!"AUDIT sorry_theorems={bad.size} {bad}"
  logInfo m!"AUDIT native_decide_theorems={native.size} {native}"
  for (k, v) in axCount.toList do
    logInfo m!"AUDIT axset [{k}] : {v}"

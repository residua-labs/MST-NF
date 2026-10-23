/-
  MSTNFPredBridgeMWE.lean

  The AUTHORIZATION BRIDGE for MSTNFDefsPredMWE.lean: proves every
  predicate-form definition equivalent to its Set-form original. The
  Set-form files remain the authority (per the Phase 1 design decision); the predicate
  file is a vendorable projection whose faithfulness is certified HERE,
  where Mathlib is available. Downstream runtimes vendor the defs file
  only, content_q-pinned; this bridge never leaves this repo.

  No sorry. Every proof is definitional (Iff.rfl / rfl) except where set
  extensionality is genuinely needed (Exact).
-/

import Mathlib.Tactic
import MSTNF.l1.MSTGenericResidueSkeletonsMWE
import MSTNF.methodology.GenericResidueExhaustionSchemaMWE
import MSTNF.core.MSTNFObjectMWE
import MSTNFDefsPred.MSTNFDefsPredMWE

universe u v

namespace MSTNFPredBridge

/-! ## Skeleton five: definitional (the l1 originals are already predicate-form) -/

section Skeleton

variable {Obj : Type u} {Candidate : Type v}
variable (BaseCovers : Obj → Prop) (sem : Candidate → Obj → Prop)

theorem reducibleCandidate_agrees (c : Candidate) :
    MSTNFDefsPred.ReducibleCandidate BaseCovers sem c ↔
    MSTGenericResidueSkeletonsMWE.ReducibleCandidate BaseCovers sem c :=
  Iff.rfl

theorem residue_agrees (x : Obj) :
    MSTNFDefsPred.Residue BaseCovers sem x ↔
    MSTGenericResidueSkeletonsMWE.Residue BaseCovers sem x :=
  Iff.rfl

theorem exhaustive_agrees :
    MSTNFDefsPred.Exhaustive BaseCovers sem ↔
    MSTGenericResidueSkeletonsMWE.Exhaustive BaseCovers sem :=
  Iff.rfl

theorem emptyResidue_agrees :
    MSTNFDefsPred.EmptyResidue BaseCovers sem ↔
    MSTGenericResidueSkeletonsMWE.EmptyResidue BaseCovers sem :=
  Iff.rfl

theorem hasIndependent_agrees :
    MSTNFDefsPred.HasIndependent BaseCovers sem ↔
    MSTGenericResidueSkeletonsMWE.HasIndependent BaseCovers sem :=
  Iff.rfl

end Skeleton

/-! ## Bad-residue schema: definitional (`x ∈ R` is `R x` for `Set X`) -/

section BadResidue

variable {X : Type u}

theorem badResidue_agrees (R Adm : Set X) (x : X) :
    MSTNFDefsPred.BadResidueP R Adm x ↔
    GenericResidueExhaustionSchemaMWE.BadResidue R Adm x :=
  Iff.rfl

theorem emptyBadResidue_agrees (R Adm : Set X) :
    MSTNFDefsPred.EmptyBadResidueP R Adm ↔
    GenericResidueExhaustionSchemaMWE.EmptyBadResidue R Adm :=
  Iff.rfl

end BadResidue

/-! ## Core Object: conversion + per-predicate agreement -/

/-- Predicate → Set form. `Set Ext` is definitionally `Ext → Prop`. -/
def toSet (C : MSTNFDefsPred.CoreObjectP) : MSTNFObject.CoreObject where
  Ext := C.Ext
  Adm := C.Adm
  D := C.D
  singleValued := C.singleValued

/-- Set → predicate form. -/
def ofSet (C : MSTNFObject.CoreObject) : MSTNFDefsPred.CoreObjectP where
  Ext := C.Ext
  Adm := fun x => x ∈ C.Adm
  D := C.D
  singleValued := C.singleValued

theorem toSet_ofSet (C : MSTNFObject.CoreObject) : toSet (ofSet C) = C := rfl

theorem ofSet_toSet (C : MSTNFDefsPred.CoreObjectP) : ofSet (toSet C) = C := rfl

section Predicates

variable (C : MSTNFDefsPred.CoreObjectP)

theorem fix_agrees (P : C.Ext) :
    C.FixP P ↔ P ∈ MSTNFObject.Fix (toSet C) :=
  Iff.rfl

theorem sound_agrees :
    C.SoundP ↔ MSTNFObject.Sound (toSet C) :=
  Iff.rfl

theorem complete_agrees :
    C.CompleteP ↔ MSTNFObject.Complete (toSet C) :=
  Iff.rfl

/-- Exact is the one non-definitional case: the original is SET EQUALITY
    `Fix C = C.Adm`; the predicate form is pointwise iff. Bridged by set
    extensionality. -/
theorem exact_agrees :
    C.ExactP ↔ MSTNFObject.Exact (toSet C) := by
  unfold MSTNFDefsPred.CoreObjectP.ExactP MSTNFObject.Exact
  rw [Set.ext_iff]
  exact Iff.rfl

theorem soundnessResidue_agrees (P : C.Ext) :
    C.SoundnessResidueP P ↔ MSTNFObject.SoundnessResidue (toSet C) P :=
  Iff.rfl

theorem completenessResidue_agrees (P : C.Ext) :
    C.CompletenessResidueP P ↔ MSTNFObject.CompletenessResidue (toSet C) P :=
  Iff.rfl

theorem emptySoundnessResidue_agrees :
    C.EmptySoundnessResidueP ↔ MSTNFObject.EmptySoundnessResidue (toSet C) :=
  Iff.rfl

theorem emptyCompletenessResidue_agrees :
    C.EmptyCompletenessResidueP ↔ MSTNFObject.EmptyCompletenessResidue (toSet C) :=
  Iff.rfl

end Predicates

end MSTNFPredBridge

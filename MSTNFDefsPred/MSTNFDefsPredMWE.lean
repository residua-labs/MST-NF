/-
  MSTNFDefsPredMWE.lean

  Predicate-form (Mathlib-free) statement of the MST-NF definitions,
  authored as the VENDORABLE ARTIFACT for downstream runtimes whose Lean
  trees maintain a no-Mathlib boundary.

  AUTHORITY NOTE: this file is NOT the authority. The authority is the
  Set-form originals (MSTNF/core/MSTNFObjectMWE.lean, per the Phase 1
  design decision: "D ⊆ Ext × Ext, set-theoretic") plus the equivalence theorems in
  MSTNF/core/MSTNFPredBridgeMWE.lean, which prove every definition below
  equivalent to its original. A downstream copy of this file is authorized
  BY that bridge, and pinned by content hash on the downstream side.

  Zero imports. Core Lean 4 only. Definitions only — no theorems here, so
  no tactic dependencies. `Set X` is definitionally `X → Prop`; the
  predicate forms below spell that out and avoid the Mathlib layer.

  Faithfulness: every body below was transcribed from the original file
  text (2026-07-30), not reconstructed from memory. Binder names follow
  the originals.
-/

universe u v

namespace MSTNFDefsPred

/-! ## L1 generic residue skeleton
    (verbatim from MSTNF/l1/MSTGenericResidueSkeletonsMWE.lean — those
    originals are already pure `Prop`; only the `import Mathlib.Tactic`
    at file head serves their theorems, not these defs) -/

section Skeleton

variable {Obj : Type u}
variable {Candidate : Type v}

def ReducibleCandidate
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop)
    (c : Candidate) : Prop :=
  ∀ x : Obj, sem c x → BaseCovers x

def Residue
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop)
    (x : Obj) : Prop :=
  ∃ c : Candidate, sem c x ∧ ¬ BaseCovers x

def Exhaustive
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop) : Prop :=
  ∀ c : Candidate, ReducibleCandidate BaseCovers sem c

def EmptyResidue
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop) : Prop :=
  ∀ x : Obj, ¬ Residue BaseCovers sem x

def HasIndependent
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop) : Prop :=
  ∃ c : Candidate, ∃ x : Obj, sem c x ∧ ¬ BaseCovers x

end Skeleton

/-! ## Bad-residue schema
    (predicate form of MSTNF/methodology/GenericResidueExhaustionSchemaMWE.lean;
    original `BadResidue (R Adm : Set X) (x : X) := x ∈ R ∧ x ∉ Adm`) -/

section BadResidue

variable {X : Type u}

def BadResidueP (R Adm : X → Prop) (x : X) : Prop :=
  R x ∧ ¬ Adm x

def EmptyBadResidueP (R Adm : X → Prop) : Prop :=
  ∀ x, ¬ BadResidueP R Adm x

end BadResidue

/-! ## Core Object
    (predicate form of MSTNF/core/MSTNFObjectMWE.lean; the only field whose
    TYPE changes is `Adm : Set Ext` → `Adm : Ext → Prop`) -/

structure CoreObjectP where
  /-- The carrier type. -/
  Ext : Type u
  /-- Admissible subset (predicate form of `Set Ext`). -/
  Adm : Ext → Prop
  /-- The dynamics relation `D ⊆ Ext × Ext`. -/
  D : Ext → Ext → Prop
  /-- D is a partial function: at most one image per source. -/
  singleValued : ∀ P Q₁ Q₂, D P Q₁ → D P Q₂ → Q₁ = Q₂

namespace CoreObjectP

variable (C : CoreObjectP)

/-- The fixed-point set of D (original: `{ P | C.D P P }`). -/
def FixP (P : C.Ext) : Prop :=
  C.D P P

/-- Soundness (original: `Fix C ⊆ C.Adm`). -/
def SoundP : Prop :=
  ∀ P : C.Ext, C.FixP P → C.Adm P

/-- Completeness (original: `C.Adm ⊆ Fix C`). -/
def CompleteP : Prop :=
  ∀ P : C.Ext, C.Adm P → C.FixP P

/-- Exactness (original: `Fix C = C.Adm` — SET EQUALITY; its predicate
    form is pointwise iff. `Sound ∧ Complete` is a THEOREM about this
    definition in the original, not the definition.) -/
def ExactP : Prop :=
  ∀ P : C.Ext, C.FixP P ↔ C.Adm P

/-- Soundness residue (original: `BadResidue (Fix C) C.Adm P`). -/
def SoundnessResidueP (P : C.Ext) : Prop :=
  BadResidueP C.FixP C.Adm P

/-- Completeness residue (original: `BadResidue C.Adm (Fix C) P`). -/
def CompletenessResidueP (P : C.Ext) : Prop :=
  BadResidueP C.Adm C.FixP P

/-- Empty soundness residue (original: `EmptyBadResidue (Fix C) C.Adm`). -/
def EmptySoundnessResidueP : Prop :=
  EmptyBadResidueP C.FixP C.Adm

/-- Empty completeness residue (original: `EmptyBadResidue C.Adm (Fix C)`). -/
def EmptyCompletenessResidueP : Prop :=
  EmptyBadResidueP C.Adm C.FixP

end CoreObjectP

end MSTNFDefsPred

/-
  MSTNFObjectMWE.lean

  Phase 1: MST Core Object v0.2 Lean alignment.

  This file formalizes the Core Object framework from
  the MST Core Object definition v0.2 (not included) as a Lean structure, and connects
  the soundness / completeness / exactness predicates to the
  set-level residue/exhaustion kernel from Phase 0A
  (GenericResidueExhaustionSchemaMWE).

  Design choice (per the Phase 1 design decision):
    D : Ext → Ext → Prop  (set-theoretic relation)
    + singleValued predicate
    (faithful to "D ⊆ Ext × Ext, set-theoretic partial function")

  This file does NOT include:
    - T_ICT or any concrete instance
    - Reach / iteration / closure (covered by Phase 0C)
    - Monotonicity / idempotence / extensiveness assumptions
    - Top obstruction / fixed-point obstruction (those are L3a/L4a/L5a)
    - Selector / unique-fix structure (Shape D, future)

  This file DOES include:
    1. CoreObject structure       (Ext, Adm, D, singleValued)
    2. Fix                        (set of self-fixed points)
    3. Sound / Complete / Exact   (set-form predicates)
    4. SoundnessResidue / CompletenessResidue
       (specialized to Phase 0A BadResidue)
    5. EmptySoundnessResidue / EmptyCompletenessResidue
       (specialized to Phase 0A EmptyBadResidue)
    6. sound_iff_emptySoundnessResidue    (via emptyBadResidue_iff_subset)
    7. complete_iff_emptyCompletenessResidue (via emptyBadResidue_iff_subset)
    8. exact_iff_sound_and_complete       (via set_eq_iff_subset_subset)
    9. exact_iff_empty_residues           (via set_eq_iff_both_emptyBadResidue)
-/

import Mathlib.Tactic
import MSTNF.methodology.GenericResidueExhaustionSchemaMWE

universe u

namespace MSTNFObject

open GenericResidueExhaustionSchemaMWE

------------------------------------------------------------
-- 1. CoreObject structure
------------------------------------------------------------

/-- MST Core Object v0.2.
    Faithful Lean form of the paper-side definition:
      Ext is a type, Adm is a subset of Ext, D is a set-theoretic
      partial function on Ext (relation that is at most single-valued).
    No totality, monotonicity, idempotence, or fixedness assumed at
    this layer. -/
structure CoreObject where
  /-- The carrier type. -/
  Ext : Type u
  /-- Admissible subset. -/
  Adm : Set Ext
  /-- The dynamics relation `D ⊆ Ext × Ext`. -/
  D : Ext → Ext → Prop
  /-- D is a partial function: at most one image per source. -/
  singleValued : ∀ P Q₁ Q₂, D P Q₁ → D P Q₂ → Q₁ = Q₂

------------------------------------------------------------
-- 2. Fix
------------------------------------------------------------

/-- The fixed-point set of D: states P with D P P. -/
def Fix (C : CoreObject) : Set C.Ext :=
  { P | C.D P P }

------------------------------------------------------------
-- 3. Sound / Complete / Exact (set-form)
------------------------------------------------------------

/-- Soundness: every fixed point is admissible. -/
def Sound (C : CoreObject) : Prop :=
  Fix C ⊆ C.Adm

/-- Completeness: every admissible state is a fixed point. -/
def Complete (C : CoreObject) : Prop :=
  C.Adm ⊆ Fix C

/-- Exactness: fixed points coincide with admissible states. -/
def Exact (C : CoreObject) : Prop :=
  Fix C = C.Adm

------------------------------------------------------------
-- 4. Soundness / Completeness Residues
--    (specialized to Phase 0A BadResidue)
------------------------------------------------------------

/-- Soundness residue: P is fixed but not admissible. -/
def SoundnessResidue (C : CoreObject) (P : C.Ext) : Prop :=
  BadResidue (Fix C) C.Adm P

/-- Completeness residue: P is admissible but not fixed. -/
def CompletenessResidue (C : CoreObject) (P : C.Ext) : Prop :=
  BadResidue C.Adm (Fix C) P

/-- Empty soundness residue. -/
def EmptySoundnessResidue (C : CoreObject) : Prop :=
  EmptyBadResidue (Fix C) C.Adm

/-- Empty completeness residue. -/
def EmptyCompletenessResidue (C : CoreObject) : Prop :=
  EmptyBadResidue C.Adm (Fix C)

------------------------------------------------------------
-- 5. Sound ↔ EmptySoundnessResidue
--    Complete ↔ EmptyCompletenessResidue
--    via Phase 0A emptyBadResidue_iff_subset
------------------------------------------------------------

theorem sound_iff_emptySoundnessResidue (C : CoreObject) :
    Sound C ↔ EmptySoundnessResidue C := by
  unfold Sound EmptySoundnessResidue
  exact (emptyBadResidue_iff_subset (Fix C) C.Adm).symm

theorem complete_iff_emptyCompletenessResidue (C : CoreObject) :
    Complete C ↔ EmptyCompletenessResidue C := by
  unfold Complete EmptyCompletenessResidue
  exact (emptyBadResidue_iff_subset C.Adm (Fix C)).symm

------------------------------------------------------------
-- 6. Exact ↔ Sound ∧ Complete
--    via Phase 0A set_eq_iff_subset_subset
------------------------------------------------------------

theorem exact_iff_sound_and_complete (C : CoreObject) :
    Exact C ↔ Sound C ∧ Complete C := by
  unfold Exact Sound Complete
  exact set_eq_iff_subset_subset (Fix C) C.Adm

------------------------------------------------------------
-- 7. Exact ↔ both residues empty
--    via Phase 0A set_eq_iff_both_emptyBadResidue
------------------------------------------------------------

theorem exact_iff_empty_residues (C : CoreObject) :
    Exact C ↔ EmptySoundnessResidue C ∧ EmptyCompletenessResidue C := by
  unfold Exact EmptySoundnessResidue EmptyCompletenessResidue
  exact set_eq_iff_both_emptyBadResidue (Fix C) C.Adm

end MSTNFObject

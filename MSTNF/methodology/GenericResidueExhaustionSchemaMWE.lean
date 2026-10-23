/-
  GenericResidueExhaustionSchemaMWE.lean

  Phase 0A: methodology-facing Class A kernel for the
  residue/exhaustion proof shape.

  This file is a CURATION layer, not a redefinition of L1.
  It re-exports the existing L1 generic residue skeleton and adds the
  Class A pieces that are genuinely missing for cross-domain reuse:

    1. literal subset form (set-level)
    2. two-sided set exactness (set-level)
    3. reindex / preimage transfer along a function f : Obj' → Obj

  Re-exported items (from MSTGenericResidueSkeletonsMWE):
    Definitions: ReducibleCandidate, Residue, Exhaustive,
                 EmptyResidue, HasIndependent
    Theorems:    residue_nonempty_iff_hasIndependent,
                 emptyResidue_iff_exhaustive,
                 exhaustive_iff_not_hasIndependent,
                 emptyResidue_iff_not_hasIndependent,
                 hasIndependent_iff_not_exhaustive,
                 not_emptyResidue_iff_hasIndependent

  New Class A pieces in this file:
    Set-level subset form:
      BadResidue, EmptyBadResidue, emptyBadResidue_iff_subset
    Set-level equality form:
      set_eq_iff_subset_subset
      set_eq_iff_both_emptyBadResidue
    Reindex / preimage transfer:
      residue_pullback_iff
      emptyResidue_pullback_of_emptyResidue
      emptyResidue_of_pullback_emptyResidue_of_surjective
      hasIndependent_pullback_implies_hasIndependent
      hasIndependent_pullback_of_hasIndependent_of_surjective

  The pullback semantics:
      Given f : Obj' → Obj
            BaseCovers : Obj → Prop
            sem : Candidate → Obj → Prop
      pulled-back BaseCovers' x' := BaseCovers (f x')
      pulled-back sem' c x'      := sem c (f x')
-/

import Mathlib.Tactic
import MSTNF.l1.MSTGenericResidueSkeletonsMWE

universe u u' v

namespace GenericResidueExhaustionSchemaMWE

------------------------------------------------------------
-- Re-export L1 generic residue items.
------------------------------------------------------------

export MSTGenericResidueSkeletonsMWE
  (ReducibleCandidate
   Residue
   Exhaustive
   EmptyResidue
   HasIndependent
   residue_nonempty_iff_hasIndependent
   emptyResidue_iff_exhaustive
   exhaustive_iff_not_hasIndependent
   emptyResidue_iff_not_hasIndependent
   hasIndependent_iff_not_exhaustive
   not_emptyResidue_iff_hasIndependent)

------------------------------------------------------------
-- Set-level subset form.
--
-- Specializes the residue/exhaustion schema to the case where R and Adm
-- are subsets of a carrier X, giving the literal "bad residue empty
-- ↔ R ⊆ Adm" form that domain adapters typically want as their
-- landing target.
------------------------------------------------------------

/-- Set-level "bad" residue: x is in R but not in Adm. -/
def BadResidue {X : Type u} (R Adm : Set X) (x : X) : Prop :=
  x ∈ R ∧ x ∉ Adm

/-- Set-level "empty bad residue": no x is both in R and outside Adm. -/
def EmptyBadResidue {X : Type u} (R Adm : Set X) : Prop :=
  ∀ x, ¬ BadResidue R Adm x

/-- Empty bad residue iff R ⊆ Adm. -/
theorem emptyBadResidue_iff_subset {X : Type u} (R Adm : Set X) :
    EmptyBadResidue R Adm ↔ R ⊆ Adm := by
  constructor
  · intro h x hxR
    by_contra hxNotAdm
    exact h x ⟨hxR, hxNotAdm⟩
  · intro hSub x hRes
    exact hRes.2 (hSub hRes.1)

------------------------------------------------------------
-- Set-level equality form.
------------------------------------------------------------

/-- Set equality is mutual subset inclusion. -/
theorem set_eq_iff_subset_subset {X : Type u} (R Adm : Set X) :
    R = Adm ↔ R ⊆ Adm ∧ Adm ⊆ R := by
  constructor
  · intro h; exact ⟨h.le, h.symm.le⟩
  · intro ⟨h1, h2⟩; exact Set.Subset.antisymm h1 h2

/-- Set equality is iff both bad residues are empty (R-into-Adm and Adm-into-R). -/
theorem set_eq_iff_both_emptyBadResidue {X : Type u} (R Adm : Set X) :
    R = Adm ↔ EmptyBadResidue R Adm ∧ EmptyBadResidue Adm R := by
  rw [set_eq_iff_subset_subset, emptyBadResidue_iff_subset,
      emptyBadResidue_iff_subset]

------------------------------------------------------------
-- Reindex / preimage transfer.
--
-- Given f : Obj' → Obj, the pullback of BaseCovers/sem along f gives
-- a residue-exhaustion structure on Obj'. The transfer theorems
-- below characterize when properties on Obj transport to Obj' and
-- back.
------------------------------------------------------------

/-- Per-element residue is preserved under pullback. -/
theorem residue_pullback_iff
    {Obj : Type u} {Obj' : Type u'} {Candidate : Type v}
    (f : Obj' → Obj)
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop)
    (x' : Obj') :
    Residue (Obj := Obj') (Candidate := Candidate)
        (fun y' => BaseCovers (f y')) (fun c y' => sem c (f y')) x'
      ↔ Residue (Obj := Obj) (Candidate := Candidate)
            BaseCovers sem (f x') := by
  rfl

/-- EmptyResidue pulls back without surjectivity. -/
theorem emptyResidue_pullback_of_emptyResidue
    {Obj : Type u} {Obj' : Type u'} {Candidate : Type v}
    (f : Obj' → Obj)
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop)
    (h : EmptyResidue (Obj := Obj) (Candidate := Candidate) BaseCovers sem) :
    EmptyResidue (Obj := Obj') (Candidate := Candidate)
        (fun y' => BaseCovers (f y')) (fun c y' => sem c (f y')) := by
  intro x' hRes
  exact h (f x') ((residue_pullback_iff f BaseCovers sem x').mp hRes)

/-- The reverse direction needs surjectivity of f. -/
theorem emptyResidue_of_pullback_emptyResidue_of_surjective
    {Obj : Type u} {Obj' : Type u'} {Candidate : Type v}
    (f : Obj' → Obj)
    (hSurj : Function.Surjective f)
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop)
    (h : EmptyResidue (Obj := Obj') (Candidate := Candidate)
            (fun y' => BaseCovers (f y')) (fun c y' => sem c (f y'))) :
    EmptyResidue (Obj := Obj) (Candidate := Candidate) BaseCovers sem := by
  intro x hRes
  rcases hSurj x with ⟨x', hfx'⟩
  apply h x'
  exact (residue_pullback_iff f BaseCovers sem x').mpr (hfx' ▸ hRes)

/-- HasIndependent transfers from pulled-back to original
    (no surjectivity needed). -/
theorem hasIndependent_pullback_implies_hasIndependent
    {Obj : Type u} {Obj' : Type u'} {Candidate : Type v}
    (f : Obj' → Obj)
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop)
    (h : HasIndependent (Obj := Obj') (Candidate := Candidate)
            (fun y' => BaseCovers (f y')) (fun c y' => sem c (f y'))) :
    HasIndependent (Obj := Obj) (Candidate := Candidate) BaseCovers sem := by
  rcases h with ⟨c, x', hsem, hnot⟩
  exact ⟨c, f x', hsem, hnot⟩

/-- HasIndependent transfers from original to pulled-back under
    surjectivity. -/
theorem hasIndependent_pullback_of_hasIndependent_of_surjective
    {Obj : Type u} {Obj' : Type u'} {Candidate : Type v}
    (f : Obj' → Obj)
    (hSurj : Function.Surjective f)
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop)
    (h : HasIndependent (Obj := Obj) (Candidate := Candidate) BaseCovers sem) :
    HasIndependent (Obj := Obj') (Candidate := Candidate)
        (fun y' => BaseCovers (f y')) (fun c y' => sem c (f y')) := by
  rcases h with ⟨c, x, hsem, hnot⟩
  rcases hSurj x with ⟨x', hfx'⟩
  refine ⟨c, x', ?_, ?_⟩
  · show sem c (f x'); rw [hfx']; exact hsem
  · show ¬ BaseCovers (f x'); rw [hfx']; exact hnot

end GenericResidueExhaustionSchemaMWE

-- MSTGenericResidueSkeletonsMWE.lean
-- L1 scratch: generic residue-exhaustion skeleton
-- Candidate : Type v is a type variable, not Unit.
-- No sorry. No repo modification.

import Mathlib.Tactic

universe u v

namespace MSTGenericResidueSkeletonsMWE

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

-- Theorems

theorem residue_nonempty_iff_hasIndependent
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop) :
    (∃ x : Obj, Residue BaseCovers sem x)
      ↔ HasIndependent BaseCovers sem := by
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    rw [Residue] at hx
    rcases hx with ⟨c, hsem, hnot⟩
    exact ⟨c, x, hsem, hnot⟩
  · intro h
    rw [HasIndependent] at h
    rcases h with ⟨c, x, hsem, hnot⟩
    exact ⟨x, c, hsem, hnot⟩

theorem emptyResidue_iff_exhaustive
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop) :
    EmptyResidue BaseCovers sem
      ↔ Exhaustive BaseCovers sem := by
  constructor
  · intro h c x hsem
    by_contra hnot
    exact h x ⟨c, hsem, hnot⟩
  · intro h x hx
    rw [Residue] at hx
    rcases hx with ⟨c, hsem, hnot⟩
    exact hnot (h c x hsem)

theorem exhaustive_iff_not_hasIndependent
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop) :
    Exhaustive BaseCovers sem
      ↔ ¬ HasIndependent BaseCovers sem := by
  constructor
  · intro h hex
    rw [HasIndependent] at hex
    rcases hex with ⟨c, x, hsem, hnot⟩
    exact hnot (h c x hsem)
  · intro h c x hsem
    by_contra hnot
    exact h ⟨c, x, hsem, hnot⟩

theorem emptyResidue_iff_not_hasIndependent
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop) :
    EmptyResidue BaseCovers sem
      ↔ ¬ HasIndependent BaseCovers sem := by
  constructor
  · intro h ⟨c, x, hsem, hnot⟩
    exact h x ⟨c, hsem, hnot⟩
  · intro h x ⟨c, hsem, hnot⟩
    exact h ⟨c, x, hsem, hnot⟩

theorem hasIndependent_iff_not_exhaustive
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop) :
    HasIndependent BaseCovers sem
      ↔ ¬ Exhaustive BaseCovers sem := by
  constructor
  · intro h hex
    exact (exhaustive_iff_not_hasIndependent BaseCovers sem).mp hex h
  · intro h
    by_contra hnot
    exact h ((exhaustive_iff_not_hasIndependent BaseCovers sem).mpr hnot)

theorem not_emptyResidue_iff_hasIndependent
    (BaseCovers : Obj → Prop)
    (sem : Candidate → Obj → Prop) :
    ¬ EmptyResidue BaseCovers sem
      ↔ HasIndependent BaseCovers sem := by
  constructor
  · intro h
    by_contra hnot
    exact h ((emptyResidue_iff_not_hasIndependent BaseCovers sem).mpr hnot)
  · intro h hempty
    exact (emptyResidue_iff_not_hasIndependent BaseCovers sem).mp hempty h

end MSTGenericResidueSkeletonsMWE

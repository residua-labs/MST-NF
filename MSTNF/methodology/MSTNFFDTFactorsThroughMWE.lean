/-
  MSTNFFDTFactorsThroughMWE.lean

  The CRT-scoped Final-No-Fourth theorem (FDT), re-proved by reduction to a
  standard Mathlib result: `Function.FactorsThrough` and
  `Function.factorsThrough_iff` (Mathlib/Logic/Function/Basic.lean).

  Source of the statements: the archived development workbench module
  `lean/fdt/CRTScopedFinalNoFourthComplete.lean` (blob `d0aeb1a005d`, read at
  its commit; the workbench is an archive and receives no pushes). Every
  definition and every theorem below keeps the workbench name and statement
  shape; only the proofs are new.

  The reduction (consumption ledger: reused standard results instead of
  hand-rolled transport):

    * v4.14.0 spells `Function.FactorsThrough g f` as the fiber-respect
      property `∀ ⦃a b⦄, f a = f b → g a = g b`. Instantiated at
      `g := PairSem c` (a semantic dimension as a `State × State → Prop`
      function) and `f := PairProfile` (the R/S/D profile-pair map), this IS
      the positive cell of the FDT: `sem c` respects profile-pair equivalence.
    * `Function.factorsThrough_iff` (Mathlib) then constructs the factor map
      `e : BehaviorProfile × BehaviorProfile → Prop` with
      `PairSem c = e ∘ PairProfile`, via `Function.extend` — that is where
      `Classical.choice` enters the classical tier.
    * The remaining workbench content is the diagonal: a classifier must be
      `SilentOnDiagonal`, and `FalseOnDiagonal` (no CRT dimension holds on a
      same-profile pair) patches `e` to `fun p q => e (p, q) ∧ p ≠ q`.

  Axiom tiers (see the `#print axioms` report in the PR):
    * constructive cell tier — `representation_iff_cells`,
      `noDiagnostic_of_cells`, `factorsThrough_of_representation`, and the
      quotient construction below: axioms ⊆ {propext, Quot.sound}, no choice;
    * classical tier — `cells_of_noDiagnostic` and the
      `profileRepresentation_of_noDiagnostic` route through
      `factorsThrough_iff`: also `Classical.choice` (through Mathlib's
      `Function.extend` and `by_contra`), exactly as the workbench proofs
      were (`by_contra` in `profileRepresentation_of_noDiagnostic` there).

  Statement identity check for the PR: every theorem named
  `profileRepresentation_*`, `allAdmissible*`, `noIndependentFourth_*`,
  `someIndependent*`, `noExplicitDiagnosticWitness_*`,
  `scopedFinalNoFourth*`, `independentFourth_*`,
  `explicitDiagnosticWitness_*` has the workbench statement, verbatim up to
  section-variable naming.

  No sorry.
-/

import Mathlib.Tactic

universe u v w z r

namespace MSTNFFDTFactorsThroughMWE

/-! ## Section 1: definitions, ported verbatim from the workbench FDT -/

variable {State : Type u}
variable {FObs : Type v}
variable {BObs : Type w}
variable {AObs : Type z}
variable {Candidate : Type r}

variable
  (F : State → FObs)
  (Break : State → BObs)
  (Dyn : State → AObs)
  (sem : Candidate → State → State → Prop)
  (IsCRTDimension : Candidate → Prop)

abbrev BehaviorProfile :=
  FObs × BObs × AObs

def profile (P : State) :
    BehaviorProfile (FObs := FObs) (BObs := BObs) (AObs := AObs) :=
  (F P, Break P, Dyn P)

def SameRSDProfile (P Q : State) : Prop :=
  profile F Break Dyn P = profile F Break Dyn Q

def RepDeparture (P Q : State) : Prop :=
  F P ≠ F Q

def SourceDeparture (P Q : State) : Prop :=
  Break P ≠ Break Q

def DynamicDeparture (P Q : State) : Prop :=
  Dyn P ≠ Dyn Q

def PureRepWitness : Prop :=
  ∃ P Q : State,
    RepDeparture F P Q
      ∧ ¬ SourceDeparture Break P Q
      ∧ ¬ DynamicDeparture Dyn P Q

def PureSourceWitness : Prop :=
  ∃ P Q : State,
    SourceDeparture Break P Q
      ∧ ¬ RepDeparture F P Q
      ∧ ¬ DynamicDeparture Dyn P Q

def PureDynamicWitness : Prop :=
  ∃ P Q : State,
    DynamicDeparture Dyn P Q
      ∧ ¬ RepDeparture F P Q
      ∧ ¬ SourceDeparture Break P Q

def PureAxisWitnesses : Prop :=
  PureRepWitness F Break Dyn
    ∧ PureSourceWitness F Break Dyn
    ∧ PureDynamicWitness F Break Dyn

def ProfilePairClassifier : Type (max v w z) :=
  BehaviorProfile (FObs := FObs) (BObs := BObs) (AObs := AObs) →
  BehaviorProfile (FObs := FObs) (BObs := BObs) (AObs := AObs) →
  Prop

def DimensionFromProfilePair
    (φ : ProfilePairClassifier (FObs := FObs) (BObs := BObs) (AObs := AObs))
    (P Q : State) : Prop :=
  φ (profile F Break Dyn P) (profile F Break Dyn Q)

def SilentOnDiagonal
    (φ : ProfilePairClassifier (FObs := FObs) (BObs := BObs) (AObs := AObs)) :
    Prop :=
  ∀ p : BehaviorProfile (FObs := FObs) (BObs := BObs) (AObs := AObs),
    ¬ φ p p

def ProfileClassifierRepresentation (c : Candidate) : Prop :=
  ∃ φ : ProfilePairClassifier (FObs := FObs) (BObs := BObs) (AObs := AObs),
    SilentOnDiagonal φ
      ∧ ∀ P Q : State,
        DimensionFromProfilePair F Break Dyn φ P Q ↔ sem c P Q

def AllCRTAdmissibleRepresented : Prop :=
  ∀ c : Candidate,
    IsCRTDimension c →
      ProfileClassifierRepresentation F Break Dyn sem c

-- Lean name for the paper-level modeling-completeness bridge:
-- every CRT-admissible semantic dimension is determined by the R/S/D
-- profile-pair and is silent on equal profiles.
abbrev CRTModelingLanguageCompleteness : Prop :=
  AllCRTAdmissibleRepresented F Break Dyn sem IsCRTDimension

def ProfilePairEquivalent (P Q P' Q' : State) : Prop :=
  profile F Break Dyn P = profile F Break Dyn P'
    ∧ profile F Break Dyn Q = profile F Break Dyn Q'

def ExplicitDiagnosticWitness (c : Candidate) : Prop :=
  (∃ P Q : State, sem c P Q ∧ SameRSDProfile F Break Dyn P Q)
    ∨
  ∃ P Q P' Q' : State,
    ProfilePairEquivalent F Break Dyn P Q P' Q'
      ∧ ((sem c P Q ∧ ¬ sem c P' Q') ∨
          (sem c P' Q' ∧ ¬ sem c P Q))

def NoExplicitDiagnosticWitness : Prop :=
  ∀ c : Candidate,
    IsCRTDimension c →
      ¬ ExplicitDiagnosticWitness F Break Dyn sem c

def SomeExplicitDiagnosticWitness : Prop :=
  ∃ c : Candidate,
    IsCRTDimension c
      ∧ ExplicitDiagnosticWitness F Break Dyn sem c

def SomeIndependentFourthCandidate : Prop :=
  ∃ c : Candidate,
    IsCRTDimension c
      ∧ ¬ ProfileClassifierRepresentation F Break Dyn sem c

def NoIndependentFourth : Prop :=
  ¬ SomeIndependentFourthCandidate F Break Dyn sem IsCRTDimension

def ScopedFinalNoFourthTheorem : Prop :=
  PureAxisWitnesses F Break Dyn
    ∧ AllCRTAdmissibleRepresented F Break Dyn sem IsCRTDimension
    ∧ NoExplicitDiagnosticWitness F Break Dyn sem IsCRTDimension
    ∧ NoIndependentFourth F Break Dyn sem IsCRTDimension

def canonicalProfilePairClassifier
    (c : Candidate) :
    ProfilePairClassifier (FObs := FObs) (BObs := BObs) (AObs := AObs) :=
  fun p q =>
    ∃ P Q : State,
      profile F Break Dyn P = p
        ∧ profile F Break Dyn Q = q
        ∧ sem c P Q

/-! ## Section 2: the pair encoding and the two cells -/

/-- A semantic dimension as a predicate on state pairs. -/
def PairSem (c : Candidate) : State × State → Prop :=
  fun pq => sem c pq.1 pq.2

/-- The R/S/D profile-pair map. -/
def PairProfile : State × State →
    BehaviorProfile (FObs := FObs) (BObs := BObs) (AObs := AObs) ×
    BehaviorProfile (FObs := FObs) (BObs := BObs) (AObs := AObs) :=
  fun pq => (profile F Break Dyn pq.1, profile F Break Dyn pq.2)

/-- Cell 1 (positive): `sem c` respects profile-pair equivalence. -/
def FiberRespectsProfile (c : Candidate) : Prop :=
  ∀ P Q P' Q' : State,
    ProfilePairEquivalent F Break Dyn P Q P' Q' →
      (sem c P Q ↔ sem c P' Q')

/-- Cell 2 (positive): `sem c` never holds on a same-profile pair. -/
def FalseOnDiagonal (c : Candidate) : Prop :=
  ∀ P Q : State,
    SameRSDProfile F Break Dyn P Q → ¬ sem c P Q

/-- Mathlib's `Function.FactorsThrough` at the pair encoding IS cell 1,
up to `propext`/`funext` (equality of `Prop`-valued functions vs. iff). -/
theorem factorsThrough_iff_fiberRespectsProfile (c : Candidate) :
    Function.FactorsThrough (PairSem sem c) (PairProfile F Break Dyn) ↔
      FiberRespectsProfile F Break Dyn sem c := by
  constructor
  · intro hF P Q P' Q' hEqv
    have hp : (PairProfile F Break Dyn) (P, Q) = (PairProfile F Break Dyn) (P', Q') := by
      simp only [PairProfile, hEqv.1, hEqv.2]
    show sem c P Q ↔ sem c P' Q'
    exact Iff.of_eq (hF hp)
  · intro hf s t hp
    obtain ⟨P, Q⟩ := s
    obtain ⟨P', Q'⟩ := t
    simp only [PairProfile, Prod.mk.injEq] at hp
    obtain ⟨h1, h2⟩ := hp
    show sem c P Q = sem c P' Q'
    exact propext (hf P Q P' Q' ⟨h1, h2⟩)

/-- The cell decomposition: the workbench's `ProfileClassifierRepresentation`
is, constructively, exactly the conjunction of the two positive cells. -/
theorem representation_iff_cells (c : Candidate) :
    ProfileClassifierRepresentation F Break Dyn sem c ↔
      FiberRespectsProfile F Break Dyn sem c ∧
      FalseOnDiagonal F Break Dyn sem c := by
  constructor
  · rintro ⟨φ, hSilent, hIff⟩
    refine ⟨?_, ?_⟩
    · intro P Q P' Q' hEqv
      constructor
      · intro hsem
        have hφ : φ (profile F Break Dyn P) (profile F Break Dyn Q) :=
          (hIff P Q).mpr hsem
        rw [hEqv.1, hEqv.2] at hφ
        exact (hIff P' Q').mp hφ
      · intro hsem
        have hφ : φ (profile F Break Dyn P') (profile F Break Dyn Q') :=
          (hIff P' Q').mpr hsem
        rw [← hEqv.1, ← hEqv.2] at hφ
        exact (hIff P Q).mp hφ
    · intro P Q hSame hsem
      have hφ : φ (profile F Break Dyn P) (profile F Break Dyn Q) :=
        (hIff P Q).mpr hsem
      rw [hSame] at hφ
      exact hSilent _ hφ
  · rintro ⟨hfib, hdiag⟩
    refine ⟨canonicalProfilePairClassifier F Break Dyn sem c, ?_, ?_⟩
    · rintro p ⟨P, Q, hP, hQ, hsem⟩
      exact hdiag P Q (hP.trans hQ.symm) hsem
    · intro P Q
      constructor
      · rintro ⟨P', Q', hP', hQ', hsem'⟩
        exact (hfib P' Q' P Q ⟨hP', hQ'⟩).mp hsem'
      · intro hsem
        exact ⟨P, Q, rfl, rfl, hsem⟩

/-- Cells refute the explicit diagnostic witness (constructive). -/
theorem noDiagnostic_of_cells (c : Candidate)
    (hcells : FiberRespectsProfile F Break Dyn sem c ∧
      FalseOnDiagonal F Break Dyn sem c) :
    ¬ ExplicitDiagnosticWitness F Break Dyn sem c := by
  rintro (hViol | hAmb)
  · obtain ⟨P, Q, hsem, hSame⟩ := hViol
    exact hcells.2 P Q hSame hsem
  · obtain ⟨P, Q, P', Q', hEqv, hAsym⟩ := hAmb
    rcases hAsym with ⟨hsem, hnot⟩ | ⟨hsem, hnot⟩
    · exact hnot ((hcells.1 P Q P' Q' hEqv).mp hsem)
    · exact hnot ((hcells.1 P Q P' Q' hEqv).mpr hsem)

/-- The witness clause is the contrapositive: no witness gives the cells.
This is the classical direction (`by_contra`); compare the workbench's
`by_contra` in `profileRepresentation_of_noDiagnostic`. -/
theorem cells_of_noDiagnostic (c : Candidate)
    (h : ¬ ExplicitDiagnosticWitness F Break Dyn sem c) :
    FiberRespectsProfile F Break Dyn sem c ∧
      FalseOnDiagonal F Break Dyn sem c := by
  refine ⟨?_, ?_⟩
  · intro P Q P' Q' hEqv
    constructor
    · intro hsem
      by_contra hnot
      exact h (Or.inr ⟨P, Q, P', Q', hEqv, Or.inl ⟨hsem, hnot⟩⟩)
    · intro hsem
      by_contra hnot
      exact h (Or.inr ⟨P, Q, P', Q', hEqv, Or.inr ⟨hsem, hnot⟩⟩)
  · intro P Q hSame hsem
    exact h (Or.inl ⟨P, Q, hsem, hSame⟩)

/-! ## Section 3: the Mathlib engine

`Function.factorsThrough_iff` (Mathlib v4.14.0, `Mathlib/Logic/Function/
Basic.lean`) constructs, from fiber-respect, a factor map `e` with
`PairSem c = e ∘ PairProfile` — via `Function.extend`, i.e. `Classical.choice`.
We consume that construction instead of hand-rolling a transport, and patch
the diagonal with cell 2. -/

/-- Representation gives fiber-respect directly (constructive). -/
theorem factorsThrough_of_representation (c : Candidate)
    (h : ProfileClassifierRepresentation F Break Dyn sem c) :
    Function.FactorsThrough (PairSem sem c) (PairProfile F Break Dyn) := by
  obtain ⟨φ, -, hIff⟩ := h
  intro s t hp
  obtain ⟨P, Q⟩ := s
  obtain ⟨P', Q'⟩ := t
  simp only [PairProfile, Prod.mk.injEq] at hp
  obtain ⟨h1, h2⟩ := hp
  show sem c P Q = sem c P' Q'
  refine propext ⟨fun hsem => ?_, fun hsem => ?_⟩
  · have hφ : φ (profile F Break Dyn P) (profile F Break Dyn Q) :=
      (hIff P Q).mpr hsem
    rw [h1, h2] at hφ
    exact (hIff P' Q').mp hφ
  · have hφ : φ (profile F Break Dyn P') (profile F Break Dyn Q') :=
      (hIff P' Q').mpr hsem
    rw [← h1, ← h2] at hφ
    exact (hIff P Q).mp hφ

/-- The Mathlib construction: from `Function.FactorsThrough` (Mathlib's
`factorsThrough_iff` builds `e` by `Function.extend` — `Classical.choice`)
and the diagonal cell, a silent profile-pair classifier. -/
theorem representation_of_factorsThrough (c : Candidate)
    (hFT : Function.FactorsThrough (PairSem sem c)
      (PairProfile F Break Dyn))
    (hdiag : FalseOnDiagonal F Break Dyn sem c) :
    ProfileClassifierRepresentation F Break Dyn sem c := by
  haveI : Nonempty Prop := ⟨True⟩
  obtain ⟨e, he⟩ :=
    (Function.factorsThrough_iff (PairSem sem c)).mp hFT
  refine ⟨fun p q => e (p, q) ∧ p ≠ q, ?_, ?_⟩
  · rintro p ⟨-, hne⟩
    exact hne rfl
  · intro P Q
    have hbeta : ∀ s : State × State,
        (e ∘ PairProfile F Break Dyn) s = e (PairProfile F Break Dyn s) := fun _ => rfl
    constructor
    · rintro ⟨hePQ, -⟩
      have : (e ∘ PairProfile F Break Dyn) (P, Q) := hePQ
      rw [hbeta] at this
      show sem c P Q
      have hsem : PairSem sem c (P, Q) := by
        rw [he]
        exact this
      exact hsem
    · intro hsem
      refine ⟨?_, ?_⟩
      · have : PairSem sem c (P, Q) := hsem
        rw [he, hbeta] at this
        exact this
      · intro hEq
        exact hdiag P Q hEq hsem

/-! ## Section 4: the workbench theorem chain, re-proved -/

theorem profileRepresentation_implies_noDiagnostic
    (c : Candidate)
    (hRep : ProfileClassifierRepresentation F Break Dyn sem c) :
    ¬ ExplicitDiagnosticWitness F Break Dyn sem c :=
  noDiagnostic_of_cells F Break Dyn sem c
    ((representation_iff_cells F Break Dyn sem c).mp hRep)

theorem profileRepresentation_of_noDiagnostic
    (c : Candidate)
    (hNoDiag : ¬ ExplicitDiagnosticWitness F Break Dyn sem c) :
    ProfileClassifierRepresentation F Break Dyn sem c := by
  apply representation_of_factorsThrough F Break Dyn sem c
  · exact (factorsThrough_iff_fiberRespectsProfile F Break Dyn sem c).mpr
      ((cells_of_noDiagnostic F Break Dyn sem c hNoDiag).1)
  · exact (cells_of_noDiagnostic F Break Dyn sem c hNoDiag).2

theorem profileRepresentation_iff_noDiagnostic
    (c : Candidate) :
    ProfileClassifierRepresentation F Break Dyn sem c
      ↔ ¬ ExplicitDiagnosticWitness F Break Dyn sem c :=
  ⟨profileRepresentation_implies_noDiagnostic F Break Dyn sem c,
    profileRepresentation_of_noDiagnostic F Break Dyn sem c⟩

theorem allAdmissibleRepresented_iff_noExplicitDiagnosticWitness :
    AllCRTAdmissibleRepresented F Break Dyn sem IsCRTDimension
      ↔ NoExplicitDiagnosticWitness F Break Dyn sem IsCRTDimension := by
  constructor
  · intro hAll c hC
    exact
      (profileRepresentation_iff_noDiagnostic F Break Dyn sem c).mp
        (hAll c hC)
  · intro hNo c hC
    exact
      (profileRepresentation_iff_noDiagnostic F Break Dyn sem c).mpr
        (hNo c hC)

theorem allAdmissibleRepresented_implies_noIndependentFourth
    (hAll : AllCRTAdmissibleRepresented F Break Dyn sem IsCRTDimension) :
    NoIndependentFourth F Break Dyn sem IsCRTDimension := by
  intro hSome
  obtain ⟨c, hC, hNotRep⟩ := hSome
  exact hNotRep (hAll c hC)

theorem noIndependentFourth_implies_allAdmissibleRepresented
    (hNo : NoIndependentFourth F Break Dyn sem IsCRTDimension) :
    AllCRTAdmissibleRepresented F Break Dyn sem IsCRTDimension := by
  intro c hC
  by_contra hNotRep
  exact hNo ⟨c, hC, hNotRep⟩

theorem noIndependentFourth_iff_allAdmissibleRepresented :
    NoIndependentFourth F Break Dyn sem IsCRTDimension
      ↔ AllCRTAdmissibleRepresented F Break Dyn sem IsCRTDimension :=
  ⟨
    noIndependentFourth_implies_allAdmissibleRepresented
      F Break Dyn sem IsCRTDimension,
    allAdmissibleRepresented_implies_noIndependentFourth
      F Break Dyn sem IsCRTDimension⟩

theorem someIndependentFourth_iff_someExplicitDiagnosticWitness :
    SomeIndependentFourthCandidate F Break Dyn sem IsCRTDimension
      ↔ SomeExplicitDiagnosticWitness F Break Dyn sem IsCRTDimension := by
  constructor
  · intro hSome
    obtain ⟨c, hC, hNotRep⟩ := hSome
    have hDiag : ExplicitDiagnosticWitness F Break Dyn sem c := by
      by_contra hNoDiag
      exact hNotRep
        ((profileRepresentation_iff_noDiagnostic F Break Dyn sem c).mpr
          hNoDiag)
    exact ⟨c, hC, hDiag⟩
  · intro hSome
    obtain ⟨c, hC, hDiag⟩ := hSome
    have hNotRep : ¬ ProfileClassifierRepresentation F Break Dyn sem c := by
      intro hRep
      exact
        ((profileRepresentation_iff_noDiagnostic F Break Dyn sem c).mp
          hRep) hDiag
    exact ⟨c, hC, hNotRep⟩

theorem noIndependentFourth_iff_noExplicitDiagnosticWitness :
    NoIndependentFourth F Break Dyn sem IsCRTDimension
      ↔ NoExplicitDiagnosticWitness F Break Dyn sem IsCRTDimension := by
  rw [noIndependentFourth_iff_allAdmissibleRepresented,
    allAdmissibleRepresented_iff_noExplicitDiagnosticWitness]

theorem noExplicitDiagnosticWitness_of_modelingLanguageCompleteness
    (hComplete :
      CRTModelingLanguageCompleteness F Break Dyn sem IsCRTDimension) :
    NoExplicitDiagnosticWitness F Break Dyn sem IsCRTDimension :=
  (allAdmissibleRepresented_iff_noExplicitDiagnosticWitness
    F Break Dyn sem IsCRTDimension).mp hComplete

theorem noIndependentFourth_of_modelingLanguageCompleteness
    (hComplete :
      CRTModelingLanguageCompleteness F Break Dyn sem IsCRTDimension) :
    NoIndependentFourth F Break Dyn sem IsCRTDimension :=
  allAdmissibleRepresented_implies_noIndependentFourth
    F Break Dyn sem IsCRTDimension hComplete

theorem scopedFinalNoFourthTheorem_iff_pureAxes_and_noExplicitDiagnosticWitness :
    ScopedFinalNoFourthTheorem F Break Dyn sem IsCRTDimension
      ↔ PureAxisWitnesses F Break Dyn
        ∧ NoExplicitDiagnosticWitness F Break Dyn sem IsCRTDimension := by
  constructor
  · intro hFinal
    exact ⟨hFinal.1, hFinal.2.2.1⟩
  · intro h
    obtain ⟨hPure, hNoDiag⟩ := h
    have hAll : AllCRTAdmissibleRepresented F Break Dyn sem IsCRTDimension :=
      (allAdmissibleRepresented_iff_noExplicitDiagnosticWitness
        F Break Dyn sem IsCRTDimension).mpr hNoDiag
    have hNoFourth : NoIndependentFourth F Break Dyn sem IsCRTDimension :=
      allAdmissibleRepresented_implies_noIndependentFourth
        F Break Dyn sem IsCRTDimension hAll
    exact ⟨hPure, hAll, hNoDiag, hNoFourth⟩

theorem scopedFinalNoFourthTheorem_of_modelingLanguageCompleteness
    (hPure : PureAxisWitnesses F Break Dyn)
    (hComplete :
      CRTModelingLanguageCompleteness F Break Dyn sem IsCRTDimension) :
    ScopedFinalNoFourthTheorem F Break Dyn sem IsCRTDimension := by
  have hNoDiag :
      NoExplicitDiagnosticWitness F Break Dyn sem IsCRTDimension :=
    noExplicitDiagnosticWitness_of_modelingLanguageCompleteness
      F Break Dyn sem IsCRTDimension hComplete
  exact
    (scopedFinalNoFourthTheorem_iff_pureAxes_and_noExplicitDiagnosticWitness
      F Break Dyn sem IsCRTDimension).mpr
      ⟨hPure, hNoDiag⟩

theorem independentFourth_requires_explicitDiagnosticWitness
    (hSome :
      SomeIndependentFourthCandidate F Break Dyn sem IsCRTDimension) :
    SomeExplicitDiagnosticWitness F Break Dyn sem IsCRTDimension :=
  (someIndependentFourth_iff_someExplicitDiagnosticWitness
    F Break Dyn sem IsCRTDimension).mp hSome

theorem explicitDiagnosticWitness_yields_independentFourth
    (hSome :
      SomeExplicitDiagnosticWitness F Break Dyn sem IsCRTDimension) :
    SomeIndependentFourthCandidate F Break Dyn sem IsCRTDimension :=
  (someIndependentFourth_iff_someExplicitDiagnosticWitness
    F Break Dyn sem IsCRTDimension).mpr hSome

/-! ## Section 5: the constructive tier

The classical step in Section 4 is exactly one: `cells_of_noDiagnostic`
(the contrapositive of the witness clause). Stated positively — "no
independent fourth" as fiber-respect — the FDT content is choice-free, and
the factor map lives on the quotient by profile-pair equality, built by
`Quot.lift` (`Quot.sound` only, no `Function.extend`). -/

/-- "No independent fourth" against the two positive cells. The ←
direction is constructive; the → direction inherits the one classical
step of Section 4 (`profileRepresentation_of_noDiagnostic`), since
`NoIndependentFourth` is a negation and the cells are positive. -/
theorem noIndependentFourth_iff_cells :
    NoIndependentFourth F Break Dyn sem IsCRTDimension
      ↔ ∀ c : Candidate,
          IsCRTDimension c →
            FiberRespectsProfile F Break Dyn sem c ∧
              FalseOnDiagonal F Break Dyn sem c := by
  constructor
  · intro hNo c hC
    have hNotDiag : ¬ ExplicitDiagnosticWitness F Break Dyn sem c := by
      intro hDiag
      refine hNo ⟨c, hC, ?_⟩
      intro hRep
      exact (profileRepresentation_implies_noDiagnostic F Break Dyn sem c) hRep hDiag
    exact (representation_iff_cells F Break Dyn sem c).mp
      (profileRepresentation_of_noDiagnostic F Break Dyn sem c hNotDiag)
  · rintro hCells ⟨c, hC, hNotRep⟩
    exact hNotRep
      ((representation_iff_cells F Break Dyn sem c).mpr (hCells c hC))

/-- Profile-pair equality as a `Quot` relation. -/
def PairProfileEqv (s t : State × State) : Prop :=
  PairProfile F Break Dyn s = PairProfile F Break Dyn t

/-- The factor map on the quotient, built by `Quot.lift` — the constructive
home of "factors through". -/
def QuotientPairClassifier (c : Candidate)
    (h : ∀ s t : State × State,
      PairProfileEqv F Break Dyn s t →
        PairSem sem c s = PairSem sem c t) :
    Quot (PairProfileEqv F Break Dyn) → Prop :=
  Quot.lift (PairSem sem c) h

theorem fiberEq_of_factorsThrough (c : Candidate)
    (hFT : Function.FactorsThrough (PairSem sem c)
      (PairProfile F Break Dyn)) :
    ∀ s t : State × State,
      PairProfileEqv F Break Dyn s t →
        PairSem sem c s = PairSem sem c t :=
  hFT

theorem quotientPairClassifier_spec (c : Candidate)
    (hFT : Function.FactorsThrough (PairSem sem c)
      (PairProfile F Break Dyn))
    (P Q : State) :
    QuotientPairClassifier F Break Dyn sem c
      (fiberEq_of_factorsThrough F Break Dyn sem c hFT)
      (Quot.mk _ (P, Q)) ↔
      sem c P Q := Iff.rfl

end MSTNFFDTFactorsThroughMWE

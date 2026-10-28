import Mathlib.Tactic

universe u v w z r

namespace CRTScopedFinalNoFourthComplete

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

-- PROBE O1 (ORIGINAL statement, constructive engine direction)
example (c : Candidate)
    (hNoDiag : ¬ ExplicitDiagnosticWitness F Break Dyn sem c) :
    ProfileClassifierRepresentation F Break Dyn sem c := by
  exact?


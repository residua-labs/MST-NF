/-!
# MST-NF execution no-fifth-role MWE

This file instantiates the FDT/CRT "no independent fourth" proof shape at the
execution-object-formation layer.

The scoped claim is not that no external engineering concern can ever be added.
It is:

```text
Inside a Φ-exec admissible role language, if every execution structural role is
represented by the q/a/ρ/σ profile, then there is no independent fifth
execution-object-formation role.
```

The proof shape mirrors the FDT construction:

```text
profile representation ⇔ no explicit diagnostic witness
all admissible roles represented ⇔ no explicit diagnostic witness
all admissible roles represented ⇒ no independent fifth role
```
-/

namespace MSTNFExecutionNoFifthRoleMWE

universe u v w

namespace Generic

variable {Obj : Type u}
variable {Role : Type v}
variable {Profile : Type w}

variable
  (profile : Obj → Profile)
  (sem : Role → Obj → Prop)
  (IsExecutionRole : Role → Prop)

def RoleClassifier : Type w :=
  Profile → Prop

def RoleProfileRepresentation (r : Role) : Prop :=
  ∃ φ : RoleClassifier (Profile := Profile),
    ∀ x : Obj, φ (profile x) ↔ sem r x

def ExplicitDiagnosticWitness (r : Role) : Prop :=
  ∃ x y : Obj,
    profile x = profile y
      ∧ ((sem r x ∧ ¬ sem r y) ∨
          (sem r y ∧ ¬ sem r x))

def NoExplicitDiagnosticWitness : Prop :=
  ∀ r : Role,
    IsExecutionRole r →
      ¬ ExplicitDiagnosticWitness profile sem r

def SomeExplicitDiagnosticWitness : Prop :=
  ∃ r : Role,
    IsExecutionRole r
      ∧ ExplicitDiagnosticWitness profile sem r

def AllExecutionRolesRepresented : Prop :=
  ∀ r : Role,
    IsExecutionRole r →
      RoleProfileRepresentation profile sem r

def SomeIndependentFifthRole : Prop :=
  ∃ r : Role,
    IsExecutionRole r
      ∧ ¬ RoleProfileRepresentation profile sem r

def NoIndependentFifthRole : Prop :=
  ¬ SomeIndependentFifthRole profile sem IsExecutionRole

def canonicalRoleClassifier (r : Role) :
    RoleClassifier (Profile := Profile) :=
  fun p => ∃ x : Obj, profile x = p ∧ sem r x

theorem roleRepresentation_implies_noDiagnostic
    (r : Role)
    (hRep : RoleProfileRepresentation profile sem r) :
    ¬ ExplicitDiagnosticWitness profile sem r := by
  rcases hRep with ⟨φ, hIff⟩
  intro hDiag
  rcases hDiag with ⟨x, y, hSame, hAsym⟩
  have hSemIff : sem r x ↔ sem r y := by
    constructor
    · intro hx
      have hxφ : φ (profile x) := (hIff x).mpr hx
      have hyφ : φ (profile y) := by
        rwa [hSame] at hxφ
      exact (hIff y).mp hyφ
    · intro hy
      have hyφ : φ (profile y) := (hIff y).mpr hy
      have hxφ : φ (profile x) := by
        rwa [← hSame] at hyφ
      exact (hIff x).mp hxφ
  rcases hAsym with ⟨hx, hny⟩ | ⟨hy, hnx⟩
  · exact hny (hSemIff.mp hx)
  · exact hnx (hSemIff.mpr hy)

theorem roleRepresentation_of_noDiagnostic
    (r : Role)
    (hNoDiag : ¬ ExplicitDiagnosticWitness profile sem r) :
    RoleProfileRepresentation profile sem r := by
  refine ⟨canonicalRoleClassifier profile sem r, ?_⟩
  intro x
  constructor
  · intro hφ
    rcases hφ with ⟨y, hProfile, hy⟩
    exact Classical.byContradiction
      (fun hnx => hNoDiag ⟨y, x, hProfile, Or.inl ⟨hy, hnx⟩⟩)
  · intro hx
    exact ⟨x, rfl, hx⟩

theorem roleRepresentation_iff_noDiagnostic
    (r : Role) :
    RoleProfileRepresentation profile sem r
      ↔ ¬ ExplicitDiagnosticWitness profile sem r := by
  exact ⟨
    roleRepresentation_implies_noDiagnostic profile sem r,
    roleRepresentation_of_noDiagnostic profile sem r⟩

theorem allRolesRepresented_iff_noExplicitDiagnosticWitness :
    AllExecutionRolesRepresented profile sem IsExecutionRole
      ↔ NoExplicitDiagnosticWitness profile sem IsExecutionRole := by
  constructor
  · intro hAll r hRole
    exact
      (roleRepresentation_iff_noDiagnostic profile sem r).mp
        (hAll r hRole)
  · intro hNo r hRole
    exact
      (roleRepresentation_iff_noDiagnostic profile sem r).mpr
        (hNo r hRole)

theorem allRolesRepresented_implies_noIndependentFifth
    (hAll : AllExecutionRolesRepresented profile sem IsExecutionRole) :
    NoIndependentFifthRole profile sem IsExecutionRole := by
  intro hSome
  rcases hSome with ⟨r, hRole, hNotRep⟩
  exact hNotRep (hAll r hRole)

theorem noIndependentFifth_implies_allRolesRepresented
    (hNo : NoIndependentFifthRole profile sem IsExecutionRole) :
    AllExecutionRolesRepresented profile sem IsExecutionRole := by
  intro r hRole
  exact Classical.byContradiction
    (fun hNotRep => hNo ⟨r, hRole, hNotRep⟩)

theorem noIndependentFifth_iff_allRolesRepresented :
    NoIndependentFifthRole profile sem IsExecutionRole
      ↔ AllExecutionRolesRepresented profile sem IsExecutionRole := by
  exact ⟨
    noIndependentFifth_implies_allRolesRepresented profile sem IsExecutionRole,
    allRolesRepresented_implies_noIndependentFifth profile sem IsExecutionRole⟩

theorem noIndependentFifth_iff_noExplicitDiagnosticWitness :
    NoIndependentFifthRole profile sem IsExecutionRole
      ↔ NoExplicitDiagnosticWitness profile sem IsExecutionRole := by
  rw [noIndependentFifth_iff_allRolesRepresented,
    allRolesRepresented_iff_noExplicitDiagnosticWitness]

theorem noIndependentFifth_of_modelingCompleteness
    (hComplete : AllExecutionRolesRepresented profile sem IsExecutionRole) :
    NoIndependentFifthRole profile sem IsExecutionRole :=
  allRolesRepresented_implies_noIndependentFifth profile sem IsExecutionRole
    hComplete

end Generic

namespace CoreExecutionProfile

inductive ExecutionRole where
  | distinguish
  | constrain
  | residueClosure
  | representative
deriving DecidableEq, Repr

inductive RoleProfile where
  | q
  | a
  | rho
  | sigma
deriving DecidableEq, Repr

open ExecutionRole RoleProfile

def profile : RoleProfile → RoleProfile :=
  id

def roleProfile : ExecutionRole → RoleProfile
  | distinguish => q
  | constrain => a
  | residueClosure => rho
  | representative => sigma

def sem (r : ExecutionRole) (p : RoleProfile) : Prop :=
  p = roleProfile r

def IsExecutionRole (_r : ExecutionRole) : Prop :=
  True

def classifierFor (r : ExecutionRole) :
    Generic.RoleClassifier (Profile := RoleProfile) :=
  fun p => p = roleProfile r

theorem coreRole_represented (r : ExecutionRole) :
    Generic.RoleProfileRepresentation profile sem r := by
  exact ⟨classifierFor r, by
    intro p
    rfl⟩

theorem coreRolesRepresented :
    Generic.AllExecutionRolesRepresented profile sem IsExecutionRole := by
  intro r _h
  exact coreRole_represented r

theorem noIndependentFifth_for_coreProfile :
    Generic.NoIndependentFifthRole profile sem IsExecutionRole :=
  Generic.noIndependentFifth_of_modelingCompleteness profile sem IsExecutionRole
    coreRolesRepresented

theorem coreProfile_noExplicitDiagnostic :
    Generic.NoExplicitDiagnosticWitness profile sem IsExecutionRole := by
  intro r _ hDiag
  rcases hDiag with ⟨x, y, hxy, hAsym⟩
  have hxy' : x = y := hxy
  subst hxy'
  rcases hAsym with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact hy hx
  · exact hx hy

theorem distinguish_is_q :
    roleProfile distinguish = q := by
  rfl

theorem constrain_is_a :
    roleProfile constrain = a := by
  rfl

theorem residueClosure_is_rho :
    roleProfile residueClosure = rho := by
  rfl

theorem representative_is_sigma :
    roleProfile representative = sigma := by
  rfl

end CoreExecutionProfile

end MSTNFExecutionNoFifthRoleMWE

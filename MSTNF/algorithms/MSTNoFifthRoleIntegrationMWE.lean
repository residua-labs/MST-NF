import MSTNF.algorithms.MSTMinimalityRoleBasisMWE

/-!
# MST No-Fifth-Role Integration MWE

This file integrates the informal "no fifth coordinate" boundary with the
current RoleBasis framework.

It proves the precise statement that can be justified at this layer:

* a candidate fifth role whose property is already entailed by the MST-NF
  profile does not refine the kernel;
* adding such a role to the basis does not change the profile;
* unlike the four standard roles, such a dependent fifth role has no
  independent deletion countermodel.

Boundary: this does not prove that no future theory extension can ever add a
new independent dimension.  It proves that a dependent/refinement candidate is
not a fifth independent diagnostic coordinate.
-/

namespace MSTNoFifthRoleIntegrationMWE

open MSTNecessityExecModelMWE
open MSTNecessityRoleAblationMWE
open MSTMinimalityRoleBasisMWE

-- ---------------------------------------------------------------------------
-- Dependent fifth-role candidates
-- ---------------------------------------------------------------------------

/-- A fifth-role candidate is dependent when its property is already entailed
by the four-role MST-NF profile. -/
structure DependentFifthRole where
  property : ExecModel → Prop
  entailedByProfile : ∀ M : ExecModel, hasMSTNFProfile M → property M

def profileWithFifth (F : DependentFifthRole) (M : ExecModel) : Prop :=
  hasMSTNFProfile M ∧ F.property M

theorem profileWithFifth_iff_profile
    (F : DependentFifthRole) (M : ExecModel) :
    profileWithFifth F M ↔ hasMSTNFProfile M := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, F.entailedByProfile M h⟩

/-- A dependent fifth role cannot have the same deletion-witness shape as a
standard independent role: there is no model satisfying the full profile while
failing the dependent candidate. -/
theorem no_independent_deletion_countermodel_for_dependent_fifth
    (F : DependentFifthRole) :
    ¬ ∃ M : ExecModel, hasMSTNFProfile M ∧ ¬ F.property M := by
  intro h
  rcases h with ⟨M, hProfile, hFail⟩
  exact hFail (F.entailedByProfile M hProfile)

-- ---------------------------------------------------------------------------
-- Extended basis with a dependent fifth role
-- ---------------------------------------------------------------------------

inductive ExtendedRole where
  | standard (r : MSTRole)
  | fifth
deriving DecidableEq, Repr

def ExtendedBasis (F : DependentFifthRole) : RoleBasis where
  Role := ExtendedRole
  property := fun role M =>
    match role with
    | .standard r => roleProperty r M
    | .fifth => F.property M

/-- Adding a dependent fifth role does not change the profile determined by the
four standard roles. -/
theorem all_extended_roles_iff_profile
    (F : DependentFifthRole) (M : ExecModel) :
    (∀ role : ExtendedRole, (ExtendedBasis F).property role M) ↔
      hasMSTNFProfile M := by
  constructor
  · intro h
    exact ⟨h (.standard .quotient),
      h (.standard .admissibility),
      h (.standard .residue),
      h (.standard .representative)⟩
  · intro hProfile
    intro role
    cases role with
    | standard r =>
        cases r <;> simp [ExtendedBasis, roleProperty, hasMSTNFProfile] at hProfile ⊢
        · exact hProfile.1
        · exact hProfile.2.1
        · exact hProfile.2.2.1
        · exact hProfile.2.2.2
    | fifth =>
        exact F.entailedByProfile M hProfile

theorem extended_basis_complete
    (F : DependentFifthRole) :
    complete (ExtendedBasis F) := by
  intro M h
  exact (all_extended_roles_iff_profile F M).1 h

/-- The standard four roles embed into the extended basis; the fifth role is
not used by the simulation because it is dependent. -/
def standardSimulationIntoExtended
    (F : DependentFifthRole) : Simulation (ExtendedBasis F) where
  map := ExtendedRole.standard
  sound := by
    intro r M h
    exact h

theorem standard_simulation_into_extended_injective
    (F : DependentFifthRole) :
    InjectiveMap (standardSimulationIntoExtended F).map := by
  intro r1 r2 h
  cases h
  rfl

end MSTNoFifthRoleIntegrationMWE


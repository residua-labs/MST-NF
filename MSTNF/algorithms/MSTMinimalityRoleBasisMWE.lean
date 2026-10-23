import MSTNF.algorithms.MSTNecessityRoleAblationMWE

/-!
# MST Minimality Role Basis MWE

This file proves the P3 minimality claim in the precise diagnostic sense:

* arbitrary compression by conjunction is possible and is not ruled out;
* what cannot be compressed is independent diagnostic capacity.

If a basis can independently diagnose all four MST roles, then its simulation
map from the standard four roles must be injective.  Therefore any complete
independent diagnostic basis contains at least four distinguishable role
positions.  This is the formal version of "minimal as an independent diagnostic
basis", not "minimal as an arbitrary compressed encoding".
-/

namespace MSTMinimalityRoleBasisMWE

open MSTNecessityExecModelMWE
open MSTNecessityRoleAblationMWE

-- ---------------------------------------------------------------------------
-- Abstract role bases and simulations
-- ---------------------------------------------------------------------------

structure RoleBasis where
  Role : Type
  property : Role → ExecModel → Prop

structure Simulation (B : RoleBasis) where
  map : MSTRole → B.Role
  sound : ∀ (r : MSTRole) (M : ExecModel),
    B.property (map r) M → roleProperty r M

/-- Local injectivity predicate, kept explicit to avoid importing extra theory. -/
def InjectiveMap {α β : Type} (f : α → β) : Prop :=
  ∀ a b : α, f a = f b → a = b

/-- Completeness says satisfying every basis role entails the full MST-NF
profile.  It is recorded for the P3 vocabulary; the injectivity theorem below
uses independent diagnostics rather than completeness. -/
def complete (B : RoleBasis) : Prop :=
  ∀ (M : ExecModel),
    (∀ r : B.Role, B.property r M) →
    hasMSTNFProfile M

/-- B can independently diagnose role `r` if there is a model that satisfies
all other standard roles at the B-level but fails the B-role mapped from `r`. -/
def independentlyDiagnosable (B : RoleBasis) (S : Simulation B)
    (r : MSTRole) : Prop :=
  ∃ M : ExecModel,
    (∀ r' : MSTRole, r' ≠ r → B.property (S.map r') M) ∧
    ¬ B.property (S.map r) M

-- ---------------------------------------------------------------------------
-- P3a: non-injective simulation requires role fusion
-- ---------------------------------------------------------------------------

theorem noninjective_simulation_requires_role_fusion
    {B : RoleBasis} (S : Simulation B) :
    ¬ InjectiveMap S.map →
    ∃ r1 r2 : MSTRole, r1 ≠ r2 ∧ S.map r1 = S.map r2 := by
  classical
  intro hnot
  exact Classical.byContradiction fun hnone =>
    hnot fun r1 r2 hmap =>
      Classical.byContradiction fun hne =>
        hnone ⟨r1, r2, hne, hmap⟩

-- ---------------------------------------------------------------------------
-- P3b: fused roles cannot both remain independently diagnosable
-- ---------------------------------------------------------------------------

theorem fused_role_not_independently_diagnosable
    {B : RoleBasis} (S : Simulation B)
    {r1 r2 : MSTRole} (hne : r1 ≠ r2) (hfused : S.map r1 = S.map r2) :
    ¬ independentlyDiagnosable B S r1 := by
  intro hdiag
  rcases hdiag with ⟨M, hothers, hfail⟩
  have hother : B.property (S.map r2) M := hothers r2 hne.symm
  exact hfail (by rwa [hfused])

theorem fused_roles_lose_independent_diagnostics
    {B : RoleBasis} (S : Simulation B)
    {r1 r2 : MSTRole} (hne : r1 ≠ r2) (hfused : S.map r1 = S.map r2) :
    ¬ (independentlyDiagnosable B S r1 ∧ independentlyDiagnosable B S r2) := by
  intro hboth
  exact fused_role_not_independently_diagnosable S hne hfused hboth.1

-- ---------------------------------------------------------------------------
-- P3 main theorem
-- ---------------------------------------------------------------------------

theorem standard_basis_is_minimal_independent_diagnostic_basis
    {B : RoleBasis} (S : Simulation B)
    (_hcomplete : complete B)
    (hdiag : ∀ r : MSTRole, independentlyDiagnosable B S r) :
    InjectiveMap S.map := by
  classical
  intro r1 r2 hfused
  cases r1 <;> cases r2
  · rfl
  · exfalso
    exact fused_roles_lose_independent_diagnostics S (by intro h; cases h) hfused
      ⟨hdiag MSTRole.quotient, hdiag MSTRole.admissibility⟩
  · exfalso
    exact fused_roles_lose_independent_diagnostics S (by intro h; cases h) hfused
      ⟨hdiag MSTRole.quotient, hdiag MSTRole.residue⟩
  · exfalso
    exact fused_roles_lose_independent_diagnostics S (by intro h; cases h) hfused
      ⟨hdiag MSTRole.quotient, hdiag MSTRole.representative⟩
  · exfalso
    exact fused_roles_lose_independent_diagnostics S (by intro h; cases h) hfused
      ⟨hdiag MSTRole.admissibility, hdiag MSTRole.quotient⟩
  · rfl
  · exfalso
    exact fused_roles_lose_independent_diagnostics S (by intro h; cases h) hfused
      ⟨hdiag MSTRole.admissibility, hdiag MSTRole.residue⟩
  · exfalso
    exact fused_roles_lose_independent_diagnostics S (by intro h; cases h) hfused
      ⟨hdiag MSTRole.admissibility, hdiag MSTRole.representative⟩
  · exfalso
    exact fused_roles_lose_independent_diagnostics S (by intro h; cases h) hfused
      ⟨hdiag MSTRole.residue, hdiag MSTRole.quotient⟩
  · exfalso
    exact fused_roles_lose_independent_diagnostics S (by intro h; cases h) hfused
      ⟨hdiag MSTRole.residue, hdiag MSTRole.admissibility⟩
  · rfl
  · exfalso
    exact fused_roles_lose_independent_diagnostics S (by intro h; cases h) hfused
      ⟨hdiag MSTRole.residue, hdiag MSTRole.representative⟩
  · exfalso
    exact fused_roles_lose_independent_diagnostics S (by intro h; cases h) hfused
      ⟨hdiag MSTRole.representative, hdiag MSTRole.quotient⟩
  · exfalso
    exact fused_roles_lose_independent_diagnostics S (by intro h; cases h) hfused
      ⟨hdiag MSTRole.representative, hdiag MSTRole.admissibility⟩
  · exfalso
    exact fused_roles_lose_independent_diagnostics S (by intro h; cases h) hfused
      ⟨hdiag MSTRole.representative, hdiag MSTRole.residue⟩
  · rfl

-- ---------------------------------------------------------------------------
-- Standard basis sanity checks
-- ---------------------------------------------------------------------------

def StandardRoleBasis : RoleBasis where
  Role := MSTRole
  property := roleProperty

def standardSimulation : Simulation StandardRoleBasis where
  map := id
  sound := by
    intro r M h
    exact h

theorem allOtherRolesHold_implies_roleProperty
    {role r' : MSTRole} {M : ExecModel}
    (h : allOtherRolesHold role M) (hne : r' ≠ role) :
    roleProperty r' M := by
  cases role <;> cases r' <;> simp [allOtherRolesHold, roleProperty] at h hne ⊢
  · exact h.1
  · exact h.2.1
  · exact h.2.2
  · exact h.1
  · exact h.2.1
  · exact h.2.2
  · exact h.1
  · exact h.2.1
  · exact h.2.2
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- The standard basis has independent diagnostic witnesses, supplied by the
role-ablation theorem from P1-necessity.  The concrete `cm1..cm4` models are
private in that file; this theorem intentionally depends only on the public
ablation theorem. -/
theorem standard_basis_independently_diagnosable :
    ∀ r : MSTRole,
      independentlyDiagnosable StandardRoleBasis standardSimulation r := by
  intro r
  rcases deleting_each_role_breaks_semantics r with ⟨M, hothers, hfail⟩
  refine ⟨M, ?_, ?_⟩
  · intro r' hne
    exact allOtherRolesHold_implies_roleProperty hothers hne
  · exact hfail

theorem standardSimulation_injective :
    InjectiveMap standardSimulation.map := by
  intro r1 r2 h
  exact h

end MSTMinimalityRoleBasisMWE

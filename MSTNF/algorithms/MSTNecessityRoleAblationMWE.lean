import MSTNF.algorithms.MSTNecessityExecModelMWE

/-!
# MST Necessity Role Ablation MWE — P1-necessity

This file proves the necessity-first core of MST:

  theorem deleting_each_role_breaks_semantics

For each of the four MST roles (q / a / rho / sigma), there exists a
countermodel in which all other three role properties hold but the
target role property fails.

This proves role independence and necessity:
  - No role can be deleted without breaking a named semantic property.
  - The failure is not masked by absence of the other roles.

Proof order:
  P1-necessity (this file)  : necessity by ablation countermodel
  P1-sufficiency            : sufficiency — four roles give MST-NF profile
  P1-factorization           : semantics factors through active quotient

Boundary:
  Some non-target properties hold vacuously in the minimal countermodels.
  This is intentional: the theorem proves logical independence of the
  missing role, not non-degenerate coverage of every role in every
  countermodel.  A strengthened non-degenerate suite is future work.
-/

namespace MSTNecessityRoleAblationMWE

open MSTNecessityExecModelMWE

-- ---------------------------------------------------------------------------
-- Role taxonomy
-- ---------------------------------------------------------------------------

inductive MSTRole where
  | quotient       -- R1: q must distinguish classes
  | admissibility  -- R2: a must constrain commits
  | residue        -- Φ5: rho must totalize failures
  | representative -- Φ2b: sigma must supply executable point
  deriving DecidableEq, Repr

/-- Map each role to its named semantic property on an ExecModel. -/
def roleProperty (role : MSTRole) (M : ExecModel) : Prop :=
  match role with
  | .quotient       => quotientFactorization M
  | .admissibility  => admissibilitySound M
  | .residue        => residueTotality M
  | .representative => representativePrecision M

/-- All role properties except `role` hold on M. -/
def allOtherRolesHold (role : MSTRole) (M : ExecModel) : Prop :=
  match role with
  | .quotient =>
      admissibilitySound M ∧ residueTotality M ∧ representativePrecision M
  | .admissibility =>
      quotientFactorization M ∧ residueTotality M ∧ representativePrecision M
  | .residue =>
      quotientFactorization M ∧ admissibilitySound M ∧ representativePrecision M
  | .representative =>
      quotientFactorization M ∧ admissibilitySound M ∧ residueTotality M

-- ---------------------------------------------------------------------------
-- Countermodel 1: no quotient
-- Two raw events map to the same class but evalRaw gives different outcomes.
-- admissibilitySound / residueTotality / representativePrecision hold.
-- ---------------------------------------------------------------------------

private inductive CM1Raw    where | A | B   deriving DecidableEq
private inductive CM1Class  where | only    deriving DecidableEq
private inductive CM1Rep    where | rep0    deriving DecidableEq
private inductive CM1Res    where | res0    deriving DecidableEq
private inductive CM1Out    where | ok | bad deriving DecidableEq

private def cm1 : ExecModel where
  Raw      := CM1Raw
  Class    := CM1Class
  Rep      := CM1Rep
  Residue  := CM1Res
  Outcome  := CM1Out
  q        := fun _ => .only
  evalRaw  := fun r => match r with | .A => .ok | .B => .bad  -- different outcomes!
  evalClass := fun _ => .ok
  admissible := fun _ => true
  rho       := fun _ => none
  sigma     := fun _ => some .rep0

private theorem cm1_admissibilitySound : admissibilitySound cm1 := by
  intro c rep _; cases c <;> rfl

private theorem cm1_residueTotality : residueTotality cm1 := by
  intro c _ hadm
  cases c <;> simp [cm1] at hadm

private theorem cm1_representativePrecision : representativePrecision cm1 := by
  intro c _ _; cases c <;> simp [cm1]

private theorem cm1_not_quotientFactorization : ¬ quotientFactorization cm1 := by
  intro h
  have := h CM1Raw.B
  simp [cm1, quotientFactorization] at this

-- ---------------------------------------------------------------------------
-- Countermodel 2: no admissibility
-- A class has a representative but admissible = false.
-- quotientFactorization / residueTotality / representativePrecision hold.
-- ---------------------------------------------------------------------------

private inductive CM2Raw   where | A         deriving DecidableEq
private inductive CM2Class where | only       deriving DecidableEq
private inductive CM2Rep   where | rep0       deriving DecidableEq
private inductive CM2Res   where | res0       deriving DecidableEq
private inductive CM2Out   where | ok         deriving DecidableEq

private def cm2 : ExecModel where
  Raw      := CM2Raw
  Class    := CM2Class
  Rep      := CM2Rep
  Residue  := CM2Res
  Outcome  := CM2Out
  q        := fun _ => .only
  evalRaw  := fun _ => .ok
  evalClass := fun _ => .ok
  admissible := fun _ => false        -- not admissible!
  rho       := fun _ => some .res0   -- has residue
  sigma     := fun _ => some .rep0   -- but also has rep -> breaks admissibilitySound

private theorem cm2_quotientFactorization : quotientFactorization cm2 := by
  intro r; cases r <;> rfl

private theorem cm2_residueTotality : residueTotality cm2 := by
  intro c _ _; cases c <;> simp [cm2]

private theorem cm2_representativePrecision : representativePrecision cm2 := by
  intro c _ hadm
  cases c <;> simp [cm2] at hadm

private theorem cm2_not_admissibilitySound : ¬ admissibilitySound cm2 := by
  intro h
  have := h CM2Class.only CM2Rep.rep0 (by simp [cm2])
  simp [cm2] at this

-- ---------------------------------------------------------------------------
-- Countermodel 3: no residue
-- An active non-admissible class has rho = none.
-- quotientFactorization / admissibilitySound / representativePrecision hold.
-- ---------------------------------------------------------------------------

private inductive CM3Raw   where | A         deriving DecidableEq
private inductive CM3Class where | only       deriving DecidableEq
private inductive CM3Rep   where | rep0       deriving DecidableEq
private inductive CM3Res   where | res0       deriving DecidableEq
private inductive CM3Out   where | ok         deriving DecidableEq

private def cm3 : ExecModel where
  Raw      := CM3Raw
  Class    := CM3Class
  Rep      := CM3Rep
  Residue  := CM3Res
  Outcome  := CM3Out
  q        := fun _ => .only
  evalRaw  := fun _ => .ok
  evalClass := fun _ => .ok
  admissible := fun _ => false
  rho       := fun _ => none          -- no residue for non-admissible class!
  sigma     := fun _ => none

private theorem cm3_quotientFactorization : quotientFactorization cm3 := by
  intro r; cases r <;> rfl

private theorem cm3_admissibilitySound : admissibilitySound cm3 := by
  intro c rep h; cases c <;> simp [cm3] at h

private theorem cm3_representativePrecision : representativePrecision cm3 := by
  intro c _ hadm
  cases c <;> simp [cm3] at hadm

private theorem cm3_not_residueTotality : ¬ residueTotality cm3 := by
  intro h
  have := h CM3Class.only ⟨CM3Raw.A, rfl⟩ (by simp [cm3])
  simp [cm3] at this

-- ---------------------------------------------------------------------------
-- Countermodel 4: no representative
-- An active admissible class has sigma = none.
-- quotientFactorization / admissibilitySound / residueTotality hold.
-- ---------------------------------------------------------------------------

private inductive CM4Raw   where | A         deriving DecidableEq
private inductive CM4Class where | only       deriving DecidableEq
private inductive CM4Rep   where | rep0       deriving DecidableEq
private inductive CM4Res   where | res0       deriving DecidableEq
private inductive CM4Out   where | ok         deriving DecidableEq

private def cm4 : ExecModel where
  Raw      := CM4Raw
  Class    := CM4Class
  Rep      := CM4Rep
  Residue  := CM4Res
  Outcome  := CM4Out
  q        := fun _ => .only
  evalRaw  := fun _ => .ok
  evalClass := fun _ => .ok
  admissible := fun _ => true
  rho       := fun _ => none
  sigma     := fun _ => none          -- no representative for admissible class!

private theorem cm4_quotientFactorization : quotientFactorization cm4 := by
  intro r; cases r <;> rfl

private theorem cm4_admissibilitySound : admissibilitySound cm4 := by
  intro c rep h; cases c <;> simp [cm4] at h

private theorem cm4_residueTotality : residueTotality cm4 := by
  intro c _ hadm
  cases c <;> simp [cm4] at hadm

private theorem cm4_not_representativePrecision : ¬ representativePrecision cm4 := by
  intro h
  have := h CM4Class.only ⟨CM4Raw.A, rfl⟩ (by simp [cm4])
  simp [cm4] at this

-- ---------------------------------------------------------------------------
-- Main theorem: deleting each role breaks semantics
-- ---------------------------------------------------------------------------

/-- For each MST role, there exists a countermodel in which:
    (1) all other three role properties hold, and
    (2) the target role property fails.
    This proves that each role is independently necessary:
    it cannot be deleted without breaking a named semantic property,
    even when all other roles are intact. -/
theorem deleting_each_role_breaks_semantics :
    ∀ role : MSTRole,
      ∃ M : ExecModel,
        allOtherRolesHold role M ∧ ¬ roleProperty role M := by
  intro role
  cases role with
  | quotient =>
      exact ⟨cm1,
        ⟨cm1_admissibilitySound, cm1_residueTotality, cm1_representativePrecision⟩,
        cm1_not_quotientFactorization⟩
  | admissibility =>
      exact ⟨cm2,
        ⟨cm2_quotientFactorization, cm2_residueTotality, cm2_representativePrecision⟩,
        cm2_not_admissibilitySound⟩
  | residue =>
      exact ⟨cm3,
        ⟨cm3_quotientFactorization, cm3_admissibilitySound, cm3_representativePrecision⟩,
        cm3_not_residueTotality⟩
  | representative =>
      exact ⟨cm4,
        ⟨cm4_quotientFactorization, cm4_admissibilitySound, cm4_residueTotality⟩,
        cm4_not_representativePrecision⟩

end MSTNecessityRoleAblationMWE

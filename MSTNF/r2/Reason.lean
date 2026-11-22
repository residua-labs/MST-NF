import MSTNF.r2.Active
import MSTNF.r2.Finite

/-!
# MST-NF R2 — reason validity and refutation (contract §4)

Mechanization of the R2 contract, section 4 ("reason validity and
refutation"): independent `Reason : X → E → Prop` and `CanAdmit : X → Prop`
predicates, the two-tier obligations, the contract's observation that
requiring `rho c = some e → a c = false` is exactly Boolean exclusivity on
the same domain, and one concrete instantiation on the six-input
demonstrator together with the separation example (an operational reason
satisfying validity without refutation).

Sources (mature sources rule, preamble item 7):
- Design of record: `MST-NF-R2-mechanization-contract.md` section 4.
- Pinned base: `MSTNecessityExecModelMWE` (`ExecModel`, `activeClass`),
  `MSTNF.r2.Active` (`Cact`, `globalExclusivity`), `MSTNF.r2.Finite`
  (`base6`, `Raw6`, `Res3`, `baseQ`, `baseRho`).

Fidelity notes:
- `ReasonValid` quantifies over active classes carrying a residue and over
  all raw inputs in that class (the contract's `∀ c e, Active c →
  rho c = some e → ∀ x, q x = c → Reason x e`).
- The instantiation's `Reason` (`reasonBlocked`) is fixed **independently**
  of the model's `rho` and `q` (contract section 4: "Fix independent
  `Reason : X → E → Prop` and `CanAdmit : X → Prop`"): it is a syntactic
  description of the refused raw inputs of the demonstrator, not the
  residue assignment read back; `CanAdmit` is an explicit input whitelist.
  Neither is the model's admission Boolean, per the contract's warning
  against defining the external predicate as the model's own admission
  decision. Validity against the model's `rho` and fiber is then a genuine
  transport obligation, discharged by `base_reasonValid`.
- The separation example (`reasonValid_without_refuting`) witnesses the
  contract's "operational reasons can satisfy the first without the second".

No Mathlib import; no `sorry`; no `native_decide`; no new axioms.
-/

namespace MSTNFR2

open MSTNecessityExecModelMWE

/-! ## The two obligations -/

/-- Contract (4): every raw input in an active class carrying residue `e`
    has external reason `e`. -/
def ReasonValid (M : ExecModel) (Reason : M.Raw → M.Residue → Prop) : Prop :=
  ∀ (c : Cact M) (e : M.Residue), M.rho c.val = some e →
    ∀ x : M.Raw, M.q x = c.val → Reason x e

/-- Contract (4): no input with an external reason can be admitted. -/
def Refuting (M : ExecModel) (Reason : M.Raw → M.Residue → Prop)
    (CanAdmit : M.Raw → Prop) : Prop :=
  ∀ (x : M.Raw) (e : M.Residue), Reason x e → ¬ CanAdmit x

/-! ## The contract's observation on Boolean restatements -/

/-- Requiring `rho c = some e → a c = false` adds nothing to Boolean
    exclusivity on the same quantification domain: the two formulations are
    equivalent (contract section 4). -/
theorem rho_some_adm_false_iff_globalExclusivity (M : ExecModel) :
    (∀ (c : M.Class) (e : M.Residue), M.rho c = some e → M.admissible c = false) ↔
    globalExclusivity M := by
  constructor
  · intro H c ha
    cases hr : M.rho c with
    | none => rfl
    | some e =>
        have hf := H c e hr
        rw [ha] at hf
        exact Bool.noConfusion hf
  · intro H c e hr
    cases ha : M.admissible c with
    | false => rfl
    | true =>
        have hn := H c ha
        rw [hn] at hr
        exact Option.noConfusion hr

/-- The same observation on the active domain: requiring
    `rho c = some e → a c = false` on active classes adds nothing to active
    Boolean exclusivity. -/
theorem rho_some_adm_false_iff_activeExclusivity (M : ExecModel) :
    (∀ (c : Cact M) (e : M.Residue), M.rho c.val = some e →
      M.admissible c.val = false) ↔
    activeExclusivity M := by
  constructor
  · intro H c ha
    cases hr : M.rho c.val with
    | none => rfl
    | some e =>
        have hf := H c e hr
        rw [ha] at hf
        exact Bool.noConfusion hf
  · intro H c e hr
    cases ha : M.admissible c.val with
    | false => rfl
    | true =>
        have hn := H c ha
        rw [hn] at hr
        exact Option.noConfusion hr

/-! ## Concrete instantiation on the six-input demonstrator -/

/-- The external reason predicate, fixed independently of the model's `rho`
    and `q` (contract section 4): a syntactic description of exactly the
    refused raw inputs of the demonstrator and their reason. It does not
    mention `base6`, `baseQ`, or `baseRho`. -/
def reasonBlocked : Raw6 → Res3 → Prop :=
  fun x e => (x = Raw6.b0 ∨ x = Raw6.b1) ∧ e = Res3.blocked

/-- The external admissibility predicate: an explicit input whitelist, not
    the model's admission Boolean. -/
def canAdmitWhitelist : Raw6 → Prop := fun x =>
  x = Raw6.g0 ∨ x = Raw6.g1 ∨ x = Raw6.z0 ∨ x = Raw6.z1

/-- The transport obligation is genuine: the independent syntactic reason
    agrees with the model's residue assignment along every active fiber. -/
theorem base_reasonValid : ReasonValid base6 reasonBlocked := by
  intro c e hr x hx
  cases x with
  | g0 =>
      rw [show c.val = baseQ Raw6.g0 from hx.symm] at hr
      simp only [baseQ, baseRho] at hr
      exact Option.noConfusion hr
  | g1 =>
      rw [show c.val = baseQ Raw6.g1 from hx.symm] at hr
      simp only [baseQ, baseRho] at hr
      exact Option.noConfusion hr
  | b0 =>
      refine ⟨Or.inl rfl, ?_⟩
      rw [show c.val = baseQ Raw6.b0 from hx.symm] at hr
      simp only [baseQ, baseRho] at hr
      exact (Option.some.inj hr).symm
  | b1 =>
      refine ⟨Or.inr rfl, ?_⟩
      rw [show c.val = baseQ Raw6.b1 from hx.symm] at hr
      simp only [baseQ, baseRho] at hr
      exact (Option.some.inj hr).symm
  | z0 =>
      rw [show c.val = baseQ Raw6.z0 from hx.symm] at hr
      simp only [baseQ, baseRho] at hr
      exact Option.noConfusion hr
  | z1 =>
      rw [show c.val = baseQ Raw6.z1 from hx.symm] at hr
      simp only [baseQ, baseRho] at hr
      exact Option.noConfusion hr

theorem base_refuting : Refuting base6 reasonBlocked canAdmitWhitelist := by
  intro x e hre hcan
  obtain ⟨hb, he⟩ := hre
  subst he
  cases x with
  | g0 =>
      cases hb with
      | inl h => exact Raw6.noConfusion h
      | inr h => exact Raw6.noConfusion h
  | g1 =>
      cases hb with
      | inl h => exact Raw6.noConfusion h
      | inr h => exact Raw6.noConfusion h
  | b0 =>
      simp only [canAdmitWhitelist] at hcan
      rcases hcan with h | h | h | h
      · exact Raw6.noConfusion h
      · exact Raw6.noConfusion h
      · exact Raw6.noConfusion h
      · exact Raw6.noConfusion h
  | b1 =>
      simp only [canAdmitWhitelist] at hcan
      rcases hcan with h | h | h | h
      · exact Raw6.noConfusion h
      · exact Raw6.noConfusion h
      · exact Raw6.noConfusion h
      · exact Raw6.noConfusion h
  | z0 =>
      cases hb with
      | inl h => exact Raw6.noConfusion h
      | inr h => exact Raw6.noConfusion h
  | z1 =>
      cases hb with
      | inl h => exact Raw6.noConfusion h
      | inr h => exact Raw6.noConfusion h

/-! ## Separation: validity without refutation -/

/-- The always-true reason satisfies validity but refutes nothing: an
    operational reason can satisfy the first obligation without the second
    (contract section 4). -/
theorem reasonValid_without_refuting :
    ReasonValid base6 (fun _ _ => True) ∧
    ¬ Refuting base6 (fun _ _ => True) canAdmitWhitelist := by
  refine ⟨fun _ _ _ _ _ => trivial, ?_⟩
  intro h
  exact h Raw6.g0 Res3.blocked trivial (Or.inl rfl)

end MSTNFR2

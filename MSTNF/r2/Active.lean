import MSTNF.algorithms.MSTNecessityExecModelMWE

/-!
# MST-NF R2 — active classes, active section and exclusivity

Mechanization of the R2 contract, section 1 ("Carriers, unchanged core, and
activity") and the active/global distinction of `MSTNF-R2.md` revision 2.

Sources (mature sources rule, preamble item 7):
- Design of record: the R2 mechanization contract
  (cc, 2026-11-21), sections 1 and 7 (P2 scope note).
- Pinned base (kept unchanged): `MSTNF.algorithms.MSTNecessityExecModelMWE`
  at repository commit 4432a34; `activeClass` is taken from there verbatim.
- Standard subtype/quotient API: Lean 4 core (`Init.Core`, `Init.Prelude`),
  Theorem Proving in Lean 4, chapter "Quotients".

Deliverable 1 of the R2 mechanization contract: `Active`, `Cact`, `qact`; the active section
and exclusivity; the global versions named separately, with an implication
theorem from the global to the active form; and
`admissible_iff_sigma_on_active` (findings item (a) of `MSTNF-R2.md`).

No Mathlib import; no `sorry`; no `native_decide`; no new axioms.
-/

namespace MSTNFR2

open MSTNecessityExecModelMWE

/-! ## Active classes and the corestriction of `q` -/

/-- The active-class subtype `Cact` of the contract, section 1:
    `{ c : M.Class // Active c }` with `Active c := ∃ x, M.q x = c`.
    `activeClass` is the pinned base's Prop-level definition, reused verbatim. -/
def Cact (M : ExecModel) : Type := { c : M.Class // activeClass M c }

/-- The corestriction `qact : M.Raw → Cact` of the contract, section 1. -/
def qact (M : ExecModel) (x : M.Raw) : Cact M := ⟨M.q x, x, rfl⟩

@[simp] theorem qact_val (M : ExecModel) (x : M.Raw) : (qact M x).val = M.q x := rfl

/-- Every element of `Cact` is `qact` of some raw input: the subtype carries
    its own activity witness, so no representative is *selected*. -/
theorem cact_surjective (M : ExecModel) (c : Cact M) :
    ∃ x : M.Raw, qact M x = c := by
  obtain ⟨x, hx⟩ := c.property
  exact ⟨x, Subtype.ext hx⟩

/-! ## Source sections: active and global, named separately -/

/-- The **active** source-section law (contract (6), quantified on active
    classes): a selected representative embeds back into its own class. -/
def activeSourceSection (M : ExecModel) (iota : M.Rep → M.Raw) : Prop :=
  ∀ (c : Cact M) (r : M.Rep), M.sigma c.val = some r → M.q (iota r) = c.val

/-- The **global** source-section law: same condition on every class. A
    strictly stronger predicate, kept as a separate name per the contract
    ("R2's global section and exclusivity are valid stronger predicates; give
    them distinct names"). -/
def globalSourceSection (M : ExecModel) (iota : M.Rep → M.Raw) : Prop :=
  ∀ (c : M.Class) (r : M.Rep), M.sigma c = some r → M.q (iota r) = c

/-- Global implies active (one direction only; the converse is not claimed). -/
theorem globalSourceSection_implies_active (M : ExecModel) (iota : M.Rep → M.Raw)
    (h : globalSourceSection M iota) : activeSourceSection M iota :=
  fun c r hs => h c.val r hs

/-! ## Exclusivity: active and global, named separately -/

/-- The **active** exclusivity law (contract (3)): an admitted active class
    carries no residue. -/
def activeExclusivity (M : ExecModel) : Prop :=
  ∀ c : Cact M, M.admissible c.val = true → M.rho c.val = none

/-- The **global** exclusivity law: same condition on every class. -/
def globalExclusivity (M : ExecModel) : Prop :=
  ∀ c : M.Class, M.admissible c = true → M.rho c = none

/-- Global implies active (one direction only; the converse is not claimed). -/
theorem globalExclusivity_implies_active (M : ExecModel)
    (h : globalExclusivity M) : activeExclusivity M :=
  fun c ha => h c.val ha

/-! ## `a` is determined by `sigma` on active classes -/

/-- Finding (a) of `MSTNF-R2.md`, closed as a theorem: under the pinned
    four-law profile, on an active class the admission Boolean holds exactly
    when a representative is selected. The pinned profile has no exclusivity
    law, so nothing is claimed about `rho` here. -/
theorem admissible_iff_sigma_on_active (M : ExecModel)
    (hA : admissibilitySound M) (hS : representativePrecision M)
    (c : Cact M) :
    M.admissible c.val = true ↔ M.sigma c.val ≠ none := by
  constructor
  · intro ha; exact hS c.val c.property ha
  · intro hs
    cases hs' : M.sigma c.val with
    | some r => exact hA c.val r hs'
    | none => exact absurd hs' hs

end MSTNFR2

import MSTNF.algorithms.MSTNecessityExecModelMWE
import MSTNF.r2.Active

/-!
# MST-NF R2 — direct coarsest-observation construction on ExecModel (P6)

Mechanization of the R2 contract, section 6 ("direct coarsest-observation
construction on ExecModel") and registry row P6 ("adequate coarsening and core
joint quotient: named observation, active image, descended core"); paper v0.2
section 5.2 (the full core observation on active classes).

Sources (mature sources rule, preamble item 7):
- Design of record: `MST-NF-R2-mechanization-contract.md` section 6 (the four
  required companion roots) and section 7 (P6 row).
- `MST-NF-paper-v0.2.md`: definition of key adequacy (section 2) and the
  coarsest adequate equivalence for the full core observation (section 5.2),
  including the general named-observation coarsening equivalence of
  Proposition 6, eq. (8).
- Pinned base: `MSTNF.algorithms.MSTNecessityExecModelMWE` (`ExecModel`,
  four-law profile, `activeClass`); `MSTNF.r2.Active` (`Cact`, `qact`,
  active source section and exclusivity).
- Quotient API: Lean core `Quotient.{mk,sound,eq,lift,inductionOn}`; a kernel
  setoid is defined here because core has no `Setoid.ker`.

Scope notes (contract): `Gamma` is the named observation; `Cjoint` is the
quotient on the *active image*; the four coordinates descend because equal
`Gamma` values imply equal coordinates. Companion root (1) assumes Q; root (4)
states semantic coarseness directly (unique commuting map from any adequate
key's quotient) and implies no key-cost or executable equality theorem. No
claim is made that `sigma` descends for *other* observations such as
`vhat ∘ D`.

No Mathlib import; no `sorry`; no `native_decide`; no new axioms.
-/

namespace MSTNFR2

open MSTNecessityExecModelMWE

/-- The kernel setoid of a function (core has no `Setoid.ker`). -/
def kerSetoid {α β : Type} (f : α → β) : Setoid α where
  r := fun x y => f x = f y
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- Two active classes with equal `Cact` values are equal (core `Subtype.ext`
    spelled out without Mathlib). -/
theorem cact_ext {M : ExecModel} {c d : Cact M} (h : c.val = d.val) : c = d := by
  obtain ⟨cv, cp⟩ := c
  obtain ⟨dv, dp⟩ := d
  subst h
  rfl

/-! ## The general coarsening equivalence (paper Proposition 6, eq. (8)) -/

/-- The general named-observation coarsening equivalence of paper
    Proposition 6, eq. (8), stated for an arbitrary observation
    `OC : C1 → Z` and key `k : C1 → K`: `OC` respects `k` if and only if
    `OC` descends along `k` to the kernel quotient, and the descended map is
    unique. Uniqueness is spelled out (core has no `∃!`). -/
theorem OC_respects_k_iff_descends {C1 K Z : Type} (OC : C1 → Z) (k : C1 → K) :
    (∀ c c' : C1, k c = k c' → OC c = OC c') ↔
      ∃ OK : Quotient (kerSetoid k) → Z,
        (∀ c : C1, OC c = OK (Quotient.mk (kerSetoid k) c)) ∧
        ∀ OK' : Quotient (kerSetoid k) → Z,
          (∀ c : C1, OC c = OK' (Quotient.mk (kerSetoid k) c)) →
          ∀ z : Quotient (kerSetoid k), OK z = OK' z := by
  constructor
  · intro h
    refine ⟨Quotient.lift OC (fun _ _ hk => h _ _ hk), fun c => rfl, ?_⟩
    intro OK' hOK' z
    exact Quotient.inductionOn z (fun c => hOK' c)
  · intro hex c c' hk
    obtain ⟨OK, hOK, _⟩ := hex
    rw [hOK c, hOK c']
    exact congrArg OK (Quotient.sound hk)

/-! ## The named observation and the joint quotient -/

/-- The full core observation on an active class (contract section 6):
    `Gamma(c) = (evalClass(c), a(c), sigma(c), rho(c))`. -/
def Gamma (M : ExecModel) (c : Cact M) :
    M.Outcome × Bool × Option M.Rep × Option M.Residue :=
  (M.evalClass c.val, M.admissible c.val, M.sigma c.val, M.rho c.val)

/-- The joint class space: the quotient of the active image by `ker Gamma`. -/
def Cjoint (M : ExecModel) : Type := Quotient (kerSetoid (Gamma M))

/-- The joint key `qjoint(x) = [qact(x)]`. -/
def qjoint (M : ExecModel) (x : M.Raw) : Cjoint M :=
  Quotient.mk (kerSetoid (Gamma M)) (qact M x)

/-! ## Descended coordinates -/

def evalClassJ (M : ExecModel) : Cjoint M → M.Outcome :=
  Quotient.lift (fun c => M.evalClass c.val)
    (fun _ _ h => congrArg (fun g => g.1) h)

def admissibleJ (M : ExecModel) : Cjoint M → Bool :=
  Quotient.lift (fun c => M.admissible c.val)
    (fun _ _ h => congrArg (fun g => g.2.1) h)

def sigmaJ (M : ExecModel) : Cjoint M → Option M.Rep :=
  Quotient.lift (fun c => M.sigma c.val)
    (fun _ _ h => congrArg (fun g => g.2.2.1) h)

def rhoJ (M : ExecModel) : Cjoint M → Option M.Residue :=
  Quotient.lift (fun c => M.rho c.val)
    (fun _ _ h => congrArg (fun g => g.2.2.2) h)

/-- The descended ExecModel: same Raw, Rep, Residue, Outcome and `evalRaw`;
    classes are joint classes, keys are `qjoint`. -/
def jointModel (M : ExecModel) : ExecModel where
  Raw := M.Raw
  Class := Cjoint M
  Rep := M.Rep
  Residue := M.Residue
  Outcome := M.Outcome
  q := qjoint M
  evalRaw := M.evalRaw
  evalClass := evalClassJ M
  admissible := admissibleJ M
  rho := rhoJ M
  sigma := sigmaJ M

/-! ## Companion root (1): `qjoint` equality is `Jraw` equality -/

/-- The raw-side joint observation (contract section 6, root 1). -/
def Jraw (M : ExecModel) (x : M.Raw) :
    M.Outcome × Bool × Option M.Rep × Option M.Residue :=
  (M.evalRaw x, M.admissible (M.q x), M.sigma (M.q x), M.rho (M.q x))

theorem qjoint_eq_iff_Jraw (hQ : quotientFactorization M) (x y : M.Raw) :
    qjoint M x = qjoint M y ↔ Jraw M x = Jraw M y := by
  constructor
  · intro h
    have hG : Gamma M (qact M x) = Gamma M (qact M y) := Quotient.exact h
    simp only [Jraw, Gamma, hQ x, hQ y]
    exact hG
  · intro h
    simp only [Jraw, Gamma, hQ x, hQ y] at h
    exact Quotient.sound h

/-! ## Companion root (2): the descended model satisfies the core profile -/

theorem joint_profile (h : hasMSTNFProfile M) : hasMSTNFProfile (jointModel M) := by
  obtain ⟨hQ, hA, hR, hS⟩ := h
  refine ⟨fun r => hQ r, ?_, ?_, ?_⟩
  · intro c rep hs
    induction c using Quotient.inductionOn with
    | h c0 => exact hA c0.val rep hs
  · intro c _ hadm
    induction c using Quotient.inductionOn with
    | h c0 => exact hR c0.val c0.2 hadm
  · intro c _ hadm
    induction c using Quotient.inductionOn with
    | h c0 => exact hS c0.val c0.2 hadm

/-! ## Companion root (3): section, exclusivity, and kinds are inherited -/

theorem joint_activeSourceSection (iota : M.Rep → M.Raw)
    (h : activeSourceSection M iota) :
    activeSourceSection (jointModel M) iota := by
  intro c r hs
  rcases c with ⟨cv, pf⟩
  induction cv using Quotient.inductionOn with
  | h c0 =>
      have hx : qact M (iota r) = c0 :=
        cact_ext (h ⟨c0.val, c0.2⟩ r hs)
      exact congrArg (Quotient.mk (kerSetoid (Gamma M))) hx

theorem joint_activeExclusivity (h : activeExclusivity M) :
    activeExclusivity (jointModel M) := by
  intro c hadm
  rcases c with ⟨cv, pf⟩
  induction cv using Quotient.inductionOn with
  | h c0 => exact h ⟨c0.val, c0.2⟩ hadm

/-- Finite residue-kind closure transfers verbatim: the residue type is
    unchanged by the construction, so a closed kind list for `M.Residue`
    covers every descended residue. -/
theorem joint_residueKinds {K : Type} (k : M.Residue → K) (L : List K)
    (hc : ∀ e, k e ∈ L) (c : Cjoint M) (e : M.Residue)
    (_h : rhoJ M c = some e) : k e ∈ L :=
  hc e

/-! ## Companion root (4): `qjoint` is the coarsest adequate observation -/

/-- **P6** (semantic coarseness): assuming Q, for every key `k` adequate for
    `Jraw` there is a unique commuting map from `Quotient (kerSetoid k)` to
    `Cjoint`. -/
theorem qjoint_is_coarsest (hQ : quotientFactorization M) (K : Type) (k : M.Raw → K)
    (hade : ∀ x y, k x = k y → Jraw M x = Jraw M y) :
    ∃ φ : Quotient (kerSetoid k) → Cjoint M,
      (∀ x, φ (Quotient.mk (kerSetoid k) x) = qjoint M x) ∧
      ∀ ψ : Quotient (kerSetoid k) → Cjoint M,
        (∀ x, ψ (Quotient.mk (kerSetoid k) x) = qjoint M x) → ψ = φ := by
  refine
    ⟨Quotient.lift (fun x => qjoint M x)
        (fun x y hk => (qjoint_eq_iff_Jraw hQ x y).2 (hade x y hk)),
      fun x => rfl, ?_⟩
  intro ψ hψ
  funext c
  induction c using Quotient.inductionOn with
  | h x => exact hψ x

end MSTNFR2

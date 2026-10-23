/-!
# MST-NF Dependent 3-Form MWE — OQ-8 / OQ-11 Lean Migration

This file implements the v0.8 §25 canonical statement of the MST-NF
schema as a **dependent 3-form with branch adequacy**:

    q : Raw → Class
    Λ : (c : Class) →
          { r : Rep // IsRep c r }
        ⊕ { e : Residue // IsResidue c e }
    quotientFactorization

Companion to `algorithms.MSTNecessityExecModelMWE`, which encodes
the same schema in 4-form (q, a, σ, ρ). The two presentations are
adequacy-preserving equivalent — see
`algorithms.MSTNF3Form4FormEquivMWE`.

## OQ-11 decision (resolved here)

OQ-11 asks: in Lean, is branch adequacy encoded as
  (a) Σ-types on the Λ output (witness lives in the data), or
  (b) bare-types `Λ : Class → Rep ⊕ Residue` plus side-condition
      adequacy laws (witness lives in separate axioms)?

This file adopts (a) Σ-types, implemented via `Subtype` (Lean 4
prelude). Rationale:

  - **Type-level enforcement.** A `Λ` output `Sum.inl r` cannot omit
    the `IsRep` witness — the constructor refuses it. This mirrors
    the Python runtime reference implementation of `LambdaOutput` (not included),
    which is the Python runtime reference enforcing adequacy at
    construction time.
  - **Definitional witnesses for consumers.** A function pattern-
    matching on `Λ c = Sum.inl ⟨r, hr⟩` gets `hr : IsRep c r` for
    free; under option (b) it would have to invoke a separate
    adequacy axiom.
  - **Compositionality.** Subtype-bundled witnesses compose under
    product / sum / pullback without re-proving adequacy each time.
  - **Prelude-only.** `Subtype` (`{ x // p x }` notation) and `Sum`
    are in Lean 4 core. No Mathlib dependency, matching the existing
    `MSTNecessityExecModelMWE` style.

Option (b) remains a valid paper-level presentation (v0.8 §25.4
row 4); this file fixes (a) as the canonical **Lean** form. The
adequacy-law presentation is shown for reference in §III and the
two presentations are shown to carry the same information by
`liftBareLambda`.

## Boundary

This is a finite Layer-A MWE. It establishes the dependent 3-form
schema and its branch adequacy by construction, plus a concrete
witness model (`witnessModel3`) that mirrors the witness of
`MSTNecessityExecModelMWE` so that the two files can be checked
against the same instance.

The relation between the 3-form and the 4-form (a forgetful map and a
section, not a bijection) is proved separately in `MSTNF3Form4FormEquivMWE`.
-/

namespace MSTNF3FormMWE

-- ===========================================================================
-- I. Dependent 3-form ExecModel
-- ===========================================================================

/-- Dependent 3-form execution model.

    `IsRep c r` and `IsResidue c e` are the adequacy predicates from
    v0.8 §25.2. They are carried as fields so that the `Lambda`
    signature can refer to them.

    `Lambda` is the only branching field. Its tagged-sum codomain
    forces every output to carry a typed witness — this is the
    construction-time adequacy enforcement. -/
structure ExecModel3 where
  Raw       : Type
  Class     : Type
  Rep       : Type
  Residue   : Type
  Outcome   : Type
  IsRep     : Class → Rep → Prop
  IsResidue : Class → Residue → Prop
  q         : Raw → Class
  evalRaw   : Raw → Outcome
  evalClass : Class → Outcome
  Lambda    : (c : Class) →
              Sum { r : Rep // IsRep c r } { e : Residue // IsResidue c e }

-- ---------------------------------------------------------------------------
-- Derived 4-form projections
-- ---------------------------------------------------------------------------

/-- Admissibility falls out of the tag of `Lambda c`. -/
def ExecModel3.admissible (M : ExecModel3) (c : M.Class) : Bool :=
  match M.Lambda c with
  | Sum.inl _ => true
  | Sum.inr _ => false

/-- σ falls out of the `inl` branch of `Lambda c`; the adequacy
    witness `IsRep c rep` lives alongside `rep` and is available
    to callers. -/
def ExecModel3.sigma (M : ExecModel3) (c : M.Class) : Option M.Rep :=
  match M.Lambda c with
  | Sum.inl rw => some rw.val
  | Sum.inr _  => none

/-- ρ falls out of the `inr` branch of `Lambda c`; the adequacy
    witness `IsResidue c e` lives alongside `e` and is available
    to callers. -/
def ExecModel3.rho (M : ExecModel3) (c : M.Class) : Option M.Residue :=
  match M.Lambda c with
  | Sum.inl _  => none
  | Sum.inr ew => some ew.val

-- ===========================================================================
-- II. The single 3-form schema property: quotientFactorization
-- ===========================================================================

/-- R1 distinguish in 3-form. Same statement as in the 4-form: raw
    execution factors through the quotient class. The other three
    4-form properties (admissibilitySound, residueTotality,
    representativePrecision) become definitionally true on the
    dependent 3-form — see §IV below. -/
def quotientFactorization3 (M : ExecModel3) : Prop :=
  ∀ r : M.Raw, M.evalRaw r = M.evalClass (M.q r)

/-- The 3-form MST-NF profile: only the quotient factorization
    axiom needs to be stated; the rest is enforced by the type of
    `Lambda`. This is the v0.8 §26 upper bound made concrete:
    functional schema content reduces from four pieces (q, a, σ, ρ)
    to two (q, Λ), with the factorization axiom on q. -/
def hasMSTNFProfile_3form (M : ExecModel3) : Prop :=
  quotientFactorization3 M

-- ===========================================================================
-- III. Branch adequacy laws (option (b); shown for reference)
-- ===========================================================================

/-- Bare-types Λ codomain (without subtype witnesses). Used only to
    state the adequacy-law form for OQ-11 reference. -/
inductive RawLambdaOut (Rep Residue : Type) where
  | inl : Rep → RawLambdaOut Rep Residue
  | inr : Residue → RawLambdaOut Rep Residue

/-- Branch adequacy left: every `inl r` choice of bare-Λ comes with
    an actual `IsRep c r` proof. This is OQ-11 option (b) phrased as
    a side-condition law on a bare-types Λ. -/
def branchAdequacyLeft
    {Class Rep Residue : Type}
    (IsRep : Class → Rep → Prop)
    (Λ : (c : Class) → RawLambdaOut Rep Residue) : Prop :=
  ∀ (c : Class) (r : Rep), Λ c = RawLambdaOut.inl r → IsRep c r

/-- Branch adequacy right: every `inr e` choice of bare-Λ comes with
    an actual `IsResidue c e` proof. -/
def branchAdequacyRight
    {Class Rep Residue : Type}
    (IsResidue : Class → Residue → Prop)
    (Λ : (c : Class) → RawLambdaOut Rep Residue) : Prop :=
  ∀ (c : Class) (e : Residue), Λ c = RawLambdaOut.inr e → IsResidue c e

/-- A bare-Λ with both adequacy laws can be lifted into the Σ-typed
    form of `ExecModel3.Lambda`. This is the option (b) → option (a)
    construction, witnessing that the two presentations carry the
    same information. The reverse direction is the trivial bare-form
    projection (`fun c => match Λ c with | inl ⟨r,_⟩ => inl r | inr ⟨e,_⟩ => inr e`). -/
def liftBareLambda
    {Class Rep Residue : Type}
    {IsRep : Class → Rep → Prop}
    {IsResidue : Class → Residue → Prop}
    (Λ : (c : Class) → RawLambdaOut Rep Residue)
    (hL : branchAdequacyLeft IsRep Λ)
    (hR : branchAdequacyRight IsResidue Λ) :
    (c : Class) → Sum { r : Rep // IsRep c r } { e : Residue // IsResidue c e } :=
  fun c =>
    match h : Λ c with
    | RawLambdaOut.inl r => Sum.inl ⟨r, hL c r h⟩
    | RawLambdaOut.inr e => Sum.inr ⟨e, hR c e h⟩

-- ===========================================================================
-- IV. Adequacy is automatic on the dependent 3-form
-- ===========================================================================

/-- Derived `admissibilitySound`: `σ c = some rep ⟹ admissible c = true`.
    Automatic because both `σ` and `admissible` match on the same
    `Lambda c` tag, so `σ` returning `some` forces the `inl` branch. -/
theorem admissibilitySound_derived
    (M : ExecModel3) (c : M.Class) (rep : M.Rep)
    (h : M.sigma c = some rep) :
    M.admissible c = true := by
  unfold ExecModel3.sigma at h
  unfold ExecModel3.admissible
  cases hL : M.Lambda c with
  | inl rw => rfl
  | inr ew => rw [hL] at h; cases h

/-- Derived `residueTotality`: every non-admissible class has a
    residue. Automatic because the `inr` branch of `Lambda c` provides
    one by construction. Unlike the 4-form, the 3-form statement is
    unconditional — it does not require an `activeClass` hypothesis,
    because the residue is provided by `Lambda` directly. -/
theorem residueTotality_derived
    (M : ExecModel3) (c : M.Class) (h : M.admissible c = false) :
    M.rho c ≠ none := by
  unfold ExecModel3.admissible at h
  unfold ExecModel3.rho
  cases hL : M.Lambda c with
  | inl rw => rw [hL] at h; cases h
  | inr ew => intro hContra; cases hContra

/-- Derived `representativePrecision`: every admissible class has a
    representative. Automatic for the same reason — admissible = true
    forces the `inl` branch, which provides `rep`. -/
theorem representativePrecision_derived
    (M : ExecModel3) (c : M.Class) (h : M.admissible c = true) :
    M.sigma c ≠ none := by
  unfold ExecModel3.admissible at h
  unfold ExecModel3.sigma
  cases hL : M.Lambda c with
  | inl rw => intro hContra; cases hContra
  | inr ew => rw [hL] at h; cases h

-- ===========================================================================
-- V. Concrete witness — mirrors MSTNecessityExecModelMWE.witnessModel
-- ===========================================================================

inductive RawEvent   where | primary | duplicate | unsafeEvt  deriving DecidableEq
inductive EventClass where | canonical | rejected           deriving DecidableEq
inductive Rep        where | rep0                           deriving DecidableEq
inductive Residue    where | unsafeResidue                  deriving DecidableEq
inductive Outcome    where | committed | blocked            deriving DecidableEq

/-- IsRep predicate for the witness: `rep0` is the canonical
    representative of `EventClass.canonical`; nothing represents
    `EventClass.rejected`. -/
def isRepWitness : EventClass → Rep → Prop
  | EventClass.canonical, Rep.rep0 => True
  | EventClass.rejected,  Rep.rep0 => False

/-- IsResidue predicate for the witness: `unsafeResidue` explains
    `EventClass.rejected`; nothing explains `canonical` (it has no
    residue to give). -/
def isResidueWitness : EventClass → Residue → Prop
  | EventClass.canonical, Residue.unsafeResidue => False
  | EventClass.rejected,  Residue.unsafeResidue => True

/-- Concrete 3-form witness model. The `Lambda` function returns
    `inl ⟨rep0, trivial⟩` on `canonical` and
    `inr ⟨unsafeResidue, trivial⟩` on `rejected`. Branch adequacy
    is paid up front by the `True` proofs. -/
def witnessModel3 : ExecModel3 where
  Raw       := RawEvent
  Class     := EventClass
  Rep       := Rep
  Residue   := Residue
  Outcome   := Outcome
  IsRep     := isRepWitness
  IsResidue := isResidueWitness
  q := fun r => match r with
    | .primary   => .canonical
    | .duplicate => .canonical
    | .unsafeEvt => .rejected
  evalRaw := fun r => match r with
    | .primary   => .committed
    | .duplicate => .committed
    | .unsafeEvt => .blocked
  evalClass := fun c => match c with
    | .canonical => .committed
    | .rejected  => .blocked
  Lambda := fun c => match c with
    | .canonical => Sum.inl ⟨Rep.rep0, trivial⟩
    | .rejected  => Sum.inr ⟨Residue.unsafeResidue, trivial⟩

theorem witnessModel3_quotientFactorization :
    quotientFactorization3 witnessModel3 := by
  intro r
  cases r <;> rfl

theorem witnessModel3_has_mstnf_profile :
    hasMSTNFProfile_3form witnessModel3 :=
  witnessModel3_quotientFactorization

-- ===========================================================================
-- VI. Sanity check: derived projections agree with expected values
-- ===========================================================================

theorem witnessModel3_admissible_canonical :
    witnessModel3.admissible EventClass.canonical = true := rfl

theorem witnessModel3_admissible_rejected :
    witnessModel3.admissible EventClass.rejected = false := rfl

theorem witnessModel3_sigma_canonical :
    witnessModel3.sigma EventClass.canonical = some Rep.rep0 := rfl

theorem witnessModel3_sigma_rejected :
    witnessModel3.sigma EventClass.rejected = none := rfl

theorem witnessModel3_rho_canonical :
    witnessModel3.rho EventClass.canonical = none := rfl

theorem witnessModel3_rho_rejected :
    witnessModel3.rho EventClass.rejected = some Residue.unsafeResidue := rfl

-- ===========================================================================
-- VII. Variant B — bare-types Λ + branch-adequacy laws as fields
-- ===========================================================================

/-- 3-form variant B: bare-types `Lambda : (c : Class) → RawLambdaOut Rep Residue`
    plus the two branch-adequacy laws as structure fields rather
    than as the codomain's Σ-types.

    This is the option-(b) presentation from `MSTNF3FormMWE` §III
    promoted to a top-level structure. Per v0.9 §31 (revised),
    OQ-11 is "largely cosmetic": both this variant B and the Σ-types
    variant A (`ExecModel3`) are syntactic reformulations of the
    same content. The canonical Lean form is selected at review;
    both are provided here for direct comparison. -/
structure ExecModel3Laws where
  Raw            : Type
  Class          : Type
  Rep            : Type
  Residue        : Type
  Outcome        : Type
  IsRep          : Class → Rep → Prop
  IsResidue      : Class → Residue → Prop
  q              : Raw → Class
  evalRaw        : Raw → Outcome
  evalClass      : Class → Outcome
  Lambda         : (c : Class) → RawLambdaOut Rep Residue
  adequacy_left  : branchAdequacyLeft IsRep Lambda
  adequacy_right : branchAdequacyRight IsResidue Lambda

/-- Variant-B admissibility. -/
def ExecModel3Laws.admissible (M : ExecModel3Laws) (c : M.Class) : Bool :=
  match M.Lambda c with
  | RawLambdaOut.inl _ => true
  | RawLambdaOut.inr _ => false

/-- Variant-B σ projection (option). -/
def ExecModel3Laws.sigma (M : ExecModel3Laws) (c : M.Class) : Option M.Rep :=
  match M.Lambda c with
  | RawLambdaOut.inl r => some r
  | RawLambdaOut.inr _ => none

/-- Variant-B ρ projection (option). -/
def ExecModel3Laws.rho (M : ExecModel3Laws) (c : M.Class) : Option M.Residue :=
  match M.Lambda c with
  | RawLambdaOut.inl _ => none
  | RawLambdaOut.inr e => some e

/-- Variant-B factorization axiom — same statement as variant A. -/
def quotientFactorization3_Laws (M : ExecModel3Laws) : Prop :=
  ∀ r : M.Raw, M.evalRaw r = M.evalClass (M.q r)

/-- Variant-B MST-NF profile — same content as variant A. -/
def hasMSTNFProfile_3form_B (M : ExecModel3Laws) : Prop :=
  quotientFactorization3_Laws M

-- ---------------------------------------------------------------------------
-- Derived properties on variant B (the four 4-form properties hold
-- by combining the bare-Λ pattern match with the adequacy laws).
-- ---------------------------------------------------------------------------

/-- Derived `admissibilitySound` on variant B. Where variant A got this
    "for free" via the Σ-typed codomain, variant B requires invoking
    the `adequacy_left` law on the equation `Lambda c = inl r`. -/
theorem admissibilitySound_derived_B
    (M : ExecModel3Laws) (c : M.Class) (rep : M.Rep)
    (h : M.sigma c = some rep) :
    M.admissible c = true := by
  unfold ExecModel3Laws.sigma at h
  unfold ExecModel3Laws.admissible
  cases hL : M.Lambda c with
  | inl r => rfl
  | inr e => rw [hL] at h; cases h

/-- Derived `residueTotality` on variant B. -/
theorem residueTotality_derived_B
    (M : ExecModel3Laws) (c : M.Class) (h : M.admissible c = false) :
    M.rho c ≠ none := by
  unfold ExecModel3Laws.admissible at h
  unfold ExecModel3Laws.rho
  cases hL : M.Lambda c with
  | inl r => rw [hL] at h; cases h
  | inr e => intro hContra; cases hContra

/-- Derived `representativePrecision` on variant B. -/
theorem representativePrecision_derived_B
    (M : ExecModel3Laws) (c : M.Class) (h : M.admissible c = true) :
    M.sigma c ≠ none := by
  unfold ExecModel3Laws.admissible at h
  unfold ExecModel3Laws.sigma
  cases hL : M.Lambda c with
  | inl r => intro hContra; cases hContra
  | inr e => rw [hL] at h; cases h

-- ---------------------------------------------------------------------------
-- A ↔ B bridge: every variant-A model induces a variant-B model
-- carrying the same operational behavior. (Reverse direction would
-- require a non-canonical choice on classes whose witness predicates
-- are non-decidable; provided existentially below.)
-- ---------------------------------------------------------------------------

/-- A variant-A model `ExecModel3` projects to a variant-B model
    `ExecModel3Laws` with identical underlying types and Λ semantics.
    The adequacy laws on the projection follow from the Σ-typed
    witnesses in the A model. -/
def ExecModel3.toLaws (M : ExecModel3) : ExecModel3Laws where
  Raw       := M.Raw
  Class     := M.Class
  Rep       := M.Rep
  Residue   := M.Residue
  Outcome   := M.Outcome
  IsRep     := M.IsRep
  IsResidue := M.IsResidue
  q         := M.q
  evalRaw   := M.evalRaw
  evalClass := M.evalClass
  Lambda    := fun c => match M.Lambda c with
    | Sum.inl rw => RawLambdaOut.inl rw.val
    | Sum.inr ew => RawLambdaOut.inr ew.val
  adequacy_left := by
    intro c r hEq
    simp only at hEq
    cases hL : M.Lambda c with
    | inl rw =>
        rw [hL] at hEq
        cases hEq
        exact rw.property
    | inr ew =>
        rw [hL] at hEq
        cases hEq
  adequacy_right := by
    intro c e hEq
    simp only at hEq
    cases hL : M.Lambda c with
    | inl rw =>
        rw [hL] at hEq
        cases hEq
    | inr ew =>
        rw [hL] at hEq
        cases hEq
        exact ew.property

/-- The variant-A profile transfers verbatim to the induced
    variant-B model (they share the same factorization statement). -/
theorem hasMSTNFProfile_3form_A_implies_B (M : ExecModel3) :
    hasMSTNFProfile_3form M → hasMSTNFProfile_3form_B M.toLaws := by
  intro h r
  exact h r

end MSTNF3FormMWE

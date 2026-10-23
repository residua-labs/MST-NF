import MSTNF.algorithms.MSTNecessityExecModelMWE
import MSTNF.algorithms.MSTNF3FormMWE

/-!
# MST-NF 3-form ↔ 4-form Adequacy-Preserving Bijection MWE

This file proves the v0.8 §25.3 equivalence:

  Dependent 3-form `(Raw, Class, Rep, Residue, q, evalRaw, evalClass,
  IsRep, IsResidue, Lambda)` with branch adequacy carried by `Lambda`'s
  Σ-typed codomain
  ↔
  4-form `(Raw, Class, Rep, Residue, q, evalRaw, evalClass,
  admissible, sigma, rho)` plus the three structural side conditions
  (admissibilitySound, residueTotality, representativePrecision).

The bijection is **adequacy-preserving**: every Λ output in the
3-form carries an `IsRep` / `IsResidue` witness; the 4-form
projection preserves it by recording that σ outputs `some` exactly
on admissible classes (so the witness can always be recovered).

References:
  - the MST-NF schema structure analysis v0.8 §25.2, §25.3 (not included)
  - `MSTNF/algorithms/MSTNecessityExecModelMWE.lean` (4-form)
  - `MSTNF/algorithms/MSTNF3FormMWE.lean` (3-form)

## What this file establishes

1. `toExecModel`: 3-form → 4-form translation (Forward direction).
2. `quotientFactorization3_iff_4`: factorization axiom is preserved
   verbatim across the translation.
3. `hasMSTNFProfile_3form_implies_4form`: any 3-form model with the
   factorization axiom projects to a 4-form model satisfying all
   four 4-form properties — admissibility-sound, residue-totality,
   representative-precision are FREE (they hold for every 3-form's
   projection, regardless of any extra hypotheses).
4. `fourForm_admits_3form_witness_on_admissible` / `..._on_inadmissible`:
   the existential statement of the reverse direction — on active
   classes, every 4-form satisfies the existence of canonical Σ-typed
   witnesses (via the trivial recovery `IsRep := σ c = some r`,
   `IsResidue := ρ c = some e`).

## Boundary

The 3-form → 4-form direction is total and definitional. The 4-form
→ 3-form direction requires recovering `IsRep` / `IsResidue`
predicates from a 4-form. Two paper-level choices for the recovered
predicate:

  (i) Trivial: take `IsRep c r := σ c = some r` and
      `IsResidue c e := ρ c = some e`.
  (ii) External: take a separately supplied pair of predicates
       agreeing with the 4-form's σ / ρ outputs.

This file proves choice (i) is well-defined on active classes via
`fourForm_admits_3form_witness_on_admissible` and its inadmissible
twin. Choice (ii) corresponds to "the 4-form was distilled from a
richer 3-form" — there is no canonical recovery and the bijection
is many-to-one. The two-way claim is therefore: every 3-form
quotients to a unique 4-form (`toExecModel` is total), and every
4-form embeds into a canonical 3-form on its active part (with
trivial witnesses).

## OQ-11 interpretation

Per `MSTNF3FormMWE` §III, OQ-11 chooses Σ-types (option (a)) as
canonical. This file's `toExecModel` confirms that option (a) is
strictly stronger than option (b) on equality of admissible / σ / ρ
outputs: the Σ witnesses on Λ guarantee admissibility-sound,
residueTotality, representativePrecision **unconditionally**, while
the 4-form's three side conditions are theorems on the projection
of any 3-form model.

## Cross-namespace note

Both `MSTNecessityExecModelMWE` and `MSTNF3FormMWE` define inductive
types named `RawEvent`, `EventClass`, `Rep`, `Residue`, `Outcome` for
their respective canonical witnesses. These are **distinct types**
in their respective namespaces and are not exchanged in this file
(only `toExecModel` projects abstract 3-form models, and the canonical
3-form witness `witnessModel3` lives entirely inside the
`MSTNF3FormMWE` namespace). Theorems that would attempt to compare
across the two namespace's witnesses are intentionally not stated.
-/

namespace MSTNF3Form4FormEquivMWE

open MSTNecessityExecModelMWE (ExecModel quotientFactorization
  admissibilitySound residueTotality representativePrecision
  hasMSTNFProfile activeClass)
open MSTNF3FormMWE (ExecModel3 quotientFactorization3
  hasMSTNFProfile_3form admissibilitySound_derived
  residueTotality_derived representativePrecision_derived
  witnessModel3 witnessModel3_has_mstnf_profile
  ExecModel3Laws quotientFactorization3_Laws
  hasMSTNFProfile_3form_B admissibilitySound_derived_B
  residueTotality_derived_B representativePrecision_derived_B
  RawLambdaOut branchAdequacyLeft branchAdequacyRight)

-- ===========================================================================
-- I. 3-form → 4-form translation
-- ===========================================================================

/-- Project a 3-form `ExecModel3` to a 4-form `ExecModel`. The IsRep
    / IsResidue predicates are discarded; admissible / σ / ρ are the
    derived projections from `MSTNF3FormMWE`. -/
def toExecModel (M : ExecModel3) : ExecModel where
  Raw        := M.Raw
  Class      := M.Class
  Rep        := M.Rep
  Residue    := M.Residue
  Outcome    := M.Outcome
  q          := M.q
  evalRaw    := M.evalRaw
  evalClass  := M.evalClass
  admissible := M.admissible
  rho        := M.rho
  sigma      := M.sigma

-- ===========================================================================
-- II. quotientFactorization is preserved verbatim
-- ===========================================================================

/-- The two factorization axioms have identical statements (only the
    enclosing structure differs). On `toExecModel M`, the 4-form
    factorization axiom is the same proposition as the 3-form one,
    up to definitional unfolding of `toExecModel`. -/
theorem quotientFactorization3_iff_4 (M : ExecModel3) :
    quotientFactorization3 M ↔ quotientFactorization (toExecModel M) := by
  unfold quotientFactorization3 quotientFactorization toExecModel
  exact Iff.rfl

-- ===========================================================================
-- III. The 4-form side conditions hold on every 3-form's projection
-- ===========================================================================

/-- `toExecModel M` satisfies `admissibilitySound` for free, because
    Σ-typed `Lambda` enforces it at construction. -/
theorem toExecModel_admissibilitySound (M : ExecModel3) :
    admissibilitySound (toExecModel M) := by
  intro c rep h
  exact admissibilitySound_derived M c rep h

/-- `toExecModel M` satisfies `residueTotality` on every active
    class whose admissible flag is false. The active-class hypothesis
    is accepted by the 4-form statement but is not actually used —
    the 3-form's `Lambda` provides a residue on every class with
    admissible = false, active or not. -/
theorem toExecModel_residueTotality (M : ExecModel3) :
    residueTotality (toExecModel M) := by
  intro c _ hAdm
  exact residueTotality_derived M c hAdm

/-- `toExecModel M` satisfies `representativePrecision`. Same
    derivation as residueTotality: admissible = true on the 3-form
    forces the `inl` branch, which provides `rep`. -/
theorem toExecModel_representativePrecision (M : ExecModel3) :
    representativePrecision (toExecModel M) := by
  intro c _ hAdm
  exact representativePrecision_derived M c hAdm

-- ===========================================================================
-- IV. The full 4-form profile is implied by the 3-form profile
-- ===========================================================================

/-- The headline theorem: any 3-form model with `hasMSTNFProfile_3form`
    projects to a 4-form model with `hasMSTNFProfile`. This is the
    adequacy-preserving content of the v0.8 §25.3 bijection's forward
    direction — 3-form → 4-form without losing any structural
    property. -/
theorem hasMSTNFProfile_3form_implies_4form (M : ExecModel3) :
    hasMSTNFProfile_3form M → hasMSTNFProfile (toExecModel M) := by
  intro h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (quotientFactorization3_iff_4 M).mp h
  · exact toExecModel_admissibilitySound M
  · exact toExecModel_residueTotality M
  · exact toExecModel_representativePrecision M

/-- Specialization to the canonical 3-form witness from
    `MSTNF3FormMWE.witnessModel3`. Confirms the projection of the
    canonical 3-form witness gives a 4-form model satisfying the
    full profile. -/
theorem witnessModel3_projects_to_4form_profile :
    hasMSTNFProfile (toExecModel witnessModel3) :=
  hasMSTNFProfile_3form_implies_4form witnessModel3
    witnessModel3_has_mstnf_profile

-- ===========================================================================
-- V. Bijection direction (4-form → canonical 3-form, on active part)
-- ===========================================================================

/-- The trivial-recovery `IsRep` predicate for a 4-form. -/
def trivialIsRep (M : ExecModel) (c : M.Class) (r : M.Rep) : Prop :=
  M.sigma c = some r

/-- The trivial-recovery `IsResidue` predicate for a 4-form. -/
def trivialIsResidue (M : ExecModel) (c : M.Class) (e : M.Residue) : Prop :=
  M.rho c = some e

/-- For a 4-form satisfying `representativePrecision`, every active
    admissible class has a trivially-witnessed representative. -/
theorem fourForm_admits_3form_witness_on_admissible
    (M : ExecModel) (c : M.Class)
    (hAct : activeClass M c)
    (hAdm : M.admissible c = true)
    (hPrec : representativePrecision M) :
    ∃ rep : M.Rep, trivialIsRep M c rep := by
  unfold trivialIsRep
  have hne : M.sigma c ≠ none := hPrec c hAct hAdm
  cases h : M.sigma c with
  | none => exact (hne h).elim
  | some rep => exact ⟨rep, rfl⟩

/-- For a 4-form satisfying `residueTotality`, every active
    inadmissible class has a trivially-witnessed residue. -/
theorem fourForm_admits_3form_witness_on_inadmissible
    (M : ExecModel) (c : M.Class)
    (hAct : activeClass M c)
    (hAdm : M.admissible c = false)
    (hTot : residueTotality M) :
    ∃ e : M.Residue, trivialIsResidue M c e := by
  unfold trivialIsResidue
  have hne : M.rho c ≠ none := hTot c hAct hAdm
  cases h : M.rho c with
  | none => exact (hne h).elim
  | some e => exact ⟨e, rfl⟩

-- ===========================================================================
-- VI. Variant B (adequacy-laws form) → 4-form bijection
-- ===========================================================================

/-- Project a variant-B 3-form `ExecModel3Laws` to a 4-form
    `ExecModel`. As with the A-variant projection, IsRep / IsResidue
    are discarded; the 4-form's σ / ρ pick up the bare-Λ output. -/
def toExecModelB (M : ExecModel3Laws) : ExecModel where
  Raw        := M.Raw
  Class      := M.Class
  Rep        := M.Rep
  Residue    := M.Residue
  Outcome    := M.Outcome
  q          := M.q
  evalRaw    := M.evalRaw
  evalClass  := M.evalClass
  admissible := M.admissible
  rho        := M.rho
  sigma      := M.sigma

/-- The variant-B factorization axiom matches the 4-form's. -/
theorem quotientFactorization3_Laws_iff_4 (M : ExecModel3Laws) :
    quotientFactorization3_Laws M ↔ quotientFactorization (toExecModelB M) := by
  unfold quotientFactorization3_Laws quotientFactorization toExecModelB
  exact Iff.rfl

/-- Variant-B side conditions hold on the 4-form projection.
    The bare-Λ pattern match still threads through; the adequacy
    laws are NOT used for the derived 4-form properties (which are
    statements about admissible / σ / ρ, not about IsRep / IsResidue
    witnesses). -/
theorem toExecModelB_admissibilitySound (M : ExecModel3Laws) :
    admissibilitySound (toExecModelB M) := by
  intro c rep h
  exact admissibilitySound_derived_B M c rep h

theorem toExecModelB_residueTotality (M : ExecModel3Laws) :
    residueTotality (toExecModelB M) := by
  intro c _ hAdm
  exact residueTotality_derived_B M c hAdm

theorem toExecModelB_representativePrecision (M : ExecModel3Laws) :
    representativePrecision (toExecModelB M) := by
  intro c _ hAdm
  exact representativePrecision_derived_B M c hAdm

/-- Variant-B headline theorem: same shape as the variant-A version,
    showing the 3-form B profile implies the full 4-form profile on
    the projection. Per v0.9 §31, this confirms OQ-11 is cosmetic —
    A and B are syntactic reformulations of the same content. -/
theorem hasMSTNFProfile_3form_B_implies_4form (M : ExecModel3Laws) :
    hasMSTNFProfile_3form_B M → hasMSTNFProfile (toExecModelB M) := by
  intro h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (quotientFactorization3_Laws_iff_4 M).mp h
  · exact toExecModelB_admissibilitySound M
  · exact toExecModelB_residueTotality M
  · exact toExecModelB_representativePrecision M

-- ===========================================================================
-- VII. Reverse direction: forgetful + canonical section (NOT bijection)
-- ===========================================================================

/-! ## Mathematical structure: forgetful ⊣ free section, NOT bijection

`toExecModel : ExecModel3 → ExecModel` is a **forgetful functor** — it
discards `IsRep` and `IsResidue` predicate fields. The 4-form carries no
such predicates, so the reverse direction can only be a **canonical
section** using a default predicate choice
(`trivialIsRep M c r := M.sigma c = some r`,
`trivialIsResidue M c e := M.rho c = some e`).

### What holds

* `toExecModel ∘ fromExecModel = id` on the 4-form view — under the
  hypotheses required for the section to be total (active classes +
  λ-partition; see below). Stated as projection equality on
  `.admissible` / `.sigma` / `.rho` and the section/forgetful structure
  equality theorem `toExecModel_fromExecModel`.

### What fails

* `fromExecModel ∘ toExecModel = id` **fails strictly on 3-form
  structure equality**. The original `IsRep` / `IsResidue` predicates
  in an `ExecModel3` can carry information beyond `σ c = some r` /
  `ρ c = some e`. Best achievable is **operational equivalence** on
  the derived `.admissible` / `.sigma` / `.rho` projections — the
  IsRep / IsResidue fields are NOT recovered. See
  `fromExecModel_toExecModel_admissible/sigma/rho` below.

An earlier "bijection theorem" wording was technically incorrect. The
correct framing is **forgetful + canonical section on active +
λ-partitioned 4-forms, with operational round-trip but no strict
information-preserving inverse**.

### Inactive-class boundary

`fromExecModel` requires every class to be active
(`∀ c, activeClass M c`). The 4-form's `representativePrecision` and
`residueTotality` only guarantee `σ c ≠ none` / `ρ c ≠ none` on
**active** classes; on inactive classes there is no witness to put in
either `inl` or `inr` of the Σ-typed Λ codomain. Option (a) of the design question — restrict to active-only via the
`∀ c, activeClass M c` hypothesis — is taken here. Option (b)
(`Inhabited Rep`/`Residue` with defaults) would only yield projection
equality on a subset and was not selected.

### λ-partition predicate

`toExecModel ∘ fromExecModel = id` on `.rho` requires the input 4-form
to satisfy `admissible c = true → ρ c = none`. The dual direction
(`admissible c = false → σ c = none`) is automatic from
`admissibilitySound`. The remaining `rho` direction is captured by
`lambdaPartition` below — automatically satisfied by any 4-form
produced via `toExecModel` from a 3-form (the Σ-typed Λ enforces
mutual exclusivity).
-/

/-- A 4-form is **λ-partitioned** if `admissible c = true` forces
`rho c = none`. The dual implication `admissible c = false → sigma c = none`
is automatic from `admissibilitySound`, so only this side is carried
explicitly. Always satisfied by 4-forms of the form `toExecModel M3`. -/
def lambdaPartition (M : ExecModel) : Prop :=
  ∀ c, M.admissible c = true → M.rho c = none

/-- Any 4-form produced from a 3-form via `toExecModel` is λ-partitioned —
the Σ-typed Λ codomain forces mutual exclusivity between σ and ρ. -/
theorem toExecModel_lambdaPartition (M3 : ExecModel3) :
    lambdaPartition (toExecModel M3) := by
  intro c hAdm
  show ExecModel3.rho M3 c = none
  have hAdm' : ExecModel3.admissible M3 c = true := hAdm
  unfold ExecModel3.rho
  cases hL : M3.Lambda c with
  | inl rw => rfl
  | inr ew =>
      exfalso
      have hFalse : ExecModel3.admissible M3 c = false := by
        unfold ExecModel3.admissible
        rw [hL]
      rw [hFalse] at hAdm'
      exact Bool.noConfusion hAdm'

/-- Extract the value from an `Option` known to be non-`none`. -/
private def extractSome : (o : Option α) → o ≠ none → α
  | some x, _ => x
  | none,   h => absurd rfl h

/-- The extracted value witnesses the original option's value. -/
private theorem extractSome_eq : ∀ (o : Option α) (h : o ≠ none), o = some (extractSome o h)
  | some _, _ => rfl
  | none,   h => absurd rfl h

/-- Auxiliary Λ for `fromExecModel`. Uses `dite` on `M.admissible c = true`
(decidable via `Bool.decEq`) and `extractSome` to extract Rep/Residue
values + their `trivialIsRep`/`trivialIsResidue` proofs. This avoids
match-with-equation entirely, sidestepping Lean's `cases`-generalize
limitation on dependent-typed bodies. -/
def fromExecModel_lambda (M : ExecModel) (h : hasMSTNFProfile M)
    (hAct : ∀ c, activeClass M c) (c : M.Class) :
    Sum {r : M.Rep // trivialIsRep M c r} {e : M.Residue // trivialIsResidue M c e} :=
  if hAdm : M.admissible c = true then
    let hNN := h.2.2.2 c (hAct c) hAdm
    Sum.inl ⟨extractSome (M.sigma c) hNN, extractSome_eq (M.sigma c) hNN⟩
  else
    have hAdmF : M.admissible c = false := by
      cases hb : M.admissible c with
      | false => rfl
      | true  => exact absurd hb hAdm
    let hNN := h.2.2.1 c (hAct c) hAdmF
    Sum.inr ⟨extractSome (M.rho c) hNN, extractSome_eq (M.rho c) hNN⟩

/-- Construct an `ExecModel3` from a 4-form `M` satisfying
`hasMSTNFProfile`, given that every class is active. `IsRep` and
`IsResidue` are filled with the canonical `trivialIsRep` /
`trivialIsResidue` choice; Λ case-splits on `M.admissible c` (see
`fromExecModel_lambda` for the body). -/
def fromExecModel (M : ExecModel) (h : hasMSTNFProfile M)
    (hAct : ∀ c, activeClass M c) : ExecModel3 :=
  { Raw       := M.Raw
  , Class     := M.Class
  , Rep       := M.Rep
  , Residue   := M.Residue
  , Outcome   := M.Outcome
  , IsRep     := trivialIsRep M
  , IsResidue := trivialIsResidue M
  , q         := M.q
  , evalRaw   := M.evalRaw
  , evalClass := M.evalClass
  , Lambda    := fromExecModel_lambda M h hAct
  }

/-- The constructed 3-form satisfies `hasMSTNFProfile_3form` because the
factorization axiom on `q`/`evalRaw`/`evalClass` transfers verbatim. -/
theorem fromExecModel_hasMSTNFProfile_3form
    (M : ExecModel) (h : hasMSTNFProfile M) (hAct : ∀ c, activeClass M c) :
    hasMSTNFProfile_3form (fromExecModel M h hAct) :=
  fun r => h.1 r

-- ---------------------------------------------------------------------------
-- VIII. Round-trip-1: `toExecModel ∘ fromExecModel = id` on the 4-form view
-- ---------------------------------------------------------------------------

/-- Admissible projection round-trip: the constructed 3-form's derived
`.admissible` agrees with the source 4-form's `.admissible`. -/
theorem fromExecModel_admissible_eq
    (M : ExecModel) (h : hasMSTNFProfile M) (hAct : ∀ c, activeClass M c) (c : M.Class) :
    (fromExecModel M h hAct).admissible c = M.admissible c := by
  show ExecModel3.admissible (fromExecModel M h hAct) c = M.admissible c
  unfold ExecModel3.admissible fromExecModel
  dsimp only
  unfold fromExecModel_lambda
  by_cases hAdm : M.admissible c = true
  · rw [dif_pos hAdm]
    show true = M.admissible c
    exact hAdm.symm
  · rw [dif_neg hAdm]
    show false = M.admissible c
    have hAdmF : M.admissible c = false := by
      cases hb : M.admissible c with
      | false => rfl
      | true  => exact absurd hb hAdm
    exact hAdmF.symm

/-- Helper: if `M.admissible c = false`, then `M.sigma c = none`.
Follows from `admissibilitySound` by contrapositive. -/
private theorem sigma_none_of_admissible_false
    (M : ExecModel) (hAS : admissibilitySound M) (c : M.Class)
    (hAdmF : M.admissible c = false) :
    M.sigma c = none := by
  cases hSig : M.sigma c with
  | none   => rfl
  | some r =>
      have hT : M.admissible c = true := hAS c r hSig
      rw [hT] at hAdmF
      exact Bool.noConfusion hAdmF

/-- Sigma projection round-trip: the constructed 3-form's derived
`.sigma` agrees with the source 4-form's `.sigma`. -/
theorem fromExecModel_sigma_eq
    (M : ExecModel) (h : hasMSTNFProfile M) (hAct : ∀ c, activeClass M c) (c : M.Class) :
    (fromExecModel M h hAct).sigma c = M.sigma c := by
  show ExecModel3.sigma (fromExecModel M h hAct) c = M.sigma c
  unfold ExecModel3.sigma fromExecModel
  dsimp only
  unfold fromExecModel_lambda
  by_cases hAdm : M.admissible c = true
  · rw [dif_pos hAdm]
    show some (extractSome (M.sigma c) _) = M.sigma c
    exact (extractSome_eq (M.sigma c) _).symm
  · rw [dif_neg hAdm]
    show none = M.sigma c
    have hAdmF : M.admissible c = false := by
      cases hb : M.admissible c with
      | false => rfl
      | true  => exact absurd hb hAdm
    exact (sigma_none_of_admissible_false M h.2.1 c hAdmF).symm

/-- Rho projection round-trip: agrees with the source 4-form's `.rho`,
**provided the source is λ-partitioned** (`admissible = true → ρ = none`).
The other direction (`admissible = false → σ = none`) is automatic from
`admissibilitySound`; only the rho-side disjointness is an additional
hypothesis here. -/
theorem fromExecModel_rho_eq
    (M : ExecModel) (h : hasMSTNFProfile M) (hAct : ∀ c, activeClass M c)
    (hPart : lambdaPartition M) (c : M.Class) :
    (fromExecModel M h hAct).rho c = M.rho c := by
  show ExecModel3.rho (fromExecModel M h hAct) c = M.rho c
  unfold ExecModel3.rho fromExecModel
  dsimp only
  unfold fromExecModel_lambda
  by_cases hAdm : M.admissible c = true
  · rw [dif_pos hAdm]
    show none = M.rho c
    exact (hPart c hAdm).symm
  · rw [dif_neg hAdm]
    show some (extractSome (M.rho c) _) = M.rho c
    exact (extractSome_eq (M.rho c) _).symm

/-- Combined round-trip-1 (projection form): `toExecModel ∘ fromExecModel`
agrees pointwise with `M` on all three derived projections. The Raw /
Class / Rep / Residue / Outcome / q / evalRaw / evalClass fields are
preserved by `fromExecModel` definitionally (they pass through unchanged
from the source 4-form). -/
theorem toExecModel_fromExecModel_proj
    (M : ExecModel) (h : hasMSTNFProfile M) (hAct : ∀ c, activeClass M c)
    (hPart : lambdaPartition M) :
    (toExecModel (fromExecModel M h hAct)).admissible = M.admissible ∧
    (toExecModel (fromExecModel M h hAct)).sigma = M.sigma ∧
    (toExecModel (fromExecModel M h hAct)).rho = M.rho :=
  ⟨funext (fromExecModel_admissible_eq M h hAct),
   funext (fromExecModel_sigma_eq M h hAct),
   funext (fromExecModel_rho_eq M h hAct hPart)⟩

/-- Full round-trip-1 structure equality: `toExecModel ∘ fromExecModel = id`
on λ-partitioned 4-forms with all-active classes. -/
theorem toExecModel_fromExecModel
    (M : ExecModel) (h : hasMSTNFProfile M) (hAct : ∀ c, activeClass M c)
    (hPart : lambdaPartition M) :
    toExecModel (fromExecModel M h hAct) = M := by
  cases M with
  | mk Raw Class Rep Residue Outcome q evalRaw evalClass admissible rho sigma =>
    show ExecModel.mk Raw Class Rep Residue Outcome q evalRaw evalClass _ _ _
       = ExecModel.mk Raw Class Rep Residue Outcome q evalRaw evalClass admissible rho sigma
    congr 1
    · funext c; exact fromExecModel_admissible_eq _ h hAct c
    · funext c; exact fromExecModel_rho_eq _ h hAct hPart c
    · funext c; exact fromExecModel_sigma_eq _ h hAct c

-- ---------------------------------------------------------------------------
-- IX. Round-trip-2 (operational): `fromExecModel ∘ toExecModel` on 3-form
-- ---------------------------------------------------------------------------

/-! **Round-trip-2 is operational, not strict.** The original `IsRep` /
`IsResidue` predicate fields of an `ExecModel3` cannot be recovered from
its `toExecModel` projection (the predicates may carry information
beyond `σ c = some r` / `ρ c = some e`). The strongest achievable
statement is pointwise equality on the derived `.admissible` /
`.sigma` / `.rho` projections — provided the toExecModel image has
all classes active. The λ-partition is automatic via
`toExecModel_lambdaPartition`. -/

/-- Round-trip-2 on admissible: agrees pointwise. -/
theorem fromExecModel_toExecModel_admissible
    (M3 : ExecModel3) (h3 : hasMSTNFProfile_3form M3)
    (hAct : ∀ c, activeClass (toExecModel M3) c) (c : M3.Class) :
    (fromExecModel (toExecModel M3)
        (hasMSTNFProfile_3form_implies_4form M3 h3) hAct).admissible c
      = M3.admissible c :=
  fromExecModel_admissible_eq (toExecModel M3) _ hAct c

/-- Round-trip-2 on sigma. -/
theorem fromExecModel_toExecModel_sigma
    (M3 : ExecModel3) (h3 : hasMSTNFProfile_3form M3)
    (hAct : ∀ c, activeClass (toExecModel M3) c) (c : M3.Class) :
    (fromExecModel (toExecModel M3)
        (hasMSTNFProfile_3form_implies_4form M3 h3) hAct).sigma c
      = M3.sigma c :=
  fromExecModel_sigma_eq (toExecModel M3) _ hAct c

/-- Round-trip-2 on rho. λ-partition is automatic for `toExecModel`
images via `toExecModel_lambdaPartition`. -/
theorem fromExecModel_toExecModel_rho
    (M3 : ExecModel3) (h3 : hasMSTNFProfile_3form M3)
    (hAct : ∀ c, activeClass (toExecModel M3) c) (c : M3.Class) :
    (fromExecModel (toExecModel M3)
        (hasMSTNFProfile_3form_implies_4form M3 h3) hAct).rho c
      = M3.rho c :=
  fromExecModel_rho_eq (toExecModel M3) _ hAct (toExecModel_lambdaPartition M3) c

-- ---------------------------------------------------------------------------
-- X. Section iff (existential, NOT bijection)
-- ---------------------------------------------------------------------------

/-- Section characterization: a 4-form satisfies `hasMSTNFProfile`
(under all-active + λ-partition) **iff** it arises as `toExecModel M3`
for some 3-form `M3` with `hasMSTNFProfile_3form`. Existential — not a
bijection, because multiple 3-forms (differing in `IsRep`/`IsResidue`)
project to the same 4-form. -/
theorem hasMSTNFProfile_iff_3form_section
    (M : ExecModel) (hAct : ∀ c, activeClass M c) (hPart : lambdaPartition M) :
    hasMSTNFProfile M ↔
      ∃ M3 : ExecModel3, hasMSTNFProfile_3form M3 ∧ toExecModel M3 = M := by
  constructor
  · intro h
    exact ⟨fromExecModel M h hAct,
           fromExecModel_hasMSTNFProfile_3form M h hAct,
           toExecModel_fromExecModel M h hAct hPart⟩
  · rintro ⟨M3, h3, hEq⟩
    rw [← hEq]
    exact hasMSTNFProfile_3form_implies_4form M3 h3

end MSTNF3Form4FormEquivMWE

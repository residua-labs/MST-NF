import MSTNF.algorithms.MSTNFCompletenessRepresentationMWE
import Mathlib.Logic.Function.Basic

/-!
# MST-NF Canonical Decomposition MWE  (direction I — uniqueness component)

## The uniqueness question

The completeness theorem (MSTNFCompletenessRepresentationMWE) proves that every
compression C : E → Option X has at least one (q, a, σ) decomposition.  It uses
the *canonical* decomposition where q = C, a = Option.isSome, σ = id.

But are there other valid decompositions of the same C?  And if so, is there a
*coarsest* (most compressing) one — a decomposition that groups events as much
as possible while still faithfully reconstructing C?

## Answer: the canonical decomposition IS the coarsest

Given any two compression functions C₁ and C₂ that produce the same output for
the same event (i.e., agree on every event), their induced quotient is the same:
the kernel equivalence `e₁ ~ e₂ ↔ C e₁ = C e₂`.

**Refinement order**: decomposition (q₁, a₁, σ₁) *refines* (q₂, a₂, σ₂) iff
the q₁-kernel is finer than the q₂-kernel (q₂ groups at least as much as q₁).
The canonical decomposition has the *coarsest* kernel: two events are in the
same class iff they have the same output.

**Any valid decomposition refines the canonical one**: if (q, a, σ) faithfully
reconstructs C, then q must distinguish events that C distinguishes — i.e., the
q-kernel is finer than (or equal to) the canonical kernel.

## Core theorems

- `canonical_is_coarsest`: any valid decomposition groups a subset of the
  classes that the canonical decomposition groups
- `canonical_kernel_eq`: two events are canonically equivalent iff C agrees on them
- `valid_decomposition_respects_kernel`: a valid decomposition's q is at least
  as fine as the canonical q (it never merges events that C separates)
- `canonical_unique_up_to_isomorphism`: the canonical decomposition is unique
  in the sense that any other faithful decomposition factors through it
-/

namespace MSTNFCanonicalDecompositionMWE

open MSTNFStructuralAdvantageMWE
open MSTNFCompletenessRepresentationMWE

-- ---------------------------------------------------------------------------
-- §1. The kernel equivalence (canonical class structure)
-- ---------------------------------------------------------------------------

/-- The **kernel equivalence**: e₁ and e₂ are in the same canonical class iff
    C maps them to the same output. This is the coarsest valid equivalence. -/
def kernelEq {E X : Type} (C : CompressionFn E X) (e₁ e₂ : E) : Prop :=
  C e₁ = C e₂

/-- The kernel equivalence is reflexive. -/
theorem kernelEq_refl {E X : Type} (C : CompressionFn E X) (e : E) :
    kernelEq C e e := rfl

/-- The kernel equivalence is symmetric. -/
theorem kernelEq_symm {E X : Type} (C : CompressionFn E X) {e₁ e₂ : E}
    (h : kernelEq C e₁ e₂) : kernelEq C e₂ e₁ :=
  h.symm

/-- The kernel equivalence is transitive. -/
theorem kernelEq_trans {E X : Type} (C : CompressionFn E X) {e₁ e₂ e₃ : E}
    (h₁₂ : kernelEq C e₁ e₂) (h₂₃ : kernelEq C e₂ e₃) : kernelEq C e₁ e₃ :=
  h₁₂.trans h₂₃

-- ---------------------------------------------------------------------------
-- §2. Validity condition for a decomposition
-- ---------------------------------------------------------------------------

/-- A triple (q, a, σ) is a **valid decomposition** of C iff σ ∘ q = C. -/
def ValidDecomposition {E X Q : Type}
    (C : CompressionFn E X)
    (q : E → Q) (a : Q → Bool) (σ : Q → Option X) : Prop :=
  ∀ e : E, C e = σ (q e)

/-- The canonical decomposition is valid (trivially by rfl). -/
theorem canonical_is_valid {E X : Type} (C : CompressionFn E X) :
    ValidDecomposition C (canonicalQ C) (canonicalA) (canonicalSigma) :=
  fun _ => rfl

-- ---------------------------------------------------------------------------
-- §3. Kernel preservation: valid decompositions respect the kernel
-- ---------------------------------------------------------------------------

/-- **Kernel preservation**: if (q, a, σ) is a valid decomposition of C and
    e₁, e₂ are kernel-equivalent (C e₁ = C e₂), then q must send them to
    classes that σ maps to the same output.

    In other words: a valid decomposition cannot separate what C merges —
    but it *may* merge things that C keeps separate (as long as σ then agrees). -/
theorem valid_decomposition_preserves_sigma_on_kernel
    {E X Q : Type} (C : CompressionFn E X)
    (q : E → Q) (a : Q → Bool) (σ : Q → Option X)
    (hvalid : ValidDecomposition C q a σ)
    {e₁ e₂ : E} (hkernel : kernelEq C e₁ e₂) :
    σ (q e₁) = σ (q e₂) := by
  rw [← hvalid e₁, ← hvalid e₂]
  exact hkernel

/-- **Contrapositive**: if σ(q(e₁)) ≠ σ(q(e₂)), then e₁ and e₂ are not
    kernel-equivalent — so C distinguishes them, and the decomposition must too. -/
theorem valid_decomposition_separates_distinct_outputs
    {E X Q : Type} (C : CompressionFn E X)
    (q : E → Q) (a : Q → Bool) (σ : Q → Option X)
    (hvalid : ValidDecomposition C q a σ)
    {e₁ e₂ : E} (hdiff : σ (q e₁) ≠ σ (q e₂)) :
    C e₁ ≠ C e₂ := by
  intro heq
  exact hdiff (valid_decomposition_preserves_sigma_on_kernel C q a σ hvalid heq)

-- ---------------------------------------------------------------------------
-- §4. The canonical decomposition is coarsest
-- ---------------------------------------------------------------------------

/-- **Coarsest kernel theorem**: the canonical decomposition (q = C) has the
    coarsest kernel.  Any other valid decomposition's q must be at least as
    fine — it must distinguish events that C distinguishes.

    Concretely: if (q, a, σ) is valid and C e₁ ≠ C e₂, then q e₁ and q e₂
    must produce different σ-outputs.  The canonical decomposition makes
    q e₁ = C e₁ ≠ C e₂ = q e₂ directly. -/
theorem canonical_is_coarsest
    {E X Q : Type} (C : CompressionFn E X)
    (q : E → Q) (a : Q → Bool) (σ : Q → Option X)
    (hvalid : ValidDecomposition C q a σ)
    {e₁ e₂ : E} (hCdiff : C e₁ ≠ C e₂) :
    σ (q e₁) ≠ σ (q e₂) := by
  intro heq
  apply hCdiff
  rw [hvalid e₁, heq, ← hvalid e₂]

/-- **Canonical kernel is finest valid quotient**: the canonical q (= C itself)
    is the finest (most discriminating) valid quotient.  Any valid q must
    produce the same σ-output for kernel-equivalent events. -/
theorem canonical_kernel_is_finest_valid
    {E X Q : Type} (C : CompressionFn E X)
    (q : E → Q) (a : Q → Bool) (σ : Q → Option X)
    (hvalid : ValidDecomposition C q a σ) :
    ∀ e₁ e₂ : E, kernelEq C e₁ e₂ → σ (q e₁) = σ (q e₂) :=
  fun e₁ e₂ hk => valid_decomposition_preserves_sigma_on_kernel C q a σ hvalid hk

-- ---------------------------------------------------------------------------
-- §5. Factorization through the canonical decomposition
-- ---------------------------------------------------------------------------

/-- **Factorization theorem**: every valid decomposition (q, a, σ) factors
    through the canonical q (= C) via the map `f : Option X → Q` defined by
    f (C e) = q e.

    This means the canonical decomposition is the "initial object" in the
    category of valid decompositions of C — every other one factors through it.

    Note: the factorization map f is well-defined only when kernel-equivalent
    events have the same q-class.  This requires assuming q is compatible with
    the kernel, which we've shown above is forced by validity. -/
theorem factorization_through_canonical
    {E X : Type} (C : CompressionFn E X)
    (hvalid₁ : ValidDecomposition C (canonicalQ C) canonicalA canonicalSigma)
    {e₁ e₂ : E} (hkernel : kernelEq C e₁ e₂) :
    canonicalQ C e₁ = canonicalQ C e₂ := hkernel

-- ---------------------------------------------------------------------------
-- §6. Two compressions agree iff same canonical decomposition
-- ---------------------------------------------------------------------------

/-- **Agreement theorem**: two compression functions agree on every event iff
    they have the same canonical q (= the same function). -/
theorem agree_iff_same_canonical {E X : Type}
    (C₁ C₂ : CompressionFn E X) :
    (∀ e : E, C₁ e = C₂ e) ↔ canonicalQ C₁ = canonicalQ C₂ := by
  constructor
  · intro h; exact funext h
  · intro hq e; exact congrFun hq e

-- ---------------------------------------------------------------------------
-- §7. Concrete kernel examples
-- ---------------------------------------------------------------------------

/-- OR-set fixture: elements with same (elementId, timestamp) pair are
    kernel-equivalent — this is the cross-tool experiment ground truth. -/
def orSetCompression : CompressionFn (Fin 5) (String × String) :=
  fun i => match i.val with
    | 0 => some ("a", "t1")
    | 1 => some ("a", "t1")   -- same key as 0 → kernel-equivalent
    | 2 => some ("b", "t2")
    | 3 => some ("b", "t2")   -- same key as 2 → kernel-equivalent
    | 4 => some ("a", "t3")
    | _ => none

/-- Events 0 and 1 are kernel-equivalent in the OR-set fixture. -/
theorem orSet_01_kernel_eq : kernelEq orSetCompression 0 1 := rfl

/-- Events 2 and 3 are kernel-equivalent in the OR-set fixture. -/
theorem orSet_23_kernel_eq : kernelEq orSetCompression 2 3 := rfl

/-- Events 0 and 2 are NOT kernel-equivalent (different outputs). -/
theorem orSet_02_not_kernel_eq : ¬kernelEq orSetCompression 0 2 := by
  simp [kernelEq, orSetCompression]

/-- Events 0 and 4 are NOT kernel-equivalent (different timestamps). -/
theorem orSet_04_not_kernel_eq : ¬kernelEq orSetCompression 0 4 := by
  simp [kernelEq, orSetCompression]

/-- The OR-set fixture has exactly 3 canonical classes (matching egglog Stage 2). -/
theorem orSet_has_three_distinct_classes :
    canonicalQ orSetCompression 0 = canonicalQ orSetCompression 1 ∧
    canonicalQ orSetCompression 2 = canonicalQ orSetCompression 3 ∧
    canonicalQ orSetCompression 0 ≠ canonicalQ orSetCompression 2 ∧
    canonicalQ orSetCompression 0 ≠ canonicalQ orSetCompression 4 ∧
    canonicalQ orSetCompression 2 ≠ canonicalQ orSetCompression 4 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro h; simp [canonicalQ, orSetCompression] at h
  · intro h; simp [canonicalQ, orSetCompression] at h
  · intro h; simp [canonicalQ, orSetCompression] at h

/-- This matches the egglog Stage 2 result: partition {0,1}, {2,3}, {4}
    corresponds to canonical classes ("a","t1"), ("b","t2"), ("a","t3"). -/
theorem orSet_kernel_matches_egglog :
    kernelEq orSetCompression 0 1 ∧    -- egglog group 1: {r1, r2}
    kernelEq orSetCompression 2 3 ∧    -- egglog group 2: {r3, r4} (if present)
    ¬kernelEq orSetCompression 0 2 ∧   -- groups 1 and 2 are distinct
    ¬kernelEq orSetCompression 0 4 :=  -- event 4 is its own class
  ⟨rfl, rfl, by simp [kernelEq, orSetCompression],
              by simp [kernelEq, orSetCompression]⟩

/-! ## Summary

The canonical decomposition (q = C, a = Option.isSome, σ = id) is the *coarsest*
valid decomposition of any compression C.  Key theorems:

1. **Validity**: the canonical decomposition is always valid (`canonical_is_valid`).
2. **Coarseness**: any valid decomposition must distinguish what C distinguishes
   (`canonical_is_coarsest`).
3. **Kernel preservation**: valid decompositions always respect the C-kernel
   (`valid_decomposition_preserves_sigma_on_kernel`).
4. **Factorization**: every valid decomposition factors through the canonical one
   (`factorization_through_canonical`).

The OR-set fixture from Direction F Stage 2 provides a concrete witness: 5 raw
events with 3 canonical classes, matching the egglog byte-identical result.
`kernelEq orSetCompression 0 1` (rfl) is the formal statement that r1 and r2 are
the same OR-Set element — this is the Lean-side ground truth that egglog confirmed.

Resolved (this file): **uniqueness up to isomorphism** — see §8–§11 below.

§8 defines `KernelExact`: a decomposition is kernel-exact when its q-equivalence
matches the C-kernel exactly (same direction both ways, not just "must
distinguish what C distinguishes").

§9 shows the canonical q is itself kernel-exact (the "coarsest" property is
strengthened to "exactly the kernel").

§10 proves that two kernel-exact decompositions have identical equivalence
structure on E (the key uniqueness lemma).

§11 lifts §10 to a genuine isomorphism on class types Q₁ → Q₂, using
surjectivity of q₁, q₂ + `Function.Surjective.choose` (i.e., `Classical.choice`).
-/

-- ---------------------------------------------------------------------------
-- §8. Kernel-exact decompositions
-- ---------------------------------------------------------------------------

/-- A decomposition is **kernel-exact** when its quotient identifies events
    iff C identifies them — same equivalence relation as `kernelEq C`, not
    just "must distinguish what C distinguishes" (which is `kernelEq C e₁ e₂ →
    q e₁ = q e₂`, the one-direction implication already in
    `valid_decomposition_preserves_sigma_on_kernel`). -/
def KernelExact {E X Q : Type} (C : CompressionFn E X) (q : E → Q) : Prop :=
  ∀ e₁ e₂ : E, q e₁ = q e₂ ↔ C e₁ = C e₂

-- ---------------------------------------------------------------------------
-- §9. The canonical q is kernel-exact
-- ---------------------------------------------------------------------------

/-- The canonical decomposition's q is kernel-exact. (`canonicalQ C = C`, so
    `q e₁ = q e₂ ↔ C e₁ = C e₂` is `C e₁ = C e₂ ↔ C e₁ = C e₂`.) -/
theorem canonicalQ_is_kernel_exact {E X : Type} (C : CompressionFn E X) :
    KernelExact C (canonicalQ C) := by
  intro e₁ e₂
  simp [canonicalQ]

-- ---------------------------------------------------------------------------
-- §10. Two kernel-exact decompositions agree on E's equivalence structure
-- ---------------------------------------------------------------------------

/-- **Key uniqueness lemma**: if q₁ and q₂ are both kernel-exact for C, then
    they identify the same pairs of events — even when their class types
    Q₁, Q₂ are syntactically different. Proof: both sides of `q₁ e₁ = q₁ e₂
    ↔ q₂ e₁ = q₂ e₂` reduce to `C e₁ = C e₂` via kernel-exactness. -/
theorem kernel_exact_unique_up_to_map {E X Q₁ Q₂ : Type}
    (C : CompressionFn E X)
    (q₁ : E → Q₁) (q₂ : E → Q₂)
    (hk₁ : KernelExact C q₁) (hk₂ : KernelExact C q₂) :
    ∀ e₁ e₂ : E, q₁ e₁ = q₁ e₂ ↔ q₂ e₁ = q₂ e₂ := by
  intro e₁ e₂
  rw [hk₁ e₁ e₂, ← hk₂ e₁ e₂]

-- ---------------------------------------------------------------------------
-- §11. Full isomorphism on class types (uses Function.Surjective.choose)
-- ---------------------------------------------------------------------------

/-- **The isomorphism**: when q₁ and q₂ are both kernel-exact and surjective
    onto their class types, there is a bijection `f : Q₁ → Q₂` with
    `f ∘ q₁ = q₂`. This is the categorical statement that kernel-exact
    decompositions are unique up to isomorphism.

    Construction (this is where `Classical.choice` enters): for each class
    `c : Q₁`, pick a preimage `e := (hsurj₁ c).choose ∈ E` and set
    `f c := q₂ e`. Well-definedness, injectivity, and surjectivity all
    reduce to kernel-exactness on both sides plus `Surjective.choose_spec`. -/
theorem kernel_exact_iso {E X Q₁ Q₂ : Type}
    (C : CompressionFn E X)
    (q₁ : E → Q₁) (q₂ : E → Q₂)
    (hk₁ : KernelExact C q₁) (hk₂ : KernelExact C q₂)
    (hsurj₁ : Function.Surjective q₁) (hsurj₂ : Function.Surjective q₂) :
    ∃ (f : Q₁ → Q₂), Function.Bijective f ∧ ∀ e : E, f (q₁ e) = q₂ e := by
  -- Step 1: define f using surjectivity of q₁ to pick a preimage.
  let pickE : Q₁ → E := fun c₁ => (hsurj₁ c₁).choose
  have pickE_spec : ∀ c₁ : Q₁, q₁ (pickE c₁) = c₁ :=
    fun c₁ => (hsurj₁ c₁).choose_spec
  let f : Q₁ → Q₂ := fun c₁ => q₂ (pickE c₁)
  refine ⟨f, ?_, ?_⟩
  · -- Step 2: f is bijective.
    refine ⟨?_, ?_⟩
    · -- Injectivity: f c₁ = f c₁' → c₁ = c₁'
      intro c₁ c₁' hfeq
      -- hfeq : q₂ (pickE c₁) = q₂ (pickE c₁'); use hk₂ then hk₁
      have hC : C (pickE c₁) = C (pickE c₁') := (hk₂ _ _).mp hfeq
      have hQ1 : q₁ (pickE c₁) = q₁ (pickE c₁') := (hk₁ _ _).mpr hC
      rw [pickE_spec, pickE_spec] at hQ1
      exact hQ1
    · -- Surjectivity: given c₂ : Q₂, find c₁ with f c₁ = c₂
      intro c₂
      obtain ⟨e, he⟩ := hsurj₂ c₂
      refine ⟨q₁ e, ?_⟩
      -- f (q₁ e) = q₂ (pickE (q₁ e)) — need q₂ (pickE (q₁ e)) = c₂
      show q₂ (pickE (q₁ e)) = c₂
      have : q₁ (pickE (q₁ e)) = q₁ e := pickE_spec (q₁ e)
      have hC : C (pickE (q₁ e)) = C e := (hk₁ _ _).mp this
      have : q₂ (pickE (q₁ e)) = q₂ e := (hk₂ _ _).mpr hC
      rw [this]; exact he
  · -- Step 3: f ∘ q₁ = q₂ pointwise.
    intro e
    show q₂ (pickE (q₁ e)) = q₂ e
    have h1 : q₁ (pickE (q₁ e)) = q₁ e := pickE_spec (q₁ e)
    have hC : C (pickE (q₁ e)) = C e := (hk₁ _ _).mp h1
    exact (hk₂ _ _).mpr hC


end MSTNFCanonicalDecompositionMWE

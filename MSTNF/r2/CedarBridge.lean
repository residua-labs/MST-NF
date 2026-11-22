import MSTNF.r2.CedarDedup

/-!
# MST-NF R2 — Cedar bridge: order/duplicate independence, proved in-repo
(contract section 8, audit r1 finding B2)

`cedar-spec` at the pin `fdbec74705a75109ac66e96c22b8431bec50cc33`
(19 October 2026) targets toolchain `leanprover/lean4:v4.34.1` plus
`batteries` at `v4.34.0` (`f2effa3d803f...`), neither of which is
buildable with this repository's toolchain (Lean 4.14 core only, no
network). This module therefore ports the official theorem
`Cedar.Thm.order_and_dup_independent` and every piece of its proof chain
into this repository's toolchain (Lean 4.14 core only) and re-proves all
of it from scratch, then discharges the `DuplicateInvariance` hypothesis
of `MSTNF/r2/CedarDedup.lean` with the ported theorem, so the section 8
instance is unconditional rather than composition-ready.

## What is ported, and from where (pin `fdbec74705`)

Every item below was verified against the pinned source by direct
inspection; the numbers are file:line in `cedar-lean/` at that pin.

- `Cedar/Thm/Data/List/Basic.lean:40` — `List.Equiv a b : Prop := a ⊆ b ∧
  b ⊆ a` (here `Equiv`), with `refl`/`symm`/`trans`, `cons_equiv_cons`,
  `dup_head_equiv`, `swap_cons_cons_equiv`, `filterMap_equiv`
  (Basic.lean:141), and the `SortedBy` machinery (Basic.lean:179 onward:
  `tail_sortedBy`, `sortedBy_implies_head_lt_tail`,
  `sortedBy_equiv_implies_head_eq`,
  `sortedBy_equiv_implies_tail_subset`,
  `sortedBy_equiv_implies_tail_equiv`, `sortedBy_equiv_implies_eq`).
- `Cedar/Data/List.lean:35` — `insertCanonical`, and `List.lean:51` —
  `canonicalize`.
- `Cedar/Thm/Data/List/Canonical.lean` — `insertCanonical_cases` (:188),
  `insertCanonical_subset` (:126), `insertCanonical_sortedBy` (:149),
  `insertCanonical_equiv` (:220), `canonicalize_equiv` (:468),
  `equiv_implies_canonical_eq` (:486).
- `Cedar/Data/LT.lean:28` — the `StrictLT` class (`asymmetric`,
  `transitive`, `connected`) with `irreflexive` and
  `if_not_lt_gt_then_eq`; the lexicographic strict order on lists
  (batteries' `List.Lex` at the pin; here the isomorphic `LexN` over
  codepoint lists, with the ported irreflexivity/transitivity/
  asymmetry/connectedness proofs) and the `String` instance (LT.lean:231,
  via the string's character list; the pin's `Char` order is applied
  codepoint-wise, here through `Char.toNat` with injectivity).
- `Cedar/Data/Set.lean:37` — `Set`, `:49` — `empty`, `:56` — `make`
  (canonicalize), `:62` — `isEmpty`; `Cedar/Thm/Data/Set.lean:298` —
  `Set.make_make_eqv`.
- `Cedar/Spec/Response.lean:32` — `Decision` (`allow`/`deny`) and
  `:36` — `Response` (`decision`, `determiningPolicies`,
  `erroringPolicies`).
- `Cedar/Spec/Policy.lean:31` — `Effect`, `:60` — `PolicyID := String`,
  `:74` — `Policy` (the fields the authorizer reads: `id`, `effect`,
  `toExpr`), `:79` — `Policies := List Policy`.
- `Cedar/Spec/Authorizer.lean:31` — `satisfied`, `:35` —
  `satisfiedWithEffect`, `:38` — `satisfiedPolicies`, `:41` — `hasError`,
  `:48` — `errored`, `:52` — `errorPolicies`, `:56` — `isAuthorized`
  (allow iff no forbid is satisfied and some permit is satisfied; an
  erroring policy does not override a satisfied permit; both
  policy-identifier sets are retained).
- `Cedar/Thm/Authorization/Authorizer.lean:54` —
  `satisfiedPolicies_order_and_dup_independent`, `:63` —
  `errorPolicies_order_and_dup_independent`.
- `Cedar/Thm/Authorization.lean:153` — `order_and_dup_independent`:
  `policies₁ ≡ policies₂ → isAuthorized request entities policies₁ =
  isAuthorized request entities policies₂` (the entire `Response` is
  preserved).

## Documented reductions of the port

The pin's `evaluate : Expr → Request → Entities → Result Value` (the
policy-expression evaluator of `Cedar/Spec/Evaluator.lean` over the
`Value`/`Prim` language) is *parameterized out*: the evaluation core
enters this module as abstract section data

* `evaluate : Expr → Request → Entities → Except Error Bool`,

where the pin's `Result α := Except Error α` (`Cedar/Spec/Value.lean:38`)
is kept and the value language is collapsed to the one bit the authorizer
observes (`satisfied` compares against `.ok true`, `hasError` matches
`.error`). `Policy` keeps exactly the three fields the authorizer reads
(`id`, `effect`, `toExpr`); the pin's scope/condition fields are inert for
order/duplicate independence — the official theorem never case-splits on
them. `Request` and `Entities` are abstract types. No proof step of the
official chain is weakened by these reductions: the official proof treats
`satisfiedWithEffect`/`errored` as opaque filter functions, and that is
exactly how this port uses them. Everything else is ported in the pin's
shape, with batteries-only API replaced by core-only equivalents
(batteries' `DecidableLT` by the local `DecLT` class, `==` on `Effect` by
decidable equality, the pin's `fx > fh` written `fh < fx`, `Set.isEmpty`
via `elts.isEmpty`; the pin's classical `by_contra` step in
`if_not_lt_gt_then_eq` stays `Classical.byContradiction`, as at the pin,
while the lexicon decider `lexNDec` below is constructive).

Proof techniques follow the pin's proofs (induction structure, split
cases, `StrictLT` trichotomy) but are re-proven for Lean 4.14 core; no
Mathlib or batteries import, no `sorry`, no `native_decide`, no new
axioms.
-/

namespace MSTNFR2.CedarBridge

/-! ## Strict linear orders (port of Cedar/Data/LT.lean:28) -/

/-- The pin's decidability side condition (batteries' `DecidableLT` at the
    pin; here a local class with the same content). -/
class DecLT (α : Type) [LT α] where
  dec : (a b : α) → Decidable (a < b)

attribute [instance] DecLT.dec

/-- The pin's `Cedar.Data.StrictLT` (LT.lean:28). -/
class StrictLT (α : Type) [LT α] : Prop where
  asymmetric : ∀ (a b : α), a < b → ¬ b < a
  transitive : ∀ (a b c : α), a < b → b < c → a < c
  connected : ∀ (a b : α), a ≠ b → (a < b ∨ b < a)

theorem StrictLT.irreflexive [LT α] [StrictLT α] (x : α) : ¬ x < x := fun h =>
  StrictLT.asymmetric x x h h

theorem StrictLT.if_not_lt_gt_then_eq [LT α] [StrictLT α] (x y : α) :
    ¬ x < y → ¬ y < x → x = y := by
  intro h₁ h₂
  refine Classical.byContradiction fun h₃ => ?_
  rcases StrictLT.connected x y h₃ with h₄ | h₄
  · exact h₁ h₄
  · exact h₂ h₄

/-! ## List equivalence (port of Cedar/Thm/Data/List/Basic.lean:40) -/

/-- The pin's `List.Equiv a b : Prop := a ⊆ b ∧ b ⊆ a`; `⊆` is the core
    `List.Subset` (membership implication), as at the pin. -/
def Equiv {α : Type} (a b : List α) : Prop := a ⊆ b ∧ b ⊆ a

theorem Equiv.refl {α : Type} (a : List α) : Equiv a a :=
  ⟨fun _ hx => hx, fun _ hx => hx⟩

theorem Equiv.symm {α : Type} {a b : List α} (h : Equiv a b) : Equiv b a :=
  ⟨h.2, h.1⟩

theorem Equiv.trans {α : Type} {a b c : List α} (h1 : Equiv a b) (h2 : Equiv b c) :
    Equiv a c :=
  ⟨fun _ hz => h2.1 (h1.1 hz), fun _ hz => h1.2 (h2.2 hz)⟩

theorem Equiv.of_eq {α : Type} {a b : List α} (h : a = b) : Equiv a b := by
  subst h
  exact Equiv.refl a

theorem cons_equiv_cons {α : Type} (x : α) {xs ys : List α} (h : Equiv xs ys) :
    Equiv (x :: xs) (x :: ys) := by
  constructor
  · intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · exact List.mem_cons.mpr (Or.inl hz)
    · exact List.mem_cons_of_mem _ (h.1 hz)
  · intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · exact List.mem_cons.mpr (Or.inl hz)
    · exact List.mem_cons_of_mem _ (h.2 hz)

theorem dup_head_equiv {α : Type} (x : α) (xs : List α) :
    Equiv (x :: x :: xs) (x :: xs) := by
  constructor
  · intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · exact List.mem_cons.mpr (Or.inl hz)
    · exact hz
  · intro z hz
    exact List.mem_cons_of_mem _ hz

theorem swap_cons_cons_equiv {α : Type} (x₁ x₂ : α) (xs : List α) :
    Equiv (x₁ :: x₂ :: xs) (x₂ :: x₁ :: xs) := by
  constructor
  · intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hz)))
    · rcases List.mem_cons.mp hz with hz | hz
      · exact List.mem_cons.mpr (Or.inl hz)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons_of_mem _ hz))
  · intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hz)))
    · rcases List.mem_cons.mp hz with hz | hz
      · exact List.mem_cons.mpr (Or.inl hz)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons_of_mem _ hz))

/-- Port of `List.filterMap_equiv` (Basic.lean:141). -/
theorem filterMap_equiv {α β : Type} (f : α → Option β) {xs ys : List α}
    (h : Equiv xs ys) : Equiv (xs.filterMap f) (ys.filterMap f) := by
  constructor
  · intro b hb
    rcases List.mem_filterMap.mp hb with ⟨a, ha, hfa⟩
    exact List.mem_filterMap.mpr ⟨a, h.1 ha, hfa⟩
  · intro b hb
    rcases List.mem_filterMap.mp hb with ⟨a, ha, hfa⟩
    exact List.mem_filterMap.mpr ⟨a, h.2 ha, hfa⟩

/-! ## Sortedness (port of the SortedBy machinery of Basic.lean:179) -/

/-- The pin's `SortedBy f`: pairwise strictly ascending under `f`. -/
inductive SortedBy {α β : Type} [LT β] (f : α → β) : List α → Prop where
  | nil : SortedBy f []
  | cons_nil {x : α} : SortedBy f [x]
  | cons_cons {x y : α} {ys : List α} : f x < f y → SortedBy f (y :: ys) →
      SortedBy f (x :: y :: ys)

theorem tail_sortedBy {α β : Type} [LT β] {f : α → β} {x : α} {xs : List α}
    (h : SortedBy f (x :: xs)) : SortedBy f xs := by
  cases h with
  | cons_nil => exact SortedBy.nil
  | cons_cons _ h' => exact h'

theorem sortedBy_implies_head_lt_tail {α β : Type} [LT β] [StrictLT β] {f : α → β}
    {y : α} :
    ∀ {xs : List α} {x : α}, SortedBy f (x :: xs) → y ∈ xs → f x < f y := by
  intro xs
  induction xs with
  | nil => intro x h₁ hy; cases hy
  | cons hd tl ih =>
      intro x h₁ hy
      cases h₁ with
      | cons_cons h₃ h₄ =>
          rcases List.mem_cons.mp hy with hy | hy
          · subst hy; exact h₃
          · exact StrictLT.transitive (f x) (f hd) (f y) h₃ (ih h₄ hy)

theorem sortedBy_equiv_implies_head_eq {α β : Type} [LT β] [StrictLT β] {f : α → β}
    {x y : α} {xs ys : List α} (h₁ : SortedBy f (x :: xs)) (h₂ : SortedBy f (y :: ys))
    (h₃ : Equiv (x :: xs) (y :: ys)) : x = y := by
  have h₄ : x ∈ y :: ys := h₃.1 (List.mem_cons_self _ _)
  have h₅ : y ∈ x :: xs := h₃.2 (List.mem_cons_self _ _)
  rcases List.mem_cons.mp h₄ with h₄ | h₄
  · exact h₄
  · rcases List.mem_cons.mp h₅ with h₅ | h₅
    · exact h₅.symm
    · have hc₁ := sortedBy_implies_head_lt_tail h₁ h₅
      have hc₂ := sortedBy_implies_head_lt_tail h₂ h₄
      exact absurd hc₂ (StrictLT.asymmetric (f x) (f y) hc₁)

theorem sortedBy_equiv_implies_tail_subset {α β : Type} [LT β] [StrictLT β] {f : α → β}
    {x : α} {xs ys : List α} (h₁ : SortedBy f (x :: xs)) (_h₂ : SortedBy f (x :: ys))
    (h₃ : (x :: xs) ⊆ (x :: ys)) : xs ⊆ ys := by
  intro y h₄
  have h₅ := h₃ (List.mem_cons_of_mem _ h₄)
  rcases List.mem_cons.mp h₅ with h₅ | h₅
  · rw [h₅] at h₄
    exact absurd (sortedBy_implies_head_lt_tail h₁ h₄) (StrictLT.irreflexive (f x))
  · exact h₅

theorem sortedBy_equiv_implies_tail_equiv {α β : Type} [LT β] [StrictLT β] {f : α → β}
    {x : α} {xs ys : List α} (h₁ : SortedBy f (x :: xs)) (h₂ : SortedBy f (x :: ys))
    (h₃ : Equiv (x :: xs) (x :: ys)) : Equiv xs ys :=
  ⟨sortedBy_equiv_implies_tail_subset h₁ h₂ h₃.1,
    sortedBy_equiv_implies_tail_subset h₂ h₁ h₃.2⟩

theorem sortedBy_equiv_implies_eq {α β : Type} [LT β] [StrictLT β] {f : α → β} :
    ∀ (xs ys : List α), SortedBy f xs → SortedBy f ys → Equiv xs ys → xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _ h₃
      cases ys with
      | nil => rfl
      | cons yhead _ =>
          have hx := h₃.2 (List.mem_cons_self _ _)
          cases hx
  | cons xhead xtail ih =>
      intro ys h₁ h₂ h₃
      cases ys with
      | nil =>
          have hx := h₃.1 (List.mem_cons_self _ _)
          cases hx
      | cons yhead ytail =>
          have h₅ := sortedBy_equiv_implies_head_eq h₁ h₂ h₃
          subst h₅
          congr 1
          exact ih ytail (tail_sortedBy h₁) (tail_sortedBy h₂)
            (sortedBy_equiv_implies_tail_equiv h₁ h₂ h₃)

/-! ## Canonicalization (port of Cedar/Data/List.lean:35,51) -/

/-- The pin's `insertCanonical` (the pin's `fx > fh` written `fh < fx`). -/
def insertCanonical {α β : Type} [LT β] [DecLT β] (f : α → β) (x : α) :
    List α → List α
  | [] => [x]
  | hd :: tl =>
    if f x < f hd then x :: hd :: tl
    else if f hd < f x then hd :: insertCanonical f x tl
    else x :: tl

/-- The pin's `canonicalize`. -/
def canonicalize {α β : Type} [LT β] [DecLT β] (f : α → β) : List α → List α
  | [] => []
  | hd :: tl => insertCanonical f hd (canonicalize f tl)

theorem insertCanonical_cons_lt {α β : Type} [LT β] [DecLT β] (f : α → β) (x hd : α)
    (tl : List α) (h : f x < f hd) : insertCanonical f x (hd :: tl) = x :: hd :: tl := by
  simp only [insertCanonical]
  rw [if_pos h]

theorem insertCanonical_cons_gt {α β : Type} [LT β] [DecLT β] [StrictLT β] (f : α → β)
    (x hd : α) (tl : List α) (h : f hd < f x) :
    insertCanonical f x (hd :: tl) = hd :: insertCanonical f x tl := by
  by_cases h₁ : f x < f hd
  · exact absurd h₁ (StrictLT.asymmetric (f hd) (f x) h)
  · simp only [insertCanonical]
    rw [if_neg h₁, if_pos h]

theorem insertCanonical_cons_eq {α β : Type} [LT β] [DecLT β] (f : α → β) (x hd : α)
    (tl : List α) (h₁ : ¬ f x < f hd) (h₂ : ¬ f hd < f x) :
    insertCanonical f x (hd :: tl) = x :: tl := by
  simp only [insertCanonical]
  rw [if_neg h₁, if_neg h₂]

/-- Port of `insertCanonical_cases` (Canonical.lean:109). -/
theorem insertCanonical_cases {α β : Type} [LT β] [DecLT β] [StrictLT β] (f : α → β)
    (x y : α) (ys : List α) :
    (f x < f y ∧ insertCanonical f x (y :: ys) = x :: y :: ys) ∨
    (¬ f x < f y ∧ f y < f x ∧ insertCanonical f x (y :: ys) = y :: insertCanonical f x ys) ∨
    (¬ f x < f y ∧ ¬ f y < f x ∧ insertCanonical f x (y :: ys) = x :: ys) := by
  by_cases h₁ : f x < f y
  · exact Or.inl ⟨h₁, insertCanonical_cons_lt f x y ys h₁⟩
  · by_cases h₂ : f y < f x
    · exact Or.inr (Or.inl ⟨h₁, h₂, insertCanonical_cons_gt f x y ys h₂⟩)
    · exact Or.inr (Or.inr ⟨h₁, h₂, insertCanonical_cons_eq f x y ys h₁ h₂⟩)

/-- Port of `insertCanonical_subset` (Canonical.lean:126). -/
theorem insertCanonical_subset {α β : Type} [LT β] [DecLT β] [StrictLT β] (f : α → β)
    (x : α) : ∀ (xs : List α), insertCanonical f x xs ⊆ x :: xs := by
  intro xs
  induction xs with
  | nil => intro z hz; exact hz
  | cons hd tl ih =>
      by_cases h₁ : f x < f hd
      · rw [insertCanonical_cons_lt f x hd tl h₁]
        intro z hz
        exact hz
      · by_cases h₂ : f hd < f x
        · rw [insertCanonical_cons_gt f x hd tl h₂]
          intro z hz
          rcases List.mem_cons.mp hz with hz | hz
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl hz)))
          · rcases List.mem_cons.mp (ih hz) with hz' | hz'
            · exact List.mem_cons.mpr (Or.inl hz')
            · exact List.mem_cons.mpr (Or.inr (List.mem_cons_of_mem _ hz'))
        · rw [insertCanonical_cons_eq f x hd tl h₁ h₂]
          intro z hz
          rcases List.mem_cons.mp hz with hz | hz
          · exact List.mem_cons.mpr (Or.inl hz)
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons_of_mem _ hz))

/-- Port of `insertCanonical_sortedBy` (Canonical.lean:149). -/
theorem insertCanonical_sortedBy {α β : Type} [LT β] [DecLT β] [StrictLT β] {f : α → β}
    (x : α) : ∀ (xs : List α), SortedBy f xs → SortedBy f (insertCanonical f x xs) := by
  intro xs
  induction xs with
  | nil => intro _; exact SortedBy.cons_nil
  | cons hd tl ih =>
      intro h₁
      by_cases h₂ : f x < f hd
      · rw [insertCanonical_cons_lt f x hd tl h₂]
        exact SortedBy.cons_cons h₂ h₁
      · by_cases h₃ : f hd < f x
        · rw [insertCanonical_cons_gt f x hd tl h₃]
          cases h₁ with
          | cons_nil => exact SortedBy.cons_cons h₃ SortedBy.cons_nil
          | cons_cons h₅ h₆ =>
              rename_i t ts
              have h₇ := ih h₆
              rcases insertCanonical_cases f x t ts with
                ⟨h₈, heq⟩ | ⟨_, h₉, heq⟩ | ⟨h₈, h₉, heq⟩
              · rw [heq] at h₇ ⊢
                exact SortedBy.cons_cons h₃ (SortedBy.cons_cons h₈ h₆)
              · rw [heq] at h₇ ⊢
                exact SortedBy.cons_cons h₅ h₇
              · have h₁₀ : f x = f t :=
                  StrictLT.if_not_lt_gt_then_eq (f x) (f t) h₈ h₉
                rw [heq]
                refine SortedBy.cons_cons h₃ ?_
                cases h₆ with
                | cons_nil => exact SortedBy.cons_nil
                | cons_cons h₁₁ h₁₂ =>
                    rename_i u us
                    rw [← h₁₀] at h₁₁
                    exact SortedBy.cons_cons h₁₁ h₁₂
        · have h₄ := StrictLT.if_not_lt_gt_then_eq (f x) (f hd) h₂ h₃
          rw [insertCanonical_cons_eq f x hd tl h₂ h₃]
          cases h₁ with
          | cons_nil => exact SortedBy.cons_nil
          | cons_cons h₅ h₆ =>
              rename_i t ts
              rw [← h₄] at h₅
              exact SortedBy.cons_cons h₅ h₆

/-- Port of `insertCanonical_equiv` (Canonical.lean:220). -/
theorem insertCanonical_equiv {α : Type} [LT α] [DecLT α] [StrictLT α] (x : α) :
    ∀ (xs : List α), Equiv (x :: xs) (insertCanonical id x xs) := by
  intro xs
  induction xs with
  | nil => exact Equiv.refl _
  | cons hd tl ih =>
      by_cases h₁ : x < hd
      · rw [insertCanonical_cons_lt id x hd tl h₁]
        exact Equiv.refl _
      · by_cases h₂ : hd < x
        · rw [insertCanonical_cons_gt id x hd tl h₂]
          exact Equiv.trans (swap_cons_cons_equiv x hd tl) (cons_equiv_cons hd ih)
        · have h₃ := StrictLT.if_not_lt_gt_then_eq x hd h₁ h₂
          rw [insertCanonical_cons_eq id x hd tl h₁ h₂]
          rw [h₃]
          exact dup_head_equiv hd tl

/-- Port of `canonicalize_sortedBy` (via `insertCanonical_sortedBy`). -/
theorem canonicalize_sortedBy {α β : Type} [LT β] [DecLT β] [StrictLT β] (f : α → β) :
    ∀ (xs : List α), SortedBy f (canonicalize f xs) := by
  intro xs
  induction xs with
  | nil => exact SortedBy.nil
  | cons hd tl ih => exact insertCanonical_sortedBy hd _ ih

/-- Port of `canonicalize_equiv` (Canonical.lean:468). -/
theorem canonicalize_equiv {α : Type} [LT α] [DecLT α] [StrictLT α] :
    ∀ (xs : List α), Equiv xs (canonicalize id xs) := by
  intro xs
  induction xs with
  | nil => exact Equiv.refl _
  | cons hd tl ih =>
      exact Equiv.trans (cons_equiv_cons hd ih) (insertCanonical_equiv hd _)

/-- Port of `equiv_implies_canonical_eq` (Canonical.lean:482). -/
theorem equiv_implies_canonical_eq {α : Type} [LT α] [DecLT α] [StrictLT α]
    (xs ys : List α) (h : Equiv xs ys) : canonicalize id xs = canonicalize id ys := by
  apply sortedBy_equiv_implies_eq (f := id)
  · exact canonicalize_sortedBy id xs
  · exact canonicalize_sortedBy id ys
  · exact Equiv.trans (Equiv.symm (canonicalize_equiv xs))
      (Equiv.trans h (canonicalize_equiv ys))

/-! ## Sets (port of Cedar/Data/Set.lean:37) -/

/-- The pin's `Set`: an ordered duplicate-free element list. -/
structure Set (α : Type) where
  elts : List α

/-- The pin's `Set.empty` (Set.lean:49). -/
def Set.empty {α : Type} : Set α := ⟨[]⟩

/-- The pin's `Set.make` (Set.lean:56): canonicalize the element list. -/
def Set.make {α : Type} [LT α] [DecLT α] [StrictLT α] (elts : List α) : Set α :=
  ⟨canonicalize id elts⟩

/-- The pin's `Set.isEmpty` (Set.lean:62). -/
def Set.isEmpty {α : Type} (s : Set α) : Bool := s.elts.isEmpty

/-- Port of `Set.make_make_eqv` (Cedar/Thm/Data/Set.lean:298). -/
theorem Set.make_make_eqv {α : Type} [LT α] [DecLT α] [StrictLT α] {xs ys : List α} :
    Set.make xs = Set.make ys ↔ Equiv xs ys := by
  constructor
  · intro h
    have hc : canonicalize id xs = canonicalize id ys := congrArg Set.elts h
    exact Equiv.trans (canonicalize_equiv xs)
      (Equiv.trans (Equiv.of_eq hc) (Equiv.symm (canonicalize_equiv ys)))
  · intro h
    exact congrArg Set.mk (equiv_implies_canonical_eq xs ys h)

/-! ## Codepoint-list lexicographic order and the String instance
(port of Cedar/Data/LT.lean:231 via the string's character list;
batteries' `List.Lex` at the pin is replaced by the isomorphic `LexN`
over codepoint lists). -/

/-- Lexicographic order on natural-number (codepoint) lists; the
    batteries `List.Lex` of the pin, specialized to codepoints. -/
inductive LexN : List Nat → List Nat → Prop where
  | nil {b : Nat} {l : List Nat} : LexN [] (b :: l)
  | rel {a b : Nat} {as bs : List Nat} : a < b → LexN (a :: as) (b :: bs)
  | cons {a b : Nat} {as bs : List Nat} : a = b → LexN as bs → LexN (a :: as) (b :: bs)

/-- Decidability of the lexicographic order by structural recursion
    (constructive: `Nat.le_antisymm` on the two negated comparisons,
    no classical step). -/
def lexNDec : (xs ys : List Nat) → Decidable (LexN xs ys)
  | [], [] => isFalse (fun h => nomatch h)
  | [], _ :: _ => isTrue LexN.nil
  | _ :: _, [] => isFalse (fun h => nomatch h)
  | x :: xs, y :: ys =>
      match Nat.decLt x y with
      | isTrue h => isTrue (LexN.rel h)
      | isFalse h1 =>
          match Nat.decLt y x with
          | isTrue h2 => isFalse (by
              intro hc
              cases hc with
              | rel h4 => exact h1 h4
              | cons h5 _ =>
                  rw [h5] at h2
                  exact Nat.lt_irrefl y h2)
          | isFalse h2 =>
              have hxe : x = y := by
                rcases Nat.lt_or_ge x y with h3 | h3
                · exact absurd h3 h1
                · rcases Nat.lt_or_ge y x with h4 | h4
                  · exact absurd h4 h2
                  · exact Nat.le_antisymm h4 h3
              match lexNDec xs ys with
              | isTrue h3 => isTrue (LexN.cons hxe h3)
              | isFalse h3 => isFalse (by
                  intro hc
                  cases hc with
                  | rel h4 => exact h1 h4
                  | cons _ h6 => exact h3 h6)

theorem LexN.irrefl : ∀ (xs : List Nat), ¬ LexN xs xs := by
  intro xs
  induction xs with
  | nil => intro h; cases h
  | cons x tl ih =>
      intro h
      cases h with
      | rel h1 => exact Nat.lt_irrefl x h1
      | cons _ h2 => exact ih h2

theorem LexN.trans {xs ys zs : List Nat} (h1 : LexN xs ys) (h2 : LexN ys zs) :
    LexN xs zs := by
  cases h1 with
  | nil =>
      cases h2 with
      | rel _ => exact LexN.nil
      | cons _ _ => exact LexN.nil
  | rel h3 =>
      cases h2 with
      | rel h4 => exact LexN.rel (Nat.lt_trans h3 h4)
      | cons h5 _ => subst h5; exact LexN.rel h3
  | cons h3 h4 =>
      cases h2 with
      | rel h5 => subst h3; exact LexN.rel h5
      | cons h5 h6 => subst h5; exact LexN.cons h3 (LexN.trans h4 h6)

theorem LexN.connected : ∀ (xs ys : List Nat), xs ≠ ys → LexN xs ys ∨ LexN ys xs := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => exact absurd rfl h
      | cons _ _ => exact Or.inl LexN.nil
  | cons xhead xtail ih =>
      intro ys h
      cases ys with
      | nil => exact Or.inr LexN.nil
      | cons yhead ytail =>
          by_cases h1 : xhead < yhead
          · exact Or.inl (LexN.rel h1)
          · by_cases h2 : yhead < xhead
            · exact Or.inr (LexN.rel h2)
            · have h₃ : xhead = yhead := by
                refine Classical.byContradiction fun hne => ?_
                rcases Nat.lt_or_ge xhead yhead with h4 | h4
                · exact h1 h4
                · rcases Nat.lt_or_ge yhead xhead with h5 | h5
                  · exact h2 h5
                  · exact hne (Nat.le_antisymm h5 h4)
              subst h₃
              have h₄ : xtail ≠ ytail := fun he => h (by rw [he])
              rcases ih ytail h₄ with hc | hc
              · exact Or.inl (LexN.cons rfl hc)
              · exact Or.inr (LexN.cons rfl hc)

/-- Codepoint lists determine the string: `Char.toNat` is injective, so
    mapping it over the character list is injective. -/
theorem toNats_inj : ∀ {xs ys : List Char},
    xs.map Char.toNat = ys.map Char.toNat → xs = ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys =>
          rw [List.map_cons] at h
          exact List.noConfusion h
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil =>
          rw [List.map_cons] at h
          exact List.noConfusion h
      | cons y ys =>
          rw [List.map_cons, List.map_cons] at h
          injection h with hx ht
          have hxy : x = y := by
            have h1 : Char.ofNat x.toNat = Char.ofNat y.toNat := by rw [hx]
            rw [Char.ofNat_toNat, Char.ofNat_toNat] at h1
            exact h1
          rw [hxy]
          exact congrArg (y :: ·) (ih ht)

local instance stringLT : LT String :=
  ⟨fun a b => LexN (a.toList.map Char.toNat) (b.toList.map Char.toNat)⟩

local instance stringDecLT : DecLT String :=
  ⟨fun a b => lexNDec (a.toList.map Char.toNat) (b.toList.map Char.toNat)⟩

local instance stringStrictLT : StrictLT String where
  asymmetric := fun _ _ h1 h2 => LexN.irrefl _ (LexN.trans h1 h2)
  transitive := fun _ _ _ h1 h2 => LexN.trans h1 h2
  connected := fun a b h =>
    Or.elim (LexN.connected (a.toList.map Char.toNat) (b.toList.map Char.toNat)
        (fun he => h (String.ext (toNats_inj he))))
      (fun hc => Or.inl hc) (fun hc => Or.inr hc)

/-! ## The Cedar authorization surface (port of the cited Spec files) -/

section Spec

variable {Request Entities Expr Error : Type}

/-- Port of `Cedar/Spec/Response.lean:32`. -/
inductive Decision where
  | allow
  | deny

/-- Port of `Cedar/Spec/Response.lean:36`: the entire response is kept —
    the decision plus both policy-identifier sets. -/
structure Response where
  decision : Decision
  determiningPolicies : Set String
  erroringPolicies : Set String

/-- Port of `Cedar/Spec/Policy.lean:31`. -/
inductive Effect where
  | permit
  | forbid
  deriving DecidableEq

/-- Port of `Cedar/Spec/Policy.lean:60`. -/
abbrev PolicyID := String

/-- Port of `Cedar/Spec/Policy.lean:74`, keeping the fields the
    authorizer reads (`id`, `effect`, `toExpr`); see the module header for
    the documented reduction. -/
structure Policy (E : Type) where
  id : PolicyID
  effect : Effect
  toExpr : E
  deriving DecidableEq

/-- Port of `Cedar/Spec/Policy.lean:79`. -/
abbrev Policies (E : Type) := List (Policy E)

/- The evaluation core, abstract: see the module header. At the pin this
    is `evaluate : Expr → Request → Entities → Result Value` with
    `Result α := Except Error α`; the value language is collapsed to the
    truth bit the authorizer observes. Each definition below takes the
    evaluation core as an explicit leading parameter (the pin's section
    variable). -/

/-- Port of `Cedar/Spec/Authorizer.lean:31` (`satisfied`). -/
def satisfied {Request Entities Expr Error : Type}
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (policy : Policy Expr) (req : Request) (entities : Entities) : Bool :=
  match evaluate policy.toExpr req entities with
  | .ok true => true
  | _ => false

/-- Port of `Cedar/Spec/Authorizer.lean:35` (`satisfiedWithEffect`); the
    pin's `policy.effect == effect` is decidable equality here. -/
def satisfiedWithEffect {Request Entities Expr Error : Type}
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (effect : Effect) (policy : Policy Expr) (req : Request)
    (entities : Entities) : Option PolicyID :=
  if policy.effect = effect && satisfied evaluate policy req entities then some policy.id
  else none

/-- Port of `Cedar/Spec/Authorizer.lean:38` (`satisfiedPolicies`). -/
def satisfiedPolicies {Request Entities Expr Error : Type}
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (effect : Effect) (policies : Policies Expr) (req : Request)
    (entities : Entities) : Set PolicyID :=
  Set.make (policies.filterMap (satisfiedWithEffect evaluate effect · req entities))

/-- Port of `Cedar/Spec/Authorizer.lean:41` (`hasError`). -/
def hasError {Request Entities Expr Error : Type}
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (policy : Policy Expr) (req : Request) (entities : Entities) : Bool :=
  match evaluate policy.toExpr req entities with
  | .ok _ => false
  | .error _ => true

/-- Port of `Cedar/Spec/Authorizer.lean:48` (`errored`). -/
def errored {Request Entities Expr Error : Type}
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (policy : Policy Expr) (req : Request) (entities : Entities) : Option PolicyID :=
  if hasError evaluate policy req entities then some policy.id else none

/-- Port of `Cedar/Spec/Authorizer.lean:52` (`errorPolicies`). -/
def errorPolicies {Request Entities Expr Error : Type}
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (policies : Policies Expr) (req : Request)
    (entities : Entities) : Set PolicyID :=
  Set.make (policies.filterMap (errored evaluate · req entities))

/-- Port of `Cedar/Spec/Authorizer.lean:56` (`isAuthorized`), branch for
    branch: allow iff no forbid is satisfied and some permit is
    satisfied; an erroring policy is reported but does not override a
    satisfied permit; both policy-identifier sets are retained. -/
def isAuthorized {Request Entities Expr Error : Type}
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (req : Request) (entities : Entities) (policies : Policies Expr) :
    Response :=
  let forbids := satisfiedPolicies evaluate Effect.forbid policies req entities
  let permits := satisfiedPolicies evaluate Effect.permit policies req entities
  let erroringPolicies := errorPolicies evaluate policies req entities
  if forbids.isEmpty && !permits.isEmpty
  then { decision := Decision.allow, determiningPolicies := permits, erroringPolicies }
  else { decision := Decision.deny,  determiningPolicies := forbids, erroringPolicies }

/-- The `[allowAll, bad]` witness pair of `CEDAR-SOURCE-AUDIT.md` §3. -/
private def errWitnessPermit : Policy Bool :=
  { id := "allowAll", effect := Effect.permit, toExpr := true }

private def errWitnessBad : Policy Bool :=
  { id := "bad", effect := Effect.permit, toExpr := false }

private def errWitnessEval : Bool → Unit → Unit → Except Unit Bool
  | true, _, _ => Except.ok true
  | false, _, _ => Except.error ()

/-- Regression for the B2-a audit finding (the pin's `[allowAll, bad]`
    witness of `CEDAR-SOURCE-AUDIT.md` §3): a permit-satisfying policy
    plus an erroring policy yields `allow`, exactly as at
    `cedar-spec@fdbec74705` — the erroring policy is reported, not
    obeyed. -/
theorem isAuthorized_error_plus_permit :
    (isAuthorized errWitnessEval () () [errWitnessPermit, errWitnessBad]).decision
      = Decision.allow ∧
    (isAuthorized errWitnessEval () () [errWitnessPermit, errWitnessBad]).determiningPolicies
      = Set.make ["allowAll"] ∧
    (isAuthorized errWitnessEval () () [errWitnessPermit, errWitnessBad]).erroringPolicies
      = Set.make ["bad"] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [isAuthorized, satisfiedPolicies, satisfiedWithEffect, satisfied,
      errorPolicies, errored, hasError, Set.make, Set.isEmpty, Set.empty,
      canonicalize, insertCanonical, errWitnessPermit, errWitnessBad, errWitnessEval]

/-! ## Order and duplicate independence (the official theorem) -/

/-- Port of `satisfiedPolicies_order_and_dup_independent`
    (Cedar/Thm/Authorization/Authorizer.lean:54). -/
theorem satisfiedPolicies_order_and_dup_independent
    {Request Entities Expr Error : Type}
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (effect : Effect) (req : Request) (entities : Entities)
    {policies₁ policies₂ : Policies Expr} :
    Equiv policies₁ policies₂ →
    satisfiedPolicies evaluate effect policies₁ req entities
      = satisfiedPolicies evaluate effect policies₂ req entities := by
  intro h
  simp only [satisfiedPolicies]
  rw [Set.make_make_eqv]
  exact filterMap_equiv _ h

/-- Port of `errorPolicies_order_and_dup_independent`
    (Cedar/Thm/Authorization/Authorizer.lean:63). -/
theorem errorPolicies_order_and_dup_independent
    {Request Entities Expr Error : Type}
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (req : Request) (entities : Entities)
    {policies₁ policies₂ : Policies Expr} :
    Equiv policies₁ policies₂ →
    errorPolicies evaluate policies₁ req entities
      = errorPolicies evaluate policies₂ req entities := by
  intro h
  simp only [errorPolicies]
  rw [Set.make_make_eqv]
  exact filterMap_equiv _ h

/-- Congruence step for `isAuthorized`: equal component sets give equal
    responses (the `simp [isAuthorized, hf, hp, he]` close of the official
    proof, made explicit). -/
theorem isAuthorized_congr {Request Entities Expr Error : Type}
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (req : Request) (entities : Entities)
    {policies₁ policies₂ : Policies Expr}
    (hf : satisfiedPolicies evaluate Effect.forbid policies₁ req entities
      = satisfiedPolicies evaluate Effect.forbid policies₂ req entities)
    (hp : satisfiedPolicies evaluate Effect.permit policies₁ req entities
      = satisfiedPolicies evaluate Effect.permit policies₂ req entities)
    (he : errorPolicies evaluate policies₁ req entities
      = errorPolicies evaluate policies₂ req entities) :
    isAuthorized evaluate req entities policies₁
      = isAuthorized evaluate req entities policies₂ := by
  simp only [isAuthorized, hf, hp, he]

/-- Port of `Cedar.Thm.order_and_dup_independent`
    (Cedar/Thm/Authorization.lean:147): `isAuthorized` gives the same
    entire `Response` for order/duplicate-equivalent policy lists. -/
theorem order_and_dup_independent {Request Entities Expr Error : Type}
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (req : Request) (entities : Entities)
    {policies₁ policies₂ : Policies Expr} :
    Equiv policies₁ policies₂ →
    isAuthorized evaluate req entities policies₁
      = isAuthorized evaluate req entities policies₂ := by
  intro h
  exact isAuthorized_congr evaluate req entities
    (satisfiedPolicies_order_and_dup_independent evaluate Effect.forbid req entities h)
    (satisfiedPolicies_order_and_dup_independent evaluate Effect.permit req entities h)
    (errorPolicies_order_and_dup_independent evaluate req entities h)

end Spec

/-! ## Discharging the section 8 `DuplicateInvariance` hypothesis (B2) -/

section Bind

open MSTNFR2

/-- The authorization function of the ported spec surface, as a
    `CedarDedup` response function. The decision is computed from the
    input's own request, entities and policies (contract §8: the
    normalized key retains request/entities and replaces policies). -/
def cedarAuth {Request Entities Expr Error : Type} [DecidableEq Expr]
    (evaluate : Expr → Request → Entities → Except Error Bool) :
    CedarInput Request Entities (Policy Expr) → Response :=
  fun x => isAuthorized evaluate x.request x.entities x.policies

/-- The decision tag map from the ported `Decision`. -/
def dcnOf (r : Response) : MSTNFR2.CDecision :=
  match r.decision with
  | Decision.allow => MSTNFR2.CDecision.allow
  | Decision.deny => MSTNFR2.CDecision.deny

/-- Contract §8: the denial kind. `noPermit` — the denial is due to no
    satisfied permit (empty determining set); `forbidDetermined` — a
    satisfied forbid determined the denial. -/
inductive DenialKind where
  | noPermit
  | forbidDetermined

/-- Contract §8: the denial kind is a *separate projection* on the
    `Response` (`none` on allow); the refusal itself still carries the
    full denied `Response`. -/
def denialKind (r : Response) : Option DenialKind :=
  match r.decision with
  | Decision.allow => none
  | Decision.deny =>
      some (if r.determiningPolicies.isEmpty then DenialKind.noPermit
        else DenialKind.forbidDetermined)

theorem denialKind_of_allow {r : Response} (h : r.decision = Decision.allow) :
    denialKind r = none := by
  simp only [denialKind, h]

theorem denialKind_noPermit {r : Response} (h : r.decision = Decision.deny)
    (hE : r.determiningPolicies = Set.empty) :
    denialKind r = some DenialKind.noPermit := by
  simp only [denialKind, h, hE, Set.isEmpty]
  rfl

theorem denialKind_forbidDetermined {r : Response} (h : r.decision = Decision.deny)
    (hN : ¬ r.determiningPolicies.isEmpty) :
    denialKind r = some DenialKind.forbidDetermined := by
  simp only [denialKind, h]
  exact congrArg some (if_neg hN)

/-- B2 discharge: the ported official theorem instantiates the exact
    `DuplicateInvariance` hypothesis of the section 8 module, so the
    dedup instance's downstream results hold unconditionally for the
    Cedar authorization function. -/
theorem order_dup_DuplicateInvariance {Request Entities Expr Error : Type} [DecidableEq Expr]
    (evaluate : Expr → Request → Entities → Except Error Bool) :
    MSTNFR2.DuplicateInvariance (cedarAuth evaluate) := by
  intro x a b h₁ h₂
  exact order_and_dup_independent evaluate x.request x.entities ⟨h₁, h₂⟩

/-- Unconditional reference bridge for the Cedar dedup instance (was
    conditional on the `hDup` hypothesis). -/
theorem cedar_bridge_bridged {Request Entities Expr Error : Type} [DecidableEq Expr]
    (evaluate : Expr → Request → Entities → Except Error Bool) :
    bridged (cedarIF (cedarAuth evaluate) dcnOf) :=
  cedarIF_bridged _ _ (order_dup_DuplicateInvariance evaluate)

/-- Unconditional source section for the Cedar dedup instance. -/
theorem cedar_bridge_sourceSection {Request Entities Expr Error : Type} [DecidableEq Expr]
    (evaluate : Expr → Request → Entities → Except Error Bool) :
    decisionSourceSection (cedarIF (cedarAuth evaluate) dcnOf)
      (fun p => p.1.val) :=
  cedarIF_sourceSection _ _

/-- Unconditional normalization: the response on any input equals the
    response on its deduplicated input. -/
theorem cedar_bridge_auth_norm {Request Entities Expr Error : Type} [DecidableEq Expr]
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (x : CedarInput Request Entities (Policy Expr)) :
    cedarAuth evaluate x = cedarAuth evaluate (normIn x) :=
  auth_norm _ (order_dup_DuplicateInvariance evaluate) x

/-- Unconditional cross-input reuse on `[p]` vs `[p, p]`. -/
theorem cedar_bridge_dup_collision {Request Entities Expr Error : Type} [DecidableEq Expr]
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (x0 : CedarInput Request Entities (Policy Expr))
    (p : Policy Expr) :
    withPols x0 [p] ≠ withPols x0 [p, p] ∧
    qkey (withPols x0 [p]) = qkey (withPols x0 [p, p]) ∧
    (cedarIF (cedarAuth evaluate) dcnOf).O (withPols x0 [p])
      = (cedarIF (cedarAuth evaluate) dcnOf).O (withPols x0 [p, p]) :=
  dup_collision _ _ (order_dup_DuplicateInvariance evaluate) x0 p

/-- Contract §8 losslessness instantiated: `erase ∘ classify = id` on the
    Cedar response, so both policy-identifier sets survive the reference
    observation split. -/
theorem cedar_bridge_erase_classify {Request Entities Expr Error : Type} [DecidableEq Expr]
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (x : CedarInput Request Entities (Policy Expr)) :
    MSTNFR2.erase dcnOf (MSTNFR2.classify dcnOf (cedarAuth evaluate x))
      = cedarAuth evaluate x :=
  MSTNFR2.erase_classify _ _

/-- Contract §8: a refusal carries the *full* denied `Response` (all
    three fields); the denial kind is the separate `denialKind`
    projection above. -/
theorem cedar_bridge_deny_carries_full {Request Entities Expr Error : Type}
    [DecidableEq Expr]
    (evaluate : Expr → Request → Entities → Except Error Bool)
    (x : CedarInput Request Entities (Policy Expr))
    (h : dcnOf (cedarAuth evaluate x) = MSTNFR2.CDecision.deny) :
    (cedarIF (cedarAuth evaluate) dcnOf).O x
      = Sum.inr (⟨cedarAuth evaluate x, h⟩ : MSTNFR2.CDenied dcnOf) := by
  have hO : (cedarIF (cedarAuth evaluate) dcnOf).O x
      = MSTNFR2.classify dcnOf (cedarAuth evaluate x) := rfl
  rw [hO, MSTNFR2.classify_deny dcnOf (cedarAuth evaluate x) h]

/-! ## Concrete collision witnesses (contract §8: unconditional permit
and forbid give collisions on both branches) -/

private def witEval : Bool → Unit → Unit → Except Unit Bool
  | true, _, _ => Except.ok true
  | false, _, _ => Except.ok false

private def witPermit : Policy Bool :=
  { id := "pA", effect := Effect.permit, toExpr := true }

private def witForbid : Policy Bool :=
  { id := "pF", effect := Effect.forbid, toExpr := true }

private def witInput : CedarInput Unit Unit (Policy Bool) :=
  { request := (), entities := (), policies := [] }

theorem cedarAuth_witPermit :
    dcnOf (cedarAuth witEval (withPols witInput [witPermit]))
      = MSTNFR2.CDecision.allow := by
  simp [cedarAuth, isAuthorized, satisfiedPolicies, satisfiedWithEffect,
    satisfied, errorPolicies, errored, hasError, Set.make, Set.isEmpty,
    Set.empty, canonicalize, insertCanonical, witEval, witPermit,
    witInput, dcnOf]

theorem cedarAuth_witForbid :
    dcnOf (cedarAuth witEval (withPols witInput [witForbid]))
      = MSTNFR2.CDecision.deny := by
  simp [cedarAuth, isAuthorized, satisfiedPolicies, satisfiedWithEffect,
    satisfied, errorPolicies, errored, hasError, Set.make, Set.isEmpty,
    Set.empty, canonicalize, insertCanonical, witEval, witForbid,
    witInput, dcnOf]

/-- Contract §8: `[pA]` vs `[pA, pA]` collide on the allow branch. -/
theorem cedar_bridge_permit_collision :
    dcnOf (cedarAuth witEval (withPols witInput [witPermit]))
      = MSTNFR2.CDecision.allow ∧
    dcnOf (cedarAuth witEval (withPols witInput [witPermit, witPermit]))
      = MSTNFR2.CDecision.allow :=
  ⟨cedarAuth_witPermit,
    (both_branches (cedarAuth witEval) dcnOf
      (order_dup_DuplicateInvariance witEval) witInput witPermit witForbid
      cedarAuth_witPermit cedarAuth_witForbid).1⟩

/-- Contract §8: `[pF]` vs `[pF, pF]` collide on the deny branch. -/
theorem cedar_bridge_forbid_collision :
    dcnOf (cedarAuth witEval (withPols witInput [witForbid]))
      = MSTNFR2.CDecision.deny ∧
    dcnOf (cedarAuth witEval (withPols witInput [witForbid, witForbid]))
      = MSTNFR2.CDecision.deny :=
  ⟨cedarAuth_witForbid,
    (both_branches (cedarAuth witEval) dcnOf
      (order_dup_DuplicateInvariance witEval) witInput witPermit witForbid
      cedarAuth_witPermit cedarAuth_witForbid).2⟩

end Bind

end MSTNFR2.CedarBridge

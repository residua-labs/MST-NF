import MSTNF.r2.Finite

/-!
# MST-NF R2 — operational non-vacuity: PreKey parameter structure (contract §3)

Mechanization of the R2 contract, section 3 ("operational non-vacuity: a
separate interface"), instantiated with one concrete key language on the
six-input demonstrator of the finite-instance spec.

Sources (mature sources rule, preamble item 7):
- Design of record: `MST-NF-R2-mechanization-contract.md` section 3 (the
  `PreKey(B,P,q)` schema, the no-callback-escape requirement, and the notes
  that traces and costs are bound by the operational relation, not freely
  supplied fields of a certificate).
- Pinned base + finite suite: `MSTNF.r2.Finite` (`Raw6`, `Class3`, `baseQ`).

Design notes (contract-faithful):
- The key language syntax is a first-order AST: primitive applications,
  class literals, and conditionals. There is no function-callback escape.
- The primitive space contains a reference-call capability `refEval` so that
  "no reference access" is a non-vacuous predicate; the declared manifest
  `[isG, isB]` excludes it, and `UsesDeclaredCapabilities` plus the
  instrumentation lemma below rule it out of every run.
- `Run P x v tr k` binds the trace and the cost: they appear as indices of
  the evaluation relation and are computed by its clauses (cost is
  compositional: an `ite` step costs its branches plus one).
- The instrumentation lemma `run_trace_only_program_prims` accounts for
  primitive behavior and transitive dependencies: every primitive in a run's
  trace occurs in the program text, inherited through subterm runs.
- No claim is made here about benefit, cost superiority, or absence of
  inlined recomputation (contract: that needs an additional cost bound or
  honest measurement).

No Mathlib import; no `sorry`; no `native_decide`; no new axioms.
-/

namespace MSTNFR2

open MSTNecessityExecModelMWE

/-! ## A concrete key language -/

/-- Value domain of the key language: computed keys or branch Booleans. -/
inductive KVal where
  | key : Class3 → KVal
  | bool : Bool → KVal
  deriving DecidableEq

/-- Primitive capabilities. `isG`/`isB` are local classifiers; `refEval` is a
    reference-call capability that no declared manifest of this instance
    includes (so "no reference access" is non-vacuous). There is no
    memo-read primitive, so "reads of previously computed reference results"
    cannot occur either. -/
inductive KPrim where
  | isG | isB | refEval
  deriving DecidableEq

/-- First-order key programs: no arbitrary function callbacks. -/
inductive KExpr where
  | prim (p : KPrim)
  | lit (c : Class3)
  | ite (cond thenE elseE : KExpr)
  deriving DecidableEq

/-- Denotation of the primitive capabilities. -/
def primSem : KPrim → Raw6 → Bool
  | KPrim.isG, r => (r == Raw6.g0) || (r == Raw6.g1)
  | KPrim.isB, r => (r == Raw6.b0) || (r == Raw6.b1)
  | KPrim.refEval, _ => false

/-! ## Operational semantics: `Run P x v tr k` -/

/-- Big-step evaluation binding value, primitive trace, and cost. -/
inductive Run : KExpr → Raw6 → KVal → List KPrim → Nat → Prop where
  | prim {p x b} : primSem p x = b → Run (.prim p) x (.bool b) [p] 1
  | lit {c x} : Run (.lit c) x (.key c) [] 0
  | iteTrue {cond te ee x v tr1 tr2 k1 k2} :
      Run cond x (.bool true) tr1 k1 → Run te x v tr2 k2 →
      Run (.ite cond te ee) x v (tr1 ++ tr2) (k1 + k2 + 1)
  | iteFalse {cond te ee x v tr1 tr2 k1 k2} :
      Run cond x (.bool false) tr1 k1 → Run ee x v tr2 k2 →
      Run (.ite cond te ee) x v (tr1 ++ tr2) (k1 + k2 + 1)

/-! ## Manifest, declared capabilities, no-reference access -/

/-- The declared primitive manifest of this instance. -/
def declaredPrims : List KPrim := [KPrim.isG, KPrim.isB]

/-- The primitives occurring in a program text. -/
def primsOf : KExpr → List KPrim
  | .prim p => [p]
  | .lit _ => []
  | .ite c t e => primsOf c ++ primsOf t ++ primsOf e

/-- Contract: `UsesDeclaredCapabilities(B,P)`. -/
def UsesDeclaredCapabilities (B : List KPrim) (P : KExpr) : Prop :=
  ∀ p ∈ primsOf P, p ∈ B

/-- No reference access: the run's trace contains no reference-call
    primitive. -/
def noRefAccess (tr : List KPrim) : Prop := KPrim.refEval ∉ tr

/-! ## Instrumentation: determinism and transitive trace accounting -/

theorem run_det {P x v tr k} (h : Run P x v tr k) :
    ∀ {v' tr' k'}, Run P x v' tr' k' → v = v' ∧ tr = tr' ∧ k = k' := by
  induction h with
  | prim hs =>
      intro _ _ _ h'
      cases h' with
      | prim hs' => exact ⟨by rw [← hs, ← hs'], rfl, rfl⟩
  | lit =>
      intro _ _ _ h'
      cases h' with
      | lit => exact ⟨rfl, rfl, rfl⟩
  | iteTrue hc _ ihc iht =>
      intro _ _ _ h'
      cases h' with
      | iteTrue hc' ht' =>
          have ⟨h1, h2, h3⟩ := ihc hc'
          have ⟨g1, g2, g3⟩ := iht ht'
          exact ⟨g1, by rw [h2, g2], by rw [h3, g3]⟩
      | iteFalse hc' _ =>
          have ⟨h1, _, _⟩ := ihc hc'
          exact absurd h1 (by decide)
  | iteFalse hc _ ihc ihe =>
      intro _ _ _ h'
      cases h' with
      | iteTrue hc' _ =>
          have ⟨h1, _, _⟩ := ihc hc'
          exact absurd h1.symm (by decide)
      | iteFalse hc' he' =>
          have ⟨h1, h2, h3⟩ := ihc hc'
          have ⟨g1, g2, g3⟩ := ihe he'
          exact ⟨g1, by rw [h2, g2], by rw [h3, g3]⟩

/-- Every primitive in a run's trace occurs in the program text: the
    instrumentation accounts for primitive behavior and transitive
    dependencies (a compound step's trace is exactly the concatenation of its
    subterm traces). -/
theorem run_trace_only_program_prims {P x v tr k} (h : Run P x v tr k) :
    ∀ p ∈ tr, p ∈ primsOf P := by
  induction h with
  | prim => intro p hp; exact hp
  | lit => intro p hp; exact hp
  | iteTrue _ _ ihc iht =>
      intro p hp
      simp only [primsOf, List.mem_append] at hp ⊢
      rcases hp with hp | hp
      · exact Or.inl (Or.inl (ihc p hp))
      · exact Or.inl (Or.inr (iht p hp))
  | iteFalse _ _ ihc ihe =>
      intro p hp
      simp only [primsOf, List.mem_append] at hp ⊢
      rcases hp with hp | hp
      · exact Or.inl (Or.inl (ihc p hp))
      · exact Or.inr (ihe p hp)

/-! ## The PreKey schema and the concrete instance -/

/-- Contract section 3, the `PreKey(B,P,q)` schema: declared capabilities,
    total runs returning the key, correctness with no reference access, and
    a cross-input collision. -/
def PreKey (B : List KPrim) (P : KExpr) (key : Raw6 → Class3) : Prop :=
  UsesDeclaredCapabilities B P ∧
  (∀ x, ∃ tr k, Run P x (.key (key x)) tr k) ∧
  (∀ x v tr k, Run P x v tr k → v = .key (key x) ∧ noRefAccess tr) ∧
  (∃ x y, x ≠ y ∧ key x = key y)

/-- The concrete key program: classify by testing `isG`, then `isB`,
    defaulting to `Z`. -/
def Pkey : KExpr :=
  .ite (.prim KPrim.isG) (.lit Class3.G)
    (.ite (.prim KPrim.isB) (.lit Class3.B) (.lit Class3.Z))

theorem pkey_usesDeclared : UsesDeclaredCapabilities declaredPrims Pkey := by
  intro p hp
  simp [primsOf, declaredPrims] at hp
  simpa [declaredPrims] using hp

theorem pkey_total : ∀ x, ∃ tr k, Run Pkey x (.key (baseQ x)) tr k := by
  intro x
  cases x with
  | g0 =>
      exact ⟨[KPrim.isG], 2,
        Run.iteTrue (Run.prim (show primSem KPrim.isG Raw6.g0 = true from rfl)) Run.lit⟩
  | g1 =>
      exact ⟨[KPrim.isG], 2,
        Run.iteTrue (Run.prim (show primSem KPrim.isG Raw6.g1 = true from rfl)) Run.lit⟩
  | b0 =>
      exact ⟨[KPrim.isG, KPrim.isB], 4,
        Run.iteFalse (Run.prim (show primSem KPrim.isG Raw6.b0 = false from rfl))
          (Run.iteTrue (Run.prim (show primSem KPrim.isB Raw6.b0 = true from rfl)) Run.lit)⟩
  | b1 =>
      exact ⟨[KPrim.isG, KPrim.isB], 4,
        Run.iteFalse (Run.prim (show primSem KPrim.isG Raw6.b1 = false from rfl))
          (Run.iteTrue (Run.prim (show primSem KPrim.isB Raw6.b1 = true from rfl)) Run.lit)⟩
  | z0 =>
      exact ⟨[KPrim.isG, KPrim.isB], 4,
        Run.iteFalse (Run.prim (show primSem KPrim.isG Raw6.z0 = false from rfl))
          (Run.iteFalse (Run.prim (show primSem KPrim.isB Raw6.z0 = false from rfl)) Run.lit)⟩
  | z1 =>
      exact ⟨[KPrim.isG, KPrim.isB], 4,
        Run.iteFalse (Run.prim (show primSem KPrim.isG Raw6.z1 = false from rfl))
          (Run.iteFalse (Run.prim (show primSem KPrim.isB Raw6.z1 = false from rfl)) Run.lit)⟩

theorem pkey_correct : ∀ x v tr k, Run Pkey x v tr k →
    v = .key (baseQ x) ∧ noRefAccess tr := by
  intro x v tr k h
  refine ⟨?_, ?_⟩
  · obtain ⟨_, _, h0⟩ := pkey_total x
    exact (run_det h0 h).1.symm
  · intro hmem
    have hmem' : KPrim.refEval ∈ primsOf Pkey :=
      run_trace_only_program_prims h _ hmem
    simp [primsOf] at hmem'

theorem pkey_collision : ∃ x y, x ≠ y ∧ baseQ x = baseQ y :=
  ⟨Raw6.g0, Raw6.g1, fun h => Raw6.noConfusion h, rfl⟩

/-- **PreKey instance**: the concrete key language with manifest
    `[isG, isB]` and program `Pkey` satisfies the contract's `PreKey` schema
    for the six-input demonstrator's key `baseQ`. -/
theorem Pkey_preKey : PreKey declaredPrims Pkey baseQ :=
  ⟨pkey_usesDeclared, pkey_total, pkey_correct, pkey_collision⟩

end MSTNFR2

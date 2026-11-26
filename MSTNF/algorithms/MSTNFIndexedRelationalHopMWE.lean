import MSTNF.algorithms.MSTNFIndexedRunMWE
import MSTNF.algorithms.MSTNFNamedPassageMWE

/-!
Generalized indexed hops and declared carrier passages.
-/

set_option autoImplicit false

namespace NfCompose.Indexed

/-- One successful artifact translation, with its own monotone runtime bound.
The runs already fix the runtime context; R retains both actual artifacts.
The target's static domain is separate from its runtime refusal policy. -/
def IndexedRelHopAt {X Y I J VA VB EA EB EF : Type}
    (a : BudgetOrder I) (b : BudgetOrder J)
    (A : X → RunView I VA EA) (B : Y → RunView J VB EB)
    (F : X → Except EF Y) (accept : Y → Prop)
    (R : X → Y → VA → VB → Prop) (named : Y → EB → Prop)
    (x : X) : Prop :=
  ∃ y, F x = .ok y ∧ accept y ∧
    ∃ g : FuelBound a b, RunRefines a b (A x) (B y) g (R x y) (named y)

def IndexedRelHopOn {X Y I J VA VB EA EB EF : Type}
    (a : BudgetOrder I) (b : BudgetOrder J)
    (A : X → RunView I VA EA) (B : Y → RunView J VB EB)
    (F : X → Except EF Y) (accept : Y → Prop)
    (R : X → Y → VA → VB → Prop) (named : Y → EB → Prop)
    (P : X → Prop) : Prop :=
  ∀ x, P x → IndexedRelHopAt a b A B F accept R named x

/-- This relation records the actual artifact path, as well as its middle value.
A different image with a convenient value cannot discharge the witness. -/
def PathRel {X Y Z VA VB VC EF EG : Type}
    (F : X → Except EF Y) (G : Y → Except EG Z)
    (R : X → Y → VA → VB → Prop) (S : Y → Z → VB → VC → Prop) :
    X → Z → VA → VC → Prop :=
  fun x z va vc =>
    ∃ y vb, F x = .ok y ∧ G y = .ok z ∧ R x y va vb ∧ S y z vb vc

theorem indexedRelHopAt_mono {X Y I J VA VB EA EB EF : Type}
    (a : BudgetOrder I) (b : BudgetOrder J)
    (A : X → RunView I VA EA) (B : Y → RunView J VB EB)
    (F : X → Except EF Y) (accept : Y → Prop)
    (R S : X → Y → VA → VB → Prop) (named : Y → EB → Prop)
    (hRS : ∀ x y va vb, R x y va vb → S x y va vb)
    (x : X) (h : IndexedRelHopAt a b A B F accept R named x) :
    IndexedRelHopAt a b A B F accept S named x := by
  obtain ⟨y, hf, hy, g, hr⟩ := h
  exact ⟨y, hf, hy, g, RunRefines.relation_mono (hRS x y) hr⟩

theorem indexedRelHopOn_mono {X Y I J VA VB EA EB EF : Type}
    (a : BudgetOrder I) (b : BudgetOrder J)
    (A : X → RunView I VA EA) (B : Y → RunView J VB EB)
    (F : X → Except EF Y) (accept : Y → Prop)
    (R S : X → Y → VA → VB → Prop) (named : Y → EB → Prop)
    (P : X → Prop)
    (hRS : ∀ x y va vb, R x y va vb → S x y va vb)
    (h : IndexedRelHopOn a b A B F accept R named P) :
    IndexedRelHopOn a b A B F accept S named P :=
  fun x hx => indexedRelHopAt_mono a b A B F accept R S named hRS x (h x hx)

/-- The first output's domain is exactly the premise of the next stage.
Bounds compose inside the actual path; no choice of a global program-independent
bound is made. Native runtime refusals retain the final endpoint's exact policy.
Translation failures retain the stage tags supplied by namedSeq. -/
theorem indexedRelHopAt_seq {X Y Z I J K VA VB VC EA EB EC EF EG : Type}
    (a : BudgetOrder I) (b : BudgetOrder J) (c : BudgetOrder K)
    (A : X → RunView I VA EA) (B : Y → RunView J VB EB)
    (C : Z → RunView K VC EC)
    (F : X → Except EF Y) (G : Y → Except EG Z)
    (acceptB : Y → Prop) (acceptC : Z → Prop)
    (R : X → Y → VA → VB → Prop) (S : Y → Z → VB → VC → Prop)
    (namedB : Y → EB → Prop) (namedC : Z → EC → Prop)
    (x : X)
    (hAB : IndexedRelHopAt a b A B F acceptB R namedB x)
    (hBC : ∀ y, acceptB y →
      IndexedRelHopAt b c B C G acceptC S namedC y) :
    IndexedRelHopAt a c A C (namedSeq F G) acceptC
      (PathRel F G R S) namedC x := by
  obtain ⟨y, hf, hy, g, hab⟩ := hAB
  obtain ⟨z, hg, hz, h, hbc⟩ := hBC y hy
  refine ⟨z, namedSeq_ok F G x y z hf hg, hz, FuelBound.comp g h, ?_⟩
  refine RunRefines.relation_mono (fun va vc hrel => ?_) (hab.seq hbc)
  obtain ⟨vb, hr, hs⟩ := hrel
  exact ⟨y, vb, hf, hg, hr, hs⟩

theorem indexedRelHopOn_seq {X Y Z I J K VA VB VC EA EB EC EF EG : Type}
    (a : BudgetOrder I) (b : BudgetOrder J) (c : BudgetOrder K)
    (A : X → RunView I VA EA) (B : Y → RunView J VB EB)
    (C : Z → RunView K VC EC)
    (F : X → Except EF Y) (G : Y → Except EG Z)
    (acceptB : Y → Prop) (acceptC : Z → Prop)
    (R : X → Y → VA → VB → Prop) (S : Y → Z → VB → VC → Prop)
    (namedB : Y → EB → Prop) (namedC : Z → EC → Prop)
    (P : X → Prop)
    (hAB : IndexedRelHopOn a b A B F acceptB R namedB P)
    (hBC : IndexedRelHopOn b c B C G acceptC S namedC acceptB) :
    IndexedRelHopOn a c A C (namedSeq F G) acceptC
      (PathRel F G R S) namedC P :=
  fun x hx => indexedRelHopAt_seq a b c A B C F G acceptB acceptC R S
    namedB namedC x (hAB x hx) hBC

/-- Collapse a path relation only through the caller's explicit relation law. -/
theorem indexedRelHopOn_comp {X Y Z I J K VA VB VC EA EB EC EF EG : Type}
    (a : BudgetOrder I) (b : BudgetOrder J) (c : BudgetOrder K)
    (A : X → RunView I VA EA) (B : Y → RunView J VB EB)
    (C : Z → RunView K VC EC)
    (F : X → Except EF Y) (G : Y → Except EG Z)
    (acceptB : Y → Prop) (acceptC : Z → Prop)
    (R : X → Y → VA → VB → Prop) (S : Y → Z → VB → VC → Prop)
    (U : X → Z → VA → VC → Prop)
    (namedB : Y → EB → Prop) (namedC : Z → EC → Prop)
    (P : X → Prop)
    (hcomp : ∀ x y z va vb vc,
      F x = .ok y → G y = .ok z →
      R x y va vb → S y z vb vc → U x z va vc)
    (hAB : IndexedRelHopOn a b A B F acceptB R namedB P)
    (hBC : IndexedRelHopOn b c B C G acceptC S namedC acceptB) :
    IndexedRelHopOn a c A C (namedSeq F G) acceptC U namedC P := by
  apply indexedRelHopOn_mono a c A C (namedSeq F G) acceptC
    (PathRel F G R S) U namedC P
  · intro x z va vc hr
    obtain ⟨y, vb, hf, hg, hR, hS⟩ := hr
    exact hcomp x y z va vb vc hf hg hR hS
  · exact indexedRelHopOn_seq a b c A B C F G acceptB acceptC R S
      namedB namedC P hAB hBC

/-- Declaration, not an alternative execution model: a named carrier map,
its domain, target acceptance, actual-artifact relation and runtime laws.
Any context parameter (environment, entry, mode, arguments, version) must be
fixed in A/B/R or retained in X/Y before this declaration can be constructed. -/
structure DeclaredPassage {X Y I J VA VB EA EB EF : Type}
    (a : BudgetOrder I) (b : BudgetOrder J)
    (A : X → RunView I VA EA) (B : Y → RunView J VB EB)
    (domain : X → Prop) (accept : Y → Prop)
    (R : X → Y → VA → VB → Prop) (named : Y → EB → Prop) where
  map : X → Except EF Y
  laws : IndexedRelHopOn a b A B map accept R named domain

namespace DeclaredPassage

/-- An explicit passage is consumed by the same law as a compiler stage. -/
def comp {X Y Z I J K VA VB VC EA EB EC EF EG : Type}
    {a : BudgetOrder I} {b : BudgetOrder J} {c : BudgetOrder K}
    {A : X → RunView I VA EA} {B : Y → RunView J VB EB}
    {C : Z → RunView K VC EC}
    {domain : X → Prop} {acceptB : Y → Prop} {acceptC : Z → Prop}
    {R : X → Y → VA → VB → Prop} {S : Y → Z → VB → VC → Prop}
    {namedB : Y → EB → Prop} {namedC : Z → EC → Prop}
    (F : DeclaredPassage (EF := EF) a b A B domain acceptB R namedB)
    (G : DeclaredPassage (EF := EG) b c B C acceptB acceptC S namedC) :
    DeclaredPassage (EF := Sum EF EG) a c A C domain acceptC
      (PathRel F.map G.map R S) namedC where
  map := namedSeq F.map G.map
  laws := indexedRelHopOn_seq a b c A B C F.map G.map acceptB acceptC
    R S namedB namedC domain F.laws G.laws

theorem comp_laws {X Y Z I J K VA VB VC EA EB EC EF EG : Type}
    {a : BudgetOrder I} {b : BudgetOrder J} {c : BudgetOrder K}
    {A : X → RunView I VA EA} {B : Y → RunView J VB EB}
    {C : Z → RunView K VC EC}
    {domain : X → Prop} {acceptB : Y → Prop} {acceptC : Z → Prop}
    {R : X → Y → VA → VB → Prop} {S : Y → Z → VB → VC → Prop}
    {namedB : Y → EB → Prop} {namedC : Z → EC → Prop}
    (F : DeclaredPassage (EF := EF) a b A B domain acceptB R namedB)
    (G : DeclaredPassage (EF := EG) b c B C acceptB acceptC S namedC) :
    IndexedRelHopOn a c A C (namedSeq F.map G.map) acceptC
      (PathRel F.map G.map R S) namedC domain :=
  (F.comp G).laws

end DeclaredPassage

/-- Reporting a native runtime refusal keeps the original name as evidence and
requires a declared classification map. This is not cross-budget transport. -/
theorem report_runtime_refusal {I J VA VB EA EB EReport : Type}
    {a : BudgetOrder I} {b : BudgetOrder J}
    {A : RunView I VA EA} {B : RunView J VB EB}
    {g : FuelBound a b} {R : VA → VB → Prop}
    {allowed : EB → Prop} {reported : EReport → Prop}
    (h : RunRefines a b A B g R allowed)
    (names : NameMap allowed reported) (j : J) (e : EB)
    (he : B.refusal j e) :
    ∃ native, native = e ∧ allowed native ∧ reported (names.map native) :=
  ⟨e, rfl, h.named j e he, names.preserves e (h.named j e he)⟩

/-- A stronger, optional passage law for transporting actual runtime refusals.
The caller supplies the index relation and exact name map. Indexed adequacy
and value soundness alone do not manufacture this law. -/
def RefusalTransport {I J VA VB EA EB : Type}
    (A : RunView I VA EA) (B : RunView J VB EB)
    (indices : I → J → Prop) (names : EA → EB) : Prop :=
  ∀ i j e, indices i j → A.refusal i e → B.refusal j (names e)

/-- Runtime refusal transport composes through the declared index witness and
by exact name-map composition; equality of the budgets is not required. -/
theorem refusalTransport_seq {I J K VA VB VC EA EB EC : Type}
    (A : RunView I VA EA) (B : RunView J VB EB) (C : RunView K VC EC)
    (ij : I → J → Prop) (jk : J → K → Prop)
    (ab : EA → EB) (bc : EB → EC)
    (hAB : RefusalTransport A B ij ab)
    (hBC : RefusalTransport B C jk bc) :
    RefusalTransport A C (RelComp ij jk) (fun e => bc (ab e)) := by
  intro i k e hik he
  obtain ⟨j, hij, hjk⟩ := hik
  exact hBC j k (ab e) hjk (hAB i j e hij he)

end NfCompose.Indexed

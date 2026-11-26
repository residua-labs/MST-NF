import MSTNF.algorithms.MSTNFIndexedRelationalHopMWE

/-!
The original relHopOn_seq statement is recovered from indexed composition.
The original composition theorem is not invoked by this proof.
The source class predicate remains arbitrary; source admission is not added.
-/
namespace NfCompose.Indexed
open MSTNecessityExecModelMWE

/-- Legacy Option arrows gain one explicit absence name. -/
def legacyNamedOption {X : Type} : Option X → Except Unit X
  | none => .error ()
  | some x => .ok x

theorem legacyNamedOption_ok_iff {X : Type} (o : Option X) (x : X) :
    legacyNamedOption o = .ok x ↔ o = some x := by
  cases o <;> simp [legacyNamedOption]

theorem legacyBind_some_iff {X Y : Type} (o : Option X)
    (f : X → Option Y) (y : Y) :
    o.bind f = some y ↔ ∃ x, o = some x ∧ f x = some y := by
  cases o <;> simp [Option.bind]

/-- Constant runs use the identity bound, have no runtime refusal, and retain
the whole legacy outcome as their value. The converse reads adequacy at one
actual source index, so an empty index type cannot make the claim vacuous. -/
theorem indexedRelHopAt_constant_iff {X Y VA VB EF : Type}
    (valA : X → VA) (valB : Y → VB) (F : X → Except EF Y)
    (accept : Y → Prop) (R : X → Y → VA → VB → Prop) (x : X) :
    IndexedRelHopAt natBudget natBudget
      (fun x => RunView.constant Nat (valA x))
      (fun y => RunView.constant Nat (valB y))
      F accept R (fun _ _ => False) x ↔
      ∃ y, F x = .ok y ∧ accept y ∧ R x y (valA x) (valB y) := by
  constructor
  · rintro ⟨y, hf, hy, g, hrun⟩
    exact ⟨y, hf, hy,
      (RunRefines.constant_iff natBudget natBudget 0 g
        (valA x) (valB y) (R x y) (fun _ => False)).mp hrun⟩
  · rintro ⟨y, hf, hy, hr⟩
    refine ⟨y, hf, hy, FuelBound.id natBudget, ?_⟩
    exact (RunRefines.constant_iff natBudget natBudget 0
      (FuelBound.id natBudget) (valA x) (valB y) (R x y)
      (fun _ => False)).mpr hr

/-- Select from the existing model; no representative is chosen externally. -/
def legacyClassArrow (A B : ExecModel) (F : A.Rep → Option B.Raw) :
    A.Class → Except Unit B.Raw :=
  fun c => legacyNamedOption ((A.sigma c).bind F)

/-- Enter the following hop through that model's actual raw-to-class map. -/
def legacyRawArrow (A B : ExecModel) (F : A.Rep → Option B.Raw) :
    A.Raw → Except Unit B.Raw :=
  fun a => legacyClassArrow A B F (A.q a)

/-- The generalized pointwise assertion is exactly the old assertion on
constant runs, even when the source class is not admitted. -/
theorem relHopAt_indexed_iff (A B : ExecModel)
    (F : A.Rep → Option B.Raw) (R : A.Outcome → B.Outcome → Prop)
    (c : A.Class) :
    IndexedRelHopAt natBudget natBudget
      (fun c => RunView.constant Nat (A.evalClass c))
      (fun b => RunView.constant Nat (B.evalRaw b))
      (legacyClassArrow A B F)
      (fun b => B.admissible (B.q b) = true)
      (fun _ _ => R) (fun _ _ => False) c ↔
      RelHopAt A B F R c := by
  rw [indexedRelHopAt_constant_iff]
  constructor
  · rintro ⟨b, hf, hb, hr⟩
    have hbind : (A.sigma c).bind F = some b :=
      (legacyNamedOption_ok_iff _ _).mp hf
    obtain ⟨p, hp, hF⟩ := (legacyBind_some_iff _ _ _).mp hbind
    exact ⟨p, b, hp, hF, hb, hr⟩
  · rintro ⟨p, b, hp, hF, hb, hr⟩
    refine ⟨b, ?_, hb, hr⟩
    simp [legacyClassArrow, hp, hF, legacyNamedOption]

/-- The existing quotient law aligns the middle raw evaluator with the class
evaluator consumed by RelHopCorrect. This adds no full-profile hypothesis. -/
theorem relHopCorrect_indexed_raw (A B : ExecModel)
    (F : A.Rep → Option B.Raw) (R : A.Outcome → B.Outcome → Prop)
    (hqA : quotientFactorization A) (h : RelHopCorrect A B F R) :
    ∀ a, A.admissible (A.q a) = true →
      IndexedRelHopAt natBudget natBudget
        (fun a => RunView.constant Nat (A.evalRaw a))
        (fun b => RunView.constant Nat (B.evalRaw b))
        (legacyRawArrow A B F)
        (fun b => B.admissible (B.q b) = true)
        (fun _ _ => R) (fun _ _ => False) a := by
  intro a ha
  obtain ⟨p, b, hp, hf, hb, hr⟩ := h (A.q a) ⟨a, rfl⟩ ha
  apply (indexedRelHopAt_constant_iff A.evalRaw B.evalRaw
    (legacyRawArrow A B F) (fun b => B.admissible (B.q b) = true)
    (fun _ _ => R) a).mpr
  refine ⟨b, ?_, hb, ?_⟩
  · simp [legacyRawArrow, legacyClassArrow, hp, hf, legacyNamedOption]
  · rw [hqA a]
    exact hr

end NfCompose.Indexed

namespace NfCompose
open MSTNecessityExecModelMWE
open Indexed

/-- The exact old relHopOn_seq statement, obtained from indexed composition.
In particular, the old arbitrary source predicate P, canonical middle
selection, and sole quotient-factorization hypothesis are retained. -/
theorem relHopOn_seq_indexed (A B C : ExecModel)
    (F : A.Rep → Option B.Raw) (G : B.Rep → Option C.Raw)
    (R : A.Outcome → B.Outcome → Prop) (S : B.Outcome → C.Outcome → Prop)
    (P : A.Class → Prop) (hqB : quotientFactorization B)
    (hAB : RelHopOn A B F R P) (hBC : RelHopCorrect B C G S) :
    RelHopOn A C (partialHopSeq B F G) (RelComp R S) P := by
  intro c hc hp
  have hfirst := (relHopAt_indexed_iff A B F R c).mpr (hAB c hc hp)
  have hsecond := relHopCorrect_indexed_raw B C G S hqB hBC
  have hseq := indexedRelHopAt_seq natBudget natBudget natBudget
    (fun c => RunView.constant Nat (A.evalClass c))
    (fun b => RunView.constant Nat (B.evalRaw b))
    (fun d => RunView.constant Nat (C.evalRaw d))
    (legacyClassArrow A B F) (legacyRawArrow B C G)
    (fun b => B.admissible (B.q b) = true)
    (fun d => C.admissible (C.q d) = true)
    (fun _ _ => R) (fun _ _ => S)
    (fun _ _ => False) (fun _ _ => False) c hfirst hsecond
  obtain ⟨d, _harrow, hd, hpath⟩ :=
    (indexedRelHopAt_constant_iff A.evalClass C.evalRaw
      (namedSeq (legacyClassArrow A B F) (legacyRawArrow B C G))
      (fun d => C.admissible (C.q d) = true)
      (PathRel (legacyClassArrow A B F) (legacyRawArrow B C G)
        (fun _ _ => R) (fun _ _ => S)) c).mp hseq
  obtain ⟨b, vb, hFb, hGd, hR, hS⟩ := hpath
  have hFbind : (A.sigma c).bind F = some b :=
    (legacyNamedOption_ok_iff _ _).mp hFb
  have hGbind : (B.sigma (B.q b)).bind G = some d :=
    (legacyNamedOption_ok_iff _ _).mp hGd
  obtain ⟨p, hsp, hF⟩ := (legacyBind_some_iff _ _ _).mp hFbind
  obtain ⟨q, hsq, hG⟩ := (legacyBind_some_iff _ _ _).mp hGbind
  refine ⟨p, d, hsp, ?_, hd, vb, hR, hS⟩
  simp [partialHopSeq, hF, hsq, hG]

end NfCompose

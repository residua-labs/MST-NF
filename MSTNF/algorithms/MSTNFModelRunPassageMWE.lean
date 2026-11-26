import MSTNF.algorithms.MSTNFIndexedRelationalHopMWE

/-!
Carrier passages anchored to the imported model family.
-/

set_option autoImplicit false

namespace NfCompose.Indexed
open MSTNecessityExecModelMWE

/-- The native evaluator and its value/refusal decoding are both explicit.
Fam keeps the existing model's carriers, admission, quotient and selector.
The decoder is a declaration: anchoring it to Fam does not by itself certify
that it faithfully distinguishes every native outcome. -/
def familyRawView {I V E : Type} (L : Fam I)
    (isValue : L.Outcome → V → Prop) (isRefusal : L.Outcome → E → Prop)
    (raw : L.Raw) : RunView I V E where
  value := fun i v => isValue (L.runRaw i raw) v
  refusal := fun i e => isRefusal (L.runRaw i raw) e

def familyClassView {I V E : Type} (L : Fam I)
    (isValue : L.Outcome → V → Prop) (isRefusal : L.Outcome → E → Prop)
    (cls : L.Class) : RunView I V E where
  value := fun i v => isValue (L.runClass i cls) v
  refusal := fun i e => isRefusal (L.runClass i cls) e

/-- A selected representative is interpreted through its recorded class.
The pinned ExecModel does not provide a separate evalRep operation. -/
def familySelectedView {I V E : Type} (L : Fam I) (i₀ : I)
    (isValue : L.Outcome → V → Prop) (isRefusal : L.Outcome → E → Prop)
    (s : Selection (L.model i₀)) : RunView I V E :=
  familyClassView L isValue isRefusal (L.q s.raw)

theorem family_raw_class_value {I V E : Type} (L : Fam I)
    (hq : L.qf) (isValue : L.Outcome → V → Prop)
    (isRefusal : L.Outcome → E → Prop) (raw : L.Raw) (i : I) (v : V) :
    (familyRawView L isValue isRefusal raw).value i v ↔
      (familyClassView L isValue isRefusal (L.q raw)).value i v := by
  change isValue (L.runRaw i raw) v ↔ isValue (L.runClass i (L.q raw)) v
  rw [hq i raw]

theorem family_raw_class_refusal {I V E : Type} (L : Fam I)
    (hq : L.qf) (isValue : L.Outcome → V → Prop)
    (isRefusal : L.Outcome → E → Prop) (raw : L.Raw) (i : I) (e : E) :
    (familyRawView L isValue isRefusal raw).refusal i e ↔
      (familyClassView L isValue isRefusal (L.q raw)).refusal i e := by
  change isRefusal (L.runRaw i raw) e ↔ isRefusal (L.runClass i (L.q raw)) e
  rw [hq i raw]

/-- An external artifact enters the already-declared model's Raw.
The target-domain predicate can retain a fragment condition in addition
to the model's mandatory admission condition. This is a fixed-family adapter.
For artifact-dependent entry/arguments/mode/nImg, instantiate a context fiber
or retain context in the generic carrier; this adapter does not change L. -/
abbrev RawRunPassage {X I J VA VB EA EB EF : Type}
    (a : BudgetOrder I) (b : BudgetOrder J)
    (A : X → RunView I VA EA) (L : Fam J)
    (isValue : L.Outcome → VB → Prop) (isRefusal : L.Outcome → EB → Prop)
    (domain : X → Prop) (targetDomain : L.Raw → Prop)
    (R : X → L.Raw → VA → VB → Prop) (named : L.Raw → EB → Prop) :=
  DeclaredPassage (EF := EF) a b A (familyRawView L isValue isRefusal)
    domain (fun raw => L.admissible (L.q raw) = true ∧ targetDomain raw)
    R named

/-- An outgoing map genuinely consumes Rep. A selected-class witness carries
the semantics and the domain; identical Raw and Rep carrier types alone do
not justify a representative-run equation. -/
structure RepresentativeRunPassage {Y I J VA VB EA EB EF : Type}
    (a : BudgetOrder I) (b : BudgetOrder J) (L : Fam I) (i₀ : I)
    (isValue : L.Outcome → VA → Prop) (isRefusal : L.Outcome → EA → Prop)
    (B : Y → RunView J VB EB)
    (domain : Selection (L.model i₀) → Prop) (accept : Y → Prop)
    (R : Selection (L.model i₀) → Y → VA → VB → Prop)
    (named : Y → EB → Prop) where
  map : L.Rep → Except EF Y
  laws : IndexedRelHopOn a b (familySelectedView L i₀ isValue isRefusal)
    B (fun s => map s.rep) accept R named domain

/-- Only canonical selection and the same-family quotient law are automatic.
A preceding Image-to-Raw declaration must already have proved its own
entry/arguments/mode/nImg, observation, admission and indexed-run obligations. -/
theorem rawPassage_select {X I J VA VB EA EB EF : Type}
    (a : BudgetOrder I) (b : BudgetOrder J)
    (A : X → RunView I VA EA) (L : Fam J) (j₀ : J)
    (isValue : L.Outcome → VB → Prop) (isRefusal : L.Outcome → EB → Prop)
    (domain : X → Prop) (targetDomain : L.Raw → Prop)
    (R : X → L.Raw → VA → VB → Prop) (named : L.Raw → EB → Prop)
    (P : RawRunPassage (EF := EF) a b A L isValue isRefusal
      domain targetDomain R named)
    (hq : L.qf) (hp : representativePrecision (L.model j₀)) :
    IndexedRelHopOn a b A (familySelectedView L j₀ isValue isRefusal)
      (namedSeq P.map (selectRaw (L.model j₀)))
      (fun s => targetDomain s.raw)
      (fun x s => R x s.raw) (fun s => named s.raw) domain := by
  intro x hx
  obtain ⟨raw, hf, ha, g, hr⟩ := P.laws x hx
  obtain ⟨s, hs⟩ := selectRaw_exists (L.model j₀) hp raw ha.1
  have hraw : s.raw = raw := selectRaw_raw (L.model j₀) raw s hs
  refine ⟨s, namedSeq_ok P.map (selectRaw (L.model j₀)) x raw s hf hs,
    ?_, g, ?_⟩
  · change targetDomain s.raw
    rw [hraw]
    exact ha.2
  · have hv : ∀ j v,
        (familyRawView L isValue isRefusal raw).value j v ↔
          (familySelectedView L j₀ isValue isRefusal s).value j v := by
      intro j v
      change isValue (L.runRaw j raw) v ↔
        isValue (L.runClass j (L.q s.raw)) v
      rw [hraw, hq j raw]
    have he : ∀ j e,
        (familyRawView L isValue isRefusal raw).refusal j e ↔
          (familySelectedView L j₀ isValue isRefusal s).refusal j e := by
      intro j e
      change isRefusal (L.runRaw j raw) e ↔
        isRefusal (L.runClass j (L.q s.raw)) e
      rw [hraw, hq j raw]
    have ht := RunRefines.target_transport hv he hr
    simpa only [hraw] using ht

namespace RawRunPassage

def toSelection {X I J VA VB EA EB EF : Type}
    {a : BudgetOrder I} {b : BudgetOrder J}
    {A : X → RunView I VA EA} {L : Fam J} (j₀ : J)
    {isValue : L.Outcome → VB → Prop} {isRefusal : L.Outcome → EB → Prop}
    {domain : X → Prop} {targetDomain : L.Raw → Prop}
    {R : X → L.Raw → VA → VB → Prop} {named : L.Raw → EB → Prop}
    (P : RawRunPassage (EF := EF) a b A L isValue isRefusal
      domain targetDomain R named)
    (hq : L.qf) (hp : representativePrecision (L.model j₀)) :
    DeclaredPassage (EF := Sum EF (SelectionError (L.model j₀))) a b A
      (familySelectedView L j₀ isValue isRefusal) domain
      (fun s => targetDomain s.raw)
      (fun x s => R x s.raw) (fun s => named s.raw) where
  map := namedSeq P.map (selectRaw (L.model j₀))
  laws := rawPassage_select a b A L j₀ isValue isRefusal domain targetDomain
    R named P hq hp

end RawRunPassage

namespace RepresentativeRunPassage

def asDeclared {Y I J VA VB EA EB EF : Type}
    {a : BudgetOrder I} {b : BudgetOrder J} {L : Fam I} {i₀ : I}
    {isValue : L.Outcome → VA → Prop} {isRefusal : L.Outcome → EA → Prop}
    {B : Y → RunView J VB EB}
    {domain : Selection (L.model i₀) → Prop} {accept : Y → Prop}
    {R : Selection (L.model i₀) → Y → VA → VB → Prop}
    {named : Y → EB → Prop}
    (P : RepresentativeRunPassage (EF := EF) a b L i₀ isValue isRefusal
      B domain accept R named) :
    DeclaredPassage (EF := EF) a b (familySelectedView L i₀ isValue isRefusal)
      B domain accept R named where
  map := fun s => P.map s.rep
  laws := P.laws

end RepresentativeRunPassage

/-- The actual downstream arrow receives the representative selected from the
actual intermediate raw. A caller can then apply DeclaredPassage.comp to the
two declarations, retaining their value relation and composed fuel bound. -/
theorem raw_rep_arrow_ok_iff {X Y I E1 E2 : Type}
    (L : Fam I) (i₀ : I) (F : X → Except E1 L.Raw)
    (G : L.Rep → Except E2 Y) (x : X) (y : Y) :
    namedSeq (namedSeq F (selectRaw (L.model i₀)))
      (fun s => G s.rep) x = .ok y ↔
    ∃ raw s, F x = .ok raw ∧
      selectRaw (L.model i₀) raw = .ok s ∧
      L.sigma (L.q raw) = some s.rep ∧ G s.rep = .ok y := by
  constructor
  · intro h
    obtain ⟨s, hfirst, hG⟩ :=
      (namedSeq_ok_iff (namedSeq F (selectRaw (L.model i₀)))
        (fun s => G s.rep) x y).mp h
    obtain ⟨raw, hF, hs⟩ :=
      (namedSeq_ok_iff F (selectRaw (L.model i₀)) x s).mp hfirst
    exact ⟨raw, s, hF, hs, selectRaw_selected (L.model i₀) raw s hs, hG⟩
  · rintro ⟨raw, s, hF, hs, _hselected, hG⟩
    exact namedSeq_ok _ _ x s y
      (namedSeq_ok F (selectRaw (L.model i₀)) x raw s hF hs) hG

end NfCompose.Indexed

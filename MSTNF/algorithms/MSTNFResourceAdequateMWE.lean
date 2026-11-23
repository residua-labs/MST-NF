import MSTNF.algorithms.MSTNFHopComposeMWE

/-!
# MSTNF Resource Adequate MWE — progress for clocked hops

Mechanization of the generic resource-adequacy part of the paper's
mechanization addendum v0.3 (24 November 2026, sections 1.5–1.7;
addendum sha256
`49c50807a6abad1331d0712fb321966bf5f9d77fc79f693d3567520ba48f119d`).

A clocked hop whose correctness law may always stop on the named resource
residue is vacuous as a realization claim: an implementation that stops on
resources everywhere satisfies it. Progress is therefore stated separately
from the resource-permitting correctness law, and it does not change
`hopCorrect` or `clockCorrectOn` — `AdequateWitness.clock_correct_but_not_adequate`
is a model where the clocked law holds and adequacy fails.

- `resourceAdequate` (H-progress): on an independently specified feasible
  domain `D`, every semantic (non-resource) source observation has some
  target clock with a semantic observation on the translated input. The
  target clock may depend on the input and the source clock; the statement
  is realization only, not safety.
- `resourceAdequateExact`: the stronger direct form that fixes the
  observation through a decoder (`obs (B.runRaw kB (h x)) = A.runRaw kA x`).
- `nondegenerate` (H-witness): the feasible domain has an input with a
  semantic source observation; with it, the all-resource target refutes
  adequacy (`all_resource_not_adequate`), while an empty feasible domain
  makes adequacy vacuous (`resourceAdequate_of_empty`,
  `AdequateWitness.vacuous_adequate_example`).
- Composition (`resourceAdequate_seq`, `resourceAdequateExact_seq`):
  adequacy of two sequential translations composes through the
  feasible-domain image condition `∀ x, D1 x → D2 (h1 x)`; the exact form
  composes through the composed decoder. `AdequateWitness.image_needed` is
  the deletion witness for the image condition.

The layers are the clock-indexed `Fam` of the hop modules; the semantic /
resource split of an outcome is the caller's `lim` predicate, the same
naming used by `clockHopModel`'s resource residue. Resource capacity stays
a fixed context parameter of the statement (the `lim` predicates), not an
increasing clock: more clock fuel is not more memory. The addendum's
pending/done machine distinction is not needed over total layer
observations: at every clock the layer reports an outcome, and "the
observation at `kA` is semantic" is `limA (A.runRaw kA x) = false`.
-/

namespace NfCompose

open MSTNecessityExecModelMWE

/-! ## H-progress -/

/-- H-progress: on the feasible domain `D`, every semantic (non-resource)
    source observation has some target clock with a semantic observation on
    the translated input. Realization form: the target observation is not
    required to equal (a decode of) the source's. -/
def resourceAdequate {KA KB : Type} (A : Fam KA) (B : Fam KB)
    (limA : A.Outcome → Bool) (limB : B.Outcome → Bool)
    (h : A.Raw → B.Raw) (D : A.Raw → Prop) : Prop :=
  ∀ x, D x → ∀ kA, limA (A.runRaw kA x) = false →
    ∃ kB, limB (B.runRaw kB (h x)) = false

/-- the stronger direct form of H-progress: the target's semantic
    observation decodes to the source's. -/
def resourceAdequateExact {KA KB : Type} (A : Fam KA) (B : Fam KB)
    (limA : A.Outcome → Bool) (limB : B.Outcome → Bool)
    (obs : B.Outcome → A.Outcome) (h : A.Raw → B.Raw)
    (D : A.Raw → Prop) : Prop :=
  ∀ x, D x → ∀ kA, limA (A.runRaw kA x) = false →
    ∃ kB, obs (B.runRaw kB (h x)) = A.runRaw kA x ∧
      limB (B.runRaw kB (h x)) = false

/-- the exact form implies the realization form. -/
theorem resourceAdequateExact_stronger {KA KB : Type} (A : Fam KA) (B : Fam KB)
    (limA : A.Outcome → Bool) (limB : B.Outcome → Bool)
    (obs : B.Outcome → A.Outcome) (h : A.Raw → B.Raw) (D : A.Raw → Prop)
    (hex : resourceAdequateExact A B limA limB obs h D) :
    resourceAdequate A B limA limB h D :=
  fun _ hx _ hk => (hex _ hx _ hk).imp fun _ hw => hw.2

/-- sequential composition of H-progress through the feasible-domain image
    condition: if `h1` is adequate on `D1`, `h2` is adequate on `D2`, and
    `h1` maps `D1` into `D2`, then `h2 ∘ h1` is adequate on `D1`. -/
theorem resourceAdequate_seq {KA KB KC : Type} (A : Fam KA) (B : Fam KB)
    (C : Fam KC) (limA : A.Outcome → Bool) (limB : B.Outcome → Bool)
    (limC : C.Outcome → Bool) (h1 : A.Raw → B.Raw) (h2 : B.Raw → C.Raw)
    (D1 : A.Raw → Prop) (D2 : B.Raw → Prop)
    (a1 : resourceAdequate A B limA limB h1 D1)
    (a2 : resourceAdequate B C limB limC h2 D2)
    (img : ∀ x, D1 x → D2 (h1 x)) :
    resourceAdequate A C limA limC (fun x => h2 (h1 x)) D1 := by
  intro x hx kA hk
  obtain ⟨kB, hb⟩ := a1 x hx kA hk
  obtain ⟨kC, hc⟩ := a2 (h1 x) (img x hx) kB hb
  exact ⟨kC, hc⟩

/-- the exact form composes through the composed decoder. -/
theorem resourceAdequateExact_seq {KA KB KC : Type} (A : Fam KA) (B : Fam KB)
    (C : Fam KC) (limA : A.Outcome → Bool) (limB : B.Outcome → Bool)
    (limC : C.Outcome → Bool) (obs12 : B.Outcome → A.Outcome)
    (obs23 : C.Outcome → B.Outcome) (h1 : A.Raw → B.Raw)
    (h2 : B.Raw → C.Raw) (D1 : A.Raw → Prop) (D2 : B.Raw → Prop)
    (a1 : resourceAdequateExact A B limA limB obs12 h1 D1)
    (a2 : resourceAdequateExact B C limB limC obs23 h2 D2)
    (img : ∀ x, D1 x → D2 (h1 x)) :
    resourceAdequateExact A C limA limC (fun o => obs12 (obs23 o))
      (fun x => h2 (h1 x)) D1 := by
  intro x hx kA hk
  obtain ⟨kB, hb⟩ := a1 x hx kA hk
  obtain ⟨kC, hc⟩ := a2 (h1 x) (img x hx) kB hb.2
  refine ⟨kC, ?_, hc.2⟩
  exact (congrArg obs12 hc.1).trans hb.1

/-! ## The H-witness shape -/

/-- H-witness: the feasible domain is nonempty in semantic observations.
    An instance-level nondegeneracy condition; the composition theorem does
    not require it. -/
def nondegenerate {KA : Type} (A : Fam KA) (limA : A.Outcome → Bool)
    (D : A.Raw → Prop) : Prop :=
  ∃ x, D x ∧ ∃ kA, limA (A.runRaw kA x) = false

/-- on an empty feasible domain, H-progress holds vacuously: it cannot
    alone justify a realization claim. -/
theorem resourceAdequate_of_empty {KA KB : Type} (A : Fam KA) (B : Fam KB)
    (limA : A.Outcome → Bool) (limB : B.Outcome → Bool)
    (h : A.Raw → B.Raw) (D : A.Raw → Prop) (hD : ∀ x, ¬ D x) :
    resourceAdequate A B limA limB h D :=
  fun x hx => absurd hx (hD x)

/-- the all-resource target (every observation a named resource stop)
    refutes H-progress whenever the feasible domain is nondegenerate: with
    the H-witness, adequacy excludes the implementation that always stops
    on resources. -/
theorem all_resource_not_adequate {KA KB : Type} (A : Fam KA) (B : Fam KB)
    (limA : A.Outcome → Bool) (limB : B.Outcome → Bool)
    (h : A.Raw → B.Raw) (D : A.Raw → Prop)
    (hall : ∀ kB y, limB (B.runRaw kB y) = true)
    (hne : nondegenerate A limA D) :
    ¬ resourceAdequate A B limA limB h D := by
  obtain ⟨x, hx, kA, hk⟩ := hne
  intro had
  obtain ⟨kB, hb⟩ := had x hx kA hk
  rw [hall kB (h x)] at hb
  exact Bool.noConfusion hb

/-! ## Witnesses -/

namespace AdequateWitness

/-- a one-input, one-class layer: every observation is `true`. The
    semantic/resource split is the caller's `lim` predicate, so the same
    layer serves as the semantic source, the semantic middle and the
    all-resource target of the witnesses below. -/
def unitLayer : Fam Unit where
  Raw := Unit
  Class := Unit
  Rep := Unit
  Residue := Unit
  Outcome := Bool
  q := fun _ => ()
  runRaw := fun _ _ => true
  runClass := fun _ _ => true
  admissible := fun _ => true
  rho := fun _ => none
  sigma := fun _ => some ()

/-- the motivating witness: the clocked hop law holds — the target's only
    observation is the named resource stop, so every residue is `none` or
    the resource residue — while H-progress fails on the full feasible
    domain. Resource-permitting correctness and adequacy are independent. -/
theorem clock_correct_but_not_adequate :
    clockHopCorrect unitLayer unitLayer (fun _ => ()) (fun b => b)
        (fun _ _ => false) (fun _ => true) ∧
    ¬ resourceAdequate unitLayer unitLayer (fun _ => false) (fun _ => true)
        (fun _ => ()) (fun _ => True) := by
  constructor
  · intro c _ _ kA
    exact ⟨(), (clock_resourceOk_iff unitLayer unitLayer (fun _ => ())
      (fun b => b) (fun _ _ => false) (fun _ => true) kA () c).mpr
      ⟨(), rfl, rfl, Or.inr rfl⟩⟩
  · exact all_resource_not_adequate unitLayer unitLayer (fun _ => false)
      (fun _ => true) (fun _ => ()) (fun _ => True) (fun _ _ => rfl)
      ⟨(), trivial, (), rfl⟩

/-- an empty feasible domain: adequacy holds vacuously and the domain is
    not nondegenerate — H-progress alone says nothing here. -/
theorem vacuous_adequate_example :
    resourceAdequate unitLayer unitLayer (fun _ => false) (fun _ => true)
        (fun _ => ()) (fun _ => False) ∧
    ¬ nondegenerate unitLayer (fun _ => false) (fun _ => False) := by
  constructor
  · exact resourceAdequate_of_empty unitLayer unitLayer (fun _ => false)
      (fun _ => true) (fun _ => ()) (fun _ => False) (fun x h => h)
  · intro ⟨x, hx, _⟩
    exact hx

/-- the deletion witness for the image condition of
    `resourceAdequate_seq`: both components are adequate (the second
    vacuously, its feasible domain being empty), and the composite through
    an all-resource last layer is refuted. -/
theorem image_needed :
    resourceAdequate unitLayer unitLayer (fun _ => false) (fun _ => false)
        (fun _ => ()) (fun _ => True) ∧
    resourceAdequate unitLayer unitLayer (fun _ => false) (fun _ => true)
        (fun _ => ()) (fun _ => False) ∧
    ¬ resourceAdequate unitLayer unitLayer (fun _ => false) (fun _ => true)
        (fun x => ()) (fun _ => True) := by
  refine ⟨fun _ _ _ _ => ⟨(), rfl⟩, resourceAdequate_of_empty unitLayer
    unitLayer (fun _ => false) (fun _ => true) (fun _ => ()) (fun _ => False)
    (fun x h => h), ?_⟩
  exact all_resource_not_adequate unitLayer unitLayer (fun _ => false)
    (fun _ => true) (fun x => ()) (fun _ => True) (fun _ _ => rfl)
    ⟨(), trivial, (), rfl⟩

end AdequateWitness

end NfCompose

import MSTNF.algorithms.MSTNFVSoundnessConformanceMWE
import MSTNF.algorithms.MSTNFExecutionNoFifthRoleMWE
import MSTNF.algorithms.MSTNFKernelConformanceMWE

/-!
# Concrete ↔ Abstract Lean bridge

Closes the last inspection link in the V + kernel executed-conformance
chain. After the V and kernel conformance modules:

    Python adapter  ≡  concrete Lean boolean mirror  (decide)  ✅
    concrete mirror ≡  abstract source-of-truth Prop  (inspection)    ⟵ this module

For each bridge, this file pairs the existing concrete boolean (e.g.
`hasWitness`, `isEmptyResidue`) with a **direct unfolding** of the abstract
`∀ / ∃`-quantified source-of-truth Prop over the same finite encoding.
The unfolded form is Bool (equivalent to `decide`-ing the abstract Prop
when both sides of the quantifier ranges are Fintype / finite-list);
expressing it as Bool keeps `decide` directly applicable without
manually constructing `Decidable` instances for `∃ x : Fin n, P x`-shaped
existentials (which require Mathlib's `Fintype.decidableExistsFintype`).

The unfoldings are mechanically corresponded to the abstract definitions:

  hasWitness                              ↔  Generic.ExplicitDiagnosticWitness
   (over List (Nat × Bool))                  (over Obj := Fin n, Role := Unit)

  isEmptyResidue / isHasIndependent /     ↔  EmptyResidue / HasIndependent /
   isExhaustive                              Exhaustive
                                            (over Obj := index into list,
                                             Candidate := index into list)

  isSound / isComplete / isExact          ↔  Sound / Complete / Exact
                                            (over Ext := list, Adm := list)

Each "Unfolded" def below transcribes the source-of-truth abstract
definition one-step-at-a-time onto the concrete carrier; the bridge
theorem then asserts the concrete-mirror boolean equals the Unfolded
boolean for every fixture used in the V and kernel conformance modules, via `decide`.

Publication note: the development source proves the three bridge theorems with
`native_decide`; this repository uses `decide` so that the kernel checks them
(no `Lean.ofReduceBool`, replayable by lean4checker). Statements are unchanged.

If any fixture's concrete-mirror boolean disagrees with the Unfolded
abstract boolean, `decide` fails to elaborate → red CI → typed
residue (the concrete mirror's i<j filter or the abstract instantiation
is wrong; STOP, do not fudge).
-/

namespace MSTNFConcreteAbstractEquivMWE

open MSTNFVSoundnessConformanceMWE
open MSTNFKernelConformanceMWE

/-! ## V side -/

/-- Direct unfolding of `Generic.ExplicitDiagnosticWitness` instantiated as
    `Obj := Fin objs.length, Role := Unit, profile := fun i => (objs.get i).1,
     sem := fun _ i => (objs.get i).2 = true`. The `∃ x y : Obj` becomes
    `(List.range n).any (fun i => (List.range n).any (fun j => ...))`.

    Symmetric form: ranges over all (i, j), unlike `hasWitness` which filters
    to i<j as an optimization. The bridge theorem proves both compute the
    same Bool for every fixture. -/
def vAbstractWitnessUnfolded (objs : List (Nat × Bool)) : Bool :=
  let n := objs.length
  let idxs := List.range n
  idxs.any (fun i =>
    idxs.any (fun j =>
      ((objs.get! i).1 == (objs.get! j).1) &&
      ((((objs.get! i).2 == true) && !((objs.get! j).2 == true)) ||
       (((objs.get! j).2 == true) && !((objs.get! i).2 == true)))))

/-- Fixture list — the SAME 10 objects emitted by Python `v_soundness_fixtures.py`. -/
def vAllFixturesObjects : List (List (Nat × Bool)) :=
  [ [(0, true), (1, false), (2, false), (3, false)]
  , [(0, false), (1, true), (2, false), (3, false)]
  , [(0, false), (1, false), (2, true), (3, false)]
  , [(0, false), (1, false), (2, false), (3, true)]
  , [(0, true), (0, false)]
  , [(0, false), (1, true), (1, false), (2, false)]
  , [(0, true), (0, true), (1, false)]
  , []
  , [(7, true)]
  , [(0, true), (1, true), (2, false)]
  ]

/-- V bridge: concrete `hasWitness` ≡ abstract `vAbstractWitnessUnfolded` on
    every fixture used by the V-soundness conformance theorem. -/
theorem v_concrete_eq_abstract_on_all_fixtures :
    vAllFixturesObjects.all (fun objs =>
      hasWitness objs == vAbstractWitnessUnfolded objs) = true := by
  decide

/-! ## Kernel residue side -/

/-- Direct unfolding of `EmptyResidue`: `∀ x : Obj, ¬ Residue x`, where
    `Residue x := ∃ c : Candidate, sem c x ∧ ¬ BaseCovers x`. On the concrete
    encoding (Obj indexed by `objects`, Candidate by `candidates`, sem from
    `semPairs`, BaseCovers from list membership). -/
def residueEmptyUnfolded
    (objects baseCovers : List String) (semPairs : List StrPair) : Bool :=
  objects.all (fun x =>
    !(candidatesExistsSemUnbase x baseCovers semPairs))
where
  /-- ∃ c, sem c x ∧ ¬ BaseCovers x — read off semPairs as "∃ pair (c,x) with
      second component = x" combined with "x is not in baseCovers". -/
  candidatesExistsSemUnbase (x : String) (baseCovers : List String)
                            (semPairs : List StrPair) : Bool :=
    !(baseCovers.contains x) && semPairs.any (fun p => p.2 == x)

/-- Direct unfolding of `HasIndependent`: `∃ c, ∃ x, sem c x ∧ ¬ BaseCovers x`. -/
def residueHasIndependentUnfolded
    (baseCovers : List String) (semPairs : List StrPair) : Bool :=
  semPairs.any (fun p => !baseCovers.contains p.2)

/-- Direct unfolding of `Exhaustive`: `∀ c, ReducibleCandidate c` where
    `ReducibleCandidate c := ∀ x, sem c x → BaseCovers x`. -/
def residueExhaustiveUnfolded
    (objects candidates baseCovers : List String) (semPairs : List StrPair) : Bool :=
  candidates.all (fun c =>
    objects.all (fun x =>
      !(semPairs.contains (c, x)) || baseCovers.contains x))

/-- Residue fixture data — same 4 fixtures as Python emits. -/
structure ResidueData where
  objects : List String
  candidates : List String
  baseCovers : List String
  semPairs : List StrPair
  deriving Repr

def kernelResidueFixturesObjects : List ResidueData :=
  [ { objects := ["o0", "o1", "o2"], candidates := ["c0", "c1"],
      baseCovers := ["o0", "o1", "o2"],
      semPairs := [("c0", "o0"), ("c1", "o1")] }
  , { objects := ["o0", "o1", "o2"], candidates := ["c0", "c1"],
      baseCovers := ["o0"],
      semPairs := [("c0", "o0"), ("c1", "o2")] }
  , { objects := ["o0", "o1"], candidates := ["c0", "c1"],
      baseCovers := [], semPairs := [] }
  , { objects := ["o0", "o1"], candidates := ["c0", "c1"],
      baseCovers := ["o0"],
      semPairs := [("c0", "o1")] }
  ]

/-- Residue bridge: every concrete-mirror predicate equals the abstract Unfolded
    form on every fixture. -/
theorem residue_concrete_eq_abstract_on_all_fixtures :
    kernelResidueFixturesObjects.all (fun f =>
      (isEmptyResidue f.objects f.baseCovers f.semPairs
        == residueEmptyUnfolded f.objects f.baseCovers f.semPairs) &&
      (isHasIndependent f.baseCovers f.semPairs
        == residueHasIndependentUnfolded f.baseCovers f.semPairs) &&
      (isExhaustive f.objects f.candidates f.baseCovers f.semPairs
        == residueExhaustiveUnfolded f.objects f.candidates f.baseCovers f.semPairs))
      = true := by
  decide

/-! ## Kernel CoreObject side -/

/-- Direct unfolding of `Sound`: `∀ x : Ext, x ∈ Fix → x ∈ Adm` where
    `Fix := {x | D x x}`. -/
def coreSoundUnfolded (ext adm : List String) (d : List StrPair) : Bool :=
  ext.all (fun x =>
    !(d.contains (x, x)) || adm.contains x)

/-- Direct unfolding of `Complete`: `∀ x : Adm, x ∈ Fix`. -/
def coreCompleteUnfolded (adm : List String) (d : List StrPair) : Bool :=
  adm.all (fun x => d.contains (x, x))

/-- Direct unfolding of `Exact = Sound ∧ Complete`. -/
def coreExactUnfolded (ext adm : List String) (d : List StrPair) : Bool :=
  coreSoundUnfolded ext adm d && coreCompleteUnfolded adm d

structure CoreData where
  ext : List String
  adm : List String
  d : List StrPair
  deriving Repr

def kernelCoreFixturesObjects : List CoreData :=
  [ { ext := ["a", "b", "c"], adm := ["a", "b"],
      d := [("a", "a"), ("b", "b"), ("c", "a")] }
  , { ext := ["a", "b", "c"], adm := ["a", "b"],
      d := [("a", "a"), ("c", "c"), ("b", "a")] }
  ]

/-- CoreObject bridge. -/
theorem core_concrete_eq_abstract_on_all_fixtures :
    kernelCoreFixturesObjects.all (fun f =>
      (isSound f.ext f.adm f.d == coreSoundUnfolded f.ext f.adm f.d) &&
      (isComplete f.adm f.d == coreCompleteUnfolded f.adm f.d) &&
      (isExact f.ext f.adm f.d == coreExactUnfolded f.ext f.adm f.d))
      = true := by
  decide

end MSTNFConcreteAbstractEquivMWE

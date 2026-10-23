/-!
# MST-NF V-soundness executed conformance

Lean side of the B1-completion executed conformance gate.

Python emits `tools/mstnf_runtime/v_soundness_fixtures.py` →
`{name, objects=[(profile,holds)], python_representable}` triples. The same
encoding is interpreted here, evaluated through a computable boolean form of
`Generic.RoleProfileRepresentation` from
`MSTNFExecutionNoFifthRoleMWE.lean`, and asserted EXACTLY agreeing with
`python_representable` for every fixture (see the bridge theorems in `MSTNFConcreteAbstractEquivMWE`).

Disagreement on any fixture = a real V-soundness bug (the Python micro-verifier
fails to faithfully realize the Lean source-of-truth predicate). Rule:
do not modify either side to force agreement; report it as a typed residue.

Encoding (matches `v_soundness_fixtures.py:FIXTURES`):

    objects = List (Nat × Bool)    -- (profile, holds)
    profile(obj) = obj.1
    sem(obj)     = obj.2
    representable ⟺  no two indices i ≠ j with objects[i].1 = objects[j].1
                  ∧ objects[i].2 ≠ objects[j].2
                  (= no ExplicitDiagnosticWitness on this single-role instance)
-/

namespace MSTNFVSoundnessConformanceMWE

/-- A fixture pinned to a name + the Python V verdict to cross-check against. -/
structure Fixture where
  name : String
  objects : List (Nat × Bool)
  pythonVerdict : Bool
  deriving Repr

/-- Computable boolean form of the diagnostic-witness predicate restricted to
    the single-role concrete encoding. Equivalent to:
    `∃ i j : Fin n, i ≠ j ∧ profile i = profile j ∧ sem i ≠ sem j`. -/
def hasWitness (objects : List (Nat × Bool)) : Bool :=
  let n := objects.length
  let idxs := List.range n
  idxs.any (fun i =>
    idxs.any (fun j =>
      decide (i < j) &&
      (objects.get! i).1 == (objects.get! j).1 &&
      ((objects.get! i).2 != (objects.get! j).2)))

/-- Lean side of `python_representable`: representable ⟺ no diagnostic witness.
    Same shape as `¬ Generic.ExplicitDiagnosticWitness` in
    `MSTNFExecutionNoFifthRoleMWE.lean`, decided on the concrete finite encoding. -/
def isRepresentable (objects : List (Nat × Bool)) : Bool :=
  !hasWitness objects

/-- Per-fixture cross-check: Lean predicate verdict == Python verdict EXACTLY. -/
def checkFixture (f : Fixture) : Bool :=
  isRepresentable f.objects == f.pythonVerdict

/-- All-fixture cross-check (final conformance statement). -/
def allFixturesAgree (fixtures : List Fixture) : Bool :=
  fixtures.all checkFixture

end MSTNFVSoundnessConformanceMWE

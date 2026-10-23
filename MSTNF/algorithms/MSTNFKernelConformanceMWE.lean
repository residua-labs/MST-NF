/-!
# MST-NF kernel-adapter executed conformance

Lean side of the executed conformance between Python adapters
(`residue_schema.py`, `core_object.py`) and the Lean source-of-truth files
(`MSTNF/l1/MSTGenericResidueSkeletonsMWE.lean`, `MSTNF/core/MSTNFObjectMWE.lean`).

Encoding (matches `tools/mstnf_runtime/kernel_conformance_fixtures.py`):

  residue-schema:
    objects   : List String   -- finite Obj sample
    candidates: List String   -- finite Candidate sample
    baseCovers: List String   -- objects x with BaseCovers x = True
    semPairs  : List (String × String)  -- (c, x) pairs with sem c x = True
  All ∀ / ∃ over the sample become enumeration over the finite list — faithful
  by construction (no semantics invented; same reconstruction the JSON encoding
  promises).

  core-object:
    ext : List String                    -- carrier
    adm : List String                    -- elements in Adm
    d   : List (String × String)         -- (p, q) pairs with D p q = True

Cross-side EXACT (no tolerance — R1 applies): for each fixture the Lean
boolean verdicts must equal the corresponding Python verdicts. Disagreement
on any field is a real residue (adapter mis-mirrors Lean) — STOP + report,
do NOT fudge.
-/

namespace MSTNFKernelConformanceMWE

abbrev StrPair := String × String

/-! ## Residue-schema predicates (mirror of MSTGenericResidueSkeletonsMWE.lean) -/

/-- `Residue x` = ∃ c, sem c x ∧ ¬ BaseCovers x. Boolean form over the encoding:
    x is not in `baseCovers` and some `semPair`'s second component equals x. -/
def isResidueAt (baseCovers : List String) (semPairs : List StrPair) (x : String) : Bool :=
  !baseCovers.contains x && semPairs.any (fun p => p.2 == x)

/-- `EmptyResidue` = ∀ x, ¬ Residue x. -/
def isEmptyResidue (objects baseCovers : List String) (semPairs : List StrPair) : Bool :=
  objects.all (fun x => !isResidueAt baseCovers semPairs x)

/-- `HasIndependent` = ∃ c, ∃ x, sem c x ∧ ¬ BaseCovers x. -/
def isHasIndependent (baseCovers : List String) (semPairs : List StrPair) : Bool :=
  semPairs.any (fun p => !baseCovers.contains p.2)

/-- `ReducibleCandidate c` = ∀ x, sem c x → BaseCovers x. -/
def isReducibleCandidate
    (objects baseCovers : List String) (semPairs : List StrPair) (c : String) : Bool :=
  objects.all (fun x =>
    !(semPairs.contains (c, x)) || baseCovers.contains x)

/-- `Exhaustive` = ∀ c, ReducibleCandidate c. -/
def isExhaustive
    (objects candidates baseCovers : List String) (semPairs : List StrPair) : Bool :=
  candidates.all (fun c => isReducibleCandidate objects baseCovers semPairs c)

/-! ## CoreObject predicates (mirror of MSTNFObjectMWE.lean) -/

/-- D is single-valued: ∀ p q₁ q₂, D p q₁ → D p q₂ → q₁ = q₂. -/
def isSingleValued (d : List StrPair) : Bool :=
  d.all (fun pq1 =>
    d.all (fun pq2 =>
      !(pq1.1 == pq2.1) || (pq1.2 == pq2.2)))

/-- `Fix C` = { x ∈ Ext | D x x }. Returned as the ext-ordered list. -/
def fixSet (ext : List String) (d : List StrPair) : List String :=
  ext.filter (fun x => d.contains (x, x))

/-- `Sound` = ∀ x, x ∈ Fix → x ∈ Adm. -/
def isSound (ext adm : List String) (d : List StrPair) : Bool :=
  (fixSet ext d).all (fun x => adm.contains x)

/-- `Complete` = ∀ x, x ∈ Adm → x ∈ Fix. -/
def isComplete (adm : List String) (d : List StrPair) : Bool :=
  adm.all (fun x => d.contains (x, x))

/-- `Exact` = Sound ∧ Complete (= residue-emptiness on both sides). -/
def isExact (ext adm : List String) (d : List StrPair) : Bool :=
  isSound ext adm d && isComplete adm d

/-! ## Fixture structures + per-fixture conformance check -/

structure ResidueFixture where
  name : String
  objects : List String
  candidates : List String
  baseCovers : List String
  semPairs : List StrPair
  pyEmptyResidue : Bool
  pyExhaustive : Bool
  pyHasIndependent : Bool
  deriving Repr

structure CoreObjectFixture where
  name : String
  ext : List String
  adm : List String
  d : List StrPair
  pySingleValued : Bool
  pyFix : List String
  pySound : Bool
  pyComplete : Bool
  pyExact : Bool
  deriving Repr

/-- Cross-side check: Lean verdicts on the encoded finite instance ==
    Python verdicts, field-for-field EXACT. -/
def checkResidueFixture (f : ResidueFixture) : Bool :=
  isEmptyResidue f.objects f.baseCovers f.semPairs == f.pyEmptyResidue
    && isExhaustive f.objects f.candidates f.baseCovers f.semPairs == f.pyExhaustive
    && isHasIndependent f.baseCovers f.semPairs == f.pyHasIndependent

def checkCoreFixture (f : CoreObjectFixture) : Bool :=
  isSingleValued f.d == f.pySingleValued
    && fixSet f.ext f.d == f.pyFix
    && isSound f.ext f.adm f.d == f.pySound
    && isComplete f.adm f.d == f.pyComplete
    && isExact f.ext f.adm f.d == f.pyExact

def allResidueFixturesAgree (fixtures : List ResidueFixture) : Bool :=
  fixtures.all checkResidueFixture

def allCoreFixturesAgree (fixtures : List CoreObjectFixture) : Bool :=
  fixtures.all checkCoreFixture

end MSTNFKernelConformanceMWE

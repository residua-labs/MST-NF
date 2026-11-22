import MSTNF.algorithms.MSTNecessityExecModelMWE

/-!
# MSTNF Finite Instance MWE — paper v0.2 finite demonstrator

Kernel-checked port of the frozen finite-instance specification
(paper v0.2, review r1, 21 November 2026; spec sha256
`732cb16a400c7cd626ef26d7d4337769b6fb2ed3df9a8d5e80189dd08dd8e89b`).

All carriers are finite with decidable equality and explicit `List`
enumerations; `Value = Nat` and `Observation` keep decidable equality
but are not enumerated, matching the spec.  Every expected count in
spec §7 is a closed Boolean statement proved by `decide`; the
quantified laws are proved by finite case analysis.  No
`native_decide`, no `sorry`, no user axioms.

The 32-input core instance is presented as an `ExecModel` over
`MSTNecessityExecModelMWE`; the four laws referenced by the six-input
countermodel suite are the module's own registered definitions
(`quotientFactorization`, `admissibilitySound`, `residueTotality`,
`representativePrecision`).
-/

namespace MSTNFFiniteInstanceMWE

open MSTNecessityExecModelMWE

-- The 1024-pair filters below unfold long list recursions under `decide`.
set_option maxRecDepth 8192

-- ---------------------------------------------------------------------------
-- §1 Finite carriers
-- ---------------------------------------------------------------------------

inductive Verb | lower | upper deriving DecidableEq, Repr
inductive Numeral | n0 | n00 | n1 | n01 | n2 | n02 | n3 | n03 deriving DecidableEq, Repr
inductive Trace | empty | traceA deriving DecidableEq, Repr

structure Raw where
  verb : Verb
  numeral : Numeral
  trace : Trace
  deriving DecidableEq, Repr

abbrev ClassId := Fin 4
abbrev Rep := Raw

inductive Residue | outsideDomain | missingCertificate deriving DecidableEq, Repr

abbrev Value := Nat
/-- `Observation = Sum Value Residue` with constructors named `ok`/`refuse`. -/
abbrev Observation := Sum Value Residue

def ok (v : Value) : Observation := .inl v
def refuse (r : Residue) : Observation := .inr r

/-- Total value table of spec §1; no reference or decision procedure is
    called in its definition. -/
def numeralValue : Numeral → ClassId
  | .n0 => 0 | .n00 => 0 | .n1 => 1 | .n01 => 1
  | .n2 => 2 | .n02 => 2 | .n3 => 3 | .n03 => 3

def q (r : Raw) : ClassId := numeralValue r.numeral

def shortNumeral (c : ClassId) : Numeral :=
  match c.val with | 0 => .n0 | 1 => .n1 | 2 => .n2 | _ => .n3

/-- Canonical raw input of class `c`: `lower`, the short numeral, `empty`. -/
def canonical (c : ClassId) : Raw := ⟨.lower, shortNumeral c, .empty⟩

-- ---------------------------------------------------------------------------
-- §2 Reference, decision, source interpretation
-- ---------------------------------------------------------------------------

def admissible (c : ClassId) : Bool :=
  match c.val with | 0 | 1 => true | _ => false

def sigma (c : ClassId) : Option Rep :=
  match c.val with
  | 0 => some (canonical 0) | 1 => some (canonical 1) | _ => none

def rho (c : ClassId) : Option Residue :=
  match c.val with
  | 2 => some .outsideDomain | 3 => some .missingCertificate | _ => none

def v (rep : Rep) : Value := (numeralValue rep.numeral).val + 1
def iota (rep : Rep) : Raw := rep

/-- Decision on a class: representative payload on admission, residue on
    refusal (spec §2 table). -/
def D (c : ClassId) : Sum Rep Residue :=
  match c.val with
  | 0 => .inl (canonical 0)
  | 1 => .inl (canonical 1)
  | 2 => .inr .outsideDomain
  | _ => .inr .missingCertificate

/-- Lift of `v` over the representative payload; residue constructors are
    preserved exactly. -/
def liftV : Sum Rep Residue → Observation
  | .inl rep => ok (v rep)
  | .inr r => refuse r

def evalClass (c : ClassId) : Observation := liftV (D c)

/-- Reference: a direct case analysis on `numeralValue`, not defined as
    `interpret (D (q raw))` (spec §2). -/
def O (r : Raw) : Observation :=
  match (numeralValue r.numeral).val with
  | 0 => ok 1
  | 1 => ok 2
  | 2 => refuse .outsideDomain
  | _ => refuse .missingCertificate

/-- The 32-input core instance as an `ExecModel`. -/
def coreModel : ExecModel where
  Raw := Raw
  Class := ClassId
  Rep := Rep
  Residue := Residue
  Outcome := Observation
  q := q
  evalRaw := O
  evalClass := evalClass
  admissible := admissible
  rho := rho
  sigma := sigma

-- ---------------------------------------------------------------------------
-- Finite enumerations (spec §1: carriers enumerated; Value/Observation not)
-- ---------------------------------------------------------------------------

def allVerb : List Verb := [.lower, .upper]
def allNumeral : List Numeral :=
  [.n0, .n00, .n1, .n01, .n2, .n02, .n3, .n03]
def allTrace : List Trace := [.empty, .traceA]
def allRaw : List Raw :=
  allVerb.flatMap fun v => allNumeral.flatMap fun n =>
    allTrace.map fun t => ⟨v, n, t⟩
def allClass : List ClassId := [0, 1, 2, 3]
def allRep : List Rep := allRaw
def allResidue : List Residue := [.outsideDomain, .missingCertificate]

theorem allVerb_complete : ∀ x : Verb, x ∈ allVerb := by
  intro x; cases x <;> decide
theorem allNumeral_complete : ∀ x : Numeral, x ∈ allNumeral := by
  intro x; cases x <;> decide
theorem allTrace_complete : ∀ x : Trace, x ∈ allTrace := by
  intro x; cases x <;> decide
theorem allRaw_complete : ∀ r : Raw, r ∈ allRaw := by
  intro r; cases r with | mk v n t => cases v <;> cases n <;> cases t <;> decide
theorem allRaw_nodup : allRaw.Nodup := by decide
theorem allClass_complete : ∀ c : ClassId, c ∈ allClass := by
  intro c
  cases c using Fin.cases with
  | zero => decide
  | succ i =>
    cases i using Fin.cases with
    | zero => decide
    | succ j =>
      cases j using Fin.cases with
      | zero => decide
      | succ k =>
        cases k using Fin.cases with
        | zero => decide
        | succ l => exact absurd l.isLt (Nat.not_lt_zero _)
theorem allResidue_complete : ∀ x : Residue, x ∈ allResidue := by
  intro x; cases x <;> decide

def rawPairs : List (Raw × Raw) :=
  allRaw.flatMap fun x => allRaw.map fun y => (x, y)

theorem rawPairs_complete : ∀ p : Raw × Raw, p ∈ rawPairs := by
  intro p; cases p with | mk a b =>
  apply List.mem_flatMap.mpr
  exact ⟨a, allRaw_complete a,
    List.mem_map.mpr ⟨b, allRaw_complete b, rfl⟩⟩

-- ---------------------------------------------------------------------------
-- §7 checks: cardinalities, fibers, admission split, pair counts
-- ---------------------------------------------------------------------------

theorem check_raw_cardinality : allRaw.length = 32 := by decide

def isActive (c : ClassId) : Bool :=
  allRaw.any fun r => decide (q r = c)

theorem check_active_classes :
    (allClass.filter isActive).length = 4 := by decide

theorem check_fiber_cardinality :
    allClass.all (fun c =>
      decide ((allRaw.filter (fun r => decide (q r = c))).length = 8)) = true := by
  decide

/-- Reference equals the lifted decision on every raw input — this is
    `quotientFactorization` of the core instance. -/
theorem check_reference_eq_lifted : quotientFactorization coreModel := by
  intro r; cases r with | mk v n t =>
    cases v <;> cases n <;> cases t <;> rfl

def admitted (r : Raw) : Bool := admissible (q r)

theorem check_admission_split :
    (allRaw.filter admitted).length = 16 ∧
    (allRaw.filter (fun r => !admitted r)).length = 16 := by decide

theorem check_ordered_pairs : rawPairs.length = 1024 := by decide

theorem check_equal_key_pairs :
    (rawPairs.filter (fun p => decide (q p.1 = q p.2))).length = 256 := by decide

/-- Section and normalization on every admitted input: the representative
    of the input's class is a raw of the same class, and evaluating the
    reference on it reproduces the input's observation. -/
def sectionStable (r : Raw) : Bool :=
  match sigma (q r) with
  | some rep =>
      decide (q (iota rep) = q r) && decide (O (iota rep) = O r)
  | none => false

theorem check_section_normalization :
    (allRaw.filter admitted).all sectionStable = true := by decide

/-- The remaining Tier-1 laws of the core instance. -/
theorem core_admissibilitySound : admissibilitySound coreModel := by
  intro c rep h
  cases c using Fin.cases with
  | zero => rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      cases j using Fin.cases with
      | zero => exact Option.noConfusion h
      | succ k =>
        cases k using Fin.cases with
        | zero => exact Option.noConfusion h
        | succ l => exact absurd l.isLt (Nat.not_lt_zero _)

theorem core_residueTotality : residueTotality coreModel := by
  intro c hact hadm
  cases c using Fin.cases with
  | zero => exact absurd hadm (by decide)
  | succ i =>
    cases i using Fin.cases with
    | zero => exact absurd hadm (by decide)
    | succ j =>
      cases j using Fin.cases with
      | zero => intro e; exact Option.noConfusion e
      | succ k =>
        cases k using Fin.cases with
        | zero => intro e; exact Option.noConfusion e
        | succ l => exact absurd l.isLt (Nat.not_lt_zero _)

theorem core_representativePrecision : representativePrecision coreModel := by
  intro c hact hadm
  cases c using Fin.cases with
  | zero => intro e; exact Option.noConfusion e
  | succ i =>
    cases i using Fin.cases with
    | zero => intro e; exact Option.noConfusion e
    | succ j =>
      cases j using Fin.cases with
      | zero => exact absurd hadm (by decide)
      | succ k =>
        cases k using Fin.cases with
        | zero => exact absurd hadm (by decide)
        | succ l => exact absurd l.isLt (Nat.not_lt_zero _)

theorem core_hasMSTNFProfile : hasMSTNFProfile coreModel :=
  ⟨check_reference_eq_lifted, core_admissibilitySound,
    core_residueTotality, core_representativePrecision⟩

/-- Two distinct admitted inputs with the same key (spec §2). -/
theorem same_key_distinct_admitted :
    (⟨.lower, .n0, .empty⟩ : Raw) ≠ ⟨.upper, .n00, .traceA⟩ ∧
    q ⟨.lower, .n0, .empty⟩ = q ⟨.upper, .n00, .traceA⟩ :=
  ⟨by decide, rfl⟩

/-- Two distinct refused inputs with the same key (spec §2). -/
theorem same_key_distinct_refused :
    (⟨.lower, .n2, .empty⟩ : Raw) ≠ ⟨.upper, .n02, .traceA⟩ ∧
    q ⟨.lower, .n2, .empty⟩ = q ⟨.upper, .n02, .traceA⟩ :=
  ⟨by decide, rfl⟩

-- ---------------------------------------------------------------------------
-- §3 Sequential composition: retain both representatives
-- ---------------------------------------------------------------------------

inductive Stage2Residue | oddIntermediate deriving DecidableEq

inductive SeqResidue
  | first (r : Residue) | second (r : Stage2Residue)
  deriving DecidableEq

/-- Stage-2 decision on `Raw2 = Nat`: even `n` is its own representative. -/
def D2 (n : Nat) : Sum Nat Stage2Residue :=
  if n % 2 = 0 then .inl n else .inr .oddIntermediate

/-- Stage-2 reference: `ok (2*n)` on even, `oddIntermediate` otherwise. -/
def O2 (n : Nat) : Sum Nat Stage2Residue :=
  if n % 2 = 0 then .inl (2 * n) else .inr .oddIntermediate

abbrev SeqObs := Sum Nat SeqResidue

/-- Reference pipeline: run `O`, then `O2` on the successful value. -/
def compositeO (r : Raw) : SeqObs :=
  match O r with
  | .inl n => match O2 n with
    | .inl w => .inl w
    | .inr e => .inr (.second e)
  | .inr e => .inr (.first e)

/-- Composite decision: stage-1 representative, then stage-2 decision on
    its value; `Rep21 = Rep × Nat`. -/
def compositeD (c : ClassId) : Sum (Rep × Nat) SeqResidue :=
  match D c with
  | .inl rep => match D2 (v rep) with
    | .inl rep2 => .inl (rep, rep2)
    | .inr e2 => .inr (.second e2)
  | .inr e1 => .inr (.first e1)

def v21 (p : Rep × Nat) : Nat := 2 * p.2
def iota21 (p : Rep × Nat) : Raw := iota p.1

def compositeEval (c : ClassId) : SeqObs :=
  match compositeD c with
  | .inl p => .inl (v21 p)
  | .inr e => .inr e

theorem check_composite_reference :
    ∀ r : Raw, compositeO r = compositeEval (q r) := by
  intro r; cases r with | mk v n t =>
    cases v <;> cases n <;> cases t <;> decide

def isSeqOk : SeqObs → Bool
  | .inl _ => true | .inr _ => false

theorem check_composite_outcomes :
    (allRaw.filter (fun r => isSeqOk (compositeO r))).length = 8 ∧
    (allRaw.filter (fun r => !isSeqOk (compositeO r))).length = 24 := by decide

/-- The composite representative of a successful raw: the stage-1
    representative paired with the stage-2 representative of its value. -/
def compositeRep (r : Raw) : Option (Rep × Nat) :=
  match O r with
  | .inl n => match D2 n with
    | .inl rep2 => match sigma (q r) with
      | some rep1 => some (rep1, rep2)
      | none => none
    | .inr _ => none
  | .inr _ => none

/-- The composite representative for class 1 is `(canonical 1, 2)`
    (spec §3). -/
theorem composite_rep_on_class1 :
    allRaw.all (fun r =>
      if decide (q r = 1) then
        decide (compositeRep r = some (canonical 1, 2))
      else true) = true := by decide

/-- Composite pair section and stability on every successful input: the
    pair's `iota21` is a raw of the same class and the composite reference
    on it reproduces the input's composite observation. -/
def compositeStable (r : Raw) : Bool :=
  match compositeRep r with
  | some p =>
      decide (q (iota21 p) = q r) &&
        decide (compositeO (iota21 p) = compositeO r)
  | none => false

theorem check_composite_section_stability :
    (allRaw.filter (fun r => isSeqOk (compositeO r))).all compositeStable = true := by
  decide

-- ---------------------------------------------------------------------------
-- §4 Tagged sum and independent product
-- ---------------------------------------------------------------------------

abbrev SumValue := Sum Nat Nat
abbrev SumResidue := Sum Residue Residue
abbrev SumObs := Sum SumValue SumResidue

/-- Tagged-sum reference: the same first-stage instance on either branch,
    branch tag preserved in success and refusal. -/
def taggedO : Sum Raw Raw → SumObs
  | .inl r => match O r with
    | .inl n => .inl (.inl n) | .inr e => .inr (.inl e)
  | .inr r => match O r with
    | .inl n => .inl (.inr n) | .inr e => .inr (.inr e)

def taggedQ : Sum Raw Raw → Sum ClassId ClassId
  | .inl r => .inl (q r) | .inr r => .inr (q r)

def taggedD : Sum ClassId ClassId → Sum (Sum Rep Rep) SumResidue
  | .inl c => match D c with
    | .inl rep => .inl (.inl rep) | .inr e => .inr (.inl e)
  | .inr c => match D c with
    | .inl rep => .inl (.inr rep) | .inr e => .inr (.inr e)

def taggedEval (c : Sum ClassId ClassId) : SumObs :=
  match taggedD c with
  | .inl (.inl rep) => .inl (.inl (v rep))
  | .inl (.inr rep) => .inl (.inr (v rep))
  | .inr (.inl e) => .inr (.inl e)
  | .inr (.inr e) => .inr (.inr e)

def allSum : List (Sum Raw Raw) := allRaw.map .inl ++ allRaw.map .inr

theorem allSum_count : allSum.length = 64 := by decide

theorem check_tagged_sum_reference :
    ∀ s : Sum Raw Raw, taggedO s = taggedEval (taggedQ s) := by
  intro s
  cases s with
  | inl r => cases r with | mk v n t =>
      cases v <;> cases n <;> cases t <;> decide
  | inr r => cases r with | mk v n t =>
      cases v <;> cases n <;> cases t <;> decide

/-- Residues of the independent product: single failures keep their side,
    double failures keep both positions (spec §4). -/
inductive ProductResidue
  | leftOnly (r : Residue) | rightOnly (r : Residue)
  | both (r1 r2 : Residue)
  deriving DecidableEq

abbrev ProdObs := Sum (Nat × Nat) ProductResidue

def productO (p : Raw × Raw) : ProdObs :=
  match O p.1, O p.2 with
  | .inl v1, .inl v2 => .inl (v1, v2)
  | .inl _, .inr e => .inr (.rightOnly e)
  | .inr e, .inl _ => .inr (.leftOnly e)
  | .inr e1, .inr e2 => .inr (.both e1 e2)

def productD (cp : ClassId × ClassId) : Sum (Rep × Rep) ProductResidue :=
  match D cp.1, D cp.2 with
  | .inl r1, .inl r2 => .inl (r1, r2)
  | .inl _, .inr e => .inr (.rightOnly e)
  | .inr e, .inl _ => .inr (.leftOnly e)
  | .inr e1, .inr e2 => .inr (.both e1 e2)

def productEval (cp : ClassId × ClassId) : ProdObs :=
  match productD cp with
  | .inl (r1, r2) => .inl (v r1, v r2)
  | .inr e => .inr e

theorem product_reference_eq_bool :
    rawPairs.all (fun p =>
      decide (productO p = productEval (q p.1, q p.2))) = true := by decide

theorem check_product_reference :
    ∀ p : Raw × Raw, productO p = productEval (q p.1, q p.2) := by
  intro p
  exact of_decide_eq_true
    (List.all_eq_true.mp product_reference_eq_bool p (rawPairs_complete p))

/-- The raw pair failed on both sides. -/
def bothRefused (p : Raw × Raw) : Bool :=
  match O p.1, O p.2 with | .inr _, .inr _ => true | _, _ => false

/-- The product observation keeps both residues. -/
def retainsBoth (p : Raw × Raw) : Bool :=
  match productO p with | .inr (.both _ _) => true | _ => false

theorem check_double_failure :
    (rawPairs.filter bothRefused).length = 256 := by decide

theorem double_failure_retains :
    ∀ p : Raw × Raw, bothRefused p = true →
      ∃ e1 e2, productO p = .inr (.both e1 e2) := by
  intro p h
  match hO1 : O p.1, hO2 : O p.2 with
  | .inr e1, .inr e2 => exact ⟨e1, e2, by simp [productO, hO1, hO2]⟩
  | .inl _, .inr _ => simp [bothRefused, hO1, hO2] at h
  | .inr _, .inl _ => simp [bothRefused, hO1, hO2] at h
  | .inl _, .inl _ => simp [bothRefused, hO1, hO2] at h

-- ---------------------------------------------------------------------------
-- §5 Coarse-key counterexample
-- ---------------------------------------------------------------------------

def coarseClass : ClassId → Option Nat :=
  fun c => match c.val with
    | 0 => some 1 | 1 => some 2 | _ => none

def coarseKey (r : Raw) : Option Nat := coarseClass (q r)

theorem coarse_key_table :
    coarseClass 0 = some 1 ∧ coarseClass 1 = some 2 ∧
      coarseClass 2 = none ∧ coarseClass 3 = none := by decide

/-- Ordered pairs `(x,y)` with equal coarse keys but different
    observations: exactly the class-2 × class-3 cross pairs, both
    orientations — `8*8*2 = 128` (spec §5). -/
theorem check_coarse_mismatch :
    (rawPairs.filter (fun p =>
      decide (coarseKey p.1 = coarseKey p.2) &&
        decide (O p.1 ≠ O p.2))).length = 128 := by decide

-- ---------------------------------------------------------------------------
-- §6 Independent six-input countermodel suite
-- ---------------------------------------------------------------------------

inductive Raw6 | g0 | g1 | b0 | b1 | z0 | z1 deriving DecidableEq
inductive Class3 | G | B | Z deriving DecidableEq
inductive Rep3 | g | bad | z deriving DecidableEq
inductive Residue6 | blocked | spurious deriving DecidableEq

def q6 : Raw6 → Class3
  | .g0 | .g1 => .G | .b0 | .b1 => .B | .z0 | .z1 => .Z

def outcome6 : Class3 → Int
  | .G => 10 | .B => -1 | .Z => 20

/-- Raw reference: each raw input gets its class outcome. -/
def evalRaw6 (r : Raw6) : Int := outcome6 (q6 r)

def a6 : Class3 → Bool
  | .G | .Z => true | .B => false

def sigma6 : Class3 → Option Rep3
  | .G => some .g | .B => none | .Z => some .z

def rho6 : Class3 → Option Residue6
  | .B => some .blocked | _ => none

def iota6 : Rep3 → Raw6
  | .g => .g0 | .bad => .b0 | .z => .z0

def base6 : ExecModel where
  Raw := Raw6
  Class := Class3
  Rep := Rep3
  Residue := Residue6
  Outcome := Int
  q := q6
  evalRaw := evalRaw6
  evalClass := outcome6
  admissible := a6
  rho := rho6
  sigma := sigma6

/-- Residue exclusivity: an admitted class carries no residue. -/
def residueExclusive (M : ExecModel) : Prop :=
  ∀ c : M.Class, M.admissible c = true → M.rho c = none

/-- Specified source section: a representative's `iota` lands in the class
    it was chosen from. -/
def sigmaSection (M : ExecModel) (iotaF : M.Rep → M.Raw) : Prop :=
  ∀ (c : M.Class) (rep : M.Rep), M.sigma c = some rep → M.q (iotaF rep) = c

theorem base6_quotientFactorization : quotientFactorization base6 := by
  intro r; cases r <;> rfl

theorem base6_admissibilitySound : admissibilitySound base6 := by
  intro c rep h; cases c <;> first | rfl | exact Option.noConfusion h

theorem base6_residueTotality : residueTotality base6 := by
  intro c hact hadm; cases c <;> first
    | exact absurd hadm (by decide) | (intro e; exact Option.noConfusion e)

theorem base6_representativePrecision : representativePrecision base6 := by
  intro c hact hadm; cases c <;> first
    | exact absurd hadm (by decide) | (intro e; exact Option.noConfusion e)

theorem base6_hasMSTNFProfile : hasMSTNFProfile base6 :=
  ⟨base6_quotientFactorization, base6_admissibilitySound,
    base6_residueTotality, base6_representativePrecision⟩

theorem base6_residueExclusive : residueExclusive base6 := by
  intro c hadm; cases c <;> first | rfl | exact absurd hadm (by decide)

theorem base6_sigmaSection : sigmaSection base6 iota6 := by
  intro c rep h; cases c <;> cases rep <;> first
    | rfl | exact Option.noConfusion h
    | exact Rep3.noConfusion (Option.some.inj h)

-- Mutants: each changes exactly the displayed field of `base6`.

/-- Mutant Q: `evalRaw(g1) := 11` — breaks only `quotientFactorization`. -/
def mutantQ : ExecModel :=
  { base6 with evalRaw := fun r => match r with
    | .g1 => (11 : Int) | _ => evalRaw6 r }

/-- Mutant A: `sigma(B) := some bad` — breaks only `admissibilitySound`. -/
def mutantA : ExecModel :=
  { base6 with sigma := fun c => match c with | .B => some .bad | _ => sigma6 c }

/-- Mutant R: `rho(B) := none` — breaks only `residueTotality`. -/
def mutantR : ExecModel :=
  { base6 with rho := fun c => match c with | .B => none | _ => rho6 c }

/-- Mutant S: `sigma(G) := none` — breaks only `representativePrecision`. -/
def mutantS : ExecModel :=
  { base6 with sigma := fun c => match c with | .G => none | _ => sigma6 c }

/-- Base mutation: `rho(G) := some spurious` — keeps all four laws, breaks
    residue exclusivity. -/
def mutantX : ExecModel :=
  { base6 with rho := fun c => match c with
    | .G => some .spurious | _ => rho6 c }

/-- Base mutation: `sigma(G) := some z` — keeps all four laws, breaks the
    specified source section (`q (iota z) = Z ≠ G`). -/
def mutantSec : ExecModel :=
  { base6 with sigma := fun c => match c with
    | .G => some .z | _ => sigma6 c }

theorem mutantQ_laws :
    ¬ quotientFactorization mutantQ ∧
    admissibilitySound mutantQ ∧
    residueTotality mutantQ ∧
    representativePrecision mutantQ :=
  ⟨fun h => absurd (h .g1) (by decide : (11 : Int) ≠ 10),
    by intro c rep h; cases c <;> first
      | rfl | exact Option.noConfusion h,
    by intro c hact hadm; cases c <;> first
      | exact absurd hadm (by decide) | (intro e; exact Option.noConfusion e),
    by intro c hact hadm; cases c <;> first
      | exact absurd hadm (by decide) | (intro e; exact Option.noConfusion e)⟩

theorem mutantQ_nondegenerate :
    (∃ c : Class3, activeClass mutantQ c ∧ mutantQ.admissible c = true) ∧
    (∃ c : Class3, activeClass mutantQ c ∧ mutantQ.admissible c = false) ∧
    (∃ r1 r2 : Raw6, r1 ≠ r2 ∧ mutantQ.q r1 = mutantQ.q r2) ∧
    (∃ c rep r, mutantQ.sigma c = some rep ∧
      mutantQ.admissible c = true ∧ mutantQ.q r = c) :=
  ⟨⟨.G, ⟨.g0, rfl⟩, rfl⟩, ⟨.B, ⟨.b0, rfl⟩, rfl⟩,
    ⟨.g0, .g1, by decide, rfl⟩, ⟨.Z, .z, .z0, rfl, rfl, rfl⟩⟩

theorem mutantA_laws :
    quotientFactorization mutantA ∧
    ¬ admissibilitySound mutantA ∧
    residueTotality mutantA ∧
    representativePrecision mutantA :=
  ⟨by intro r; cases r <;> rfl,
    fun h => absurd (h .B .bad rfl) (by decide),
    by intro c hact hadm; cases c <;> first
      | exact absurd hadm (by decide) | (intro e; exact Option.noConfusion e),
    by intro c hact hadm; cases c <;> first
      | exact absurd hadm (by decide) | (intro e; exact Option.noConfusion e)⟩

theorem mutantA_nondegenerate :
    (∃ c : Class3, activeClass mutantA c ∧ mutantA.admissible c = true) ∧
    (∃ c : Class3, activeClass mutantA c ∧ mutantA.admissible c = false) ∧
    (∃ r1 r2 : Raw6, r1 ≠ r2 ∧ mutantA.q r1 = mutantA.q r2) ∧
    (∃ c rep r, mutantA.sigma c = some rep ∧
      mutantA.admissible c = true ∧ mutantA.q r = c) :=
  ⟨⟨.G, ⟨.g0, rfl⟩, rfl⟩, ⟨.B, ⟨.b0, rfl⟩, rfl⟩,
    ⟨.g0, .g1, by decide, rfl⟩, ⟨.Z, .z, .z0, rfl, rfl, rfl⟩⟩

theorem mutantR_laws :
    quotientFactorization mutantR ∧
    admissibilitySound mutantR ∧
    ¬ residueTotality mutantR ∧
    representativePrecision mutantR :=
  ⟨by intro r; cases r <;> rfl,
    by intro c rep h; cases c <;> first
      | rfl | exact Option.noConfusion h,
    fun h => (h .B ⟨.b0, rfl⟩ rfl) rfl,
    by intro c hact hadm; cases c <;> first
      | exact absurd hadm (by decide) | (intro e; exact Option.noConfusion e)⟩

theorem mutantR_nondegenerate :
    (∃ c : Class3, activeClass mutantR c ∧ mutantR.admissible c = true) ∧
    (∃ c : Class3, activeClass mutantR c ∧ mutantR.admissible c = false) ∧
    (∃ r1 r2 : Raw6, r1 ≠ r2 ∧ mutantR.q r1 = mutantR.q r2) ∧
    (∃ c rep r, mutantR.sigma c = some rep ∧
      mutantR.admissible c = true ∧ mutantR.q r = c) :=
  ⟨⟨.G, ⟨.g0, rfl⟩, rfl⟩, ⟨.B, ⟨.b0, rfl⟩, rfl⟩,
    ⟨.g0, .g1, by decide, rfl⟩, ⟨.Z, .z, .z0, rfl, rfl, rfl⟩⟩

theorem mutantS_laws :
    quotientFactorization mutantS ∧
    admissibilitySound mutantS ∧
    residueTotality mutantS ∧
    ¬ representativePrecision mutantS :=
  ⟨by intro r; cases r <;> rfl,
    by intro c rep h; cases c <;> first
      | rfl | exact Option.noConfusion h,
    by intro c hact hadm; cases c <;> first
      | exact absurd hadm (by decide) | (intro e; exact Option.noConfusion e),
    fun h => (h .G ⟨.g0, rfl⟩ rfl) rfl⟩

theorem mutantS_nondegenerate :
    (∃ c : Class3, activeClass mutantS c ∧ mutantS.admissible c = true) ∧
    (∃ c : Class3, activeClass mutantS c ∧ mutantS.admissible c = false) ∧
    (∃ r1 r2 : Raw6, r1 ≠ r2 ∧ mutantS.q r1 = mutantS.q r2) ∧
    (∃ c rep r, mutantS.sigma c = some rep ∧
      mutantS.admissible c = true ∧ mutantS.q r = c) :=
  ⟨⟨.G, ⟨.g0, rfl⟩, rfl⟩, ⟨.B, ⟨.b0, rfl⟩, rfl⟩,
    ⟨.g0, .g1, by decide, rfl⟩, ⟨.Z, .z, .z0, rfl, rfl, rfl⟩⟩

theorem mutantX_exclusive_violation :
    hasMSTNFProfile mutantX ∧ ¬ residueExclusive mutantX :=
  ⟨⟨by intro r; cases r <;> rfl,
      by intro c rep h; cases c <;> first
        | rfl | exact Option.noConfusion h,
      by intro c hact hadm; cases c <;> first
        | exact absurd hadm (by decide) | (intro e; exact Option.noConfusion e),
      by intro c hact hadm; cases c <;> first
        | exact absurd hadm (by decide) | (intro e; exact Option.noConfusion e)⟩,
    fun h => Option.noConfusion (h .G rfl)⟩

theorem mutantSec_section_violation :
    hasMSTNFProfile mutantSec ∧ ¬ sigmaSection mutantSec iota6 :=
  ⟨⟨by intro r; cases r <;> rfl,
      by intro c rep h; cases c <;> first
        | rfl | exact Option.noConfusion h,
      by intro c hact hadm; cases c <;> first
        | exact absurd hadm (by decide) | (intro e; exact Option.noConfusion e),
      by intro c hact hadm; cases c <;> first
        | exact absurd hadm (by decide) | (intro e; exact Option.noConfusion e)⟩,
    fun h => Class3.noConfusion (h .G .z rfl)⟩

end MSTNFFiniteInstanceMWE

import MSTNF.algorithms.MSTNecessityExecModelMWE
import MSTNF.r2.Active

/-!
# MST-NF R2 — nondegenerate finite independence witnesses (P9)

Mechanization of the R2 contract, section 7 registry row P9 ("nondegenerate
finite independence witnesses: exactly one failed law and explicit
witnesses"); finite-instance spec section 6 (six-input countermodel suite) and
the two additional base-model mutations.

Sources (mature sources rule, preamble item 7):
- the finite-instance specification, section 6
  (the definitive field values and the mutant table) and section 7 (the
  "exactly one false law per named mutant" check).
- Design of record: `MST-NF-R2-mechanization-contract.md` section 3 (both an
  admitted and a refused collision for operational non-vacuity) and section 9.
- Pinned base: `MSTNF.algorithms.MSTNecessityExecModelMWE` (four Tier 1 laws,
  `activeClass`), `MSTNF.r2.Active` (active/global section and exclusivity).

Every proposition is closed by structural case analysis and definitional
reduction, or by `decide` on integer literals; no `native_decide`, no `sorry`,
no new axioms, no Mathlib.
-/

namespace MSTNFR2

open MSTNecessityExecModelMWE

/-! ## The six-input base model (finite-instance spec section 6) -/

inductive Raw6 where
  | g0 | g1 | b0 | b1 | z0 | z1
  deriving DecidableEq

inductive Class3 where
  | G | B | Z
  deriving DecidableEq

inductive Rep3 where
  | g | bad | z
  deriving DecidableEq

inductive Res3 where
  | blocked | spurious
  deriving DecidableEq

def baseQ : Raw6 → Class3
  | Raw6.g0 | Raw6.g1 => Class3.G
  | Raw6.b0 | Raw6.b1 => Class3.B
  | Raw6.z0 | Raw6.z1 => Class3.Z

def baseEvalClass : Class3 → Int
  | Class3.G => 10
  | Class3.B => -1
  | Class3.Z => 20

def baseEvalRaw : Raw6 → Int := fun r => baseEvalClass (baseQ r)

def baseAdm : Class3 → Bool
  | Class3.G => true
  | Class3.B => false
  | Class3.Z => true

def baseSigma : Class3 → Option Rep3
  | Class3.G => some Rep3.g
  | Class3.B => none
  | Class3.Z => some Rep3.z

def baseRho : Class3 → Option Res3
  | Class3.G => none
  | Class3.B => some Res3.blocked
  | Class3.Z => none

/-- `iota(g)=g0`, `iota(bad)=b0`, `iota(z)=z0` (spec section 6). -/
def baseIota : Rep3 → Raw6
  | Rep3.g => Raw6.g0
  | Rep3.bad => Raw6.b0
  | Rep3.z => Raw6.z0

def base6 : ExecModel where
  Raw := Raw6
  Class := Class3
  Rep := Rep3
  Residue := Res3
  Outcome := Int
  q := baseQ
  evalRaw := baseEvalRaw
  evalClass := baseEvalClass
  admissible := baseAdm
  rho := baseRho
  sigma := baseSigma

/-! ## The base model satisfies everything -/

theorem base_quotientFactorization : quotientFactorization base6 := fun _ => rfl

theorem base_admissibilitySound : admissibilitySound base6 := by
  intro c _rep h
  cases c with
  | G => rfl
  | B => exact Option.noConfusion h
  | Z => rfl

theorem base_residueTotality : residueTotality base6 := by
  intro c _ hadm
  cases c with
  | G => exact Bool.noConfusion hadm
  | B => intro hc; exact Option.noConfusion hc
  | Z => exact Bool.noConfusion hadm

theorem base_representativePrecision : representativePrecision base6 := by
  intro c _ hadm
  cases c with
  | G => intro hc; exact Option.noConfusion hc
  | B => exact Bool.noConfusion hadm
  | Z => intro hc; exact Option.noConfusion hc

theorem base_profile : hasMSTNFProfile base6 :=
  ⟨base_quotientFactorization, base_admissibilitySound, base_residueTotality,
    base_representativePrecision⟩

theorem base_activeSourceSection : activeSourceSection base6 baseIota := by
  intro c r hs
  rcases c with ⟨c, r0, _hq⟩
  cases c with
  | G => cases r with
    | g => rfl
    | bad => exact Rep3.noConfusion (Option.some.inj hs)
    | z => exact Rep3.noConfusion (Option.some.inj hs)
  | B => exact Option.noConfusion hs
  | Z => cases r with
    | g => exact Rep3.noConfusion (Option.some.inj hs)
    | bad => exact Rep3.noConfusion (Option.some.inj hs)
    | z => rfl

theorem base_activeExclusivity : activeExclusivity base6 := by
  intro c hadm
  rcases c with ⟨c, r0, _hq⟩
  cases c with
  | G => rfl
  | B => exact Bool.noConfusion hadm
  | Z => rfl

/-! ## Shared independence witnesses (contract section 3) -/

/-- For a suite model: a distinct same-key pair in an admitted class
    (operational cross-input reuse) and in a refused class, an active admitted
    class, an active refused class, and a realized admitted class. The realized
    admitted class is `Z` in every mutant (mutant S removes `sigma G`; mutant A
    adds `sigma B` on a non-admitted class). -/
def sixWitnesses (M : ExecModel) : Prop :=
  (∃ r r' : M.Raw, r ≠ r' ∧ M.q r = M.q r' ∧ M.admissible (M.q r) = true) ∧
  (∃ r r' : M.Raw, r ≠ r' ∧ M.q r = M.q r' ∧ M.admissible (M.q r) = false) ∧
  (∃ c : M.Class, activeClass M c ∧ M.admissible c = true) ∧
  (∃ c : M.Class, activeClass M c ∧ M.admissible c = false) ∧
  (∃ (c : M.Class) (r : M.Rep), M.sigma c = some r ∧ M.admissible c = true)

theorem base_witnesses : sixWitnesses base6 :=
  ⟨⟨Raw6.g0, Raw6.g1, fun h => Raw6.noConfusion h, rfl, rfl⟩,
   ⟨Raw6.b0, Raw6.b1, fun h => Raw6.noConfusion h, rfl, rfl⟩,
   ⟨Class3.G, ⟨Raw6.g0, rfl⟩, rfl⟩,
   ⟨Class3.B, ⟨Raw6.b0, rfl⟩, rfl⟩,
   ⟨Class3.Z, Rep3.z, rfl, rfl⟩⟩

/-! ## Mutant Q: `evalRaw(g1) := 11` — only quotientFactorization fails -/

def mutantQ : ExecModel := { base6 with
  evalRaw := fun r => match r with | Raw6.g1 => (11 : Int) | r => baseEvalRaw r }

theorem mutantQ_truth :
    ¬ quotientFactorization mutantQ ∧ admissibilitySound mutantQ ∧
    residueTotality mutantQ ∧ representativePrecision mutantQ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hg1 : (11 : Int) = (10 : Int) := h Raw6.g1
    exact absurd hg1 (by decide)
  · intro c _rep h
    cases c with
    | G => rfl
    | B => exact Option.noConfusion h
    | Z => rfl
  · intro c _ hadm
    cases c with
    | G => exact Bool.noConfusion hadm
    | B => intro hc; exact Option.noConfusion hc
    | Z => exact Bool.noConfusion hadm
  · intro c _ hadm
    cases c with
    | G => intro hc; exact Option.noConfusion hc
    | B => exact Bool.noConfusion hadm
    | Z => intro hc; exact Option.noConfusion hc

theorem mutantQ_witnesses : sixWitnesses mutantQ :=
  ⟨⟨Raw6.g0, Raw6.g1, fun h => Raw6.noConfusion h, rfl, rfl⟩,
   ⟨Raw6.b0, Raw6.b1, fun h => Raw6.noConfusion h, rfl, rfl⟩,
   ⟨Class3.G, ⟨Raw6.g0, rfl⟩, rfl⟩,
   ⟨Class3.B, ⟨Raw6.b0, rfl⟩, rfl⟩,
   ⟨Class3.Z, Rep3.z, rfl, rfl⟩⟩

/-! ## Mutant A: `sigma(B) := some bad` — only admissibilitySound fails -/

def mutantA : ExecModel := { base6 with
  sigma := fun c => match c with
    | Class3.B => some Rep3.bad
    | c => baseSigma c }

theorem mutantA_truth :
    quotientFactorization mutantA ∧ ¬ admissibilitySound mutantA ∧
    residueTotality mutantA ∧ representativePrecision mutantA := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro h
    have hb := h Class3.B Rep3.bad rfl
    exact Bool.noConfusion hb
  · intro c _ hadm
    cases c with
    | G => exact Bool.noConfusion hadm
    | B => intro hc; exact Option.noConfusion hc
    | Z => exact Bool.noConfusion hadm
  · intro c _ hadm
    cases c with
    | G => intro hc; exact Option.noConfusion hc
    | B => exact Bool.noConfusion hadm
    | Z => intro hc; exact Option.noConfusion hc

theorem mutantA_witnesses : sixWitnesses mutantA :=
  ⟨⟨Raw6.g0, Raw6.g1, fun h => Raw6.noConfusion h, rfl, rfl⟩,
   ⟨Raw6.b0, Raw6.b1, fun h => Raw6.noConfusion h, rfl, rfl⟩,
   ⟨Class3.G, ⟨Raw6.g0, rfl⟩, rfl⟩,
   ⟨Class3.B, ⟨Raw6.b0, rfl⟩, rfl⟩,
   ⟨Class3.Z, Rep3.z, rfl, rfl⟩⟩

/-! ## Mutant R: `rho(B) := none` — only residueTotality fails -/

def mutantR : ExecModel := { base6 with
  rho := fun c => match c with | Class3.B => none | c => baseRho c }

theorem mutantR_truth :
    quotientFactorization mutantR ∧ admissibilitySound mutantR ∧
    ¬ residueTotality mutantR ∧ representativePrecision mutantR := by
  refine ⟨fun _ => rfl, base_admissibilitySound, ?_, ?_⟩
  · intro h
    exact h Class3.B ⟨Raw6.b0, rfl⟩ rfl rfl
  · intro c _ hadm
    cases c with
    | G => intro hc; exact Option.noConfusion hc
    | B => exact Bool.noConfusion hadm
    | Z => intro hc; exact Option.noConfusion hc

theorem mutantR_witnesses : sixWitnesses mutantR :=
  ⟨⟨Raw6.g0, Raw6.g1, fun h => Raw6.noConfusion h, rfl, rfl⟩,
   ⟨Raw6.b0, Raw6.b1, fun h => Raw6.noConfusion h, rfl, rfl⟩,
   ⟨Class3.G, ⟨Raw6.g0, rfl⟩, rfl⟩,
   ⟨Class3.B, ⟨Raw6.b0, rfl⟩, rfl⟩,
   ⟨Class3.Z, Rep3.z, rfl, rfl⟩⟩

/-! ## Mutant S: `sigma(G) := none` — only representativePrecision fails -/

def mutantS : ExecModel := { base6 with
  sigma := fun c => match c with | Class3.G => none | c => baseSigma c }

theorem mutantS_truth :
    quotientFactorization mutantS ∧ admissibilitySound mutantS ∧
    residueTotality mutantS ∧ ¬ representativePrecision mutantS := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro c _rep h
    cases c with
    | G => exact Option.noConfusion h
    | B => exact Option.noConfusion h
    | Z => rfl
  · intro c _ hadm
    cases c with
    | G => exact Bool.noConfusion hadm
    | B => intro hc; exact Option.noConfusion hc
    | Z => exact Bool.noConfusion hadm
  · intro h
    exact h Class3.G ⟨Raw6.g0, rfl⟩ rfl rfl

theorem mutantS_witnesses : sixWitnesses mutantS :=
  ⟨⟨Raw6.g0, Raw6.g1, fun h => Raw6.noConfusion h, rfl, rfl⟩,
   ⟨Raw6.b0, Raw6.b1, fun h => Raw6.noConfusion h, rfl, rfl⟩,
   ⟨Class3.G, ⟨Raw6.g0, rfl⟩, rfl⟩,
   ⟨Class3.B, ⟨Raw6.b0, rfl⟩, rfl⟩,
   ⟨Class3.Z, Rep3.z, rfl, rfl⟩⟩

/-! ## Two additional base-model mutations (spec section 6, after the table) -/

/-- `rho(G) := some spurious`: all four laws hold, exclusivity fails. -/
def mutantX1 : ExecModel := { base6 with
  rho := fun c => match c with | Class3.G => some Res3.spurious | c => baseRho c }

theorem mutantX1_laws : hasMSTNFProfile mutantX1 :=
  ⟨fun _ => rfl, base_admissibilitySound, by
    intro c _ hadm
    cases c with
    | G => exact Bool.noConfusion hadm
    | B => intro hc; exact Option.noConfusion hc
    | Z => exact Bool.noConfusion hadm,
    base_representativePrecision⟩

theorem mutantX1_not_activeExclusivity : ¬ activeExclusivity mutantX1 := by
  intro h
  exact Option.noConfusion (h ⟨Class3.G, Raw6.g0, rfl⟩ rfl)

/-- `sigma(G) := some z`: all four laws hold, the active source section for
    `baseIota` fails because `q (iota z) = q z0 = Z ≠ G`. -/
def mutantX2 : ExecModel := { base6 with
  sigma := fun c => match c with | Class3.G => some Rep3.z | c => baseSigma c }

theorem mutantX2_laws : hasMSTNFProfile mutantX2 :=
  ⟨fun _ => rfl, by
    intro c _rep h
    cases c with
    | G => rfl
    | B => exact Option.noConfusion h
    | Z => rfl,
    base_residueTotality, by
    intro c _ hadm
    cases c with
    | G => intro hc; exact Option.noConfusion hc
    | B => exact Bool.noConfusion hadm
    | Z => intro hc; exact Option.noConfusion hc⟩

theorem mutantX2_not_activeSourceSection : ¬ activeSourceSection mutantX2 baseIota := by
  intro h
  exact Class3.noConfusion (h ⟨Class3.G, Raw6.g0, rfl⟩ Rep3.z rfl)

end MSTNFR2

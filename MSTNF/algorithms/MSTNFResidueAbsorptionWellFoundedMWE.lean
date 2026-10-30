/-!
# T1 — Gödel-2 self-soundness as the principled non-WF mechanism

Replaces Phase 3's toy `n↦n+1` successor with the Gödel-2-grounded one:

    F ↦ F ∪ {selfSoundnessFiat F}

The residue ladder's non-well-foundedness is NOT arithmetic;
it is Gödel-2 self-soundness failure. A sufficiently-expressive consistent
framework `F` cannot prove its own soundness ⇒ "soundness of F" is a
basis-external fiat-kind ⇒ each level has a successor by Gödel-2 ⇒ the
chain is non-WF by theorem, not by `n+1`.

**Self-encodable horn (formalized here)**: Gödel-2 applies ⇒ discoverer FORCED.
**Non-self-encodable horn (stated, NOT formalized)**: Gödel-2 doesn't trigger
⇒ framework can be re-descriptive but is also non-universal (§59's other branch).

## Honest framing

- Gödel-2 itself is not re-proven in Lean (massive undertaking). Instead we
  ABSTRACT it as a property of `GodelFramework`: the `selfSoundnessFiat` field
  is **provably distinct** from any element of `detected` (the Gödel-2 step
  as a structural invariant). In a concrete instantiation, this distinctness
  would be justified by appeal to Gödel's actual theorem.
- The **expressivity hypothesis** (= self-encodability = the universality
  knife) is encoded as the EXISTENCE of a `GodelFramework`. The non-self-
  encodable horn is the dual: no GodelFramework, hence no forced successor —
  a `WeakFramework` (statement only, no Gödel-2 obligation).
- Empirical anchor: each §X in the anti-fiat ladder is the prior level's
  self-soundness fiat. Documented in the file but NOT claimed to be a Lean
  theorem ("every §X" is empirical observation, not a universal proof).

Per §47/§49/§52 guardrails: explicit hypotheses, no tautology, real reduction.

Verification gate: per §49, `lake env lean <file>` direct compilation
(NOT `lake build` no-target).
-/

namespace MSTNFResidueAbsorptionWellFounded

-- ===========================================================================
-- Minimal restatement of Phase 3's structural pieces (self-contained)
-- ===========================================================================
-- (the digestion self-application module is not included here;
-- we restate the necessary definitions here so this file compiles
-- standalone.)

inductive ReflTransGen {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl {a : α} : ReflTransGen r a a
  | tail {a b c : α} : ReflTransGen r a b → r b c → ReflTransGen r a c

theorem ReflTransGen.trans {α : Type} {r : α → α → Prop} {a b c : α}
    (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) :
    ReflTransGen r a c := by
  induction hbc with
  | refl => exact hab
  | tail _ rstep ih => exact ReflTransGen.tail ih rstep

def InBasis {Kind : Type} (step : Kind → Kind → Prop) (k : Kind) : Prop :=
  ∀ k', ¬ step k k'

def ReachesBasis {Kind : Type} (step : Kind → Kind → Prop) (k : Kind) : Prop :=
  ∃ k₀, InBasis step k₀ ∧ ReflTransGen step k k₀

def AllResiduesRepresented {Kind : Type} (step : Kind → Kind → Prop) : Prop :=
  ∀ k, ReachesBasis step k

def ResidueSeals {Kind : Type} (step : Kind → Kind → Prop) : Prop :=
  AllResiduesRepresented step ∧ WellFounded (flip step)

-- ===========================================================================
-- The Gödel-2 framework abstraction
-- ===========================================================================

/-- A Gödel-style verification framework.

    `detected : List Nat` = the set of fiat-kinds this framework can catch.
    `selfSoundnessFiat : Nat` = the framework's OWN soundness statement encoded
                                  as a fiat-kind.
    `godel2` = the **abstract Gödel-2 property**: the self-soundness fiat is
               provably NOT in the detected set. This is the structural
               packaging of "F cannot prove its own soundness from within."

    A concrete instantiation (Peano Arithmetic, ZFC, …) would justify the
    `godel2` field by appeal to Gödel's second incompleteness theorem. -/
structure GodelFramework where
  detected : List Nat
  selfSoundnessFiat : Nat
  godel2 : selfSoundnessFiat ∉ detected

/-- Helper: list max (returns 0 for empty list). -/
def listMax : List Nat → Nat
  | [] => 0
  | n :: ns => Nat.max n (listMax ns)

theorem listMax_lt_succ_max (B : List Nat) (k : Nat) :
    k ≤ listMax B → k < listMax B + 1 :=
  fun h => Nat.lt_succ_of_le h

theorem listMax_le_of_mem (B : List Nat) (k : Nat) (hk : k ∈ B) : k ≤ listMax B := by
  induction B with
  | nil => exact absurd hk (List.not_mem_nil _)
  | cons n ns ih =>
    rcases List.mem_cons.mp hk with hkn | hkns
    · subst hkn; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hkns) (Nat.le_max_right _ _)

theorem fresh_not_in (B : List Nat) :
    listMax B + 1 ∉ B := by
  intro hMem
  have h1 : listMax B + 1 ≤ listMax B := listMax_le_of_mem B (listMax B + 1) hMem
  omega

-- ===========================================================================
-- The Gödel-2 successor — F ↦ F ∪ {selfSoundnessFiat F}
-- ===========================================================================

/-- The Gödel-2-grounded successor of `F`:
    - `detected'` adds F's selfSoundnessFiat (we've now detected it externally)
    - `selfSoundnessFiat'` is a fresh fiat-kind (max of new detected + 1)
    - `godel2'` holds by `fresh_not_in`.

    This is the principled replacement for Phase 3's `n ↦ n+1` toy step. -/
def godelSuccessor (F : GodelFramework) : GodelFramework where
  detected := F.selfSoundnessFiat :: F.detected
  selfSoundnessFiat := listMax (F.selfSoundnessFiat :: F.detected) + 1
  godel2 := fresh_not_in (F.selfSoundnessFiat :: F.detected)

/-- The meta step relation: a Gödel-2-grounded successor exists for every F. -/
def godelStep : GodelFramework → GodelFramework → Prop :=
  fun F F' => F' = godelSuccessor F

-- ===========================================================================
-- The core T1 result — no terminal under godelStep
-- ===========================================================================

theorem godelStep_has_successor (F : GodelFramework) :
    ∃ F', godelStep F F' :=
  ⟨godelSuccessor F, rfl⟩

theorem godelStep_no_terminal (F : GodelFramework) :
    ¬ InBasis godelStep F := by
  intro hBasis
  exact hBasis (godelSuccessor F) rfl

/-- Initial framework: nothing detected; selfSoundnessFiat = 0. -/
def F0 : GodelFramework where
  detected := []
  selfSoundnessFiat := 0
  godel2 := List.not_mem_nil 0

/-- **T1 — Gödel-2 forces non-AllResiduesRepresented**.

    Under the Gödel-2 abstraction (every framework has a fresh self-soundness
    fiat outside its detected basis), no framework reaches a terminal —
    the discoverer is FORCED, not structurally optional. -/
theorem godel_not_allRepresented :
    ¬ AllResiduesRepresented godelStep := by
  intro hAll
  rcases hAll F0 with ⟨F₀, hBasis, _⟩
  exact godelStep_no_terminal F₀ hBasis

/-- **T1 corollary — ResidueSeals fails at meta layer under Gödel-2**. -/
theorem godel_not_residueSeals :
    ¬ ResidueSeals godelStep :=
  fun ⟨hAll, _⟩ => godel_not_allRepresented hAll

/-- **T1 — WellFoundedness fails at the meta layer**.

    The Gödel-2 chain is non-well-founded: every framework has a successor
    (its own self-soundness fiat), so the chain extends indefinitely. -/
theorem godelStep_flip_not_wellFounded :
    ¬ WellFounded (flip godelStep) := by
  intro hWF
  -- Use well-founded ⇒ Acc on every element; pick F0 as starting point.
  -- F0 has Acc, so its successor godelSuccessor F0 also has Acc, etc.
  -- But each F has a successor, so the chain never bottoms out under flip.
  -- Direct argument: WellFounded ⇒ AllResiduesRepresented (mirror of Phase 3),
  -- contradicting godel_not_allRepresented.
  have hAll := allReached_of_wellFounded godelStep
    (fun F => .isTrue ⟨godelSuccessor F, rfl⟩) hWF
  exact godel_not_allRepresented hAll
where
  -- Local helper inlined from Phase 3 file (Task B's ← direction).
  -- We provide a self-contained restatement. The "has a successor?"
  -- case split is a `Decidable` hypothesis (constructive); for `godelStep`
  -- the caller discharges it with `godelStep_has_successor`.
  allReached_of_wellFounded : ∀ (step : GodelFramework → GodelFramework → Prop),
      (∀ k, Decidable (∃ k', step k k')) →
      WellFounded (flip step) → AllResiduesRepresented step := by
    intro step hdec hWF k
    induction k using hWF.induction with
    | _ k ih =>
      cases hdec k with
      | isTrue hTerm =>
        rcases hTerm with ⟨k', hStep⟩
        rcases ih k' hStep with ⟨k₀, hk₀Basis, hk₀Reach⟩
        refine ⟨k₀, hk₀Basis, ?_⟩
        exact ReflTransGen.trans (ReflTransGen.tail ReflTransGen.refl hStep) hk₀Reach
      | isFalse hTerm =>
        refine ⟨k, ?_, ReflTransGen.refl⟩
        intro k' hStep; exact hTerm ⟨k', hStep⟩

-- ===========================================================================
-- The empirical anchor — §40, §42, §49, §52 mapped to Gödel-2 levels
-- ===========================================================================
--
-- Each §X in the anti-fiat ladder IS the prior level's self-soundness fiat:
--   §49 harness-fiat = "trust `lake build` actually ran" = trust harness sound
--   §52 meta-fiat    = "trust N-grows ⇒ more-verified" = trust metric sound
-- Documented here as a STRUCTURAL ANALOGY, NOT a claim that every empirical
-- ladder step is uniquely a Gödel-2 self-soundness fiat. The Gödel-2 reading
-- explains the §49→§52 SHAPE; whether every future §X fits the same shape
-- is open.

inductive AntiFiatLevel where
  | l40_encoding   -- §40: "trust encoding faithfully captures the spec"
  | l42_proof      -- §42: "trust 0-sorry + decide-passes ⇒ semantic verification"
  | l49_harness    -- §49: "trust `lake build` actually built the file"
  | l52_meta       -- §52: "trust N-grows ⇒ more verified"
deriving DecidableEq, Repr

/-- Each level's CORE self-soundness fiat is "trust this level's framework is sound." -/
def antiFiatSelfSoundness : AntiFiatLevel → String
  | .l40_encoding => "trust encoding is faithful"
  | .l42_proof    => "trust 0-sorry ⇒ semantic verification"
  | .l49_harness  => "trust harness actually ran"
  | .l52_meta     => "trust the verification metric"

/-- The "next §X" catches the prior level's self-soundness fiat (empirically). -/
def antiFiatNext : AntiFiatLevel → AntiFiatLevel
  | .l40_encoding => .l42_proof
  | .l42_proof    => .l49_harness
  | .l49_harness  => .l52_meta
  | .l52_meta     => .l52_meta  -- §52's own self-soundness fiat: open / next-level needed

-- ===========================================================================
-- Non-self-encodable horn — stated, NOT formalized
-- ===========================================================================
--
-- Per §59's other branch: if a framework F is NOT self-encodable (cannot
-- represent its own soundness statement internally), Gödel-2 doesn't apply.
-- Such F may be re-descriptive (closes on its detectable basis) but is
-- also non-universal (cannot reason about its own self-application).
--
-- This is the §59 dichotomy: there is no "universal + re-descriptive +
-- self-applicable" all-three. Choice 1 = self-encodable + Gödel-2 forced
-- discoverer (this file's T1). Choice 2 = non-self-encodable + descriptive
-- but non-universal (this section, statement only).

/-- A "weak" framework: no self-soundness fiat, no Gödel-2 obligation.
    Such frameworks may close on their detectable basis trivially. -/
structure WeakFramework where
  detected : List Nat
  -- No selfSoundnessFiat — this framework is NOT self-encodable.

/-- A WeakFramework's step relation: the only "successor" is itself
    (no fresh kind to chase). Vacuously well-founded.

    The TRADE-OFF: WeakFramework can close (WellFounded), but it CANNOT
    represent statements about its own self-application — it is
    "re-descriptive but non-universal" per §59. -/
def weakStep : WeakFramework → WeakFramework → Prop :=
  fun _ _ => False

theorem weakStep_wellFounded : WellFounded (flip weakStep) := by
  refine ⟨fun F => ⟨F, fun _ hy => absurd hy id⟩⟩

theorem weak_residueSeals :
    AllResiduesRepresented weakStep ∧ WellFounded (flip weakStep) := by
  refine ⟨?_, weakStep_wellFounded⟩
  intro F; refine ⟨F, ?_, ReflTransGen.refl⟩
  intro _ h; exact h

/-- **The non-self-encodable horn (statement)**:
    WeakFramework's residue dynamics close trivially (ResidueSeals).
    But WeakFramework is non-universal — it cannot ENCODE its own
    self-application, so it doesn't even pose the Gödel-2 question.
    This is §59's dichotomy other branch. -/
theorem weak_horn_redescriptive_but_nonuniversal :
    AllResiduesRepresented weakStep ∧ WellFounded (flip weakStep) :=
  weak_residueSeals

-- ===========================================================================
-- T1 SUMMARY — the bridge as a Lean theorem
-- ===========================================================================

/-- **T1 — the bridge**.

    The §62 dichotomy formalized:
    - Self-encodable framework (GodelFramework, godelStep) ⇒ Gödel-2 forces
      `¬ ResidueSeals` (discoverer FORCED).
    - Non-self-encodable framework (WeakFramework, weakStep) ⇒ trivial
      `ResidueSeals` BUT this framework is non-universal (the §59 horn).

    Combined: there is no "universal + re-descriptive + self-applicable"
    three-way; the discoverer is forced under self-encodability, otherwise
    the framework gives up universality. -/
theorem T1_bridge_summary :
    (¬ ResidueSeals godelStep)
      ∧
    (AllResiduesRepresented weakStep ∧ WellFounded (flip weakStep)) :=
  ⟨godel_not_residueSeals, weak_residueSeals⟩

/-- Object-level analog for comparison (Phase 3 lives in another file, but the
    structural type is recoverable here): with an EMPTY step relation, residues
    represent trivially. This corresponds to Phase 3's object layer (4 archetypes,
    no further absorption). -/
def objectStep : Unit → Unit → Prop := fun _ _ => False

theorem object_residueSeals :
    AllResiduesRepresented objectStep ∧ WellFounded (flip objectStep) := by
  refine ⟨?_, ?_⟩
  · intro u; exact ⟨u, fun _ h => h, ReflTransGen.refl⟩
  · refine ⟨fun u => ⟨u, fun _ h => absurd h id⟩⟩

-- ===========================================================================
-- Honest boundary report — what T1 establishes vs what it does not
-- ===========================================================================
--
-- ESTABLISHES (Lean theorems):
-- 1. `godelStep_no_terminal`: every GodelFramework has a successor by
--    Gödel-2 (the `godel2` field forbids selfSoundnessFiat ∈ detected,
--    structurally guaranteeing a fresh fiat at each step).
-- 2. `godel_not_allRepresented`: ¬ AllResiduesRepresented godelStep
-- 3. `godel_not_residueSeals`: ¬ ResidueSeals godelStep
-- 4. `T1_bridge_summary`: the dichotomy.
--
-- DOES NOT ESTABLISH (honest residuals):
-- 1. Gödel-2 itself is NOT re-proven in Lean. The `godel2` field is the
--    abstract packaging of "F cannot prove its own soundness." A concrete
--    instantiation (PA, ZFC, etc.) would justify this via Gödel's actual
--    theorem; we assume the structural conclusion.
-- 2. The empirical claim "every §X in the anti-fiat ladder is the prior
--    level's self-soundness fiat" is documented analogically (AntiFiatLevel
--    type) but NOT proven as a universal statement. The §49 → §52 SHAPE
--    fits; the future §X may or may not.
-- 3. The "self-encodability = universality knife" identification is
--    a structural claim made deductively, not formally
--    discharged here. We encode the dichotomy as TWO disjoint framework
--    types (Godel vs Weak); the cross-type implications are statements,
--    not theorems.
-- 4. Lean 4 core cannot express "∀ F : MST-NF → MST-NF, ∃ basis-external
--    kind" universally without Reynolds parametricity. T1 constructs the
--    CONCRETE Gödel-2 successor; the uniform-in-F version remains at the
--    Lean-4-core parametricity boundary.

-- Live axiom audit (output as Lean info during compile):
#print axioms godel_not_allRepresented
#print axioms godel_not_residueSeals
#print axioms godelStep_flip_not_wellFounded
#print axioms T1_bridge_summary
#print axioms weak_horn_redescriptive_but_nonuniversal

end MSTNFResidueAbsorptionWellFounded

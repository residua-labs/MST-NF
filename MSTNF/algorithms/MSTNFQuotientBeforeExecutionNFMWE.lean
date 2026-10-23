/-!
# QBE (Quotient-Before-Execution) re-anchored in the current NF line

Re-states the load-bearing lemmas of the archived QBE proofs (under
`MSTNF/algorithms/MSTNecessityExecModelMWE.lean` +
`MSTNFQuotientBeforeExecutionMWE.lean`) over an abstract `ExecModel` and
puts them on the current build — so the QBE soundness is kernel-checked on every build.

This file is `sorry`/`admit`/`axiom`-free; all proofs are pure-core Lean 4
without Mathlib imports (matches the archived self-contained style).

## The content_store instance hook (document, not over-engineer)

For our content-addressed substrate:

  * `q          = content_hash`     (q : Raw → Class — the content hash)
  * `evalRaw    = eval_grown / interp.eval_` (raw execution)
  * `evalClass  = base interp on the canonical body` (class execution)
  * `quotientFactorization` holds because the frozen base interp is a pure
    function of structure, and `content_hash` is injective-on-structure
    (collision-freedom = the one cryptographic assumption, named honestly).

Therefore B5.3 / B5.4 hash-resolved parity is an INSTANCE of
`sameClass_sameOutcome`: two raw forms that hash to the same Class (same
content) must produce the same Outcome under `evalRaw`. The hash-resolved
execution loop is `sameClass_sameOutcome` materialised.

## Role isolation (project owner, 2026-06-07)

This module is written in pure core Lean 4 (no Mathlib imports).
-/

namespace MSTNFQuotientBeforeExecutionNFMWE

/-! ## §1 — The abstract execution model -/

/-- The minimal execution model carrying the QBE shape: a raw type, a class
    type, an outcome type, a quotient `q : Raw → Class`, and the two
    evaluation arrows `evalRaw : Raw → Outcome` and `evalClass : Class →
    Outcome`. The richer archived `ExecModel` carries admissibility /
    residue / representative fields too; for the load-bearing
    `sameClass_sameOutcome` only the three arrows are needed, so this MWE
    keeps the structure minimal (R1 distinguish, the active core of the
    "raw identity does not influence outcome" claim). -/
structure ExecModel where
  Raw     : Type
  Class   : Type
  Outcome : Type
  q         : Raw → Class
  evalRaw   : Raw → Outcome
  evalClass : Class → Outcome

/-- `quotientFactorization`: raw execution factors through the class.
    Raw identity cannot influence outcome — outcome is determined by class.
    This is the QBE substrate axiom. -/
def quotientFactorization (M : ExecModel) : Prop :=
  ∀ r : M.Raw, M.evalRaw r = M.evalClass (M.q r)

/-! ## §2 — `sameClass_sameOutcome` (the load-bearing lemma)

Under quotientFactorization, two raw events with the same class produce the
same outcome. The proof is one `rw` chain over the quotient factor:
`evalRaw r1 = evalClass (q r1) = evalClass (q r2) = evalRaw r2`.

This is the abstract shape the B5.3 / B5.4 parity is an INSTANCE of (when
`q = content_hash`, `evalRaw = eval_grown`, etc.) — the parity theorem
generalises to: any factor system where raw → class → outcome holds. -/

theorem sameClass_sameOutcome
    (M : ExecModel) (h : quotientFactorization M)
    {r1 r2 : M.Raw} (hq : M.q r1 = M.q r2) :
    M.evalRaw r1 = M.evalRaw r2 := by
  rw [h r1, h r2, hq]

/-! ## §3 — The counting bound `|A(E)| ≤ |Q(E)| ≤ |E|`

Over a finite raw event list, the quotient pass produces at most as many
distinct classes as raw events, and the admissibility filter produces at
most as many admitted classes as total classes. So the MST-NF backend's
work is monotone-bounded by the classic backend's work. Pure-core Lean 4,
no Mathlib. -/

/-- Dedup-insert: add `c` to a list of classes only if not already present.
    Matches the archived form for proof simplicity. -/
def insertClass {Class : Type} [DecidableEq Class]
    (c : Class) (classes : List Class) : List Class :=
  if c ∈ classes then classes else c :: classes

/-- The list of distinct classes encountered when quotienting a raw event list. -/
def classesOf {Raw Class : Type} [DecidableEq Class]
    (quotient : Raw → Class) : List Raw → List Class
  | [] => []
  | r :: rs => insertClass (quotient r) (classesOf quotient rs)

/-- The list of admitted classes among a list of classes. -/
def admissibleClasses {Class : Type}
    (admissible : Class → Bool) : List Class → List Class
  | [] => []
  | c :: cs =>
      if admissible c then c :: admissibleClasses admissible cs
      else admissibleClasses admissible cs

/-- Classic backend work = total raw events. -/
def classicBackendAttempts {Raw : Type} (events : List Raw) : Nat :=
  events.length

/-- MST-NF backend work = number of admitted distinct classes. -/
def mstnfBackendAttempts {Raw Class : Type} [DecidableEq Class]
    (quotient : Raw → Class) (admissible : Class → Bool)
    (events : List Raw) : Nat :=
  (admissibleClasses admissible (classesOf quotient events)).length

theorem insertClass_length_le_succ {Class : Type} [DecidableEq Class]
    (c : Class) (classes : List Class) :
    (insertClass c classes).length ≤ classes.length + 1 := by
  by_cases h : c ∈ classes
  · simp [insertClass, h]
  · simp [insertClass, h]

theorem classesOf_length_le_raw {Raw Class : Type} [DecidableEq Class]
    (quotient : Raw → Class) (events : List Raw) :
    (classesOf quotient events).length ≤ events.length := by
  induction events with
  | nil =>
      simp [classesOf]
  | cons e es ih =>
      have hInsert :
          (insertClass (quotient e) (classesOf quotient es)).length ≤
            (classesOf quotient es).length + 1 :=
        insertClass_length_le_succ (quotient e) (classesOf quotient es)
      have hTail :
          (classesOf quotient es).length + 1 ≤ es.length + 1 :=
        Nat.succ_le_succ ih
      exact Nat.le_trans hInsert hTail

theorem admissibleClasses_length_le_classes {Class : Type}
    (admissible : Class → Bool) (classes : List Class) :
    (admissibleClasses admissible classes).length ≤ classes.length := by
  induction classes with
  | nil =>
      simp [admissibleClasses]
  | cons c cs ih =>
      by_cases h : admissible c
      · simp [admissibleClasses, h, ih]
      · have hStep :
            (admissibleClasses admissible cs).length ≤ cs.length + 1 :=
          Nat.le_trans ih (Nat.le_succ cs.length)
        simp [admissibleClasses, h, hStep]

/-- **The counting bound**: MST-NF backend work ≤ classic backend work.
    `|A(Q(events))| ≤ |Q(events)| ≤ |events|`. -/
theorem mstnf_backend_le_classic
    {Raw Class : Type} [DecidableEq Class]
    (quotient : Raw → Class) (admissible : Class → Bool)
    (events : List Raw) :
    mstnfBackendAttempts quotient admissible events ≤
      classicBackendAttempts events := by
  unfold mstnfBackendAttempts classicBackendAttempts
  exact Nat.le_trans
    (admissibleClasses_length_le_classes admissible (classesOf quotient events))
    (classesOf_length_le_raw quotient events)

end MSTNFQuotientBeforeExecutionNFMWE

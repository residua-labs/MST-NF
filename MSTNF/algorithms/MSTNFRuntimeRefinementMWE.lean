import MSTNF.algorithms.MSTNFForwardBackwardMWE
import MSTNF.algorithms.MSTNFHopWitnessMWE

/-!
Witnesses with explicit runtime values, named refusals and resource limits.
The policy below permits a target limit; it never turns a source refusal or
limit into a target value. Consumers may supply a different relation explicitly.
-/
namespace NfCompose
open MSTNecessityExecModelMWE

inductive RuntimeOutcome (V E L : Type) where
  | value (v : V)
  | refused (reason : E)
  | limit (resource : L)
  deriving DecidableEq

/-- A policy, not an identification of successful values and resource limits. -/
def RuntimeRefines {V E L : Type} (source target : RuntimeOutcome V E L) : Prop :=
  match target with
  | .value v => source = .value v
  | .refused e => source = .refused e
  | .limit _ => True

theorem runtimeRefines_refl {V E L : Type} (a : RuntimeOutcome V E L) :
    RuntimeRefines a a := by
  cases a <;> simp [RuntimeRefines]

theorem runtimeRefines_trans {V E L : Type} (a b c : RuntimeOutcome V E L)
    (hab : RuntimeRefines a b) (hbc : RuntimeRefines b c) :
    RuntimeRefines a c := by
  cases c with
  | value v =>
    have e : b = .value v := hbc
    rw [e] at hab
    exact hab
  | refused e =>
    have he : b = .refused e := hbc
    rw [he] at hab
    exact hab
  | limit _ => exact True.intro

def mapRuntimeValue {V W E L : Type} (f : V → W) :
    RuntimeOutcome V E L → RuntimeOutcome W E L
  | .value v => .value (f v)
  | .refused e => .refused e
  | .limit l => .limit l

theorem mapRuntimeValue_mono {V W E L : Type} (f : V → W)
    (a b : RuntimeOutcome V E L) (h : RuntimeRefines a b) :
    RuntimeRefines (mapRuntimeValue f a) (mapRuntimeValue f b) := by
  cases b with
  | value v =>
    have e : a = .value v := h
    rw [e]
    exact rfl
  | refused e =>
    have he : a = .refused e := h
    rw [he]
    exact rfl
  | limit _ => exact True.intro

theorem runtime_success_noWrong {V E L : Type}
    (a : RuntimeOutcome V E L) (v : V) (h : RuntimeRefines a (.value v)) :
    a = .value v := h

theorem runtime_refusal_preserved {V E L : Type}
    (a : RuntimeOutcome V E L) (e : E) (h : RuntimeRefines a (.refused e)) :
    a = .refused e := h

/-- Runtime limit payloads remain distinguishable in the outcome vocabulary. -/
theorem allowed_limit_not_value :
    RuntimeRefines (.value 7 : RuntimeOutcome Nat String Nat) (.limit 3) ∧
    (.limit 3 : RuntimeOutcome Nat String Nat) ≠ .value 7 :=
  ⟨True.intro, fun h => RuntimeOutcome.noConfusion h⟩

/-- Keep all existing structural fields of the imported point model. -/
def runtimePoint (o : RuntimeOutcome Nat String Nat) : ExecModel :=
  { HopWitness.pt 0 with
    Outcome := RuntimeOutcome Nat String Nat
    evalRaw := fun _ => o
    evalClass := fun _ => o }

theorem runtimePoint_profile (o : RuntimeOutcome Nat String Nat) :
    hasMSTNFProfile (runtimePoint o) := by
  refine ⟨fun _ => rfl, fun _ _ _ => rfl, ?_, ?_⟩
  · intro _ _ h
    cases h
  · intro _ _ _ h
    cases h

theorem runtime_point_hop (a b : RuntimeOutcome Nat String Nat)
    (h : RuntimeRefines a b) :
    RelHopCorrect (runtimePoint a) (runtimePoint b)
      (fun _ => some ()) RuntimeRefines := by
  intro _ _ _
  exact ⟨(), (), rfl, rfl, rfl, h⟩

/-- A nonempty composed chain genuinely permits a different, named target
    outcome, while carrying an actual final raw witness. -/
theorem runtime_limit_chain :
    RelHopCorrect (runtimePoint (.value 7)) (runtimePoint (.limit 3))
      (partialHopSeq (runtimePoint (.value 7))
        (fun _ => some ()) (fun _ => some ())) RuntimeRefines ∧
    partialHopSeq (runtimePoint (.value 7))
      (fun _ : Unit => some ()) (fun _ => some ()) () = some () := by
  refine ⟨?_, rfl⟩
  exact relHopOn_comp
    (runtimePoint (.value 7)) (runtimePoint (.value 7)) (runtimePoint (.limit 3))
    (fun _ => some ()) (fun _ => some ())
    RuntimeRefines RuntimeRefines RuntimeRefines
    (fun c => (runtimePoint (.value 7)).admissible c = true)
    runtimeRefines_trans (fun _ => rfl)
    (runtime_point_hop (.value 7) (.value 7) (runtimeRefines_refl _))
    (runtime_point_hop (.value 7) (.limit 3) True.intro)

/-- Actual refused/limit source outcomes cannot be omitted from the premise.
    Here the target is deterministic, yet a success-only forward premise is
    vacuous and its sole success is unsupported by the source. -/
theorem success_only_forward_insufficient :
    ForwardOutcomes
      (fun a : RuntimeOutcome Unit Unit Unit =>
        a = .limit () ∧ ∃ v, a = .value v)
      (fun b => b = .value ()) RuntimeRefines ∧
    DeterminateOutcomes (fun b : RuntimeOutcome Unit Unit Unit => b = .value ()) ∧
    ¬ BackwardOutcomes (fun a : RuntimeOutcome Unit Unit Unit => a = .limit ())
      (fun b => b = .value ()) RuntimeRefines := by
  refine ⟨?_, fun _ _ hx hy => hx.trans hy.symm, ?_⟩
  · intro a ha
    obtain ⟨he, v, hv⟩ := ha
    rw [he] at hv
    cases hv
  · intro h
    obtain ⟨a, ha, hr⟩ := h (.value ()) rfl
    have he : a = .value () := hr
    rw [ha] at he
    cases he

/-- Compile-time absence is the imported named translation refusal. -/
theorem absent_translation_named :
    relHopRho (HopWitness.pt 0) (HopWitness.pt 0)
      (fun _ => none) (fun _ _ => true) () = some .translationRefused := rfl

def refusalPoint : ExecModel :=
  { HopWitness.ptOff 0 with sigma := fun _ => none }

theorem refusalPoint_profile : hasMSTNFProfile refusalPoint := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro _ _ h
    cases h
  · intro _ _ _ h
    cases h
  · intro _ _ h
    cases h

theorem target_refusal_named :
    relHopRho (HopWitness.pt 0) refusalPoint
      (fun _ => some ()) (fun _ _ => true) () =
      some (.targetRefused (some ())) := rfl

theorem absent_middle_no_final_witness :
    partialHopSeq refusalPoint
      (fun _ : Unit => some ()) (fun _ => some ()) () = none := rfl

end NfCompose

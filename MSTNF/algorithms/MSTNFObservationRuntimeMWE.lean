import MSTNF.algorithms.MSTNFObservationMWE
import MSTNF.algorithms.MSTNFRuntimeRefinementMWE

/-!
Observers of successful runs extend to the full outcome type by recording
each refusal reason and resource-limit label verbatim.
-/

namespace NfCompose.Observation

variable {V E L : Type}

def liftRuntime (p : Projection V) : Projection (RuntimeOutcome V E L) :=
  ⟨RuntimeOutcome p.View E L, mapRuntimeValue p.read⟩

/-- This kernel distinguishes all three outcome tags. Within the refusal
    and limit branches it distinguishes their complete payloads. -/
theorem liftRuntime_agreement (p : Projection V) (x y : RuntimeOutcome V E L) :
    (liftRuntime p).read x = (liftRuntime p).read y ↔
      match x, y with
      | .value a, .value b => p.read a = p.read b
      | .refused e, .refused f => e = f
      | .limit l, .limit k => l = k
      | _, _ => False := by
  cases x <;> cases y <;> simp [liftRuntime, mapRuntimeValue]

theorem liftRuntime_mono {p q : Projection V} (h : Coarser p q) :
    Coarser (liftRuntime (E := E) (L := L) p) (liftRuntime q) := by
  intro x y eq
  apply (liftRuntime_agreement p x y).2
  have eq' := (liftRuntime_agreement q x y).1 eq
  cases x with
  | value a =>
    cases y with
    | value b => exact h a b eq'
    | refused _ => exact eq'
    | limit _ => exact eq'
  | refused _ => cases y <;> exact eq'
  | limit _ => cases y <;> exact eq'

theorem runtime_value_coarsenings (V H E L : Type) :
    let pureView := liftRuntime (E := E) (L := L) (valueOnly : Projection (Run V H))
    Coarser pureView (liftRuntime valueHeap) ∧
    Coarser pureView (liftRuntime valueSteps) ∧
    Coarser pureView (liftRuntime valuePeak) := by
  have h := value_coarsenings V H
  exact ⟨liftRuntime_mono h.1, liftRuntime_mono h.2.1, liftRuntime_mono h.2.2⟩


end NfCompose.Observation

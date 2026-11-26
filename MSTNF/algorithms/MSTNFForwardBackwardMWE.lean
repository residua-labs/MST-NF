import MSTNF.algorithms.MSTNFRelationalHopMWE

/-!
All-outcome forward correctness and deterministic-target backward safety.
These are outcome-level statements. They do not claim to construct a small-step
backward simulation, prove receptiveness, or cover traces absent from Outcome.
-/
namespace NfCompose
open MSTNecessityExecModelMWE

def ForwardOutcomes {S T : Type} (source : S → Prop) (target : T → Prop)
    (R : S → T → Prop) : Prop :=
  ∀ s, source s → ∃ t, target t ∧ R s t

def DeterminateOutcomes {T : Type} (target : T → Prop) : Prop :=
  ∀ x y, target x → target y → x = y

def BackwardOutcomes {S T : Type} (source : S → Prop) (target : T → Prop)
    (R : S → T → Prop) : Prop :=
  ∀ t, target t → ∃ s, source s ∧ R s t

/-- A fixed source behavior and any actual target behavior are related.
    Forward correctness covers the whole source predicate, not just success. -/
theorem forward_determinate_pointwise {S T : Type}
    (source : S → Prop) (target : T → Prop) (R : S → T → Prop)
    (hf : ForwardOutcomes source target R) (hd : DeterminateOutcomes target) :
    ∀ s t, source s → target t → R s t := by
  intro s t hs ht
  obtain ⟨u, hu, hr⟩ := hf s hs
  have e := hd u t hu ht
  rw [← e]
  exact hr

/-- An existential backward witness also requires a source behavior.
    This prevents a vacuous forward proof for an empty source semantics. -/
theorem forward_determinate_backward {S T : Type}
    (source : S → Prop) (target : T → Prop) (R : S → T → Prop)
    (hne : ∃ s, source s) (hf : ForwardOutcomes source target R)
    (hd : DeterminateOutcomes target) : BackwardOutcomes source target R := by
  intro t ht
  obtain ⟨s, hs⟩ := hne
  exact ⟨s, hs, forward_determinate_pointwise source target R hf hd s t hs ht⟩

/-- A pinned ExecModel supplies a source behavior constructively. -/
theorem execModel_forward_backward (A B : ExecModel) (c : A.Class)
    (target : B.Outcome → Prop) (R : A.Outcome → B.Outcome → Prop)
    (hf : ForwardOutcomes (fun a => a = A.evalClass c) target R)
    (hd : DeterminateOutcomes target) :
    BackwardOutcomes (fun a => a = A.evalClass c) target R :=
  forward_determinate_backward _ _ R ⟨A.evalClass c, rfl⟩ hf hd

/-- The evaluator graph is deterministic; this is unrelated to AtMostOneAdmit. -/
theorem evalRaw_determinate (B : ExecModel) (b : B.Raw) :
    DeterminateOutcomes (fun o => o = B.evalRaw b) :=
  fun _ _ hx hy => hx.trans hy.symm

/-- Bind backward safety to the actual artifact produced by sigma and F.
    The interpreter must realize the selected evalRaw outcome, and every
    outcome in Run at that exact artifact must be deterministic. -/
theorem relHopCorrect_backward_actual (A B : ExecModel)
    (F : A.Rep → Option B.Raw) (R : A.Outcome → B.Outcome → Prop)
    (h : RelHopCorrect A B F R) (hqA : quotientFactorization A)
    (Run : B.Raw → B.Outcome → Prop)
    (realizes : ∀ b, Run b (B.evalRaw b))
    (determinate : ∀ b, DeterminateOutcomes (Run b))
    (a : A.Raw) (ha : A.admissible (A.q a) = true)
    (b : B.Raw) (hw : (A.sigma (A.q a)).bind F = some b) :
    B.admissible (B.q b) = true ∧
      ∀ o, Run b o → R (A.evalRaw a) o := by
  obtain ⟨hb, hr⟩ := relHopCorrect_actual A B F R h hqA a ha b hw
  refine ⟨hb, ?_⟩
  have hf : ForwardOutcomes (fun s => s = A.evalRaw a) (Run b) R := by
    intro s hs
    exact ⟨B.evalRaw b, realizes b, by rw [hs]; exact hr⟩
  exact fun o ho => forward_determinate_pointwise _ _ R hf (determinate b)
    (A.evalRaw a) o rfl ho

theorem target_determinism_needed :
    ForwardOutcomes (fun b : Bool => b = false) (fun _ : Bool => True) Eq ∧
    ¬ BackwardOutcomes (fun b : Bool => b = false) (fun _ : Bool => True) Eq := by
  constructor
  · intro s _
    exact ⟨s, True.intro, rfl⟩
  · intro h
    obtain ⟨s, hs, he⟩ := h true True.intro
    cases he
    cases hs

theorem source_nonempty_needed :
    ForwardOutcomes (fun _ : Bool => False) (fun b : Bool => b = false) Eq ∧
    DeterminateOutcomes (fun b : Bool => b = false) ∧
    ¬ BackwardOutcomes (fun _ : Bool => False) (fun b : Bool => b = false) Eq := by
  refine ⟨fun _ h => False.elim h, fun _ _ hx hy => hx.trans hy.symm, ?_⟩
  intro h
  obtain ⟨_, hs, _⟩ := h false rfl
  exact hs

end NfCompose

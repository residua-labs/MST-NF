import MSTNF.algorithms.MSTNFIndexedRunMWE

/-!
Native step-indexed quantifiers expressed through the indexed run
contract. The concrete program, image, code table and assumptions are
fixed outside this adapter. It proves no concrete compiler instance
and introduces no ExecModel.
-/

set_option autoImplicit false

namespace NfCompose.Indexed

/-- The successful native payload keeps its state. The relation also requires
    exactly one returned value, as in a pure-run contract with a fuel bound. -/
def singletonRelation {VA VB St : Type} (H : St → VA → VB → Prop)
    (va : VA) (out : List VB × St) : Prop :=
  ∃ vb, out.1 = [vb] ∧ H out.2 va vb

/-- One sufficient threshold for two independently chosen target resources. -/
def stepBound (g : Nat → Nat) (hg : ∀ a b, a ≤ b → g a ≤ g b) :
    FuelBound natBudget (pairBudget natBudget natBudget) where
  apply := fun n => (g n, g n)
  mono := fun {i j} hij => ⟨hg i j hij, hg i j hij⟩

/-- Exact quantifier adapter for the step-indexed adequacy and named-safety clauses.
    The sufficient bound is existential for the fixed native source/target pair.
    No uniform bound over unrelated programs and no same-budget refusal equality
    is asserted. Both fuel and steps remain independently quantified. -/
theorem stepShape_iff_runRefines {VA VB St E : Type}
    (runA : Nat → Option VA) (runB : Nat → Nat → Except E (List VB × St))
    (H : St → VA → VB → Prop) (named : E → Prop) :
    ((∃ g : Nat → Nat,
        (∀ a b, a ≤ b → g a ≤ g b) ∧
        ∀ n va, runA n = some va →
          ∀ fuel steps, g n ≤ fuel → g n ≤ steps →
            ∃ vb st, runB fuel steps = .ok ([vb], st) ∧ H st va vb) ∧
      (∀ fuel steps,
        (∃ vb st n va, runB fuel steps = .ok ([vb], st) ∧
          runA n = some va ∧ H st va vb) ∨
        (∃ e, runB fuel steps = .error e ∧ named e))) ↔
    ∃ (g : Nat → Nat) (hg : ∀ a b, a ≤ b → g a ≤ g b),
      RunRefines natBudget (pairBudget natBudget natBudget)
        (RunView.ofOption runA)
        (RunView.ofExcept (fun k : Nat × Nat => runB k.1 k.2))
        (stepBound g hg) (singletonRelation H) named := by
  constructor
  · rintro ⟨⟨g, hg, hadequate⟩, hsafe⟩
    refine ⟨g, hg, ?_⟩
    apply (RunRefines.ofOption_ofExcept_iff
      natBudget (pairBudget natBudget natBudget)
      runA (fun k : Nat × Nat => runB k.1 k.2)
      (stepBound g hg) (singletonRelation H) named).mpr
    constructor
    · intro n va hva j hj
      obtain ⟨vb, st, hrun, hval⟩ :=
        hadequate n va hva j.1 j.2 hj.1 hj.2
      exact ⟨([vb], st), hrun, vb, rfl, hval⟩
    · intro j
      rcases hsafe j.1 j.2 with
        ⟨vb, st, n, va, hrun, hva, hval⟩ | ⟨e, he, hn⟩
      · exact Or.inl ⟨([vb], st), n, va, hrun, hva, vb, rfl, hval⟩
      · exact Or.inr ⟨e, he, hn⟩
  · rintro ⟨g, hg, hrun⟩
    obtain ⟨hadequate, hsafe⟩ :=
      (RunRefines.ofOption_ofExcept_iff
        natBudget (pairBudget natBudget natBudget)
        runA (fun k : Nat × Nat => runB k.1 k.2)
        (stepBound g hg) (singletonRelation H) named).mp hrun
    constructor
    · refine ⟨g, hg, ?_⟩
      intro n va hva fuel steps hf hs
      obtain ⟨out, hout, hrel⟩ :=
        hadequate n va hva (fuel, steps) ⟨hf, hs⟩
      rcases out with ⟨rs, st⟩
      obtain ⟨vb, hlist, hval⟩ := hrel
      change rs = [vb] at hlist
      subst rs
      exact ⟨vb, st, hout, hval⟩
    · intro fuel steps
      rcases hsafe (fuel, steps) with
        ⟨out, n, va, hout, hva, hrel⟩ | ⟨e, he, hn⟩
      · rcases out with ⟨rs, st⟩
        obtain ⟨vb, hlist, hval⟩ := hrel
        change rs = [vb] at hlist
        subst rs
        exact Or.inl ⟨vb, st, n, va, hout, hva, hval⟩
      · exact Or.inr ⟨e, he, hn⟩

end NfCompose.Indexed

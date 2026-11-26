import MSTNF.algorithms.MSTNFRelationalHopMWE

/-!
Indexed runs, adequate monotone bounds, related values,
and pointwise named refusals. No new ExecModel is introduced.
-/

set_option autoImplicit false

namespace NfCompose.Indexed

/-- The order on runtime budgets is declared independently of any global instance. -/
structure BudgetOrder (I : Type) where
  le : I → I → Prop
  refl : ∀ i, le i i
  trans : ∀ {i j k}, le i j → le j k → le i k

def natBudget : BudgetOrder Nat where
  le := Nat.le
  refl := Nat.le_refl
  trans := fun h₁ h₂ => Nat.le_trans h₁ h₂

/-- Independent resource coordinates, such as a fuel budget and interpreter steps. -/
def pairBudget {I J : Type} (a : BudgetOrder I) (b : BudgetOrder J) :
    BudgetOrder (I × J) where
  le := fun i j => a.le i.1 j.1 ∧ b.le i.2 j.2
  refl := fun i => ⟨a.refl i.1, b.refl i.2⟩
  trans := fun h₁ h₂ => ⟨a.trans h₁.1 h₂.1, b.trans h₁.2 h₂.2⟩

/-- A threshold above which every target budget is required to give a value.
    The bound can depend on the particular successful artifact witness. -/
structure FuelBound {I J : Type} (a : BudgetOrder I) (b : BudgetOrder J) where
  apply : I → J
  mono : ∀ {i j}, a.le i j → b.le (apply i) (apply j)

namespace FuelBound

def id {I : Type} (a : BudgetOrder I) : FuelBound a a where
  apply := fun i => i
  mono := fun hij => hij

/-- First use g, then h. -/
def comp {I J K : Type} {a : BudgetOrder I} {b : BudgetOrder J}
    {c : BudgetOrder K} (g : FuelBound a b) (h : FuelBound b c) :
    FuelBound a c where
  apply := fun i => h.apply (g.apply i)
  mono := fun hij => h.mono (g.mono hij)

/-- The same source threshold bounds both independently chosen target resources. -/
def diagonal : FuelBound natBudget (pairBudget natBudget natBudget) where
  apply := fun n => (n, n)
  mono := fun h => ⟨h, h⟩

theorem id_apply {I : Type} (a : BudgetOrder I) (i : I) :
    (id a).apply i = i := rfl

theorem comp_apply {I J K : Type} {a : BudgetOrder I}
    {b : BudgetOrder J} {c : BudgetOrder K}
    (g : FuelBound a b) (h : FuelBound b c) (i : I) :
    (comp g h).apply i = h.apply (g.apply i) := rfl

theorem diagonal_apply (n : Nat) : diagonal.apply n = (n, n) := rfl

end FuelBound

/-- A semantic view of one fixed artifact in its declared runtime context.
    Predicates permit native interpreters to be used without recoding their outcomes.
    No determinacy or totality is silently imposed on an arbitrary view. -/
structure RunView (I V E : Type) where
  value : I → V → Prop
  refusal : I → E → Prop

namespace RunView

/-- A native Option interpreter. None supplies no value and no refusal name;
    it may describe exhaustion or nontermination, without choosing between them. -/
def ofOption {I V : Type} (run : I → Option V) : RunView I V Empty where
  value := fun i v => run i = some v
  refusal := fun _ _ => False

/-- A native Except interpreter; its complete error payload is retained. -/
def ofExcept {I V E : Type} (run : I → Except E V) : RunView I V E where
  value := fun i v => run i = .ok v
  refusal := fun i e => run i = .error e

/-- The unindexed evaluator embedding. No refusal is added. -/
def constant {V : Type} (I : Type) (v : V) : RunView I V Empty where
  value := fun _ w => w = v
  refusal := fun _ _ => False

end RunView

/-- Forward adequacy above a monotone threshold, backward value soundness, and
    complete named target behavior. The named field covers every refusal witness,
    including for a nondeterministic view; total alone would not imply that.

    A run view fixes its artifact and context. When used in a hop, R can therefore
    depend on the exact source representative and the exact translated artifact. -/
structure RunRefines {I J VA VB EA EB : Type}
    (a : BudgetOrder I) (b : BudgetOrder J)
    (A : RunView I VA EA) (B : RunView J VB EB)
    (g : FuelBound a b) (R : VA → VB → Prop) (allowed : EB → Prop) : Prop where
  adequate : ∀ i va, A.value i va →
    ∀ j, b.le (g.apply i) j → ∃ vb, B.value j vb ∧ R va vb
  sound : ∀ j vb, B.value j vb → ∃ i va, A.value i va ∧ R va vb
  named : ∀ j e, B.refusal j e → allowed e
  total : ∀ j, (∃ vb, B.value j vb) ∨ ∃ e, B.refusal j e

namespace RunRefines

theorem at_bound {I J VA VB EA EB : Type}
    {a : BudgetOrder I} {b : BudgetOrder J}
    {A : RunView I VA EA} {B : RunView J VB EB}
    {g : FuelBound a b} {R : VA → VB → Prop} {allowed : EB → Prop}
    (h : RunRefines a b A B g R allowed)
    (i : I) (va : VA) (hv : A.value i va) :
    ∃ vb, B.value (g.apply i) vb ∧ R va vb :=
  h.adequate i va hv (g.apply i) (b.refl (g.apply i))

/-- Only final-endpoint names are required. A refusal of the middle run at one
    budget is not asserted to equal a refusal of the final run at that budget. -/
theorem seq {I J K VA VB VC EA EB EC : Type}
    {a : BudgetOrder I} {b : BudgetOrder J} {c : BudgetOrder K}
    {A : RunView I VA EA} {B : RunView J VB EB} {C : RunView K VC EC}
    {g : FuelBound a b} {h : FuelBound b c}
    {R : VA → VB → Prop} {S : VB → VC → Prop}
    {namedB : EB → Prop} {namedC : EC → Prop}
    (hAB : RunRefines a b A B g R namedB)
    (hBC : RunRefines b c B C h S namedC) :
    RunRefines a c A C (FuelBound.comp g h) (RelComp R S) namedC := by
  refine ⟨?_, ?_, hBC.named, hBC.total⟩
  · intro i va hva k hk
    obtain ⟨vb, hvb, hR⟩ := hAB.at_bound i va hva
    obtain ⟨vc, hvc, hS⟩ := hBC.adequate (g.apply i) vb hvb k hk
    exact ⟨vc, hvc, vb, hR, hS⟩
  · intro k vc hvc
    obtain ⟨j, vb, hvb, hS⟩ := hBC.sound k vc hvc
    obtain ⟨i, va, hva, hR⟩ := hAB.sound j vb hvb
    exact ⟨i, va, hva, vb, hR, hS⟩

theorem relation_mono {I J VA VB EA EB : Type}
    {a : BudgetOrder I} {b : BudgetOrder J}
    {A : RunView I VA EA} {B : RunView J VB EB}
    {g : FuelBound a b} {R S : VA → VB → Prop} {allowed : EB → Prop}
    (hRS : ∀ va vb, R va vb → S va vb)
    (h : RunRefines a b A B g R allowed) :
    RunRefines a b A B g S allowed := by
  refine ⟨?_, ?_, h.named, h.total⟩
  · intro i va hva j hj
    obtain ⟨vb, hvb, hR⟩ := h.adequate i va hva j hj
    exact ⟨vb, hvb, hRS va vb hR⟩
  · intro j vb hvb
    obtain ⟨i, va, hva, hR⟩ := h.sound j vb hvb
    exact ⟨i, va, hva, hRS va vb hR⟩

theorem names_mono {I J VA VB EA EB : Type}
    {a : BudgetOrder I} {b : BudgetOrder J}
    {A : RunView I VA EA} {B : RunView J VB EB}
    {g : FuelBound a b} {R : VA → VB → Prop} {P Q : EB → Prop}
    (h : RunRefines a b A B g R P)
    (hPQ : ∀ e, P e → Q e) :
    RunRefines a b A B g R Q := by
  refine ⟨h.adequate, h.sound, ?_, h.total⟩
  intro j e he
  exact hPQ e (h.named j e he)

/-- Lifting the adequate threshold preserves the contract. Both thresholds are
    still explicitly monotone FuelBounds. -/
theorem bound_mono {I J VA VB EA EB : Type}
    {a : BudgetOrder I} {b : BudgetOrder J}
    {A : RunView I VA EA} {B : RunView J VB EB}
    {g g' : FuelBound a b} {R : VA → VB → Prop} {allowed : EB → Prop}
    (h : RunRefines a b A B g R allowed)
    (hgg' : ∀ i, b.le (g.apply i) (g'.apply i)) :
    RunRefines a b A B g' R allowed := by
  refine ⟨?_, h.sound, h.named, h.total⟩
  intro i va hva j hj
  exact h.adequate i va hva j (b.trans (hgg' i) hj)

/-- Source views may have unrelated refusal carriers: only source successes
    occur in the refinement obligations. The index is kept exactly. -/
theorem source_transport {I J VA VB EA EA' EB : Type}
    {a : BudgetOrder I} {b : BudgetOrder J}
    {A : RunView I VA EA} {A' : RunView I VA EA'} {B : RunView J VB EB}
    {g : FuelBound a b} {R : VA → VB → Prop} {allowed : EB → Prop}
    (hvalue : ∀ i va, A.value i va ↔ A'.value i va)
    (h : RunRefines a b A B g R allowed) :
    RunRefines a b A' B g R allowed := by
  refine ⟨?_, ?_, h.named, h.total⟩
  · intro i va hva j hj
    exact h.adequate i va ((hvalue i va).mpr hva) j hj
  · intro j vb hvb
    obtain ⟨i, va, hva, hR⟩ := h.sound j vb hvb
    exact ⟨i, va, (hvalue i va).mp hva, hR⟩

/-- A declared change of target view keeps both values and refusal names at
    the same index. No equality between different resource budgets is inferred. -/
theorem target_transport {I J VA VB EA EB : Type}
    {a : BudgetOrder I} {b : BudgetOrder J}
    {A : RunView I VA EA} {B B' : RunView J VB EB}
    {g : FuelBound a b} {R : VA → VB → Prop} {allowed : EB → Prop}
    (hvalue : ∀ j vb, B.value j vb ↔ B'.value j vb)
    (hrefusal : ∀ j e, B.refusal j e ↔ B'.refusal j e)
    (h : RunRefines a b A B g R allowed) :
    RunRefines a b A B' g R allowed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i va hva j hj
    obtain ⟨vb, hvb, hR⟩ := h.adequate i va hva j hj
    exact ⟨vb, (hvalue j vb).mp hvb, hR⟩
  · intro j vb hvb
    exact h.sound j vb ((hvalue j vb).mpr hvb)
  · intro j e he
    exact h.named j e ((hrefusal j e).mpr he)
  · intro j
    rcases h.total j with ⟨vb, hvb⟩ | ⟨e, he⟩
    · exact Or.inl ⟨vb, (hvalue j vb).mp hvb⟩
    · exact Or.inr ⟨e, (hrefusal j e).mp he⟩

/-- A success-or-named-refusal disjunction follows without determinacy assumptions. -/
theorem safe {I J VA VB EA EB : Type}
    {a : BudgetOrder I} {b : BudgetOrder J}
    {A : RunView I VA EA} {B : RunView J VB EB}
    {g : FuelBound a b} {R : VA → VB → Prop} {allowed : EB → Prop}
    (h : RunRefines a b A B g R allowed) (j : J) :
    (∃ vb i va, B.value j vb ∧ A.value i va ∧ R va vb) ∨
      (∃ e, B.refusal j e ∧ allowed e) := by
  rcases h.total j with ⟨vb, hvb⟩ | ⟨e, he⟩
  · obtain ⟨i, va, hva, hR⟩ := h.sound j vb hvb
    exact Or.inl ⟨vb, i, va, hvb, hva, hR⟩
  · exact Or.inr ⟨e, he, h.named j e he⟩

/-- A source index is explicit: an empty index carrier cannot supply the
    backward witness required by soundness. This embedding recovers arbitrary
    relations on the old evaluator outcomes, without assuming equality. -/
theorem constant_iff {I J VA VB : Type}
    (a : BudgetOrder I) (b : BudgetOrder J) (i₀ : I)
    (g : FuelBound a b) (va : VA) (vb : VB)
    (R : VA → VB → Prop) (allowed : Empty → Prop) :
    RunRefines a b (RunView.constant I va) (RunView.constant J vb)
      g R allowed ↔ R va vb := by
  constructor
  · intro h
    obtain ⟨w, hw, hR⟩ := h.at_bound i₀ va rfl
    have hw' : w = vb := hw
    rw [hw'] at hR
    exact hR
  · intro hR
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i va' hva j hj
      have hv : va' = va := hva
      subst va'
      exact ⟨vb, rfl, hR⟩
    · intro j vb' hvb
      have hv : vb' = vb := hvb
      subst vb'
      exact ⟨i₀, va, rfl, hR⟩
    · intro j e he
      exact False.elim he
    · intro j
      exact Or.inl ⟨vb, rfl⟩

/-- Exact bridge for native Option/Except interpreters. The native function gives
    uniqueness and value/error disjointness in the reverse direction; arbitrary
    RunViews do not acquire either law.

    For a fuel-and-step budget use J = Nat × Nat and target payload List V × St. The relation on that
    payload states that the list is a singleton and that HVal holds in its heap.
    Thus malformed successful payloads are excluded by soundness. -/
theorem ofOption_ofExcept_iff {I J VA VB E : Type}
    (a : BudgetOrder I) (b : BudgetOrder J)
    (runA : I → Option VA) (runB : J → Except E VB)
    (g : FuelBound a b) (R : VA → VB → Prop) (allowed : E → Prop) :
    RunRefines a b (RunView.ofOption runA) (RunView.ofExcept runB)
      g R allowed ↔
    (∀ i va, runA i = some va →
      ∀ j, b.le (g.apply i) j →
        ∃ vb, runB j = .ok vb ∧ R va vb) ∧
    (∀ j,
      (∃ vb i va, runB j = .ok vb ∧ runA i = some va ∧ R va vb) ∨
        (∃ e, runB j = .error e ∧ allowed e)) := by
  constructor
  · intro h
    exact ⟨h.adequate, fun j => h.safe j⟩
  · rintro ⟨hadequate, hsafe⟩
    refine ⟨hadequate, ?_, ?_, ?_⟩
    · intro j vb hvb
      rcases hsafe j with ⟨vb', i, va, hvb', hva, hR⟩ | ⟨e, he, hnamed⟩
      · have hv : vb' = vb := Except.ok.inj (hvb'.symm.trans hvb)
        subst vb'
        exact ⟨i, va, hva, hR⟩
      · have hbad : Except.ok vb = Except.error e := hvb.symm.trans he
        cases hbad
    · intro j e he
      rcases hsafe j with ⟨vb, i, va, hvb, hva, hR⟩ | ⟨e', he', hnamed⟩
      · have hbad : Except.ok vb = Except.error e := hvb.symm.trans he
        cases hbad
      · have heq : e' = e := Except.error.inj (he'.symm.trans he)
        subst e'
        exact hnamed
    · intro j
      cases hr : runB j with
      | ok vb => exact Or.inl ⟨vb, hr⟩
      | error e => exact Or.inr ⟨e, hr⟩

end RunRefines

end NfCompose.Indexed

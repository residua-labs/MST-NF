import Mathlib.Tactic

namespace RP04

variable {α β γ : Type}

-- PROBE A1 (ABSTRACTED, folded form): the exact statement of the Mathlib needle
example (f : α → β) (g : α → γ) [Nonempty γ] :
    (∀ ⦃a b : α⦄, f a = f b → g a = g b) ↔ ∃ e : β → γ, g = e ∘ f := by
  exact?

end RP04

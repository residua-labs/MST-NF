import Mathlib.Tactic

namespace RP06

variable {α β γ : Type}

-- PROBE A3 (ABSTRACTED, one direction: the step the FDT re-proof consumed)
example (f : α → β) (g : α → γ) [Nonempty γ]
    (h : ∀ ⦃a b : α⦄, f a = f b → g a = g b) :
    ∃ e : β → γ, g = e ∘ f := by
  exact?

end RP06

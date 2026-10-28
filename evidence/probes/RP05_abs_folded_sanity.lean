import Mathlib.Tactic
open Function

namespace RP05

variable {α β γ : Type}

-- PROBE A2 (ABSTRACTED, folded Mathlib form — tool sanity check)
example (f : α → β) (g : α → γ) [Nonempty γ] :
    g.FactorsThrough f ↔ ∃ e : β → γ, g = e ∘ f := by
  exact?

end RP05

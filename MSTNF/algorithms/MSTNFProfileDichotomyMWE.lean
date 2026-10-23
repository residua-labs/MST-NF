import MSTNF.algorithms.MSTNecessityExecModelMWE

/-!
# MST-NF profile: the per-input dichotomy

Under the MST-NF execution profile (`hasMSTNFProfile`), every raw input falls in an active class, and that class is
either admissible and has a representative, or is not admissible, has no representative, and has a residue.

This is a direct consequence of the four obligations; it is stated here as a theorem so that the sentence
"no refusal is without a reason" resolves to a named statement. It says nothing about the outcome `evalRaw` an input
produces (that is only required to factor through the class), and nothing about how many raw inputs of a class are
admitted (the separate `AtMostOneAdmit` condition).
-/

namespace MSTNFProfileDichotomyMWE

open MSTNecessityExecModelMWE

theorem input_dichotomy (M : ExecModel) (h : hasMSTNFProfile M) (r : M.Raw) :
    (M.admissible (M.q r) = true ∧ M.sigma (M.q r) ≠ none) ∨
    (M.admissible (M.q r) = false ∧ M.sigma (M.q r) = none ∧ M.rho (M.q r) ≠ none) := by
  obtain ⟨_hq, hs, hr, hp⟩ := h
  have hact : activeClass M (M.q r) := ⟨r, rfl⟩
  cases hadm : M.admissible (M.q r) with
  | true => exact Or.inl ⟨rfl, hp _ hact hadm⟩
  | false =>
    refine Or.inr ⟨rfl, ?_, hr _ hact hadm⟩
    cases hsig : M.sigma (M.q r) with
    | none => rfl
    | some rep =>
      have := hs _ rep hsig
      rw [hadm] at this
      exact absurd this (by decide)

/-- A class with a representative is admissible: `admissibilitySound`, restated for the per-input class. -/
theorem representative_only_if_admitted (M : ExecModel) (h : hasMSTNFProfile M) (r : M.Raw) :
    M.sigma (M.q r) ≠ none → M.admissible (M.q r) = true := by
  intro hne
  rcases input_dichotomy M h r with ⟨ha, _⟩ | ⟨_, hnone, _⟩
  · exact ha
  · exact absurd hnone hne

end MSTNFProfileDichotomyMWE

#print axioms MSTNFProfileDichotomyMWE.input_dichotomy
#print axioms MSTNFProfileDichotomyMWE.representative_only_if_admitted

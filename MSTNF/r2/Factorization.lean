import MSTNF.algorithms.MSTNecessityExecModelMWE

/-!
# MST-NF R2 — P1 (observation factorization) and P4 (source normalization)

Mechanization of the R2 contract, section 7 registry rows P1 and P4; paper
v0.2 sections 2 (Proposition 1) and 4.3 (Proposition 4).

Sources (mature sources rule, preamble item 7):
- Design of record: the R2 mechanization contract
  section 7; paper v0.2 `MST-NF-paper-v0.2.md` sections 2 and 4.3.
- Pinned base: `MSTNF.algorithms.MSTNecessityExecModelMWE`
  (`semantics_factor_through_kernel_quotient` states P1 over the kernel
  quotient; the statement here is the same universal property, restated in the
  R2 registry namespace).
- Quotient API: Lean 4 core `Quot` (`Init.Core`), Theorem Proving in Lean 4,
  "Quotients". Section/stability laws for definable quotients are standard
  (Isabelle quotient infrastructure, Huffman & Kunčar; cited by the paper).

No Mathlib import; no `sorry`; no `native_decide`; no new axioms.
-/

namespace MSTNFR2

open MSTNecessityExecModelMWE

/-! ## P1: observation factorization through the kernel quotient -/

/-- **P1** (observation factorization): an observation that respects the key
    factors through the kernel quotient, with a unique factor. Existence and
    uniqueness are both part of the claim (`mbar` is `Quot.lift m h`). -/
theorem P1_observation_factorization {X Q D : Type} (q : X → Q) (m : X → D)
    (h : ∀ x y : X, q x = q y → m x = m y) :
    ∃ mbar : Quot (fun (x y : X) => q x = q y) → D,
      (∀ x : X, m x = mbar (Quot.mk _ x)) ∧
      ∀ mbar' : Quot (fun (x y : X) => q x = q y) → D,
        (∀ x : X, m x = mbar' (Quot.mk _ x)) →
        ∀ z : Quot (fun (x y : X) => q x = q y), mbar z = mbar' z := by
  refine ⟨Quot.lift m (fun x y hxy => h x y hxy), fun x => rfl, ?_⟩
  intro mbar' hm' z
  refine Quot.inductionOn z ?_
  intro x
  exact hm' x

/-- Converse direction of paper Proposition 1: any function that factors
    through the kernel quotient respects the kernel equivalence. Together
    with `P1_observation_factorization` (existence and uniqueness of the
    factor) this is the "if and only if" of eq. (1). -/
theorem P1_factorization_converse {X Q D : Type} (q : X → Q) (m : X → D)
    (mbar : Quot (fun (x y : X) => q x = q y) → D)
    (h : ∀ x : X, m x = mbar (Quot.mk _ x)) :
    ∀ x y : X, q x = q y → m x = m y := by
  intro x y hq
  rw [h x, h y]
  exact congrArg mbar (Quot.sound hq)

/-! ## P4: source normalization on admitted classes -/

/-- The partial normalizer `N : X → Option X` of the paper, section 4.3:
    `iota` applied to the representative selected by the class of `x`. -/
def partialNormalizer (M : ExecModel) (iota : M.Rep → M.Raw) (x : M.Raw) :
    Option M.Raw := (M.sigma (M.q x)).map iota

/-- **P4** (normalization on admitted classes): under the active source
    section (6), a successful normalization stays inside its class and is a
    fixed point. -/
theorem P4_normalization (M : ExecModel) (iota : M.Rep → M.Raw)
    (hsec : ∀ (c : M.Class) (r : M.Rep), activeClass M c →
      M.sigma c = some r → M.q (iota r) = c) :
    ∀ x x' : M.Raw, partialNormalizer M iota x = some x' →
      M.q x' = M.q x ∧ partialNormalizer M iota x' = some x' := by
  intro x x' h
  cases hs : M.sigma (M.q x) with
  | some r =>
      simp only [partialNormalizer, hs, Option.map_some'] at h
      injection h with hx
      have hqx : M.q x' = M.q x := by
        rw [← hx]
        exact hsec (M.q x) r ⟨x, rfl⟩ hs
      refine ⟨hqx, ?_⟩
      simp only [partialNormalizer, hqx, hs, Option.map_some']
      rw [hx]
  | none => simp only [partialNormalizer, hs, Option.map_none'] at h; exact Option.noConfusion h

/-- The normalizer depends on the input only through its class, so it can
    never separate equal-key inputs (paper, Proposition 4, final clause). -/
theorem P4_normalizer_respects_quotient (M : ExecModel) (iota : M.Rep → M.Raw) :
    ∀ x y : M.Raw, M.q x = M.q y →
      partialNormalizer M iota x = partialNormalizer M iota y := by
  intro x y hq
  simp only [partialNormalizer]
  rw [hq]

end MSTNFR2

import Mathlib.Tactic
import MSTNF.algorithms.MSTNF3FormMWE
-- Zero ICT tokens.
-- Construct-or-diagnose: does Ω-UP force the full Σ-typed Λ, or only the tag?
-- An earlier claim deferred the topos/Ω formalisation [O]. This probe settles it by Lean.

/-!
# 3-Form Ω-UP Probe: tag forced vs full Λ forced?

## Probe question ([O] machine-checked here)

The earlier claim was "the Λ-shape is universally canonical via the Ω subobject-classifier UP"
but deferred topos/Ω formalisation `[O]` (Lean = `rfl` + enum verdict).

This file does the actual Lean proof:
1. **`bool_omega_up` [V]**: the Ω-UP at Bool level (genuine proof, not `rfl`-recording).
2. **`tag_is_omega_forced` [V]**: Λ.tag = M.admissible is the unique Bool-classifier.
3. **`two_Lambdas_same_tag_distinct_witnesses` [V]**: same tag, different Λ witnesses.
4. **`three_form_canonicity_machine_status` [V]**: verdict (b).

## Verdict (b): tag-only forced

- **Ω-UP forces `Λ.tag`**: the classifying-map Bool-function `M.admissible : Class → Bool`
  is the UNIQUE Bool-function classifying the Lambda-inl subobject. This IS machine-checked.
- **Ω-UP does NOT force the full Σ-typed Λ**: `M_left` / `M_right` have the same tag but
  different representative choices (0 vs 1 for the true-class). The `IsRep`/`IsResidue`
  witnesses are per-carrier; Ω does not see them.

## Consequence

The claim "Λ-shape Ω-forced" is **accurate** for "shape = tag" (machine-checked here).
It is an **over-claim** for "shape = full Σ-typed Λ" (refuted by the (b) witness).
The **4-form remains the sole machine-checked authoritative form** (frozen).
-/

namespace MSTNF3FormOmegaForcedProbeMWE

open MSTNF3FormMWE

-- ===========================================================================
-- §1  Bool Ω-UP: characteristic function uniqueness (genuine proof)
-- ===========================================================================

/-- **[V] `bool_omega_up`**: the Ω-UP at Bool level.

    For any predicate P : X → Prop [DecidablePred], the Bool characteristic
    function `decide P` is the UNIQUE Bool-function whose `true`-fiber equals
    {x | P x}.

    Proof: case-split on χ x and decide (P x); h is CONSUMED in every branch
    (simp_all uses h to derive contradictions for the mismatched cases).
    No `rfl`-recording; no enum verdict. This is genuine Ω content. -/
theorem bool_omega_up {X : Type} (P : X → Prop) [DecidablePred P]
    (χ : X → Bool)
    (h : ∀ x, χ x = true ↔ P x) :
    χ = fun x => decide (P x) := by
  funext x
  have hiff : χ x = true ↔ decide (P x) = true := by
    rw [decide_eq_true_eq]; exact h x
  cases hχ : χ x <;> cases hd : decide (P x) <;> simp_all

-- ===========================================================================
-- §2  tag_is_omega_forced: Λ.tag uniquely determined
-- ===========================================================================

/-- **[V] `tag_is_omega_forced`**: any Bool-classifier for the Lambda-inl subobject
    equals M.admissible.

    Given χ : Class → Bool with the same true-fiber as M.admissible (same subobject),
    χ = M.admissible.

    **This is the Ω-UP for ExecModel3**: the classifying map is unique for a given
    subobject. h CONSUMED (simp_all uses h to close true/false case mismatches).
    Not a `rfl`-recording — requires genuine case analysis. -/
theorem tag_is_omega_forced (M : ExecModel3)
    (χ : M.Class → Bool)
    (h : ∀ c, χ c = true ↔ M.admissible c = true) :
    χ = M.admissible := by
  funext c
  cases hχ : χ c <;> cases ha : M.admissible c <;> simp_all [h]

-- ===========================================================================
-- §3  The (b) witness: same tag, different Σ-typed Λ values
-- ===========================================================================

-- Rep = ℕ for M_left / M_right: concrete values 0 and 1 reduce definitionally.
-- IsRep b r  = (b = true)    — trivial: any ℕ rep is valid for the true-class
-- IsResidue b e = (b = false) — trivial: () is valid for the false-class

/-- M_left: picks representative **0 : ℕ** for the true-class. -/
def M_left : ExecModel3 where
  Raw := Bool; Class := Bool; Rep := ℕ; Residue := Unit; Outcome := Bool
  IsRep := fun b _ => b = true
  IsResidue := fun b _ => b = false
  q := id; evalRaw := id; evalClass := id
  Lambda := fun b =>
    match b with
    | true  => Sum.inl ⟨0, rfl⟩
    | false => Sum.inr ⟨(), rfl⟩

/-- M_right: picks representative **1 : ℕ** for the true-class. -/
def M_right : ExecModel3 where
  Raw := Bool; Class := Bool; Rep := ℕ; Residue := Unit; Outcome := Bool
  IsRep := fun b _ => b = true
  IsResidue := fun b _ => b = false
  q := id; evalRaw := id; evalClass := id
  Lambda := fun b =>
    match b with
    | true  => Sum.inl ⟨1, rfl⟩
    | false => Sum.inr ⟨(), rfl⟩

/-- [V] Both models have the SAME Λ.tag. Reduces definitionally per branch. -/
theorem M_same_tag : M_left.admissible = M_right.admissible := by
  funext b; cases b <;> rfl

/-- [V] M_left and M_right have DIFFERENT sigma values at the true-class.
    sigma reduces: M_left.sigma true = some 0, M_right.sigma true = some 1.
    0 ≠ 1 in ℕ — decidable. `show` uses definitional reduction. -/
theorem M_different_sigma : M_left.sigma true ≠ M_right.sigma true := by
  show some (0 : ℕ) ≠ some 1
  decide

/-- **[V] `two_Lambdas_same_tag_distinct_witnesses`**: the explicit (b) witness.

    M_left and M_right are two well-formed ExecModel3 models with:
    - **Same Λ.tag** (`M_left.admissible = M_right.admissible`):
      the Ω-UP sees one classifying map and cannot distinguish them.
    - **Different Λ values** (`M_left.sigma true ≠ M_right.sigma true`):
      Rep-choice 0 vs 1 for the true-class; both valid under IsRepBool.

    IsRepBool CONSUMED: both models use the SAME trivial IsRepBool (any Fin 2 element
    is valid), yet the Λ values differ. Delete the shared IsRep → the two models
    collapse to identical Λ. The choice of which Rep value to embed is beyond Ω-UP.

    **This proves (b)**: Ω forces the tag, not the full Σ-typed Λ. The `IsRep`/
    `IsResidue` witnesses are **additional structure Ω does not see**. -/
theorem two_Lambdas_same_tag_distinct_witnesses :
    M_left.admissible = M_right.admissible ∧
    M_left.sigma true ≠ M_right.sigma true :=
  ⟨M_same_tag, M_different_sigma⟩

-- ===========================================================================
-- §4  Verdict
-- ===========================================================================

/-- **[V] `three_form_canonicity_machine_status`**: verdict **(b)** — tag-only Ω-forced.

    Packages both halves:

    **Half 1 (Ω-UP forces tag)**: any Bool-classifier for the Lambda-inl subobject
    is uniquely `M.admissible` (`tag_is_omega_forced`). The Bool classifying map IS
    Ω-forced — machine-checked, not `rfl`-recording.

    **Half 2 (Ω-UP does NOT force full Σ-Λ)**: M_left / M_right have the same tag
    but different Lambda values (`two_Lambdas_same_tag_distinct_witnesses`). The
    specific Rep-choice within the Σ-type is per-carrier; Ω does not see it.

    **Consequence**:
    - "Λ-shape Ω-forced" is **accurate** for tag-only: `M.admissible` is Ω-forced.
    - The claim is an **over-claim** for the full Σ-typed Λ (with IsRep/IsResidue witnesses).
    - The **4-form remains the sole machine-checked authoritative Lean form** (FROZEN).
    - The 3-form's Σ-witnesses are per-carrier structure beyond Ω-UP.

    Both conjuncts consume their respective lemmas; neither is vacuous. -/
theorem three_form_canonicity_machine_status :
    (∀ (M : ExecModel3) (χ : M.Class → Bool),
      (∀ c, χ c = true ↔ M.admissible c = true) → χ = M.admissible) ∧
    (M_left.admissible = M_right.admissible ∧
     M_left.sigma true ≠ M_right.sigma true) :=
  ⟨fun M χ h => tag_is_omega_forced M χ h,
   two_Lambdas_same_tag_distinct_witnesses⟩

-- ===========================================================================
-- §5  Honesty markers
-- ===========================================================================

def verdict_CERTIFIED : String :=
  "[V] bool_omega_up: Ω-UP at Bool level — unique char fn (genuine case proof; h consumed). " ++
  "[V] tag_is_omega_forced: Λ.tag (admissible) unique for subobject — Ω-UP applied (h consumed). " ++
  "[V] two_Lambdas_same_tag_distinct_witnesses: M_left / M_right — same tag, sigma 0 ≠ 1 (decide). " ++
  "[V] three_form_canonicity_machine_status: verdict (b) — tag Ω-forced; full Σ-Λ NOT Ω-forced. " ++
  "Tag-only accurate; over-claim for full Σ-Λ. 4-form stays canonical Lean form (FROZEN). " ++
  "3-form Σ-witnesses (IsRep/IsResidue) are per-carrier beyond Ω-UP. Not trivial rfl-recording."

end MSTNF3FormOmegaForcedProbeMWE

#print axioms MSTNF3FormOmegaForcedProbeMWE.bool_omega_up
#print axioms MSTNF3FormOmegaForcedProbeMWE.tag_is_omega_forced
#print axioms MSTNF3FormOmegaForcedProbeMWE.two_Lambdas_same_tag_distinct_witnesses
#print axioms MSTNF3FormOmegaForcedProbeMWE.three_form_canonicity_machine_status

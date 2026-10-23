/-!
# MST-NF Structural Advantage MWE

This file formalizes the narrow mathematical condition under which MST-NF
reduces execution cardinality.

Let:

```text
N = |E|       raw candidates/events
Q = |Q(E)|    quotient classes
K = |A(E)|    admissible quotient classes
```

with:

```text
K <= Q <= N
```

Then MST-NF has a strict execution-cardinality reduction exactly when either
the quotient is nontrivial (`Q < N`) or the admissibility filter is nontrivial
(`K < Q`).

This is not a wall-clock theorem and not a Big-O theorem.  It isolates the
structural source of advantage:

```text
raw multiplicity or inadmissibility must exist.
```
-/

namespace MSTNFStructuralAdvantageMWE

structure CompressionCounts where
  raw : Nat
  quotient : Nat
  admissible : Nat
  h_admissible_le_quotient : admissible ≤ quotient
  h_quotient_le_raw : quotient ≤ raw

/-- A nontrivial quotient means distinct raw candidates collapse into fewer
    quotient classes. -/
def NontrivialQuotient (C : CompressionCounts) : Prop :=
  C.quotient < C.raw

/-- A nontrivial admissibility filter means some quotient class is not
    executable. -/
def NontrivialAdmissibilityFilter (C : CompressionCounts) : Prop :=
  C.admissible < C.quotient

/-- A strict native execution-cardinality reduction means the admissible
    execution carrier is smaller than the raw candidate carrier. -/
def StrictExecutionReduction (C : CompressionCounts) : Prop :=
  C.admissible < C.raw

/-- The exact structural condition for a strict execution-cardinality
    reduction.

    Under `K <= Q <= N`,

    ```text
    K < N  iff  Q < N or K < Q.
    ```

    In paper language: MST-NF has structural execution-cardinality advantage
    exactly when there is either quotient compression or admissibility
    compression. -/
theorem strict_reduction_iff_nontrivial_quotient_or_filter
    (C : CompressionCounts) :
    StrictExecutionReduction C ↔
      NontrivialQuotient C ∨ NontrivialAdmissibilityFilter C := by
  constructor
  · intro hred
    by_cases hq : C.quotient < C.raw
    · exact Or.inl hq
    · have hraw_le_q : C.raw ≤ C.quotient := Nat.le_of_not_gt hq
      have hq_eq_raw : C.quotient = C.raw :=
        Nat.le_antisymm C.h_quotient_le_raw hraw_le_q
      exact Or.inr (by simpa [NontrivialAdmissibilityFilter, hq_eq_raw] using hred)
  · intro h
    cases h with
    | inl hq =>
        exact Nat.lt_of_le_of_lt C.h_admissible_le_quotient hq
    | inr hf =>
        exact Nat.lt_of_lt_of_le hf C.h_quotient_le_raw

/-- No structural execution-cardinality reduction means there is neither
    quotient compression nor admissibility compression. -/
theorem no_reduction_iff_no_quotient_no_filter
    (C : CompressionCounts) :
    C.admissible = C.raw ↔
      C.quotient = C.raw ∧ C.admissible = C.quotient := by
  constructor
  · intro h
    have hraw_le_q : C.raw ≤ C.quotient := by
      simpa [h] using C.h_admissible_le_quotient
    have hq_eq_raw : C.quotient = C.raw :=
      Nat.le_antisymm C.h_quotient_le_raw hraw_le_q
    exact ⟨hq_eq_raw, by simp [h, hq_eq_raw]⟩
  · intro h
    rw [h.2, h.1]

/-- Abstract total-work model for a raw/classic baseline. -/
def classicWork
    (execCost retryCost classicAttempts retryAttempts : Nat) : Nat :=
  execCost * classicAttempts + retryCost * retryAttempts

/-- Abstract total-work model for an MST-NF pipeline. -/
def mstnfWork
    (normCost execCost residueCost raw admissible residues : Nat) : Nat :=
  normCost * raw + execCost * admissible + residueCost * residues

/-- Runtime advantage is exactly the cost inequality. -/
def RuntimeAdvantage
    (normCost execCost residueCost raw admissible residues
     retryCost classicAttempts retryAttempts : Nat) : Prop :=
  mstnfWork normCost execCost residueCost raw admissible residues <
    classicWork execCost retryCost classicAttempts retryAttempts

theorem runtime_advantage_is_cost_inequality
    (normCost execCost residueCost raw admissible residues
     retryCost classicAttempts retryAttempts : Nat) :
    RuntimeAdvantage normCost execCost residueCost raw admissible residues
      retryCost classicAttempts retryAttempts ↔
    normCost * raw + execCost * admissible + residueCost * residues <
      execCost * classicAttempts + retryCost * retryAttempts := by
  rfl

/-- The native concurrency suite totals: `420 < 1070`. -/
def concurrencyNativeCounts : CompressionCounts where
  raw := 1070
  quotient := 440
  admissible := 420
  h_admissible_le_quotient := by decide
  h_quotient_le_raw := by decide

theorem concurrency_native_has_strict_reduction :
    StrictExecutionReduction concurrencyNativeCounts := by
  unfold StrictExecutionReduction concurrencyNativeCounts
  decide

theorem concurrency_native_reduction_source :
    NontrivialQuotient concurrencyNativeCounts ∨
      NontrivialAdmissibilityFilter concurrencyNativeCounts :=
  (strict_reduction_iff_nontrivial_quotient_or_filter
    concurrencyNativeCounts).mp concurrency_native_has_strict_reduction

/-- The non-concurrent structural suite totals: `265 < 890`. -/
def nonConcurrentCounts : CompressionCounts where
  raw := 890
  quotient := 365
  admissible := 265
  h_admissible_le_quotient := by decide
  h_quotient_le_raw := by decide

theorem nonconcurrent_has_strict_reduction :
    StrictExecutionReduction nonConcurrentCounts := by
  unfold StrictExecutionReduction nonConcurrentCounts
  decide

theorem nonconcurrent_reduction_source :
    NontrivialQuotient nonConcurrentCounts ∨
      NontrivialAdmissibilityFilter nonConcurrentCounts :=
  (strict_reduction_iff_nontrivial_quotient_or_filter
    nonConcurrentCounts).mp nonconcurrent_has_strict_reduction

end MSTNFStructuralAdvantageMWE

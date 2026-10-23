import MSTNF.algorithms.MSTNFStructuralAdvantageMWE

/-!
# MST-NF Algorithm-Class Coverage MWE

This file records the coverage criterion for applying MST-NF beyond the
original concurrency examples.

The criterion is not the name of the algorithm.  It is the structure of the
algorithm's candidate space:

```text
raw candidates
  -> quotient classes
  -> admissible classes
  -> representative / residue
```

Any algorithm family that admits this presentation falls under the same
structural cardinality theorem.  If it does not contain nontrivial quotient
compression or nontrivial admissibility filtering, MST-NF has no execution
cardinality advantage.
-/

namespace MSTNFAlgorithmClassCoverageMWE

open MSTNFStructuralAdvantageMWE

inductive AlgorithmRegion where
  | search
  | optimization
  | parsing
  | constraintSolving
  | scheduling
  | routing
  | compilerOptimization
  | databasePlanning
  | mlPlanning
  deriving DecidableEq, Repr

structure AlgorithmCoverage where
  region : AlgorithmRegion
  counts : CompressionCounts

def HasStructuralCompression (A : AlgorithmCoverage) : Prop :=
  NontrivialQuotient A.counts ∨ NontrivialAdmissibilityFilter A.counts

def HasStrictExecutionCardinalityAdvantage (A : AlgorithmCoverage) : Prop :=
  StrictExecutionReduction A.counts

theorem algorithm_coverage_advantage_iff_structural_compression
    (A : AlgorithmCoverage) :
    HasStrictExecutionCardinalityAdvantage A ↔ HasStructuralCompression A :=
  strict_reduction_iff_nontrivial_quotient_or_filter A.counts

theorem no_advantage_without_candidate_space_structure
    (A : AlgorithmCoverage)
    (hNoQ : ¬ NontrivialQuotient A.counts)
    (hNoA : ¬ NontrivialAdmissibilityFilter A.counts) :
    ¬ HasStrictExecutionCardinalityAdvantage A := by
  intro h
  have hstruct := (algorithm_coverage_advantage_iff_structural_compression A).mp h
  cases hstruct with
  | inl hq => exact hNoQ hq
  | inr ha => exact hNoA ha

theorem quotient_compression_suffices_for_advantage
    (A : AlgorithmCoverage)
    (h : NontrivialQuotient A.counts) :
    HasStrictExecutionCardinalityAdvantage A :=
  (algorithm_coverage_advantage_iff_structural_compression A).mpr (Or.inl h)

theorem admissibility_filter_suffices_for_advantage
    (A : AlgorithmCoverage)
    (h : NontrivialAdmissibilityFilter A.counts) :
    HasStrictExecutionCardinalityAdvantage A :=
  (algorithm_coverage_advantage_iff_structural_compression A).mpr (Or.inr h)

def searchWitness : AlgorithmCoverage where
  region := .search
  counts := {
    raw := 100
    quotient := 40
    admissible := 30
    h_admissible_le_quotient := by decide
    h_quotient_le_raw := by decide
  }

theorem searchWitness_has_advantage :
    HasStrictExecutionCardinalityAdvantage searchWitness := by
  unfold HasStrictExecutionCardinalityAdvantage searchWitness StrictExecutionReduction
  decide

def alreadyNormalizedWitness : AlgorithmCoverage where
  region := .optimization
  counts := {
    raw := 50
    quotient := 50
    admissible := 50
    h_admissible_le_quotient := by decide
    h_quotient_le_raw := by decide
  }

theorem alreadyNormalizedWitness_has_no_advantage :
    ¬ HasStrictExecutionCardinalityAdvantage alreadyNormalizedWitness := by
  intro h
  unfold HasStrictExecutionCardinalityAdvantage alreadyNormalizedWitness StrictExecutionReduction at h
  exact Nat.lt_irrefl 50 h

end MSTNFAlgorithmClassCoverageMWE

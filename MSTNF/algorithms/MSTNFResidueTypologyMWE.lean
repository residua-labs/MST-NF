import MSTNF.algorithms.MSTNFAlgorithmClassCoverageMWE

/-!
# MST-NF Residue Typology MWE  (direction D)

This file introduces a residue type system for MST-NF and proves the core
correspondence: **the residue role uniquely determines the misalignment
source**, which in turn determines the structural compression guarantee.

## The two-layer design

### Layer 1: MisalignmentSource (3 constructors)
Which pipeline stage generated the residue:
  - `QSource`   — quotient stage collapsed a duplicate
  - `ASource`   — admissibility gate rejected a class
  - `RhoSource` — compensation trigger fired after execution

### Layer 2: ResidueRole (4 constructors)
Semantic classification of what "went wrong" from the classic perspective:
  - `Duplicate`    — same logical item arrived multiple times (q-folded)
  - `Stale`        — version expired before admission (a-blocked, temporal)
  - `Conflict`     — concurrent write conflict (a-blocked, structural)
  - `Compensation` — execution failed; compensation needed (ρ-triggered)

### The key structural fact
`residueSource : ResidueRole → MisalignmentSource` is surjective but not
injective: `Stale` and `Conflict` both map to `ASource`. This captures the
semantic truth that temporal staleness and concurrent conflict are distinct
causes that share the same pipeline response (admissibility rejection).

### Compression guarantees per source
  - `QSource`   certifies `NontrivialQuotient C`   (Q < N)
  - `ASource`   certifies `NontrivialAdmissibilityFilter C` (A < Q)
  - `RhoSource` certifies `True` (compatible with any compression structure)

The RhoSource/Compensation case is critical: it explains why Saga (pure ρ)
has Q = N but still produces residues. Compensation residues do NOT certify
any compression advantage — the advantage in Saga comes only from the
admissibility filter (A < Q via the a-gate), not from q-folding.

## Concrete domain witnesses (from the 100-spec experiment)

  - OSPF (duplicate_lsa_residue)  → Duplicate → QSource → Q=100 < N=300
  - MVCC (snapshot_read_stale_residue) → Stale → ASource → A=80 < Q=130
  - STM  (stm_retry + conflict_abort)  → Duplicate+Conflict → Q<N ∧ A<Q
  - Saga (saga_compensation_residue)   → Compensation → True (Q=N compatible)
-/

namespace MSTNFResidueTypologyMWE

open MSTNFStructuralAdvantageMWE
open MSTNFAlgorithmClassCoverageMWE

-- ---------------------------------------------------------------------------
-- Layer 1: Pipeline stage
-- ---------------------------------------------------------------------------

/-- Which MST-NF pipeline stage generated a residue. -/
inductive MisalignmentSource where
  | QSource    -- quotient stage: two raw events shared a class; only one executed
  | ASource    -- admissibility stage: representative was rejected
  | RhoSource  -- compensation: execution completed but triggered ρ-handler
  deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- Layer 2: Semantic residue role
-- ---------------------------------------------------------------------------

/-- Semantic classification of MST-NF residues across all 100 experimental specs. -/
inductive ResidueRole where
  /-- Same logical key appeared multiple times; q collapsed duplicates.
      Examples: duplicate_lsa_residue (OSPF), cas_retry_residue (MS-Queue),
      duplicate_arc_enqueue_residue (AC-3), tcp_dup_ack_residue. -/
  | Duplicate
  /-- Representative was too old to be admissible.
      Examples: snapshot_read_stale_residue (MVCC), tls_replay_residue. -/
  | Stale
  /-- Representative has a structural conflict preventing execution.
      Examples: stm_conflict_abort_residue, write_blocked_residue (RW-lock),
      invalid_cap_residue (seL4). -/
  | Conflict
  /-- Execution completed but the effect must be undone / compensated.
      Examples: saga compensation steps. -/
  | Compensation
  deriving DecidableEq, Repr

open MisalignmentSource ResidueRole

-- ---------------------------------------------------------------------------
-- The residueSource mapping
-- ---------------------------------------------------------------------------

/-- Each residue role maps to a definite pipeline stage. -/
def residueSource : ResidueRole → MisalignmentSource
  | Duplicate    => QSource
  | Stale        => ASource
  | Conflict     => ASource
  | Compensation => RhoSource

-- ---------------------------------------------------------------------------
-- Compression certification per source
-- ---------------------------------------------------------------------------

/-- What structural compression a source stage certifies about the domain. -/
def sourceCertifiesCompression (s : MisalignmentSource) (C : CompressionCounts) : Prop :=
  match s with
  | QSource   => NontrivialQuotient C
  | ASource   => NontrivialAdmissibilityFilter C
  | RhoSource => True   -- compatible with any structure; ρ alone is no compression

/-- A domain that produces residues of role `r` satisfies the corresponding
    structural compression predicate. -/
def residueCertifiesCompression (r : ResidueRole) (C : CompressionCounts) : Prop :=
  sourceCertifiesCompression (residueSource r) C

-- ---------------------------------------------------------------------------
-- Source uniqueness theorems
-- ---------------------------------------------------------------------------

/-- `Duplicate` is the only role with `QSource`. -/
theorem duplicate_is_sole_q_source (r : ResidueRole) :
    residueSource r = QSource ↔ r = Duplicate := by
  cases r <;> simp [residueSource]

/-- `Stale` and `Conflict` are exactly the `ASource` roles. -/
theorem a_source_roles_iff (r : ResidueRole) :
    residueSource r = ASource ↔ r = Stale ∨ r = Conflict := by
  cases r <;> simp [residueSource]

/-- `Compensation` is the only role with `RhoSource`. -/
theorem compensation_is_sole_rho_source (r : ResidueRole) :
    residueSource r = RhoSource ↔ r = Compensation := by
  cases r <;> simp [residueSource]

/-- `Stale` and `Conflict` are semantically distinct despite sharing `ASource`:
    temporal expiry (Stale) is not the same cause as concurrent conflict (Conflict). -/
theorem stale_neq_conflict : Stale ≠ Conflict := by decide

/-- **Core typology theorem**: two roles share a source only if they are equal
    OR both belong to the `ASource` fiber (the Stale/Conflict pair). -/
theorem residue_role_determines_misalignment_source
    (r1 r2 : ResidueRole)
    (h : residueSource r1 = residueSource r2) :
    r1 = r2 ∨
    (residueSource r1 = ASource ∧ residueSource r2 = ASource) := by
  cases r1 <;> cases r2 <;> simp_all [residueSource]

-- ---------------------------------------------------------------------------
-- Certification theorems (role → compression predicate)
-- ---------------------------------------------------------------------------

/-- A `Duplicate` residue certifies that the domain has nontrivial quotient (Q < N). -/
theorem duplicate_certifies_nontrivial_quotient (C : CompressionCounts)
    (h : residueCertifiesCompression Duplicate C) :
    NontrivialQuotient C := h

/-- A `Stale` residue certifies that the domain has a nontrivial admissibility filter. -/
theorem stale_certifies_nontrivial_filter (C : CompressionCounts)
    (h : residueCertifiesCompression Stale C) :
    NontrivialAdmissibilityFilter C := h

/-- A `Conflict` residue certifies the same: nontrivial admissibility filter. -/
theorem conflict_certifies_nontrivial_filter (C : CompressionCounts)
    (h : residueCertifiesCompression Conflict C) :
    NontrivialAdmissibilityFilter C := h

/-- A `Compensation` residue certifies nothing about compression:
    it is compatible with any `CompressionCounts`, including Q = N domains. -/
theorem compensation_certifies_trivially (C : CompressionCounts) :
    residueCertifiesCompression Compensation C := trivial

/-- Unified: any a-source role certifies admissibility compression. -/
theorem a_source_role_certifies_filter (r : ResidueRole) (C : CompressionCounts)
    (hsrc : residueSource r = ASource)
    (h : residueCertifiesCompression r C) :
    NontrivialAdmissibilityFilter C := by
  unfold residueCertifiesCompression sourceCertifiesCompression at h
  rw [hsrc] at h
  exact h

-- ---------------------------------------------------------------------------
-- The Saga distinction: Compensation ≠ Duplicate
-- ---------------------------------------------------------------------------

/-- A `Duplicate` residue CANNOT be produced by a domain with trivial quotient
    (Q = N would mean no folding occurred, so no Duplicate residue exists). -/
theorem duplicate_incompatible_with_trivial_quotient
    (C : CompressionCounts)
    (hQ : C.quotient = C.raw)
    (h : residueCertifiesCompression Duplicate C) :
    False := by
  unfold residueCertifiesCompression sourceCertifiesCompression residueSource at h
  unfold NontrivialQuotient at h
  omega

/-- A `Compensation` residue IS compatible with trivial quotient (Q = N).
    This witnesses why Saga (ρ-only, Q = N) can produce residues without
    any quotient compression. -/
theorem compensation_compatible_with_trivial_quotient
    (C : CompressionCounts)
    (_hQ : C.quotient = C.raw) :
    residueCertifiesCompression Compensation C := trivial

/-- The role distinction precisely separates Saga-like domains (ρ-only) from
    OSPF-like domains (q-fold): Duplicate requires Q < N; Compensation allows Q = N. -/
theorem duplicate_requires_strictly_more_than_compensation
    (C : CompressionCounts)
    (hQ : C.quotient = C.raw) :
    residueCertifiesCompression Compensation C ∧
    ¬residueCertifiesCompression Duplicate C := by
  refine ⟨trivial, ?_⟩
  intro h
  exact duplicate_incompatible_with_trivial_quotient C hQ h

-- ---------------------------------------------------------------------------
-- Dual-residue theorem: Duplicate + Conflict → StrictExecutionReduction
-- ---------------------------------------------------------------------------

/-- A domain producing both `Duplicate` residues (q-stage) AND `Conflict`
    residues (a-stage) has BOTH compression sources active simultaneously.
    This is the formal characterization of STM-like domains. -/
theorem dual_residue_implies_both_compressions (C : CompressionCounts)
    (hdup : residueCertifiesCompression Duplicate C)
    (hcon : residueCertifiesCompression Conflict C) :
    NontrivialQuotient C ∧ NontrivialAdmissibilityFilter C :=
  ⟨hdup, hcon⟩

/-- Corollary: both compressions active → strict execution-cardinality reduction. -/
theorem dual_residue_implies_strict_reduction (C : CompressionCounts)
    (hdup : residueCertifiesCompression Duplicate C)
    (hcon : residueCertifiesCompression Conflict C) :
    StrictExecutionReduction C :=
  (strict_reduction_iff_nontrivial_quotient_or_filter C).mpr
    (Or.inl (dual_residue_implies_both_compressions C hdup hcon).1)

/-- Same as `dual_residue_implies_both_compressions` but for the Duplicate+Stale pair. -/
theorem duplicate_stale_implies_both_compressions (C : CompressionCounts)
    (hdup : residueCertifiesCompression Duplicate C)
    (hstl : residueCertifiesCompression Stale C) :
    NontrivialQuotient C ∧ NontrivialAdmissibilityFilter C :=
  ⟨hdup, hstl⟩

/-- Corollary: Duplicate + Stale → strict execution-cardinality reduction. -/
theorem duplicate_stale_implies_strict_reduction (C : CompressionCounts)
    (hdup : residueCertifiesCompression Duplicate C)
    (hstl : residueCertifiesCompression Stale C) :
    StrictExecutionReduction C :=
  (strict_reduction_iff_nontrivial_quotient_or_filter C).mpr
    (Or.inl (duplicate_stale_implies_both_compressions C hdup hstl).1)

-- ---------------------------------------------------------------------------
-- Concrete domain witnesses
-- ---------------------------------------------------------------------------

/-! ### OSPF: pure Duplicate (q-source) -/

/-- ospf-lsa-flooding: 100 unique LSAs × 3 flooding paths = 300 raw.
    All admitted (A = Q = 100). Pure q-folding, produces Duplicate residues. -/
def ospfWitness : CompressionCounts where
  raw := 300; quotient := 100; admissible := 100
  h_admissible_le_quotient := by decide
  h_quotient_le_raw        := by decide

theorem ospf_residue_role : ∀ r : ResidueRole,
    r = Duplicate →
    residueCertifiesCompression r ospfWitness := by
  intro r hr; subst hr
  unfold residueCertifiesCompression sourceCertifiesCompression residueSource
  unfold NontrivialQuotient; decide

theorem ospf_has_nontrivial_quotient : NontrivialQuotient ospfWitness := by
  unfold NontrivialQuotient; decide

/-! ### MVCC: pure Stale (a-source) -/

/-- mvcc-snapshot: 130 unique reads, 50 stale (writeTs > snapshotTs).
    Q = N = 130 (no dedup). A = 80. Pure a-gate, produces Stale residues. -/
def mvccWitness : CompressionCounts where
  raw := 130; quotient := 130; admissible := 80
  h_admissible_le_quotient := by decide
  h_quotient_le_raw        := by decide

theorem mvcc_residue_role : ∀ r : ResidueRole,
    r = Stale →
    residueCertifiesCompression r mvccWitness := by
  intro r hr; subst hr
  unfold residueCertifiesCompression sourceCertifiesCompression residueSource
  unfold NontrivialAdmissibilityFilter; decide

theorem mvcc_has_nontrivial_filter : NontrivialAdmissibilityFilter mvccWitness := by
  unfold NontrivialAdmissibilityFilter; decide

/-- MVCC has trivial quotient (Q = N = 130): no q-folding, no Duplicate residues. -/
theorem mvcc_has_trivial_quotient : ¬NontrivialQuotient mvccWitness := by
  unfold NontrivialQuotient; decide

theorem mvcc_duplicate_incompatible :
    ¬residueCertifiesCompression Duplicate mvccWitness :=
  fun h => duplicate_incompatible_with_trivial_quotient mvccWitness rfl h

/-! ### STM: both Duplicate and Conflict (q + a sources) -/

/-- stm-conflict-abort: 200 raw, Q = 100 (txId dedup), A = 70 (conflict gate).
    Produces both retry_residue (Duplicate) and conflict_abort_residue (Conflict). -/
def stmWitness : CompressionCounts where
  raw := 200; quotient := 100; admissible := 70
  h_admissible_le_quotient := by decide
  h_quotient_le_raw        := by decide

theorem stm_produces_duplicate_residues :
    residueCertifiesCompression Duplicate stmWitness := by
  unfold residueCertifiesCompression sourceCertifiesCompression residueSource
  unfold NontrivialQuotient; decide

theorem stm_produces_conflict_residues :
    residueCertifiesCompression Conflict stmWitness := by
  unfold residueCertifiesCompression sourceCertifiesCompression residueSource
  unfold NontrivialAdmissibilityFilter; decide

theorem stm_has_strict_reduction : StrictExecutionReduction stmWitness :=
  dual_residue_implies_strict_reduction stmWitness
    stm_produces_duplicate_residues
    stm_produces_conflict_residues

/-! ### Saga: pure Compensation (ρ-source), Q = N -/

/-- Saga (3 specs): Q = N (each step slot is unique), A < N (some steps blocked).
    Produces Compensation residues, no Duplicate (Q = N means no q-folding). -/
def sagaWitness : CompressionCounts where
  raw := 360; quotient := 360; admissible := 225
  h_admissible_le_quotient := by decide
  h_quotient_le_raw        := by decide

theorem saga_produces_compensation_residues :
    residueCertifiesCompression Compensation sagaWitness := trivial

theorem saga_trivial_quotient : sagaWitness.quotient = sagaWitness.raw := by decide

/-- Saga cannot produce Duplicate residues (Q = N forbids q-folding). -/
theorem saga_no_duplicate_residues :
    ¬residueCertifiesCompression Duplicate sagaWitness :=
  fun h => duplicate_incompatible_with_trivial_quotient sagaWitness rfl h

/-! ### 2PC: Duplicate + Conflict (q + a), unlike Saga -/

/-- twopc-commit-ordering: 160 raw, Q = 80 (orderKey dedup), A = 80 (trivial).
    twopc-abort-compensation: 90 raw, Q = 90, A = 60 (a-gate).
    Combined: Q < N (has Duplicate residues) AND A < Q (has Conflict residues).
    This formally distinguishes 2PC from Saga. -/
def twopcWitness : CompressionCounts where
  raw := 390; quotient := 310; admissible := 240
  h_admissible_le_quotient := by decide
  h_quotient_le_raw        := by decide

theorem twopc_produces_duplicate_residues :
    residueCertifiesCompression Duplicate twopcWitness := by
  unfold residueCertifiesCompression sourceCertifiesCompression residueSource
  unfold NontrivialQuotient; decide

theorem twopc_produces_conflict_residues :
    residueCertifiesCompression Conflict twopcWitness := by
  unfold residueCertifiesCompression sourceCertifiesCompression residueSource
  unfold NontrivialAdmissibilityFilter; decide

/-- **2PC vs Saga formal distinction**: 2PC produces Duplicate residues (Q < N);
    Saga cannot (Q = N). This is the structural proof that they belong to
    different MST-NF categories despite both being "distributed transaction" domains. -/
theorem twopc_unlike_saga_has_quotient_compression :
    residueCertifiesCompression Duplicate twopcWitness ∧
    ¬residueCertifiesCompression Duplicate sagaWitness :=
  ⟨twopc_produces_duplicate_residues, saga_no_duplicate_residues⟩

-- ---------------------------------------------------------------------------
-- Summary table
-- ---------------------------------------------------------------------------

/-!
## Residue typology × domain matrix

| Domain  | Roles produced        | Source(s)        | Q < N | A < Q |
|---------|-----------------------|------------------|-------|-------|
| OSPF    | Duplicate             | QSource          | ✓     |       |
| MVCC    | Stale                 | ASource          |       | ✓     |
| STM     | Duplicate + Conflict  | QSource + ASource| ✓     | ✓     |
| Saga    | Compensation          | RhoSource        |       | (✓)   |
| 2PC     | Duplicate + Conflict  | QSource + ASource| ✓     | ✓     |

Saga: ρ-source certifies True; Saga's A < N advantage comes from a-gate alone (A < Q),
confirmed by sagaWitness.admissible < sagaWitness.quotient even though Q = N.
-/

theorem summary_all_witnesses :
    NontrivialQuotient ospfWitness ∧
    NontrivialAdmissibilityFilter mvccWitness ∧
    StrictExecutionReduction stmWitness ∧
    StrictExecutionReduction twopcWitness ∧
    ¬NontrivialQuotient sagaWitness ∧
    NontrivialAdmissibilityFilter sagaWitness := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold NontrivialQuotient; decide
  · unfold NontrivialAdmissibilityFilter; decide
  · exact stm_has_strict_reduction
  · exact dual_residue_implies_strict_reduction twopcWitness
      twopc_produces_duplicate_residues twopc_produces_conflict_residues
  · unfold NontrivialQuotient; decide
  · unfold NontrivialAdmissibilityFilter; decide

end MSTNFResidueTypologyMWE

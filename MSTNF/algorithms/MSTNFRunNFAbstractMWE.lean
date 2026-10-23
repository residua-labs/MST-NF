import Mathlib.Tactic.Lemma
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup

/-!
# Abstract MST-NF q/a/σ/ρ fold engine

Defines the generic four-piece normal-form engine over any event type `E`
and quotient key type `K`.  Mirrors `packages/mstnf-ocaml/lib/mstnf.ml`
(`run_nf`) in Lean 4, expressed so that structural theorems can be stated
and proved.

The three structural theorems — proved in sibling files — characterise
the semantics of `runNF`:

  `MSTNFSigmaFaithfulnessMWE`     — every belief is σ-minimal in its class
  `MSTNFPartitionCompletenessMWE` — no event is lost: rawEvents = beliefs + residues
  `MSTNFOrderInvarianceMWE`       — beliefs are invariant to input permutation

OCaml conformance anchor: `packages/mstnf-ocaml/lib/mstnf.ml`
Layer 0 fixture anchor:   the sigma fixture files (not included in this repository)

## Implementation note

`groupBy` is defined via `firstUniqueKeys ∘ filter` rather than via the OCaml
`foldl` + `find?` + `map` chain.  The two are observationally equivalent
(same key list, same per-key event list, same length, same membership), but
the filter-based form makes structural lemmas tractable.
-/

namespace MSTNFRunNFAbstractMWE

-- ---------------------------------------------------------------------------
-- §1  Core types
-- ---------------------------------------------------------------------------

/-- The four-piece MST-NF specification over event type `E` and key type `K`. -/
structure NFSpec (E K : Type) where
  /-- q: partition function — quotient key for an event -/
  quotient    : E → K
  /-- σ: `betterThan a b = true` iff `a` is strictly preferred over `b` -/
  betterThan  : E → E → Bool
  /-- a: admissibility gate applied to the per-class σ-winner -/
  admissible  : E → Bool
  /-- ρ: names the inadmissibility residue -/
  residueKind : E → String

/-- Summary counts + beliefs returned by `runNF`. -/
structure NFResult (E K : Type) where
  rawEvents         : Nat
  quotientClasses   : Nat
  admissibleClasses : Nat
  beliefs           : List (K × E)
  residueCount      : Nat
  deriving Repr

-- ---------------------------------------------------------------------------
-- §2  Building blocks
-- ---------------------------------------------------------------------------

/-- Distinct elements preserving first-occurrence order (unlike Mathlib's
    `List.dedup` which keeps last). -/
def firstUniqueKeys [DecidableEq K] : List K → List K
  | []      => []
  | k :: ks => k :: (firstUniqueKeys ks).filter (fun k' => decide (k' ≠ k))

/-- Group events by quotient key.  Key order = first-seen; events within each
    group = input order. -/
def groupBy [DecidableEq K] (q : E → K) (events : List E) : List (K × List E) :=
  (firstUniqueKeys (events.map q)).map
    (fun k => (k, events.filter (fun e => decide (q e = k))))

/-- σ-fold: select the `betterThan`-minimal element. -/
def sigmaFold (bt : E → E → Bool) : List E → Option E
  | []     => none
  | h :: t => some (t.foldl (fun acc e => if bt e acc then e else acc) h)

-- ---------------------------------------------------------------------------
-- §3  runNF
-- ---------------------------------------------------------------------------

def runNF [DecidableEq K] (spec : NFSpec E K) (events : List E) : NFResult E K :=
  let groups  := groupBy spec.quotient events
  let reps    := groups.filterMap (fun (k, es) =>
    (sigmaFold spec.betterThan es).map (fun rep => (k, rep)))
  let beliefs := reps.filter (fun pair => spec.admissible pair.2)
  { rawEvents         := events.length
    quotientClasses   := groups.length
    admissibleClasses := beliefs.length
    beliefs           := beliefs
    residueCount      := events.length - beliefs.length }

-- ---------------------------------------------------------------------------
-- §4  Properties of firstUniqueKeys
-- ---------------------------------------------------------------------------

theorem firstUniqueKeys_mem [DecidableEq K] (ks : List K) (k : K) :
    k ∈ firstUniqueKeys ks ↔ k ∈ ks := by
  induction ks with
  | nil => simp [firstUniqueKeys]
  | cons hd tl ih =>
    simp only [firstUniqueKeys, List.mem_cons, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨hmem, _⟩)
      · exact Or.inl rfl
      · exact Or.inr (ih.mp hmem)
    · rintro (rfl | hmem)
      · exact Or.inl rfl
      · by_cases hk : k = hd
        · exact Or.inl hk
        · exact Or.inr ⟨ih.mpr hmem, hk⟩

theorem firstUniqueKeys_nodup [DecidableEq K] (ks : List K) :
    (firstUniqueKeys ks).Nodup := by
  induction ks with
  | nil => simp [firstUniqueKeys]
  | cons hd tl ih =>
    rw [firstUniqueKeys, List.nodup_cons]
    refine ⟨?_, ih.filter _⟩
    intro hmem
    rw [List.mem_filter] at hmem
    exact absurd rfl (of_decide_eq_true hmem.2)

-- ---------------------------------------------------------------------------
-- §5  Partition-sum lemma (private)
-- ---------------------------------------------------------------------------

private theorem length_split_by_key [DecidableEq K]
    (q : E → K) (events : List E) (k0 : K) :
    events.length = (events.filter (fun e => decide (q e = k0))).length
                    + (events.filter (fun e => decide (q e ≠ k0))).length := by
  have hfilt_eq : events.filter (fun x => !decide (q x = k0))
                  = events.filter (fun e => decide (q e ≠ k0)) := by
    apply List.filter_congr
    intro e _
    by_cases hq : q e = k0 <;> simp [hq]
  rw [List.length_eq_length_filter_add (l := events) (fun e => decide (q e = k0)), hfilt_eq]

private theorem filter_eq_filter_of_ne [DecidableEq K]
    (q : E → K) (events : List E) {k0 k' : K} (hne : k' ≠ k0) :
    (events.filter (fun e => decide (q e ≠ k0))).filter (fun e => decide (q e = k')) =
      events.filter (fun e => decide (q e = k')) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro e _
  by_cases hqek' : q e = k'
  · have hne_qek0 : q e ≠ k0 := fun h => hne (hqek'.symm.trans h)
    simp [decide_eq_true hne_qek0, decide_eq_true hqek']
  · simp [decide_eq_false hqek']

private theorem foldr_filter_filter_eq [DecidableEq K]
    (q : E → K) (events : List E) {k0 : K}
    (ks : List K) (hno : k0 ∉ ks) :
    ks.foldr (fun k acc =>
      ((events.filter (fun e => decide (q e ≠ k0))).filter
        (fun e => decide (q e = k))).length + acc) 0
    = ks.foldr (fun k acc =>
        (events.filter (fun e => decide (q e = k))).length + acc) 0 := by
  induction ks with
  | nil => simp
  | cons k' rs ih =>
    have hk'_ne_k0 : k' ≠ k0 := fun heq => hno (heq ▸ List.mem_cons_self _ _)
    have hrs_no : k0 ∉ rs := fun h => hno (List.mem_cons_of_mem _ h)
    simp only [List.foldr_cons]
    rw [filter_eq_filter_of_ne q events hk'_ne_k0, ih hrs_no]

private theorem partition_sum_eq_length [DecidableEq K]
    (q : E → K) (events : List E) (ks : List K)
    (hnodup : ks.Nodup) (hcover : ∀ e ∈ events, q e ∈ ks) :
    ks.foldr (fun k acc => (events.filter (fun e => decide (q e = k))).length + acc) 0
      = events.length := by
  induction ks generalizing events with
  | nil =>
    cases hev : events with
    | nil => simp
    | cons e _ =>
      rw [hev] at hcover
      exact absurd (hcover e (List.mem_cons_self _ _)) (List.not_mem_nil _)
  | cons k0 rest ih =>
    rcases List.nodup_cons.mp hnodup with ⟨hk0notin, hrest_nd⟩
    set efilt_neq : List E := events.filter (fun e => decide (q e ≠ k0)) with hefilt_def
    have hcover' : ∀ e ∈ efilt_neq, q e ∈ rest := by
      intro e he
      rw [hefilt_def, List.mem_filter, decide_eq_true_eq] at he
      obtain ⟨heE, hne⟩ := he
      have hin : q e ∈ k0 :: rest := hcover e heE
      rcases List.mem_cons.mp hin with heq | hr
      · exact absurd heq hne
      · exact hr
    have ih_applied := ih efilt_neq hrest_nd hcover'
    have hrest_sum_eq :
        rest.foldr (fun k acc => (efilt_neq.filter (fun e => decide (q e = k))).length + acc) 0
        = rest.foldr (fun k acc => (events.filter (fun e => decide (q e = k))).length + acc) 0 := by
      rw [hefilt_def]
      exact foldr_filter_filter_eq q events rest hk0notin
    have hsplit : events.length =
        (events.filter (fun e => decide (q e = k0))).length + efilt_neq.length := by
      rw [hefilt_def]
      exact length_split_by_key q events k0
    simp only [List.foldr_cons]
    rw [← hrest_sum_eq, ih_applied]
    omega

-- ---------------------------------------------------------------------------
-- §6  Helper lemmas required by sibling theorem files
-- ---------------------------------------------------------------------------

/-- The representative produced by `sigmaFold` is a member of the input list. -/
lemma sigmaFold_mem (bt : E → E → Bool) (h : E) (t : List E) :
    (t.foldl (fun acc e => if bt e acc then e else acc) h) ∈ (h :: t) := by
  induction t generalizing h with
  | nil  => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    by_cases hbt : bt e h
    · simp only [hbt, if_true]
      exact List.mem_cons_of_mem h (ih e)
    · simp only [hbt, if_false]
      have hin := ih h
      rcases List.mem_cons.mp hin with heq | hmem
      · exact List.mem_cons.mpr (Or.inl heq)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem)

/-- Every group produced by `groupBy` is non-empty. -/
lemma groupBy_nonempty [DecidableEq K] (q : E → K) (events : List E)
    (k : K) (es : List E) (h : (k, es) ∈ groupBy q events) : es ≠ [] := by
  rw [groupBy, List.mem_map] at h
  obtain ⟨k', hk'_mem, hk'_eq⟩ := h
  have heq_k : k' = k := congrArg Prod.fst hk'_eq
  have heq_es : events.filter (fun e => decide (q e = k')) = es := congrArg Prod.snd hk'_eq
  rw [firstUniqueKeys_mem, List.mem_map] at hk'_mem
  obtain ⟨e, heE, hqe⟩ := hk'_mem
  subst heq_k
  intro hnil
  apply List.not_mem_nil (a := e)
  rw [← hnil, ← heq_es, List.mem_filter]
  exact ⟨heE, by simp [hqe]⟩

/-- `groupBy` preserves total event count: sum of group sizes = input length. -/
lemma groupBy_size_sum [DecidableEq K] (q : E → K) (events : List E) :
    (groupBy q events).foldr (fun (p : K × List E) acc => p.2.length + acc) 0 = events.length := by
  simp only [groupBy, List.foldr_map]
  apply partition_sum_eq_length q events (firstUniqueKeys (events.map q))
  · exact firstUniqueKeys_nodup _
  · intro e he
    rw [firstUniqueKeys_mem, List.mem_map]
    exact ⟨e, he, rfl⟩

end MSTNFRunNFAbstractMWE

import MSTNF.algorithms.MSTNecessityExecModelMWE
import MSTNF.r2.Active

/-!
# MST-NF R2 — the bound decision `D : C → R + E`, `vhat`, and the reference bridge

Mechanization of the R2 contract, section 2 ("Bound decision and source
section") and the paper's section 4 (Proposition 3).

Sources (mature sources rule, preamble item 7):
- Design of record: the R2 mechanization contract
  sections 2 and 7 (P3 scope note); paper v0.2 sections 4.1-4.3.
- Pinned base: `MSTNF.algorithms.MSTNecessityExecModelMWE` (unchanged).
- The sum-type representation of an exclusive decision is standard; the paper
  itself notes it "is not a novel type constructor".

Deliverable 2 of the R2 mechanization contract: the bound decision extracted from a profile
(`Dact`), `vhat`, the reference bridge (`bridged`), P3, and the converse
projections of an arbitrary `D`.

No Mathlib import; no `sorry`; no `native_decide`; no new axioms.
-/

namespace MSTNFR2

open MSTNecessityExecModelMWE

/-! ## The generic bound-decision interface -/

/-- The data of a bound decision, contract section 2: `q : X → C`,
    `D : C → Sum R E`, interpretation `v : R → Y`, reference observation
    `O : X → Sum Y E`. `Sum.inl` is success, `Sum.inr` is refusal. The class
    carrier is active, or `D` is explicitly totalized; nothing here depends on
    which reading is chosen. -/
structure DecisionIF (X C R E Y : Type) where
  q : X → C
  D : C → Sum R E
  v : R → Y
  O : X → Sum Y E

/-- `vhat` maps `v` on success and preserves the residue, paper eq. (5). -/
def vhat {R E Y : Type} (v : R → Y) : Sum R E → Sum Y E
  | Sum.inl r => Sum.inl (v r)
  | Sum.inr e => Sum.inr e

/-- The reference bridge `O = vhat ∘ D ∘ q` (paper eq. (5)), as a hypothesis
    each instance must discharge against its own reference. -/
def bridged {X C R E Y : Type} (K : DecisionIF X C R E Y) : Prop :=
  ∀ x, K.O x = vhat K.v (K.D (K.q x))

/-- **P3** (bound-observation reuse): under the explicit reference bridge,
    equal keys give equal reference observations, including the success/refusal
    tag and the residual payload visible in `O`. -/
theorem P3_boundObservation_reuse {X C R E Y : Type} (K : DecisionIF X C R E Y)
    (h : bridged K) : ∀ x y : X, K.q x = K.q y → K.O x = K.O y := by
  intro x y hq
  rw [h x, h y, hq]

/-- A key is active-reachable at `c` when some raw input maps to `c`. -/
def keyActive {X C : Type} (q : X → C) (c : C) : Prop := ∃ x, q x = c

/-- The decision-level source-section law (paper eq. (6)): a successful
    decision on an active class embeds back through `iota` into that class. -/
def decisionSourceSection {X C R E Y : Type} (K : DecisionIF X C R E Y)
    (iota : R → X) : Prop :=
  ∀ (c : C) (r : R), keyActive K.q c → K.D c = Sum.inl r → K.q (iota r) = c

/-! ## Converse: the Boolean and optional projections of an arbitrary `D` -/

/-- Admission Boolean recovered from a decision (contract section 2:
    "conversely obtain a/sigma/rho as the Boolean and optional projections"). -/
def admOfD {C R E : Type} (D : C → Sum R E) (c : C) : Bool := (D c).isLeft

/-- Representative projection of a decision. -/
def sigOfD {C R E : Type} (D : C → Sum R E) (c : C) : Option R :=
  match D c with
  | Sum.inl r => some r
  | Sum.inr _ => none

/-- Residue projection of a decision. -/
def rhoOfD {C R E : Type} (D : C → Sum R E) (c : C) : Option E :=
  match D c with
  | Sum.inr e => some e
  | Sum.inl _ => none

/-- Law **A** for the projections of an arbitrary decision. -/
theorem admOfD_sound {C R E : Type} (D : C → Sum R E) :
    ∀ (c : C) (r : R), sigOfD D c = some r → admOfD D c = true := by
  intro c r h
  cases hD : D c with
  | inl r' => simp only [admOfD, hD]; rfl
  | inr e => simp only [sigOfD, hD] at h; exact Option.noConfusion h

/-- Law **S** for the projections of an arbitrary decision (on any class;
    activity is not needed). -/
theorem sigOfD_ne_none_of_adm {C R E : Type} (D : C → Sum R E) (c : C)
    (ha : admOfD D c = true) : sigOfD D c ≠ none := by
  cases hD : D c with
  | inl r' => simp [sigOfD, hD]
  | inr e => simp [admOfD, hD] at ha

/-- Law **R** for the projections of an arbitrary decision (on any active
    class; activity is not needed for the implication itself). -/
theorem rhoOfD_ne_none_of_not_adm {C R E : Type} (D : C → Sum R E) (c : C)
    (ha : admOfD D c = false) : rhoOfD D c ≠ none := by
  cases hD : D c with
  | inr e' => simp [rhoOfD, hD]
  | inl r => simp [admOfD, hD] at ha

/-- Exclusivity (paper eq. (3)) for the projections of an arbitrary decision:
    a Boolean case split, adding nothing beyond the representation — the
    contract's remark on why (3) alone is not a soundness axiom. -/
theorem rhoOfD_none_of_adm {C R E : Type} (D : C → Sum R E) (c : C)
    (ha : admOfD D c = true) : rhoOfD D c = none := by
  cases hD : D c with
  | inl r' => simp only [rhoOfD, hD]
  | inr e => simp [admOfD, hD] at ha

/-! ## Extracting a decision from a core profile on active classes -/

section Extraction

variable {M : ExecModel}

/-- Total option-valued precursor of the extracted decision, keyed on the
    admission Boolean (paper eq. (4)): an admitted class contributes its
    selected representative only when it carries no residue (active
    exclusivity), a refused class contributes its residue only when it does
    not also select a representative (admissibility soundness). Any other
    triple is `none` — a law-violating model is never silently accepted, so
    extraction cannot drop residues or flip admissions. -/
def Dopt (M : ExecModel) (c : Cact M) : Option (Sum M.Rep M.Residue) :=
  match M.admissible c.val, M.sigma c.val, M.rho c.val with
  | true, some r, none => some (Sum.inl r)
  | false, none, some e => some (Sum.inr e)
  | _, _, _ => none

/-- Under the pinned four-law profile plus active exclusivity, `Dopt` is
    never `none` on an active class: an admitted active class selects a
    representative (**S**) and carries no residue (active exclusivity); a
    refused active class carries a residue (**R**) and cannot select a
    representative (**A**, contrapositive). -/
theorem Dopt_ne_none (hP : hasMSTNFProfile M) (hAE : activeExclusivity M)
    (c : Cact M) : Dopt M c ≠ none := by
  cases ha : M.admissible c.val with
  | true =>
    cases hs : M.sigma c.val with
    | some r =>
        simp only [Dopt, ha, hs, show M.rho c.val = none from hAE c ha]
        exact fun h => Option.noConfusion h
    | none => exact absurd hs (hP.2.2.2 c.val c.property ha)
  | false =>
    cases hs : M.sigma c.val with
    | some r => rw [hP.2.1 c.val r hs] at ha; exact Bool.noConfusion ha
    | none =>
        cases hro : M.rho c.val with
        | some e =>
            simp only [Dopt, ha, hs, hro]
            exact fun h => Option.noConfusion h
        | none => exact absurd hro (hP.2.2.1 c.val c.property ha)

/-- The bound decision `Dact : Cact M → Rep + Residue` extracted from a
    profile, contract eq. (4). Extraction requires the pinned four-law
    profile **and** active exclusivity (contract section 2: when extracting
    D from a core profile, require active exclusivity `a c = true →
    rho c = none`), so it neither drops residues of admitted classes nor
    flips the admission of refused classes that still select a
    representative. No inactive class is decided. -/
def Dact (hP : hasMSTNFProfile M) (hAE : activeExclusivity M) (c : Cact M) :
    Sum M.Rep M.Residue :=
  match h : Dopt M c with
  | some d => d
  | none => absurd h (Dopt_ne_none hP hAE c)

/-- Generic reduction: `Dact` returns whatever `Dopt` returns. -/
theorem Dact_eq_of_Dopt (hP : hasMSTNFProfile M) (hAE : activeExclusivity M)
    (c : Cact M) {d : Sum M.Rep M.Residue} (h : Dopt M c = some d) :
    Dact hP hAE c = d := by
  unfold Dact
  split
  · next d' hd' =>
      injection (hd'.symm.trans h) with hd''
  · next hd' => rw [hd'] at h; exact Option.noConfusion h

/-- An admitted active class decides to its selected representative. -/
theorem Dact_eq_inl_of_admissible (hP : hasMSTNFProfile M)
    (hAE : activeExclusivity M) (c : Cact M) (ha : M.admissible c.val = true) :
    ∃ r, M.sigma c.val = some r ∧ Dact hP hAE c = Sum.inl r := by
  have hs : M.sigma c.val ≠ none := hP.2.2.2 c.val c.property ha
  cases hs' : M.sigma c.val with
  | some r =>
    refine ⟨r, rfl, ?_⟩
    exact Dact_eq_of_Dopt hP hAE c
      (by simp only [Dopt, ha, hs', show M.rho c.val = none from hAE c ha])
  | none => exact absurd hs' (hP.2.2.2 c.val c.property ha)

/-- A refused active class decides to its residue, and selects no
    representative (contrapositive of **A**). -/
theorem Dact_eq_inr_of_not_admissible (hP : hasMSTNFProfile M)
    (hAE : activeExclusivity M) (c : Cact M) (ha : M.admissible c.val = false) :
    ∃ e, M.rho c.val = some e ∧ M.sigma c.val = none ∧ Dact hP hAE c = Sum.inr e := by
  have hs : M.sigma c.val = none := by
    cases hs' : M.sigma c.val with
    | some r => rw [hP.2.1 c.val r hs'] at ha; exact Bool.noConfusion ha
    | none => rfl
  have hr := hP.2.2.1 c.val c.property ha
  cases hro : M.rho c.val with
  | some e =>
    refine ⟨e, rfl, hs, ?_⟩
    exact Dact_eq_of_Dopt hP hAE c (by simp only [Dopt, ha, hs, hro])
  | none => exact absurd hro hr

/-! ### Round-trip: the projections of `Dact` recover the model -/

/-- Projection computation for a decision landing in the success branch
    (variable-headed, so the rewrite always applies). -/
theorem admOfD_inl {C R E : Type} {D : C → Sum R E} {c : C} {r : R}
    (h : D c = Sum.inl r) : admOfD D c = true := by
  simp only [admOfD, h]
  rfl

theorem admOfD_inr {C R E : Type} {D : C → Sum R E} {c : C} {e : E}
    (h : D c = Sum.inr e) : admOfD D c = false := by
  simp only [admOfD, h]
  rfl

theorem sigOfD_inl {C R E : Type} {D : C → Sum R E} {c : C} {r : R}
    (h : D c = Sum.inl r) : sigOfD D c = some r := by
  simp only [sigOfD, h]

theorem sigOfD_inr {C R E : Type} {D : C → Sum R E} {c : C} {e : E}
    (h : D c = Sum.inr e) : sigOfD D c = none := by
  simp only [sigOfD, h]

theorem rhoOfD_inl {C R E : Type} {D : C → Sum R E} {c : C} {r : R}
    (h : D c = Sum.inl r) : rhoOfD D c = none := by
  simp only [rhoOfD, h]

theorem rhoOfD_inr {C R E : Type} {D : C → Sum R E} {c : C} {e : E}
    (h : D c = Sum.inr e) : rhoOfD D c = some e := by
  simp only [rhoOfD, h]

/-- Round trip, admission Boolean: the Boolean projection of the extracted
    decision agrees with the model's admission on every active class. This is
    the content the extraction must have to "obtain `a` as the Boolean
    projection of `D`" (contract section 2); it needs all four pinned laws
    plus active exclusivity. -/
theorem Dact_admOfD (hP : hasMSTNFProfile M) (hAE : activeExclusivity M)
    (c : Cact M) : admOfD (Dact hP hAE) c = M.admissible c.val := by
  cases ha : M.admissible c.val with
  | true =>
    obtain ⟨r, _, hd⟩ := Dact_eq_inl_of_admissible hP hAE c ha
    exact admOfD_inl hd
  | false =>
    obtain ⟨e, _, _, hd⟩ := Dact_eq_inr_of_not_admissible hP hAE c ha
    exact admOfD_inr hd

/-- Round trip, representative projection: `sigOfD` of the extracted
    decision is exactly the model's `sigma` on every active class. -/
theorem Dact_sigOfD (hP : hasMSTNFProfile M) (hAE : activeExclusivity M)
    (c : Cact M) : sigOfD (Dact hP hAE) c = M.sigma c.val := by
  cases ha : M.admissible c.val with
  | true =>
    obtain ⟨r, hs', hd⟩ := Dact_eq_inl_of_admissible hP hAE c ha
    rw [hs']
    exact sigOfD_inl hd
  | false =>
    obtain ⟨e, _, hs', hd⟩ := Dact_eq_inr_of_not_admissible hP hAE c ha
    rw [hs']
    exact sigOfD_inr hd

/-- Round trip, residue projection: `rhoOfD` of the extracted decision is
    exactly the model's `rho` on every active class — under active
    exclusivity, extraction drops no residue. -/
theorem Dact_rhoOfD (hP : hasMSTNFProfile M) (hAE : activeExclusivity M)
    (c : Cact M) : rhoOfD (Dact hP hAE) c = M.rho c.val := by
  cases ha : M.admissible c.val with
  | true =>
    obtain ⟨r, _, hd⟩ := Dact_eq_inl_of_admissible hP hAE c ha
    rw [hAE c ha]
    exact rhoOfD_inl hd
  | false =>
    obtain ⟨e, hr', _, hd⟩ := Dact_eq_inr_of_not_admissible hP hAE c ha
    rw [hr']
    exact rhoOfD_inr hd

/-- Mutual exclusivity, recovered from the round trips rather than from the
    vacuous `Sum`-disjointness of any function: the representative and
    residue projections of the extracted decision can never both be `some`
    on an active class. This is the meaningful content that replaces a bare
    `inl ≠ inr` tautology. -/
theorem Dact_excl (hP : hasMSTNFProfile M) (hAE : activeExclusivity M)
    (c : Cact M) (r : M.Rep) (e : M.Residue)
    (h1 : sigOfD (Dact hP hAE) c = some r) (h2 : rhoOfD (Dact hP hAE) c = some e) :
    False := by
  rw [Dact_sigOfD hP hAE c] at h1
  rw [Dact_rhoOfD hP hAE c] at h2
  cases hs : M.sigma c.val with
  | some r' =>
    cases ha : M.admissible c.val with
    | true => rw [show M.rho c.val = none from hAE c ha] at h2; exact Option.noConfusion h2
    | false => rw [hP.2.1 c.val r' hs] at ha; exact Bool.noConfusion ha
  | none => rw [hs] at h1; exact Option.noConfusion h1

end Extraction

/-! ## Tying the extracted decision to a model's reference observation -/

/-- Model-level exclusivity (the audit r2 note on `Dact_excl`): under the
    profile and active-exclusivity hypotheses, sigma and rho are never
    simultaneously defined — the underlying fact `Dact_excl` reduces to
    via the round trips. -/
theorem sigma_rho_excl (hP : hasMSTNFProfile M) (hAE : activeExclusivity M)
    (c : Cact M) (r : M.Rep) (e : M.Residue)
    (h1 : M.sigma c.val = some r) (h2 : M.rho c.val = some e) :
    False := by
  refine Dact_excl hP hAE c r e ?_ ?_
  · rw [Dact_sigOfD hP hAE c]; exact h1
  · rw [Dact_rhoOfD hP hAE c]; exact h2

/-- The profile-side bridge lemma (paper section 4.2): any sum-typed
    observation that factors through classes (**Q**) and realizes `vhat ∘ Dact`
    on active classes satisfies the reference bridge `O = vhat ∘ Dact ∘ qact`.
    Instantiating `Oraw`/`Ocls` at a model whose `Outcome` is `Y ⊕ Residue`
    gives eq. (5); the hypotheses are exactly the instance obligations. -/

theorem profile_referenceBridge {M : ExecModel} {Y : Type}
    (hP : hasMSTNFProfile M) (hAE : activeExclusivity M)
    (v : M.Rep → Y)
    (Oraw : M.Raw → Sum Y M.Residue) (Ocls : M.Class → Sum Y M.Residue)
    (hQF : ∀ x, Oraw x = Ocls (M.q x))
    (hCls : ∀ c : Cact M, Ocls c.val = vhat v (Dact hP hAE c)) :
    ∀ x, Oraw x = vhat v (Dact hP hAE (qact M x)) := by
  intro x
  rw [hQF x]
  exact hCls (qact M x)

end MSTNFR2

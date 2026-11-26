import MSTNF.algorithms.MSTNFHopComposeMWE

/-!
Relational hops over the pinned ExecModel.
Relations are oriented source outcome -> target outcome. Translation refusal
(Option.none), target admission refusal (rho), and runtime limit outcomes are
different boundaries. All theorems quantify the actual sigma-selected witness.
-/
namespace NfCompose
open MSTNecessityExecModelMWE

def RelComp {X Y Z : Type} (R : X → Y → Prop) (S : Y → Z → Prop) :
    X → Z → Prop := fun x z => ∃ y, R x y ∧ S y z

/-- Pointwise correctness includes an actual translated raw and its admission. -/
def RelHopAt (A B : ExecModel) (F : A.Rep → Option B.Raw)
    (R : A.Outcome → B.Outcome → Prop) (c : A.Class) : Prop :=
  ∃ p b, A.sigma c = some p ∧ F p = some b ∧
    B.admissible (B.q b) = true ∧ R (A.evalClass c) (B.evalRaw b)

def RelHopOn (A B : ExecModel) (F : A.Rep → Option B.Raw)
    (R : A.Outcome → B.Outcome → Prop) (P : A.Class → Prop) : Prop :=
  ∀ c, activeClass A c → P c → RelHopAt A B F R c

def RelHopCorrect (A B : ExecModel) (F : A.Rep → Option B.Raw)
    (R : A.Outcome → B.Outcome → Prop) : Prop :=
  RelHopOn A B F R (fun c => A.admissible c = true)

/-- The partial witness arrow. No representative is picked by choice. -/
def partialHopSeq (B : ExecModel) {P R : Type}
    (F : P → Option B.Raw) (G : B.Rep → Option R) : P → Option R :=
  fun p => (F p).bind (fun b => (B.sigma (B.q b)).bind G)

theorem relHopAt_mono (A B : ExecModel) (F : A.Rep → Option B.Raw)
    (R S : A.Outcome → B.Outcome → Prop)
    (hRS : ∀ a b, R a b → S a b) (c : A.Class)
    (h : RelHopAt A B F R c) : RelHopAt A B F S c := by
  obtain ⟨p, b, hp, hf, hb, hr⟩ := h
  exact ⟨p, b, hp, hf, hb, hRS _ _ hr⟩

theorem relHopOn_mono (A B : ExecModel) (F : A.Rep → Option B.Raw)
    (R S : A.Outcome → B.Outcome → Prop) (P : A.Class → Prop)
    (hRS : ∀ a b, R a b → S a b) (h : RelHopOn A B F R P) :
    RelHopOn A B F S P :=
  fun c hc hp => relHopAt_mono A B F R S hRS c (h c hc hp)

/-- Arbitrary relations compose without assuming either one is transitive. -/
theorem relHopAt_seq (A B C : ExecModel)
    (F : A.Rep → Option B.Raw) (G : B.Rep → Option C.Raw)
    (R : A.Outcome → B.Outcome → Prop) (S : B.Outcome → C.Outcome → Prop)
    (hqB : quotientFactorization B) (c : A.Class)
    (hAB : RelHopAt A B F R c) (hBC : RelHopCorrect B C G S) :
    RelHopAt A C (partialHopSeq B F G) (RelComp R S) c := by
  obtain ⟨p, b, hp, hf, hb, hr⟩ := hAB
  obtain ⟨q, d, hq, hg, hd, hs⟩ := hBC (B.q b) ⟨b, rfl⟩ hb
  refine ⟨p, d, hp, ?_, hd, B.evalRaw b, hr, ?_⟩
  · simp [partialHopSeq, hf, hq, hg]
  · rw [hqB b]
    exact hs

theorem relHopOn_seq (A B C : ExecModel)
    (F : A.Rep → Option B.Raw) (G : B.Rep → Option C.Raw)
    (R : A.Outcome → B.Outcome → Prop) (S : B.Outcome → C.Outcome → Prop)
    (P : A.Class → Prop) (hqB : quotientFactorization B)
    (hAB : RelHopOn A B F R P) (hBC : RelHopCorrect B C G S) :
    RelHopOn A C (partialHopSeq B F G) (RelComp R S) P :=
  fun c hc hp => relHopAt_seq A B C F G R S hqB c (hAB c hc hp) hBC

/-- To collapse relational composition to a chosen relation, state its law. -/
theorem relHopOn_comp (A B C : ExecModel)
    (F : A.Rep → Option B.Raw) (G : B.Rep → Option C.Raw)
    (R : A.Outcome → B.Outcome → Prop) (S : B.Outcome → C.Outcome → Prop)
    (U : A.Outcome → C.Outcome → Prop) (P : A.Class → Prop)
    (hcomp : ∀ a b d, R a b → S b d → U a d)
    (hqB : quotientFactorization B)
    (hAB : RelHopOn A B F R P) (hBC : RelHopCorrect B C G S) :
    RelHopOn A C (partialHopSeq B F G) U P := by
  apply relHopOn_mono A C (partialHopSeq B F G) (RelComp R S) U P
    (fun a d h => ?_) (relHopOn_seq A B C F G R S P hqB hAB hBC)
  obtain ⟨b, hr, hs⟩ := h
  exact hcomp a b d hr hs

/-- The usual observation-map form: target observation refines the source.
    Monotonicity transports the BC relation, transitivity closes it in A. -/
theorem relHopOn_observed_seq (A B C : ExecModel)
    (F : A.Rep → Option B.Raw) (G : B.Rep → Option C.Raw)
    (obsAB : B.Outcome → A.Outcome) (obsBC : C.Outcome → B.Outcome)
    (leA : A.Outcome → A.Outcome → Prop) (leB : B.Outcome → B.Outcome → Prop)
    (P : A.Class → Prop)
    (htrans : ∀ x y z, leA x y → leA y z → leA x z)
    (hmono : ∀ x y, leB x y → leA (obsAB x) (obsAB y))
    (hqB : quotientFactorization B)
    (hAB : RelHopOn A B F (fun a b => leA (obsAB b) a) P)
    (hBC : RelHopCorrect B C G (fun b d => leB (obsBC d) b)) :
    RelHopOn A C (partialHopSeq B F G)
      (fun a d => leA (obsAB (obsBC d)) a) P :=
  relHopOn_comp A B C F G
    (fun a b => leA (obsAB b) a) (fun b d => leB (obsBC d) b)
    (fun a d => leA (obsAB (obsBC d)) a) P
    (fun a b d hab hbc => htrans (obsAB (obsBC d)) (obsAB b) a
      (hmono (obsBC d) b hbc) hab) hqB hAB hBC

/-- Correctness binds every raw produced by this exact partial arrow. -/
theorem relHopCorrect_actual (A B : ExecModel) (F : A.Rep → Option B.Raw)
    (R : A.Outcome → B.Outcome → Prop) (h : RelHopCorrect A B F R)
    (hqA : quotientFactorization A) (a : A.Raw)
    (ha : A.admissible (A.q a) = true) (b : B.Raw)
    (hw : (A.sigma (A.q a)).bind F = some b) :
    B.admissible (B.q b) = true ∧ R (A.evalRaw a) (B.evalRaw b) := by
  obtain ⟨p, d, hp, hf, hd, hr⟩ := h (A.q a) ⟨a, rfl⟩ ha
  have hdb : d = b := by
    simpa [hp, hf] using hw
  subst b
  exact ⟨hd, by rw [hqA a]; exact hr⟩

/-- Executable diagnostics reuse the existing HopResidue vocabulary.
    A runtime resource limit belongs in Outcome, not in this Option arrow. -/
def relHopRho (A B : ExecModel) (F : A.Rep → Option B.Raw)
    (check : A.Outcome → B.Outcome → Bool) (c : A.Class) :
    Option (HopResidue A.Outcome B.Outcome B.Residue) :=
  match A.sigma c with
  | none => some .translationRefused
  | some p => match F p with
    | none => some .translationRefused
    | some b =>
      if B.admissible (B.q b) then
        if check (A.evalClass c) (B.evalRaw b) then none
        else some (.valueMismatch (A.evalClass c) (B.evalRaw b))
      else some (.targetRefused (B.rho (B.q b)))

theorem relHopRho_none_iff (A B : ExecModel) (F : A.Rep → Option B.Raw)
    (check : A.Outcome → B.Outcome → Bool) (c : A.Class) :
    relHopRho A B F check c = none ↔
      RelHopAt A B F (fun a b => check a b = true) c := by
  cases hp : A.sigma c with
  | none => simp [relHopRho, RelHopAt, hp]
  | some p =>
    cases hf : F p with
    | none => simp [relHopRho, RelHopAt, hp, hf]
    | some b =>
      cases hb : B.admissible (B.q b) <;>
      cases hr : check (A.evalClass c) (B.evalRaw b) <;>
        simp [relHopRho, RelHopAt, hp, hf, hb, hr]

/-- The old total hop is the Boolean-relation instance, with no comparator law. -/
theorem relHopAt_total_bool_iff (A B : ExecModel) (T : A.Rep → B.Raw)
    (obs : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (c : A.Class) :
    RelHopAt A B (fun p => some (T p)) (fun a b => eqA (obs b) a = true) c ↔
      (hopModel A B T obs eqA).admissible c = true := by
  rw [hop_admissible_iff]
  constructor
  · rintro ⟨p, b, hp, hf, hb, hr⟩
    cases hf
    exact ⟨p, hp, hb, hr⟩
  · rintro ⟨p, hp, hb, hr⟩
    exact ⟨p, T p, hp, rfl, hb, hr⟩

theorem relHopCorrect_total_bool_iff (A B : ExecModel) (T : A.Rep → B.Raw)
    (obs : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool) :
    RelHopCorrect A B (fun p => some (T p)) (fun a b => eqA (obs b) a = true) ↔
      hopCorrect A B T obs eqA := by
  rw [hopCorrect_iff_exact]
  constructor
  · intro h c hc ha
    exact (relHopAt_total_bool_iff A B T obs eqA c).mp (h c hc ha)
  · intro h c hc ha
    exact (relHopAt_total_bool_iff A B T obs eqA c).mpr (h c hc ha)

theorem relHopCorrect_equality_iff (A B : ExecModel) (T : A.Rep → B.Raw)
    (obs : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (heqA : ∀ x y, eqA x y = true ↔ x = y) :
    RelHopCorrect A B (fun p => some (T p)) (fun a b => obs b = a) ↔
      hopCorrect A B T obs eqA := by
  rw [← relHopCorrect_total_bool_iff]
  constructor
  · exact relHopOn_mono A B _ _ _ _ (fun a b h => (heqA _ _).mpr h)
  · exact relHopOn_mono A B _ _ _ _ (fun a b h => (heqA _ _).mp h)

/-- A partial direct witness and the old hop-of-hop have the same admission
    once the first hop is admitted. This keeps the old theorem's weak premises. -/
theorem relHopAt_hopSeq_iff (A B C : ExecModel) (T12 : A.Rep → B.Raw)
    (obs12 : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (T23 : B.Rep → C.Raw) (obs23 : C.Outcome → B.Outcome)
    (c : A.Class) (hH : (hopModel A B T12 obs12 eqA).admissible c = true) :
    RelHopAt A C (partialHopSeq B (fun p => some (T12 p)) (fun q => some (T23 q)))
      (fun a d => eqA (obs12 (obs23 d)) a = true) c ↔
      (hopSeq A B C T12 obs12 eqA T23 obs23).admissible c = true := by
  obtain ⟨p, hp, hb, hr⟩ := (hop_admissible_iff A B T12 obs12 eqA c).mp hH
  cases hq : B.sigma (B.q (T12 p)) <;>
    simp [RelHopAt, partialHopSeq, hopSeq, hopModel, hp, hb, hr, hq, Bool.and_eq_true]

/-- The statement of hop_seq_correct, derived from relational composition.
    No hAB, no full profile, and no law on the outer comparator is added. -/
theorem hop_seq_correct_relational (A B C : ExecModel) (T12 : A.Rep → B.Raw)
    (obs12 : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (T23 : B.Rep → C.Raw) (obs23 : C.Outcome → B.Outcome)
    (eqB : B.Outcome → B.Outcome → Bool)
    (hBC : hopCorrect B C T23 obs23 eqB)
    (hqB : quotientFactorization B)
    (heqB : ∀ x y, eqB x y = true → x = y) :
    hopCorrect (hopModel A B T12 obs12 eqA) C T23
      (fun o => obs12 (obs23 o)) eqA := by
  rw [hopCorrect_iff_exact]
  intro c _ hH
  have hab := (relHopAt_total_bool_iff A B T12 obs12 eqA c).mpr hH
  have hbc := (relHopCorrect_total_bool_iff B C T23 obs23 eqB).mpr hBC
  have hs := relHopAt_seq A B C _ _ _ _ hqB c hab hbc
  apply (relHopAt_hopSeq_iff A B C T12 obs12 eqA T23 obs23 c hH).mp
  apply relHopAt_mono A C _ _ _ (fun a d h => ?_) c hs
  obtain ⟨b, h1, h2⟩ := h
  have e := heqB _ _ h2
  change eqA (obs12 (obs23 d)) a = true
  rw [e]
  exact h1

/-- Existing clock/resource semantics is an actual instance of the relation,
    including the named runtime resource limit on the target. -/
theorem clock_resource_relHopAt_iff {KA KB : Type} (A : Fam KA) (B : Fam KB)
    (T : A.Rep → B.Raw) (obs : B.Outcome → A.Outcome)
    (eqA : A.Outcome → A.Outcome → Bool) (lim : B.Outcome → Bool)
    (kA : KA) (kB : KB) (c : A.Class) :
    resourceOk ((clockHopModel A B T obs eqA lim kA kB).rho c) ↔
      RelHopAt (A.model kA) (B.model kB) (fun p => some (T p))
        (fun a b => eqA (obs b) a = true ∨ lim b = true) c := by
  rw [clock_resourceOk_iff]
  constructor
  · rintro ⟨p, hp, hb, hr⟩
    exact ⟨p, T p, hp, rfl, hb, hr⟩
  · rintro ⟨p, b, hp, hf, hb, hr⟩
    cases hf
    exact ⟨p, hp, hb, hr⟩

end NfCompose

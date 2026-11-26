import MSTNF.algorithms.MSTNFRelationalHopMWE

/-!
Named partial arrows and canonical model selections.
-/

namespace NfCompose.Indexed

open MSTNecessityExecModelMWE

/-! Named errors retain the stage in a sum. These are artifact-passage
errors, not a claim that two runtime executions refuse at the same budget. -/

def namedSeq {X Y Z E1 E2 : Type}
    (F : X → Except E1 Y) (G : Y → Except E2 Z) :
    X → Except (Sum E1 E2) Z :=
  fun x =>
    match F x with
    | .error e => .error (.inl e)
    | .ok y =>
      match G y with
      | .error e => .error (.inr e)
      | .ok z => .ok z

theorem namedSeq_error_left {X Y Z E1 E2 : Type}
    (F : X → Except E1 Y) (G : Y → Except E2 Z)
    (x : X) (e : E1) (hF : F x = .error e) :
    namedSeq F G x = .error (.inl e) := by
  simp [namedSeq, hF]

theorem namedSeq_error_right {X Y Z E1 E2 : Type}
    (F : X → Except E1 Y) (G : Y → Except E2 Z)
    (x : X) (y : Y) (e : E2)
    (hF : F x = .ok y) (hG : G y = .error e) :
    namedSeq F G x = .error (.inr e) := by
  simp [namedSeq, hF, hG]

theorem namedSeq_ok {X Y Z E1 E2 : Type}
    (F : X → Except E1 Y) (G : Y → Except E2 Z)
    (x : X) (y : Y) (z : Z)
    (hF : F x = .ok y) (hG : G y = .ok z) :
    namedSeq F G x = .ok z := by
  simp [namedSeq, hF, hG]

/-- The intermediate witness is the actual output of F, consumed by G. -/
theorem namedSeq_ok_iff {X Y Z E1 E2 : Type}
    (F : X → Except E1 Y) (G : Y → Except E2 Z) (x : X) (z : Z) :
    namedSeq F G x = .ok z ↔
      ∃ y, F x = .ok y ∧ G y = .ok z := by
  cases hF : F x with
  | error e => simp [namedSeq, hF]
  | ok y =>
    cases hG : G y with
    | error e => simp [namedSeq, hF, hG]
    | ok z' => simp [namedSeq, hF, hG]

theorem namedSeq_error_left_iff {X Y Z E1 E2 : Type}
    (F : X → Except E1 Y) (G : Y → Except E2 Z) (x : X) (e : E1) :
    namedSeq F G x = .error (.inl e) ↔ F x = .error e := by
  cases hF : F x with
  | error e' => simp [namedSeq, hF]
  | ok y =>
    cases hG : G y with
    | error e' => simp [namedSeq, hF, hG]
    | ok z => simp [namedSeq, hF, hG]

theorem namedSeq_error_right_iff {X Y Z E1 E2 : Type}
    (F : X → Except E1 Y) (G : Y → Except E2 Z) (x : X) (e : E2) :
    namedSeq F G x = .error (.inr e) ↔
      ∃ y, F x = .ok y ∧ G y = .error e := by
  cases hF : F x with
  | error e' => simp [namedSeq, hF]
  | ok y =>
    cases hG : G y with
    | error e' => simp [namedSeq, hF, hG]
    | ok z => simp [namedSeq, hF, hG]

def forgetError {E X : Type} : Except E X → Option X
  | .error _ => none
  | .ok x => some x

def optionSeq {X Y Z : Type} (F : X → Option Y) (G : Y → Option Z) :
    X → Option Z :=
  fun x => (F x).bind G

theorem namedSeq_forgetError {X Y Z E1 E2 : Type}
    (F : X → Except E1 Y) (G : Y → Except E2 Z) (x : X) :
    forgetError (namedSeq F G x) =
      optionSeq (fun x => forgetError (F x)) (fun y => forgetError (G y)) x := by
  cases hF : F x with
  | error e => simp [namedSeq, optionSeq, forgetError, hF]
  | ok y =>
    cases hG : G y with
    | error e => simp [namedSeq, optionSeq, forgetError, hF, hG]
    | ok z => simp [namedSeq, optionSeq, forgetError, hF, hG]

/-- A declaration of how refusal names pass to another name space.
The map need not be injective. Its exact output remains exposed. -/
structure NameMap {EA EB : Type} (P : EA → Prop) (Q : EB → Prop) where
  map : EA → EB
  preserves : ∀ e, P e → Q (map e)

namespace NameMap

def ident {E : Type} (P : E → Prop) : NameMap P P where
  map := id
  preserves := fun _ h => h

def comp {EA EB EC : Type} {P : EA → Prop} {Q : EB → Prop} {R : EC → Prop}
    (F : NameMap P Q) (G : NameMap Q R) : NameMap P R where
  map := fun e => G.map (F.map e)
  preserves := fun e h => G.preserves (F.map e) (F.preserves e h)

theorem comp_map {EA EB EC : Type}
    {P : EA → Prop} {Q : EB → Prop} {R : EC → Prop}
    (F : NameMap P Q) (G : NameMap Q R) (e : EA) :
    (F.comp G).map e = G.map (F.map e) := rfl

theorem comp_preserves {EA EB EC : Type}
    {P : EA → Prop} {Q : EB → Prop} {R : EC → Prop}
    (F : NameMap P Q) (G : NameMap Q R) (e : EA) (h : P e) :
    R ((F.comp G).map e) :=
  (F.comp G).preserves e h

def renameError {EA EB X : Type} {P : EA → Prop} {Q : EB → Prop}
    (F : NameMap P Q) : Except EA X → Except EB X
  | .error e => .error (F.map e)
  | .ok x => .ok x

theorem renameError_error {EA EB X : Type} {P : EA → Prop} {Q : EB → Prop}
    (F : NameMap P Q) (e : EA) :
    F.renameError (.error e : Except EA X) = .error (F.map e) := rfl

theorem renameError_ok {EA EB X : Type} {P : EA → Prop} {Q : EB → Prop}
    (F : NameMap P Q) (x : X) :
    F.renameError (.ok x : Except EA X) = .ok x := rfl

end NameMap

/-! Selection uses the existing model's q, admissible, rho and sigma.
No alternative ExecModel or evalRep is introduced. -/

structure Selection (M : ExecModel) where
  raw : M.Raw
  rep : M.Rep
  selected : M.sigma (M.q raw) = some rep
  admitted : M.admissible (M.q raw) = true

inductive SelectionError (M : ExecModel) where
  | targetRejected (reason : Option M.Residue)
  | representativeMissing

def selectRaw (M : ExecModel) (raw : M.Raw) :
    Except (SelectionError M) (Selection M) :=
  if ha : M.admissible (M.q raw) = true then
    match hs : M.sigma (M.q raw) with
    | none => .error .representativeMissing
    | some rep => .ok ⟨raw, rep, hs, ha⟩
  else
    .error (.targetRejected (M.rho (M.q raw)))

theorem selectRaw_ok (M : ExecModel) (raw : M.Raw) (rep : M.Rep)
    (ha : M.admissible (M.q raw) = true)
    (hs : M.sigma (M.q raw) = some rep) :
    selectRaw M raw = .ok ⟨raw, rep, hs, ha⟩ := by
  unfold selectRaw
  split
  · split
    · rename_i hnone
      simp [hs] at hnone
    · rename_i rep' hs'
      have heq : rep' = rep := Option.some.inj (hs'.symm.trans hs)
      subst rep'
      rfl
  · rename_i hnot
    exact False.elim (hnot ha)

theorem selectRaw_targetRejected (M : ExecModel) (raw : M.Raw)
    (ha : M.admissible (M.q raw) = false) :
    selectRaw M raw = .error (.targetRejected (M.rho (M.q raw))) := by
  simp [selectRaw, ha]

theorem selectRaw_representativeMissing (M : ExecModel) (raw : M.Raw)
    (ha : M.admissible (M.q raw) = true)
    (hs : M.sigma (M.q raw) = none) :
    selectRaw M raw = .error .representativeMissing := by
  unfold selectRaw
  split
  · split
    · rfl
    · rename_i rep hs'
      simp [hs] at hs'
  · rename_i hnot
    exact False.elim (hnot ha)

theorem selectRaw_raw (M : ExecModel) (raw : M.Raw) (s : Selection M)
    (h : selectRaw M raw = .ok s) : s.raw = raw := by
  by_cases ha : M.admissible (M.q raw) = true
  · cases hs : M.sigma (M.q raw) with
    | none =>
      rw [selectRaw_representativeMissing M raw ha hs] at h
      cases h
    | some rep =>
      have he := selectRaw_ok M raw rep ha hs
      rw [he] at h
      have hr : (⟨raw, rep, hs, ha⟩ : Selection M) = s := Except.ok.inj h
      cases hr
      rfl
  · simp [selectRaw, ha] at h

theorem selectRaw_selected (M : ExecModel) (raw : M.Raw) (s : Selection M)
    (h : selectRaw M raw = .ok s) :
    M.sigma (M.q raw) = some s.rep := by
  rw [← selectRaw_raw M raw s h]
  exact s.selected

theorem selectRaw_admitted (M : ExecModel) (raw : M.Raw) (s : Selection M)
    (h : selectRaw M raw = .ok s) :
    M.admissible (M.q raw) = true := by
  rw [← selectRaw_raw M raw s h]
  exact s.admitted

/-- Forgetting the new diagnostic structure recovers the actual sigma
selection on an admitted target raw. -/
theorem selectRaw_forget_rep (M : ExecModel) (raw : M.Raw)
    (ha : M.admissible (M.q raw) = true) :
    (forgetError (selectRaw M raw)).map (fun s => s.rep) =
      M.sigma (M.q raw) := by
  cases hs : M.sigma (M.q raw) with
  | none =>
    rw [selectRaw_representativeMissing M raw ha hs]
    simp [forgetError, hs]
  | some rep =>
    rw [selectRaw_ok M raw rep ha hs]
    simp [forgetError, hs]

theorem selectRaw_exists (M : ExecModel)
    (hp : representativePrecision M) (raw : M.Raw)
    (ha : M.admissible (M.q raw) = true) :
    ∃ s, selectRaw M raw = .ok s := by
  have hn := hp (M.q raw) ⟨raw, rfl⟩ ha
  cases hs : M.sigma (M.q raw) with
  | none => exact False.elim (hn hs)
  | some rep =>
    exact ⟨⟨raw, rep, hs, ha⟩, selectRaw_ok M raw rep ha hs⟩

theorem Selection.active (M : ExecModel) (s : Selection M) :
    activeClass M (M.q s.raw) :=
  ⟨s.raw, rfl⟩

/-- The semantic bridge is a hypothesis about raw and class, never about
an unprovided evalRep operation. -/
theorem Selection.raw_class (M : ExecModel)
    (hq : quotientFactorization M) (s : Selection M) :
    M.evalRaw s.raw = M.evalClass (M.q s.raw) :=
  hq s.raw

theorem selectRaw_raw_class (M : ExecModel)
    (hq : quotientFactorization M) (raw : M.Raw) (s : Selection M)
    (h : selectRaw M raw = .ok s) :
    M.evalRaw raw = M.evalClass (M.q s.raw) := by
  rw [selectRaw_raw M raw s h]
  exact hq raw

/-! The legacy source-class wrapper deliberately has no source-admission
premise: old RelHopOn permits an arbitrary predicate P on source classes. -/

def selectWithName (M : ExecModel) (c : M.Class) : Except Unit M.Rep :=
  match M.sigma c with
  | none => .error ()
  | some rep => .ok rep

theorem selectWithName_forgetError (M : ExecModel) (c : M.Class) :
    forgetError (selectWithName M c) = M.sigma c := by
  cases hs : M.sigma c <;> simp [selectWithName, hs, forgetError]

theorem selectWithName_ok_iff (M : ExecModel) (c : M.Class) (rep : M.Rep) :
    selectWithName M c = .ok rep ↔ M.sigma c = some rep := by
  cases hs : M.sigma c <;> simp [selectWithName, hs]

theorem selectWithName_error_iff (M : ExecModel) (c : M.Class) :
    selectWithName M c = .error () ↔ M.sigma c = none := by
  cases hs : M.sigma c <;> simp [selectWithName, hs]

end NfCompose.Indexed

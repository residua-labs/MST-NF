import MSTNF.r2.Decision

/-!
# MST-NF R2 — Cedar dedup instance (contract section 8)

Mechanization of the R2 contract, section 8, second half: the proposed
Cedar dedup instance against original cedar-spec at pin
`fdbec74705a75109ac66e96c22b8431bec50cc33`.

Sources (mature sources rule, preamble item 7):
- `cedar-spec` at the above pin (verified by direct source inspection):
  * `cedar-lean/Cedar/Thm/Data/List/Basic.lean:40` — `List.Equiv a b : Prop :=
    a ⊆ b ∧ b ⊆ a` (`⊆` is mutual membership).
  * `cedar-lean/Cedar/Thm/Authorization.lean:153` — `order_and_dup_independent
    (request entities policies₁ policies₂) : policies₁ ≡ policies₂ →
    isAuthorized request entities policies₁ = isAuthorized request entities
    policies₂` — the official duplicate/order invariance theorem that
    preserves the entire Response.
- Design of record: `MST-NF-R2-mechanization-contract.md` section 8 (the
  exact structural duplicate remover `n`, member preservation and
  idempotence, the normalized-input key with fixed-point class carrier,
  `Y`/`E`/`R = C × Y`, `v`, `iota`, `O = classify ∘ response`, the
  `erase ∘ classify = id` losslessness condition, use of official duplicate
    invariance for the reference bridge and normalization idempotence for the
    source section).
- Pinned base: `MSTNFR2.Decision` (`DecisionIF`, `vhat`, `bridged`,
  `decisionSourceSection`, `P3_boundObservation_reuse`).

Composition convention: cedar-spec itself depends on Mathlib and a newer
toolchain, so this module takes the official theorem *as a hypothesis in its
exact shape* (`DuplicateInvariance` below). Every downstream result
(reference bridge, source section, collisions, both-branch duplication) is
proved from that hypothesis plus the dedup lemmas, so instantiating it with
`Cedar.Thm.order_and_dup_independent` at the pin composes to a machine result
without re-proving anything here. No unproved bridge claim is made: closure
of this module alone remains conditional on that composition.

No Mathlib import; no `sorry`; no `native_decide`; no new axioms.
-/

namespace MSTNFR2

open MSTNecessityExecModelMWE

/-! ## Structural duplicate remover (contract: `n`) -/

section Dedup

variable {Pol : Type} [DecidableEq Pol]

/-- The exact structural duplicate remover of the contract:
    `n([]) = []`, `n(p :: ps) = let qs := n(ps); if p ∈ qs then qs else p :: qs`. -/
def dedup : List Pol → List Pol
  | [] => []
  | p :: ps =>
    let qs := dedup ps
    if p ∈ qs then qs else p :: qs

/-- Member preservation, forward direction. -/
theorem mem_dedup_of_mem : ∀ {l : List Pol} {p : Pol}, p ∈ l → p ∈ dedup l := by
  intro l p h
  induction l with
  | nil => exact h
  | cons p0 ps ih =>
      cases h with
      | head _ =>
          simp only [dedup]
          split
          next h1 => exact h1
          next _ => exact List.Mem.head _
      | tail _ ht =>
          have ihp := ih ht
          simp only [dedup]
          split
          next _ => exact ihp
          next _ => exact List.Mem.tail _ ihp

/-- Member preservation, backward direction. -/
theorem mem_of_mem_dedup : ∀ {l : List Pol} {p : Pol}, p ∈ dedup l → p ∈ l := by
  intro l p h
  induction l with
  | nil => exact h
  | cons p0 ps ih =>
      simp only [dedup] at h
      split at h
      next h1 => exact List.Mem.tail _ (ih h)
      next h1 =>
          cases h with
          | head _ => exact List.Mem.head _
          | tail _ ht => exact List.Mem.tail _ (ih ht)

/-- Member preservation as an iff: `p ∈ n l ↔ p ∈ l`. -/
theorem mem_dedup_iff (l : List Pol) (p : Pol) : p ∈ dedup l ↔ p ∈ l :=
  ⟨fun h => mem_of_mem_dedup h, fun h => mem_dedup_of_mem h⟩

/-- Idempotence: `n (n l) = n l` (used for the source section). -/
theorem dedup_idem (l : List Pol) : dedup (dedup l) = dedup l := by
  induction l with
  | nil => rfl
  | cons p0 ps ih =>
      simp only [dedup]
      by_cases h : p0 ∈ dedup ps
      · rw [if_pos h, ih]
      · rw [if_neg h]
        simp only [dedup]
        rw [if_neg (by rw [ih]; exact h), ih]

end Dedup

/-! ## Normalized inputs and the fixed-point class carrier -/

section Key

variable {Req Ent Pol : Type} [DecidableEq Pol]

/-- Cedar-shaped input: request, entities, policies (abstract components;
    the instance is parametric in them). -/
structure CedarInput (Req Ent Pol : Type) where
  request : Req
  entities : Ent
  policies : List Pol

/-- Replace policies by `n(policies)`; request and entities are retained. -/
def normIn (x : CedarInput Req Ent Pol) : CedarInput Req Ent Pol :=
  { x with policies := dedup x.policies }

/-- `x` with policies replaced by `l`. -/
def withPols (x : CedarInput Req Ent Pol) (l : List Pol) : CedarInput Req Ent Pol :=
  { x with policies := l }

/-- The fixed-point class carrier: every class is active. -/
abbrev Cfix (Req Ent Pol : Type) [DecidableEq Pol] : Type :=
  { x : CedarInput Req Ent Pol // x.policies = dedup x.policies }

/-- The normalized-input key. -/
def qkey (x : CedarInput Req Ent Pol) : Cfix Req Ent Pol :=
  ⟨normIn x, show dedup x.policies = dedup (dedup x.policies) from
    (dedup_idem x.policies).symm⟩

theorem Cfix_eq {c d : Cfix Req Ent Pol} (h : c.val = d.val) : c = d := by
  obtain ⟨cv, cp⟩ := c
  obtain ⟨dv, dp⟩ := d
  subst h
  rfl

theorem normIn_congr_policies {x y : CedarInput Req Ent Pol}
    (hr : x.request = y.request) (he : x.entities = y.entities)
    (hp : dedup x.policies = dedup y.policies) : normIn x = normIn y := by
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  simp only [normIn]
  show CedarInput.mk x1 x2 (dedup x3) = CedarInput.mk y1 y2 (dedup y3)
  rw [show x1 = y1 from hr, show x2 = y2 from he, hp]

/-- Normalization idempotence at input level: a fixed point is normalized. -/
theorem normIn_of_fix (c : Cfix Req Ent Pol) : normIn c.val = c.val := by
  obtain ⟨⟨rq, en, ps⟩, hps⟩ := c
  have hps' : ps = dedup ps := hps
  show normIn ⟨rq, en, ps⟩ = ⟨rq, en, ps⟩
  rw [hps']
  simp only [normIn]
  rw [dedup_idem]

/-- Every class is active: the key is the identity on fixed points. -/
theorem qkey_fix (c : Cfix Req Ent Pol) : qkey c.val = c := Cfix_eq (normIn_of_fix c)

theorem dedup_singleton (p : Pol) : dedup [p] = [p] := rfl

theorem dedup_dup_singleton (p : Pol) : dedup [p, p] = [p] := by
  simp [dedup]

omit [DecidableEq Pol] in
theorem withPols_dup_ne (x0 : CedarInput Req Ent Pol) (p : Pol) :
    withPols x0 [p] ≠ withPols x0 [p, p] := by
  intro h
  have hp : [p] = [p, p] := congrArg CedarInput.policies h
  exact absurd hp (by simp)

theorem qkey_withPols_dup (x0 : CedarInput Req Ent Pol) (p : Pol) :
    qkey (withPols x0 [p]) = qkey (withPols x0 [p, p]) := by
  apply Cfix_eq
  obtain ⟨rq, en, ps⟩ := x0
  show normIn ⟨rq, en, [p]⟩ = normIn ⟨rq, en, [p, p]⟩
  simp only [normIn]
  rw [dedup_singleton, dedup_dup_singleton]

end Key

/-! ## The response split and the dedup decision interface -/

section Instance

variable {Req Ent Pol Resp : Type} [DecidableEq Pol]

/-- The authorization decision tag (Cedar's `allow`/`deny`). -/
inductive CDecision where
  | allow | deny

variable (auth : CedarInput Req Ent Pol → Resp) (dcn : Resp → CDecision)

/-- Allowed-response subtype `Y = {response // response.decision = allow}`;
    both policy-identifier sets are retained (the entire Response is the
    carrier). -/
def CAllowed : Type := { r : Resp // dcn r = CDecision.allow }

/-- Denied-response subtype `E = {response // response.decision = deny}`. -/
def CDenied : Type := { r : Resp // dcn r = CDecision.deny }

/-- `classify` sends the entire Response to the appropriate subtype. -/
def classify (r : Resp) : Sum (CAllowed dcn) (CDenied dcn) :=
  match hd : dcn r with
  | CDecision.allow => Sum.inl ⟨r, hd⟩
  | CDecision.deny => Sum.inr ⟨r, hd⟩

/-- `erase` forgets only the branch proof and returns the entire Response. -/
def erase : Sum (CAllowed dcn) (CDenied dcn) → Resp :=
  Sum.elim (fun y => y.val) (fun e => e.val)

/-- Losslessness: `erase ∘ classify = id` for both policy-identifier sets. -/
theorem erase_classify (r : Resp) : erase dcn (classify dcn r) = r := by
  simp only [classify, erase]
  split
  next _ => rfl
  next _ => rfl

/-- The dedup bound-decision interface: `R = C × Y`, `v (c, y) = y`,
    `iota (c, y) = c.val`, `O = classify ∘ auth`; the class decision
    evaluates the normalized input and attaches the class on Allow. -/
def cedarIF : DecisionIF (CedarInput Req Ent Pol) (Cfix Req Ent Pol)
    (Cfix Req Ent Pol × CAllowed dcn) (CDenied dcn) (CAllowed dcn) where
  q := qkey
  D := fun c =>
    match hd : dcn (auth c.val) with
    | CDecision.allow => Sum.inl (c, ⟨auth c.val, hd⟩)
    | CDecision.deny => Sum.inr ⟨auth c.val, hd⟩
  v := fun p => p.2
  O := fun x => classify dcn (auth x)

/-- The official duplicate/order invariance, in the exact shape of
    `Cedar.Thm.order_and_dup_independent` at pin fdbec74705:
    mutual policy-list inclusion (that pin's `List.Equiv a b := a ⊆ b ∧
    b ⊆ a`) preserves the full evaluation result. Instantiate this
    hypothesis with the cedar-spec theorem to obtain an unconditional
    result. -/
def DuplicateInvariance (auth : CedarInput Req Ent Pol → Resp) : Prop :=
  ∀ (x : CedarInput Req Ent Pol) (a b : List Pol),
    (∀ p, p ∈ a → p ∈ b) → (∀ p, p ∈ b → p ∈ a) →
    auth (withPols x a) = auth (withPols x b)

/-- `classify` on an allowed response, by decision-case analysis. -/
theorem classify_allow (r : Resp) (h : dcn r = CDecision.allow) :
    classify dcn r = Sum.inl ⟨r, h⟩ := by
  simp only [classify]
  split
  next hd' => rfl
  next hd' => rw [h] at hd'; exact CDecision.noConfusion hd'

/-- `classify` on a denied response, by decision-case analysis. -/
theorem classify_deny (r : Resp) (h : dcn r = CDecision.deny) :
    classify dcn r = Sum.inr ⟨r, h⟩ := by
  simp only [classify]
  split
  next hd' => rw [h] at hd'; exact CDecision.noConfusion hd'
  next hd' => rfl

/-- The class decision on an allowed evaluation. -/
theorem D_allow (c : Cfix Req Ent Pol) (h : dcn (auth c.val) = CDecision.allow) :
    (cedarIF auth dcn).D c = Sum.inl (c, ⟨auth c.val, h⟩) := by
  simp only [cedarIF]
  split
  next hd' => rfl
  next hd' => rw [h] at hd'; exact CDecision.noConfusion hd'

/-- The class decision on a denied evaluation. -/
theorem D_deny (c : Cfix Req Ent Pol) (h : dcn (auth c.val) = CDecision.deny) :
    (cedarIF auth dcn).D c = Sum.inr ⟨auth c.val, h⟩ := by
  simp only [cedarIF]
  split
  next hd' => rw [h] at hd'; exact CDecision.noConfusion hd'
  next hd' => rfl

theorem auth_norm (hDup : DuplicateInvariance auth) (x : CedarInput Req Ent Pol) :
    auth x = auth (normIn x) :=
  hDup x x.policies (dedup x.policies) (fun _ hm => mem_dedup_of_mem hm)
    (fun _ hm => mem_of_mem_dedup hm)

/-- The reference bridge for the dedup instance, from official duplicate
    invariance. -/
theorem cedarIF_bridged (hDup : DuplicateInvariance auth) :
    bridged (cedarIF auth dcn) := by
  intro x
  have hn : auth x = auth (normIn x) := auth_norm auth hDup x
  cases hd : dcn (auth (normIn x)) with
  | allow =>
      have hD : (cedarIF auth dcn).D ((cedarIF auth dcn).q x)
          = Sum.inl (qkey x, ⟨auth (normIn x), hd⟩) := D_allow auth dcn (qkey x) hd
      have hO : classify dcn (auth x) = Sum.inl ⟨auth (normIn x), hd⟩ := by
        rw [hn, classify_allow dcn (auth (normIn x)) hd]
      rw [show (cedarIF auth dcn).O x = classify dcn (auth x) from rfl, hO, hD]
      rfl
  | deny =>
      have hD : (cedarIF auth dcn).D ((cedarIF auth dcn).q x)
          = Sum.inr ⟨auth (normIn x), hd⟩ := D_deny auth dcn (qkey x) hd
      have hO : classify dcn (auth x) = Sum.inr ⟨auth (normIn x), hd⟩ := by
        rw [hn, classify_deny dcn (auth (normIn x)) hd]
      rw [show (cedarIF auth dcn).O x = classify dcn (auth x) from rfl, hO, hD]
      rfl

/-- The source section for the dedup instance: on success the representative
    embeds through normalization back into its class (normalization
    idempotence is exactly the fixed-point property). -/
theorem cedarIF_sourceSection :
    decisionSourceSection (cedarIF auth dcn) (fun p => p.1.val) := by
  intro c r _ hD
  simp only [cedarIF] at hD
  split at hD
  next hd =>
      injection hD with hp
      subst hp
      exact qkey_fix c
  next hd => exact Sum.noConfusion hD

/-- Cross-input reuse: `[p]` and `[p, p]` are distinct inputs with the same
    key and, under the bridge, the same reference observation. -/
theorem dup_collision (hDup : DuplicateInvariance auth) (x0 : CedarInput Req Ent Pol)
    (p : Pol) :
    withPols x0 [p] ≠ withPols x0 [p, p] ∧
    qkey (withPols x0 [p]) = qkey (withPols x0 [p, p]) ∧
    (cedarIF auth dcn).O (withPols x0 [p]) = (cedarIF auth dcn).O (withPols x0 [p, p]) :=
  ⟨withPols_dup_ne x0 p, qkey_withPols_dup x0 p,
    P3_boundObservation_reuse (cedarIF auth dcn) (cedarIF_bridged auth dcn hDup)
      (withPols x0 [p]) (withPols x0 [p, p]) (qkey_withPols_dup x0 p)⟩

/-- Unconditional permit and forbid give collisions on both branches: when
    `[pA]` allows and `[pF]` denies, so do their duplicated copies, with the
    same full Response (the branch tag is preserved through the bridge). -/
theorem both_branches (hDup : DuplicateInvariance auth) (x0 : CedarInput Req Ent Pol)
    (pA pF : Pol)
    (hA : dcn (auth (withPols x0 [pA])) = CDecision.allow)
    (hF : dcn (auth (withPols x0 [pF])) = CDecision.deny) :
    dcn (auth (withPols x0 [pA, pA])) = CDecision.allow ∧
    dcn (auth (withPols x0 [pF, pF])) = CDecision.deny := by
  constructor
  · have hnp : normIn (withPols x0 [pA, pA]) = normIn (withPols x0 [pA]) :=
        normIn_congr_policies rfl rfl (by
          show dedup [pA, pA] = dedup [pA]
          rw [dedup_dup_singleton, dedup_singleton])
    rw [auth_norm auth hDup (withPols x0 [pA, pA]), hnp,
      ← auth_norm auth hDup (withPols x0 [pA])]
    exact hA
  · have hnp : normIn (withPols x0 [pF, pF]) = normIn (withPols x0 [pF]) :=
        normIn_congr_policies rfl rfl (by
          show dedup [pF, pF] = dedup [pF]
          rw [dedup_dup_singleton, dedup_singleton])
    rw [auth_norm auth hDup (withPols x0 [pF, pF]), hnp,
      ← auth_norm auth hDup (withPols x0 [pF])]
    exact hF

end Instance

end MSTNFR2

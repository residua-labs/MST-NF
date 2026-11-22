import MSTNF.algorithms.MSTNecessityExecModelMWE
import MSTNF.r2.Decision

/-!
# MST-NF R2 — composition: P5 (paired sequential), P7 (tagged sum), P8 (product)

Mechanization of the R2 contract, section 5 ("Sequential, sum, product, and
finite kinds") and section 7 registry rows P5, P7, P8; paper v0.2 sections
5.1, 5.3, 5.4, 5.5.

Sources (mature sources rule, preamble item 7):
- Design of record: the R2 mechanization contract
  sections 5 and 7; paper v0.2 `MST-NF-paper-v0.2.md` Propositions 5, 7, 8.
- Pinned base: `MSTNF.algorithms.MSTNecessityExecModelMWE` (unchanged).
- Short-fircuit sequencing vs. error accumulation as distinct effect-combination
  patterns: McBride & Paterson, "Applicative programming with effects",
  JFP 18(1), 2008 (exception example), cited by the paper's section 5.6.

Scope notes (contract): P5 is the *paired* version — success stores `(r1, r2)`,
the interpretation `v21` reads only the second component, the composite source
section goes through the first component only. P8's residue kinds are
`K1 + K2 + (K1 × K2)` (leftOnly / rightOnly / both); a plain tagged union
cannot encode a double refusal's two labels. Theorems here preserve the
declared observations only; no claim about coarsest keys, optimal abstract
interpreters, or termination of interacting rewrites is made.

No Mathlib import; no `sorry`; no `native_decide`; no new axioms.
-/

namespace MSTNFR2

open MSTNecessityExecModelMWE

/-! ## P5: paired sequential composition -/

section Seq

variable {X1 C1 R1 E1 Y1 X2 C2 R2 E2 Y2 : Type}

/-- Composite class decision `D21` (paper section 5.1): first-stage refusal
    tagged `first`; on first-stage success the second decision runs on
    `q2 (g (v1 r1))` and a success returns the pair `(r1, r2)`. -/
def seqD (K1 : DecisionIF X1 C1 R1 E1 Y1) (K2 : DecisionIF X2 C2 R2 E2 Y2)
    (g : Y1 → X2) (c : C1) : Sum (R1 × R2) (Sum E1 E2) :=
  match K1.D c with
  | Sum.inr e1 => Sum.inr (Sum.inl e1)
  | Sum.inl r1 =>
    match K2.D (K2.q (g (K1.v r1))) with
    | Sum.inl r2 => Sum.inl (r1, r2)
    | Sum.inr e2 => Sum.inr (Sum.inr e2)

/-- Composite reference pipeline `O21`: evaluate `O1`; on success evaluate
    `O2` on the connected value; refusals carry the stage tag. -/
def seqO (K1 : DecisionIF X1 C1 R1 E1 Y1) (K2 : DecisionIF X2 C2 R2 E2 Y2)
    (g : Y1 → X2) (x : X1) : Sum Y2 (Sum E1 E2) :=
  match K1.O x with
  | Sum.inr e1 => Sum.inr (Sum.inl e1)
  | Sum.inl y1 =>
    match K2.O (g y1) with
    | Sum.inl y2 => Sum.inl y2
    | Sum.inr e2 => Sum.inr (Sum.inr e2)

/-- `v21 (r1, r2) = v2 r2`: the pair retains the first realization while the
    advertised terminal value comes from the second (paper section 5.1). -/
def seqV (v2 : R2 → Y2) : R1 × R2 → Y2 := fun p => v2 p.2

/-- The composite bound-decision interface of the sequential construction. -/
def seqIF (K1 : DecisionIF X1 C1 R1 E1 Y1) (K2 : DecisionIF X2 C2 R2 E2 Y2)
    (g : Y1 → X2) : DecisionIF X1 C1 (R1 × R2) (Sum E1 E2) Y2 where
  q := K1.q
  D := seqD K1 K2 g
  v := seqV K2.v
  O := seqO K1 K2 g

/-- `iota21 (r1, r2) = iota1 r1`: only the first source section is claimed. -/
def seqIota (iota1 : R1 → X1) : R1 × R2 → X1 := fun p => iota1 p.1

/-- **P5** (sequential observation preservation): under the two component
    reference bridges, `O21 = vhat v21 ∘ D21 ∘ q1`. -/
theorem P5_sequential_preservation (K1 : DecisionIF X1 C1 R1 E1 Y1)
    (K2 : DecisionIF X2 C2 R2 E2 Y2) (g : Y1 → X2)
    (h1 : bridged K1) (h2 : bridged K2) : bridged (seqIF K1 K2 g) := by
  intro x
  cases hD1 : K1.D (K1.q x) with
  | inr e1 =>
      simp only [seqIF, seqO, seqD, h1 x, hD1, vhat]
  | inl r1 =>
      cases hD2 : K2.D (K2.q (g (K1.v r1))) with
      | inl r2 =>
          simp only [seqIF, seqO, seqD, h1 x, h2 (g (K1.v r1)), hD1, hD2, vhat, seqV]
      | inr e2 =>
          simp only [seqIF, seqO, seqD, h1 x, h2 (g (K1.v r1)), hD1, hD2, vhat, seqV]

/-- **P5** (first-source section): a first-component source section induces
    the composite source section on active admitted classes. -/
theorem P5_sequential_sourceSection (K1 : DecisionIF X1 C1 R1 E1 Y1)
    (K2 : DecisionIF X2 C2 R2 E2 Y2) (g : Y1 → X2) (iota1 : R1 → X1)
    (hsec1 : decisionSourceSection K1 iota1) :
    decisionSourceSection (seqIF K1 K2 g) (seqIota iota1) := by
  intro c p hc hD
  cases hD1 : K1.D c with
  | inr e1 =>
      simp only [seqIF, seqD, hD1] at hD
      exact Sum.noConfusion hD
  | inl r1 =>
      cases hD2 : K2.D (K2.q (g (K1.v r1))) with
      | inr e2 =>
          simp only [seqIF, seqD, hD1, hD2] at hD
          exact Sum.noConfusion hD
      | inl r2 =>
          simp only [seqIF, seqD, hD1, hD2] at hD
          injection hD with hp
          rw [← hp]
          exact hsec1 c r1 hc hD1

end Seq

/-! ## P7: tagged sum -/

section SumComp

variable {X1 C1 R1 E1 Y1 X2 C2 R2 E2 Y2 : Type}

/-- Tagged-sum class decision: each component applies on its branch, the tag
    preserved in successes and refusals (paper section 5.3). -/
def sumD (K1 : DecisionIF X1 C1 R1 E1 Y1) (K2 : DecisionIF X2 C2 R2 E2 Y2)
    (cc : Sum C1 C2) : Sum (Sum R1 R2) (Sum E1 E2) :=
  match cc with
  | Sum.inl c1 =>
    match K1.D c1 with
    | Sum.inl r => Sum.inl (Sum.inl r)
    | Sum.inr e => Sum.inr (Sum.inl e)
  | Sum.inr c2 =>
    match K2.D c2 with
    | Sum.inl r => Sum.inl (Sum.inr r)
    | Sum.inr e => Sum.inr (Sum.inr e)

/-- Tagged-sum reference observation. -/
def sumO (K1 : DecisionIF X1 C1 R1 E1 Y1) (K2 : DecisionIF X2 C2 R2 E2 Y2)
    (x : Sum X1 X2) : Sum (Sum Y1 Y2) (Sum E1 E2) :=
  match x with
  | Sum.inl x1 =>
    match K1.O x1 with
    | Sum.inl y => Sum.inl (Sum.inl y)
    | Sum.inr e => Sum.inr (Sum.inl e)
  | Sum.inr x2 =>
    match K2.O x2 with
    | Sum.inl y => Sum.inl (Sum.inr y)
    | Sum.inr e => Sum.inr (Sum.inr e)

/-- The tagged-sum bound-decision interface. -/
def sumIF (K1 : DecisionIF X1 C1 R1 E1 Y1) (K2 : DecisionIF X2 C2 R2 E2 Y2) :
    DecisionIF (Sum X1 X2) (Sum C1 C2) (Sum R1 R2) (Sum E1 E2) (Sum Y1 Y2) where
  q := Sum.map K1.q K2.q
  D := sumD K1 K2
  v := Sum.map K1.v K2.v
  O := sumO K1 K2

/-- **P7** (sum preservation): the tagged-sum decision satisfies the reference
    bridge for the tagged-sum reference observation. -/
theorem P7_sum_preservation (K1 : DecisionIF X1 C1 R1 E1 Y1)
    (K2 : DecisionIF X2 C2 R2 E2 Y2) (h1 : bridged K1) (h2 : bridged K2) :
    bridged (sumIF K1 K2) := by
  intro x
  cases x with
  | inl x1 =>
      cases hD1 : K1.D (K1.q x1) with
      | inl r => simp only [sumIF, sumO, sumD, h1 x1, hD1, vhat, Sum.map_inl]
      | inr e => simp only [sumIF, sumO, sumD, h1 x1, hD1, vhat, Sum.map_inl]
  | inr x2 =>
      cases hD2 : K2.D (K2.q x2) with
      | inl r => simp only [sumIF, sumO, sumD, h2 x2, hD2, vhat, Sum.map_inr]
      | inr e => simp only [sumIF, sumO, sumD, h2 x2, hD2, vhat, Sum.map_inr]

/-- **P7** (sum source section): tagged source interpretations satisfy the
    section law on active admitted classes of the sum. -/
theorem P7_sum_sourceSection (K1 : DecisionIF X1 C1 R1 E1 Y1)
    (K2 : DecisionIF X2 C2 R2 E2 Y2) (iota1 : R1 → X1) (iota2 : R2 → X2)
    (hsec1 : decisionSourceSection K1 iota1)
    (hsec2 : decisionSourceSection K2 iota2) :
    decisionSourceSection (sumIF K1 K2) (Sum.map iota1 iota2) := by
  intro c r hc hD
  obtain ⟨x, hx⟩ := hc
  cases x with
  | inl x1 =>
      cases c with
      | inl c1 =>
          have hq1 : K1.q x1 = c1 := by injection hx
          cases hD1 : K1.D c1 with
          | inl r' =>
              simp only [sumIF, sumD, hD1] at hD
              injection hD with hr
              rw [← hr]
              exact congrArg Sum.inl (hsec1 c1 r' ⟨x1, hq1⟩ hD1)
          | inr e =>
              simp only [sumIF, sumD, hD1] at hD
              exact Sum.noConfusion hD
      | inr c2 => exact Sum.noConfusion hx
  | inr x2 =>
      cases c with
      | inl c1 => exact Sum.noConfusion hx
      | inr c2 =>
          have hq2 : K2.q x2 = c2 := by injection hx
          cases hD2 : K2.D c2 with
          | inl r' =>
              simp only [sumIF, sumD, hD2] at hD
              injection hD with hr
              rw [← hr]
              exact congrArg Sum.inr (hsec2 c2 r' ⟨x2, hq2⟩ hD2)
          | inr e =>
              simp only [sumIF, sumD, hD2] at hD
              exact Sum.noConfusion hD

end SumComp

/-! ## P8: independent accumulating product -/

section Product

variable {X1 C1 R1 E1 Y1 X2 C2 R2 E2 Y2 : Type}

/-- Product class decision with three residue constructors: `leftOnly`
    (`Sum.inl e1`), `rightOnly` (`Sum.inr (Sum.inl e2)`), `both`
    (`Sum.inr (Sum.inr (e1, e2))`). A successful partial value is discarded
    when the other component fails (paper section 5.4). -/
def prodD (K1 : DecisionIF X1 C1 R1 E1 Y1) (K2 : DecisionIF X2 C2 R2 E2 Y2)
    (cc : C1 × C2) : Sum (R1 × R2) (Sum E1 (Sum E2 (E1 × E2))) :=
  match K1.D cc.1 with
  | Sum.inl r1 =>
    match K2.D cc.2 with
    | Sum.inl r2 => Sum.inl (r1, r2)
    | Sum.inr e2 => Sum.inr (Sum.inr (Sum.inl e2))
  | Sum.inr e1 =>
    match K2.D cc.2 with
    | Sum.inl _ => Sum.inr (Sum.inl e1)
    | Sum.inr e2 => Sum.inr (Sum.inr (Sum.inr (e1, e2)))

/-- Product reference observation with the same success/failure policy. -/
def prodO (K1 : DecisionIF X1 C1 R1 E1 Y1) (K2 : DecisionIF X2 C2 R2 E2 Y2)
    (p : X1 × X2) : Sum (Y1 × Y2) (Sum E1 (Sum E2 (E1 × E2))) :=
  match K1.O p.1 with
  | Sum.inl y1 =>
    match K2.O p.2 with
    | Sum.inl y2 => Sum.inl (y1, y2)
    | Sum.inr e2 => Sum.inr (Sum.inr (Sum.inl e2))
  | Sum.inr e1 =>
    match K2.O p.2 with
    | Sum.inl _ => Sum.inr (Sum.inl e1)
    | Sum.inr e2 => Sum.inr (Sum.inr (Sum.inr (e1, e2)))

/-- The independent-product bound-decision interface, `q× (x1,x2) =
    (q1 x1, q2 x2)`. -/
def prodIF (K1 : DecisionIF X1 C1 R1 E1 Y1) (K2 : DecisionIF X2 C2 R2 E2 Y2) :
    DecisionIF (X1 × X2) (C1 × C2) (R1 × R2) (Sum E1 (Sum E2 (E1 × E2))) (Y1 × Y2) where
  q := fun p => (K1.q p.1, K2.q p.2)
  D := prodD K1 K2
  v := fun p => (K1.v p.1, K2.v p.2)
  O := prodO K1 K2

/-- **P8** (product preservation): the four-case product decision satisfies
    the reference bridge for the reference observation with the same success
    and failure policy. -/
theorem P8_product_preservation (K1 : DecisionIF X1 C1 R1 E1 Y1)
    (K2 : DecisionIF X2 C2 R2 E2 Y2) (h1 : bridged K1) (h2 : bridged K2) :
    bridged (prodIF K1 K2) := by
  intro p
  cases hD1 : K1.D (K1.q p.1) with
  | inl r1 =>
      cases hD2 : K2.D (K2.q p.2) with
      | inl r2 =>
          simp only [prodIF, prodO, prodD, h1 p.1, h2 p.2, hD1, hD2, vhat]
      | inr e2 =>
          simp only [prodIF, prodO, prodD, h1 p.1, h2 p.2, hD1, hD2, vhat]
  | inr e1 =>
      cases hD2 : K2.D (K2.q p.2) with
      | inl r2 =>
          simp only [prodIF, prodO, prodD, h1 p.1, h2 p.2, hD1, hD2, vhat]
      | inr e2 =>
          simp only [prodIF, prodO, prodD, h1 p.1, h2 p.2, hD1, hD2, vhat]

/-- **P8** (product source section): component source sections induce a
    product source section on active, jointly admitted classes. -/
theorem P8_product_sourceSection (K1 : DecisionIF X1 C1 R1 E1 Y1)
    (K2 : DecisionIF X2 C2 R2 E2 Y2) (iota1 : R1 → X1) (iota2 : R2 → X2)
    (hsec1 : decisionSourceSection K1 iota1)
    (hsec2 : decisionSourceSection K2 iota2) :
    decisionSourceSection (prodIF K1 K2) (fun p => (iota1 p.1, iota2 p.2)) := by
  intro c p hc hD
  obtain ⟨x, hx⟩ := hc
  simp only [prodIF] at hx
  rcases c with ⟨c1, c2⟩
  injection hx with hx1 hx2
  cases hD1 : K1.D c1 with
  | inl r1 =>
      cases hD2 : K2.D c2 with
      | inl r2 =>
          simp only [prodIF, prodD, hD1, hD2] at hD
          injection hD with hp
          rw [← hp]
          simp only [prodIF]
          rw [hsec1 c1 r1 ⟨x.1, hx1⟩ hD1, hsec2 c2 r2 ⟨x.2, hx2⟩ hD2]
      | inr e2 =>
          simp only [prodIF, prodD, hD1, hD2] at hD
          exact Sum.noConfusion hD
  | inr e1 =>
      cases hD2 : K2.D c2 with
      | inl r2 =>
          simp only [prodIF, prodD, hD1, hD2] at hD
          exact Sum.noConfusion hD
      | inr e2 =>
          simp only [prodIF, prodD, hD1, hD2] at hD
          exact Sum.noConfusion hD

end Product

/-! ## Finite residue kinds (paper section 5.5) -/

section Kinds

variable {E1 E2 K1 K2 : Type}

/-- Tagged kinds `K1 + K2` for the sequential and sum residuals. -/
def taggedKind (k1 : E1 → K1) (k2 : E2 → K2) : Sum E1 E2 → Sum K1 K2 :=
  Sum.map k1 k2

/-- The declared kind list for tagged residuals: the two tagged lists. -/
def taggedKinds (L1 : List K1) (L2 : List K2) : List (Sum K1 K2) :=
  L1.map Sum.inl ++ L2.map Sum.inr

theorem taggedKinds_closed (k1 : E1 → K1) (k2 : E2 → K2) (L1 : List K1) (L2 : List K2)
    (h1 : ∀ e, k1 e ∈ L1) (h2 : ∀ e, k2 e ∈ L2) :
    ∀ e, taggedKind k1 k2 e ∈ taggedKinds L1 L2 := by
  intro e
  cases e with
  | inl e1 =>
      simp only [taggedKind, taggedKinds, Sum.map_inl, List.mem_append]
      exact Or.inl (List.mem_map_of_mem Sum.inl (h1 e1))
  | inr e2 =>
      simp only [taggedKind, taggedKinds, Sum.map_inr, List.mem_append]
      exact Or.inr (List.mem_map_of_mem Sum.inr (h2 e2))

/-- Product residue kinds `K1 + K2 + (K1 × K2)`: leftOnly, rightOnly, and
    the pair label of a simultaneous failure. -/
def prodKind (k1 : E1 → K1) (k2 : E2 → K2) :
    Sum E1 (Sum E2 (E1 × E2)) → Sum K1 (Sum K2 (K1 × K2))
  | Sum.inl e1 => Sum.inl (k1 e1)
  | Sum.inr (Sum.inl e2) => Sum.inr (Sum.inl (k2 e2))
  | Sum.inr (Sum.inr p) => Sum.inr (Sum.inr (k1 p.1, k2 p.2))

/-- The Cartesian enumeration of two finite kind lists. -/
def allPairs : List K1 → List K2 → List (K1 × K2)
  | [], _ => []
  | a :: as, bs => bs.map (fun b => (a, b)) ++ allPairs as bs

/-- The declared kind list for product residuals: both tagged lists plus the
    enumerated Cartesian product. -/
def prodKinds (L1 : List K1) (L2 : List K2) :
    List (Sum K1 (Sum K2 (K1 × K2))) :=
  L1.map Sum.inl ++ L2.map (fun k => Sum.inr (Sum.inl k)) ++
    (allPairs L1 L2).map (fun p => Sum.inr (Sum.inr p))

theorem mem_allPairs {a : K1} {b : K2} {l1 : List K1} {l2 : List K2}
    (ha : a ∈ l1) (hb : b ∈ l2) : (a, b) ∈ allPairs l1 l2 := by
  induction l1 with
  | nil => cases ha
  | cons a' as ih =>
      simp only [List.mem_cons] at ha
      cases ha with
      | inl hae => subst hae; simp only [allPairs, List.mem_append]; exact Or.inl (List.mem_map_of_mem (fun b => (a, b)) hb)
      | inr har => simp only [allPairs, List.mem_append]; exact Or.inr (ih har)

/-- **P8 kinds** (finite kind closure, accumulating product): with both
    component kind closures, every product residue kind is in the declared
    list `K1 + K2 + (K1 × K2)`. -/
theorem prodKinds_closed (k1 : E1 → K1) (k2 : E2 → K2) (L1 : List K1) (L2 : List K2)
    (h1 : ∀ e, k1 e ∈ L1) (h2 : ∀ e, k2 e ∈ L2) :
    ∀ e, prodKind k1 k2 e ∈ prodKinds L1 L2 := by
  intro e
  cases e with
  | inl e1 =>
      simp only [prodKind, prodKinds, List.mem_append]
      exact Or.inl (Or.inl (List.mem_map_of_mem Sum.inl (h1 e1)))
  | inr e' =>
      cases e' with
      | inl e2 =>
          simp only [prodKind, prodKinds, List.mem_append]
          exact Or.inl (Or.inr (List.mem_map_of_mem (fun k => Sum.inr (Sum.inl k)) (h2 e2)))
      | inr p =>
          simp only [prodKind, prodKinds, List.mem_append]
          exact Or.inr (List.mem_map_of_mem (fun p => Sum.inr (Sum.inr p)) (mem_allPairs (h1 p.1) (h2 p.2)))

end Kinds

end MSTNFR2

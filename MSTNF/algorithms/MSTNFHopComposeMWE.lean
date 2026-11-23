import MSTNF.algorithms.MSTNFHopMWE
import MSTNF.algorithms.MSTNFCompositionSumMWE
import MSTNF.algorithms.MSTNFCompositionProdMWE

/-!
Hop correctness composes, proved once.

A hop is `hopModel` (`MSTNFHopMWE`); its correctness is `hopCorrect`. This file
proves that correctness composes, so a chain's correctness is an instance
of the laws below and is never re-proved per chain.

1. Sequential (`hop_seq_correct`, `hop_seq_correct_direct`).
   The composite of `A → B` and `B → C` is the hop of a hop,
   `hopSeq = hopModel (hopModel A B T12 obs12 eqA) C T23 (obs12 ∘ obs23) eqA`,
   whose representative is B's. Hypotheses: `hBC`, B's quotient
   factorization `hqB` (a profile law), and soundness of `eqB`
   (`eqB x y = true → x = y`); `hAB` is not needed for this form, because
   the hop of a hop already carries the `A → B` check in its own admission.
   On the A-admissible classes (`hop_seq_correct_from`) `hAB` is added.
   `hopSeq_correct_iff` proves the hop-of-a-hop form equals the direct form:
   a single hop `A → seq(B, C)` (`hopDirect`) together with `A → B`.
   `eqA` needs no law at all. `hopObsSeq_comp` / `hopObsSeq_chain3` are the
   same law on the `hopObsSeq` statements of `MSTNFHopMWE`.
2. Sums and products. `hop_sum_correct_iff`: a hop on `sumModel F` into
   `sumModel G` is correct iff every component hop is (one target: `G` const,
   `hop_sum_one_target`). `hop_prod_correct`: a hop on `prodModel` is correct
   when both component hops are; `hop_prod_correct_left/right` give the
   converse when the other side has an active admissible class.
3. Necessity (`MSTNFHopWitnessMWE`): `HopWitness` gives, for every hypothesis of every law, a model
   where all other hypotheses hold and the conclusion fails.
4. Clocks and resources (CakeML's per-phase form). A `Fam K` is a layer whose
   carriers, admission, residue and representative are fixed and whose
   evaluation is indexed by a clock `k : K` (fuel, steps). `clockHopModel`
   is the hop at a clock pair with the named residue
   `ClockResidue.resourceLimit` for target outcomes the caller names as
   resource exhaustion (`lim`). `clockCorrectOn`: for every source clock
   there is a target clock at which the hop has no residue or only the
   resource residue. `clock_hop_seq_correct` composes it; the composite may
   stop by resource only where C does or where B did
   (`clockSeqLim`, minimal by `HopWitness.clock_lim_minimal`).
   `clock_const_iff`: on clock-free layers without resource residue the
   clocked law is exactly `hopCorrect`.
5. Bootstrap (`bootstrap_instance`): from the per-hop clocked theorems for
   every admissible input and the fixpoint evidence `chainOut … p = some bin`
   (the binary is the chain's image of the compiler's source `p`), the binary
   behaves as `p` on every such input, up to the named resource residue.
Prior art for the shape: CompCert's `compose_forward_simulations`; CakeML's
per-phase semantics preservation with clocks.
-/
namespace NfCompose
open MSTNecessityExecModelMWE

/-! ## Unfolding the hop admission -/

theorem hop_admissible_iff (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool) (c : M_A.Class) :
    (hopModel M_A M_B T obs eqA).admissible c = true ↔
      ∃ rep, M_A.sigma c = some rep ∧
        M_B.admissible (M_B.q (T rep)) = true ∧
        eqA (obs (M_B.evalRaw (T rep))) (M_A.evalClass c) = true := by
  cases hs : M_A.sigma c with
  | none => simp [hopModel, hs]
  | some rep =>
      have hadm : (hopModel M_A M_B T obs eqA).admissible c =
          (M_B.admissible (M_B.q (T rep)) &&
            eqA (obs (M_B.evalRaw (T rep))) (M_A.evalClass c)) := by
        simp only [hopModel, hs]
      rw [hadm]
      constructor
      · intro h
        exact ⟨rep, rfl, (bool_and_true h).1, (bool_and_true h).2⟩
      · rintro ⟨r, hr, ha, he⟩
        cases hr
        simp [ha, he]

theorem hop_sigma_eq (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool) (c : M_A.Class) (rep : M_A.Rep)
    (hs : M_A.sigma c = some rep)
    (ha : M_B.admissible (M_B.q (T rep)) = true)
    (he : eqA (obs (M_B.evalRaw (T rep))) (M_A.evalClass c) = true) :
    (hopModel M_A M_B T obs eqA).sigma c = M_B.sigma (M_B.q (T rep)) := by
  simp [hopModel, hs, ha, he]

/-! ## 1. Sequential composition -/

/-- the composite hop `A → C` through B's representative: a hop of a hop. -/
def hopSeq (A B C : ExecModel) (T12 : A.Rep → B.Raw)
    (obs12 : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (T23 : B.Rep → C.Raw) (obs23 : C.Outcome → B.Outcome) : ExecModel :=
  hopModel (hopModel A B T12 obs12 eqA) C T23 (fun o => obs12 (obs23 o)) eqA

/-- the direct form: one hop from `A` into the sequential target `seq(B, C)`. -/
def hopDirect (A B C : ExecModel) (T12 : A.Rep → B.Raw)
    (obs12 : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (T23 : B.Rep → C.Raw) (obs23 : C.Outcome → B.Outcome) : ExecModel :=
  hopModel A (seqModel B C T23) T12 (fun o => obs12 (hopSeqObs obs23 o)) eqA

/-- sequential composition, hop-of-a-hop form (fewest hypotheses). -/
theorem hop_seq_correct (A B C : ExecModel) (T12 : A.Rep → B.Raw)
    (obs12 : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (T23 : B.Rep → C.Raw) (obs23 : C.Outcome → B.Outcome)
    (eqB : B.Outcome → B.Outcome → Bool)
    (hBC : hopCorrect B C T23 obs23 eqB)
    (hqB : quotientFactorization B)
    (heqB : ∀ x y, eqB x y = true → x = y) :
    hopCorrect (hopModel A B T12 obs12 eqA) C T23 (fun o => obs12 (obs23 o)) eqA := by
  rw [hopCorrect_iff_exact]
  intro c _ hH
  obtain ⟨repA, hsA, haB, he12⟩ := (hop_admissible_iff A B T12 obs12 eqA c).mp hH
  have hBCadm := (hopCorrect_iff_exact B C T23 obs23 eqB).mp hBC
    (B.q (T12 repA)) ⟨T12 repA, rfl⟩ haB
  obtain ⟨repB, hsB, haC, he23⟩ :=
    (hop_admissible_iff B C T23 obs23 eqB _).mp hBCadm
  have hv : obs23 (C.evalRaw (T23 repB)) = B.evalRaw (T12 repA) :=
    (heqB _ _ he23).trans (hqB (T12 repA)).symm
  apply (hop_admissible_iff (hopModel A B T12 obs12 eqA) C T23
    (fun o => obs12 (obs23 o)) eqA c).mpr
  refine ⟨repB, ?_, haC, ?_⟩
  · rw [hop_sigma_eq A B T12 obs12 eqA c repA hsA haB he12]
    exact hsB
  · show eqA (obs12 (obs23 (C.evalRaw (T23 repB)))) (A.evalClass c) = true
    rw [hv]
    exact he12

/-- sequential composition on the A-admissible classes. -/
theorem hop_seq_correct_from (A B C : ExecModel) (T12 : A.Rep → B.Raw)
    (obs12 : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (T23 : B.Rep → C.Raw) (obs23 : C.Outcome → B.Outcome)
    (eqB : B.Outcome → B.Outcome → Bool)
    (hAB : hopCorrect A B T12 obs12 eqA)
    (hBC : hopCorrect B C T23 obs23 eqB)
    (hqB : quotientFactorization B)
    (heqB : ∀ x y, eqB x y = true → x = y) :
    noResidueOn (hopSeq A B C T12 obs12 eqA T23 obs23)
      (fun c => A.admissible c = true) := by
  intro c hc ha
  exact hop_seq_correct A B C T12 obs12 eqA T23 obs23 eqB hBC hqB heqB c hc
    ((hopCorrect_iff_exact A B T12 obs12 eqA).mp hAB c hc ha)

/-- the hop of a hop admits exactly what `A → B` and the direct hop
    `A → seq(B, C)` both accept. -/
theorem hopSeq_admissible (A B C : ExecModel) (T12 : A.Rep → B.Raw)
    (obs12 : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (T23 : B.Rep → C.Raw) (obs23 : C.Outcome → B.Outcome) (c : A.Class) :
    (hopSeq A B C T12 obs12 eqA T23 obs23).admissible c =
      ((hopModel A B T12 obs12 eqA).admissible c &&
        (hopDirect A B C T12 obs12 eqA T23 obs23).admissible c) := by
  cases hsA : A.sigma c with
  | none => simp [hopSeq, hopDirect, hopModel, hsA]
  | some repA =>
      cases haB : B.admissible (B.q (T12 repA)) <;>
      cases he : eqA (obs12 (B.evalRaw (T12 repA))) (A.evalClass c) <;>
      cases hsB : B.sigma (B.q (T12 repA)) <;>
      simp [hopSeq, hopDirect, hopModel, seqModel, seqAdmOf, seqEvalOf,
        hopSeqObs, hsA, haB, he, hsB]

/-- the hop-of-a-hop form equals the direct form plus `A → B`. -/
theorem hopSeq_correct_iff (A B C : ExecModel) (T12 : A.Rep → B.Raw)
    (obs12 : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (T23 : B.Rep → C.Raw) (obs23 : C.Outcome → B.Outcome) :
    noResidueOn (hopSeq A B C T12 obs12 eqA T23 obs23)
        (fun c => A.admissible c = true) ↔
      hopCorrect A B T12 obs12 eqA ∧
      hopCorrect A (seqModel B C T23) T12
        (fun o => obs12 (hopSeqObs obs23 o)) eqA := by
  have key : ∀ c, (hopSeq A B C T12 obs12 eqA T23 obs23).rho c = none ↔
      ((hopModel A B T12 obs12 eqA).admissible c = true ∧
        (hopDirect A B C T12 obs12 eqA T23 obs23).admissible c = true) := by
    intro c
    refine (hop_rho_none_iff_admissible (hopModel A B T12 obs12 eqA) C T23
      (fun o => obs12 (obs23 o)) eqA c).trans ?_
    show (hopSeq A B C T12 obs12 eqA T23 obs23).admissible c = true ↔ _
    rw [hopSeq_admissible]
    exact ⟨bool_and_true, fun h => by rw [h.1, h.2]; rfl⟩
  rw [hopCorrect_iff_exact, hopCorrect_iff_exact]
  constructor
  · intro h
    exact ⟨fun c hc ha => ((key c).mp (h c hc ha)).1,
      fun c hc ha => ((key c).mp (h c hc ha)).2⟩
  · rintro ⟨h1, h2⟩ c hc ha
    exact (key c).mpr ⟨h1 c hc ha, h2 c hc ha⟩

/-- sequential composition, direct form: `A → seq(B, C)` is a correct hop. -/
theorem hop_seq_correct_direct (A B C : ExecModel) (T12 : A.Rep → B.Raw)
    (obs12 : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (T23 : B.Rep → C.Raw) (obs23 : C.Outcome → B.Outcome)
    (eqB : B.Outcome → B.Outcome → Bool)
    (hAB : hopCorrect A B T12 obs12 eqA)
    (hBC : hopCorrect B C T23 obs23 eqB)
    (hqB : quotientFactorization B)
    (heqB : ∀ x y, eqB x y = true → x = y) :
    hopCorrect A (seqModel B C T23) T12
      (fun o => obs12 (hopSeqObs obs23 o)) eqA :=
  ((hopSeq_correct_iff A B C T12 obs12 eqA T23 obs23).mp
    (hop_seq_correct_from A B C T12 obs12 eqA T23 obs23 eqB hAB hBC hqB heqB)).2

/-- the same law on the `hopObsSeq` statements (outcome equality built in). -/
theorem hopObsSeq_comp (A B C : ExecModel) (T12 : A.Rep → B.Raw)
    (obs12 : B.Outcome → A.Outcome) (T23 : B.Rep → C.Raw)
    (obs23 : C.Outcome → B.Outcome)
    (h12 : hopObsSeq A B T12 obs12)
    (h23 : hopObsSeq B C T23 obs23)
    (hqB : quotientFactorization B) :
    hopObsSeq A (seqModel B C T23) T12 (fun o => obs12 (hopSeqObs obs23 o)) := by
  intro c hc ha
  obtain ⟨repA, hsA, haB, hv12⟩ := h12 c hc ha
  obtain ⟨repB, hsB, haC, hv23⟩ := h23 _ ⟨T12 repA, rfl⟩ haB
  have hv12' : obs12 (B.evalRaw (T12 repA)) = A.evalClass c := by
    simpa [seqModel, seqEvalOf, hsA, hopSeqObs] using hv12
  have hv23' : obs23 (C.evalRaw (T23 repB)) = B.evalClass (B.q (T12 repA)) := by
    simpa [seqModel, seqEvalOf, hsB, hopSeqObs] using hv23
  refine ⟨repA, hsA, ?_, ?_⟩
  · simp [seqModel, seqAdmOf, haB, hsB, haC]
  · have e : (seqModel A (seqModel B C T23) T12).evalClass c =
        (SeqOutcome.stage2 (SeqOutcome.stage2 (C.evalRaw (T23 repB)) :
          SeqOutcome B.Outcome C.Outcome) : SeqOutcome A.Outcome _) := by
      simp [seqModel, seqEvalOf, hsA, hsB]
    rw [e]
    show obs12 (obs23 (C.evalRaw (T23 repB))) = A.evalClass c
    rw [hv23', ← hqB (T12 repA), hv12']

/-- three hops, right-nested target: the shape of a three-layer chain. -/
theorem hopObsSeq_chain3 (A B C D : ExecModel) (T1 : A.Rep → B.Raw)
    (o1 : B.Outcome → A.Outcome) (T2 : B.Rep → C.Raw)
    (o2 : C.Outcome → B.Outcome) (T3 : C.Rep → D.Raw)
    (o3 : D.Outcome → C.Outcome)
    (h1 : hopObsSeq A B T1 o1)
    (h2 : hopObsSeq B C T2 o2)
    (h3 : hopObsSeq C D T3 o3)
    (hqB : quotientFactorization B)
    (hqC : quotientFactorization C) :
    hopObsSeq A (seqModel B (seqModel C D T3) T2) T1
      (fun o => o1 (hopSeqObs (fun o' => o2 (hopSeqObs o3 o')) o)) :=
  hopObsSeq_comp A B (seqModel C D T3) T1 o1 T2
    (fun o' => o2 (hopSeqObs o3 o')) h1
    (hopObsSeq_comp B C D T2 o2 T3 o3 h2 h3 hqC) hqB

/-! ## 2. Sums -/

section SumHop
variable {ι : Type} (F G : ι → ExecModel)

def sumT (T : ∀ i, (F i).Rep → (G i).Raw) : (Σ i, (F i).Rep) → (Σ i, (G i).Raw) :=
  fun r => ⟨r.1, T r.1 r.2⟩

def sumObs (obs : ∀ i, (G i).Outcome → (F i).Outcome) :
    (Σ i, (G i).Outcome) → (Σ i, (F i).Outcome) :=
  fun o => ⟨o.1, obs o.1 o.2⟩

/-- the component equality a sum equality induces on one tag. -/
def sumEqAt (eqS : (Σ i, (F i).Outcome) → (Σ i, (F i).Outcome) → Bool) (i : ι) :
    (F i).Outcome → (F i).Outcome → Bool :=
  fun x y => eqS ⟨i, x⟩ ⟨i, y⟩

theorem hop_sum_admissible (T : ∀ i, (F i).Rep → (G i).Raw)
    (obs : ∀ i, (G i).Outcome → (F i).Outcome)
    (eqS : (Σ i, (F i).Outcome) → (Σ i, (F i).Outcome) → Bool)
    (i : ι) (c : (F i).Class) :
    (hopModel (sumModel F) (sumModel G) (sumT F G T) (sumObs F G obs) eqS).admissible
        ⟨i, c⟩ =
      (hopModel (F i) (G i) (T i) (obs i) (sumEqAt F eqS i)).admissible c := by
  cases hs : (F i).sigma c with
  | none => simp [hopModel, sumModel, hs]
  | some rep => simp [hopModel, sumModel, sumT, sumObs, sumEqAt, hs]

/-- a hop on a sum of entry layers is correct iff every component hop is. -/
theorem hop_sum_correct_iff (T : ∀ i, (F i).Rep → (G i).Raw)
    (obs : ∀ i, (G i).Outcome → (F i).Outcome)
    (eqS : (Σ i, (F i).Outcome) → (Σ i, (F i).Outcome) → Bool) :
    hopCorrect (sumModel F) (sumModel G) (sumT F G T) (sumObs F G obs) eqS ↔
      ∀ i, hopCorrect (F i) (G i) (T i) (obs i) (sumEqAt F eqS i) := by
  simp only [hopCorrect_iff_exact]
  constructor
  · intro h i c hc ha
    have := h ⟨i, c⟩ ((sum_active_iff F i c).mpr hc) ha
    rwa [hop_sum_admissible] at this
  · rintro h ⟨i, c⟩ hc ha
    rw [hop_sum_admissible]
    exact h i c ((sum_active_iff F i c).mp hc) ha

end SumHop

/-- several entry layers into one target `C` (tagged by entry). -/
theorem hop_sum_one_target {ι : Type} (F : ι → ExecModel) (C : ExecModel)
    (T : ∀ i, (F i).Rep → C.Raw) (obs : ∀ i, C.Outcome → (F i).Outcome)
    (eqS : (Σ i, (F i).Outcome) → (Σ i, (F i).Outcome) → Bool) :
    hopCorrect (sumModel F) (sumModel fun _ : ι => C)
        (sumT F (fun _ => C) T) (sumObs F (fun _ => C) obs) eqS ↔
      ∀ i, hopCorrect (F i) C (T i) (obs i) (sumEqAt F eqS i) :=
  hop_sum_correct_iff F (fun _ => C) T obs eqS

/-! ## 2. Products -/

def prodT {P1 P2 R1 R2 : Type} (T1 : P1 → R1) (T2 : P2 → R2) :
    ProdRep P1 P2 → R1 × R2
  | .both r1 r2 => (T1 r1, T2 r2)

def prodObs {O1 O2 O1' O2' : Type} (obs1 : O1 → O1') (obs2 : O2 → O2') :
    ProdOutcome O1 O2 → ProdOutcome O1' O2'
  | .both o1 o2 => .both (obs1 o1) (obs2 o2)

def prodEq {O1 O2 : Type} (eq1 : O1 → O1 → Bool) (eq2 : O2 → O2 → Bool) :
    ProdOutcome O1 O2 → ProdOutcome O1 O2 → Bool
  | .both x1 x2, .both y1 y2 => eq1 x1 y1 && eq2 x2 y2

theorem hop_prod_admissible (A1 A2 B1 B2 : ExecModel)
    (T1 : A1.Rep → B1.Raw) (T2 : A2.Rep → B2.Raw)
    (obs1 : B1.Outcome → A1.Outcome) (obs2 : B2.Outcome → A2.Outcome)
    (eq1 : A1.Outcome → A1.Outcome → Bool) (eq2 : A2.Outcome → A2.Outcome → Bool)
    (c1 : A1.Class) (c2 : A2.Class) :
    (hopModel (prodModel A1 A2) (prodModel B1 B2) (prodT T1 T2)
        (prodObs obs1 obs2) (prodEq eq1 eq2)).admissible (c1, c2) =
      ((hopModel A1 B1 T1 obs1 eq1).admissible c1 &&
        (hopModel A2 B2 T2 obs2 eq2).admissible c2) := by
  cases hs1 : A1.sigma c1 <;> cases hs2 : A2.sigma c2 <;>
    simp [hopModel, prodModel, prodSigmaOf, prodT, prodObs, prodEq, hs1, hs2,
      Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

/-- a hop on a product is correct when both component hops are. -/
theorem hop_prod_correct (A1 A2 B1 B2 : ExecModel)
    (T1 : A1.Rep → B1.Raw) (T2 : A2.Rep → B2.Raw)
    (obs1 : B1.Outcome → A1.Outcome) (obs2 : B2.Outcome → A2.Outcome)
    (eq1 : A1.Outcome → A1.Outcome → Bool) (eq2 : A2.Outcome → A2.Outcome → Bool)
    (h1 : hopCorrect A1 B1 T1 obs1 eq1)
    (h2 : hopCorrect A2 B2 T2 obs2 eq2) :
    hopCorrect (prodModel A1 A2) (prodModel B1 B2) (prodT T1 T2)
      (prodObs obs1 obs2) (prodEq eq1 eq2) := by
  rw [hopCorrect_iff_exact] at h1 h2 ⊢
  rintro ⟨c1, c2⟩ hc ha
  obtain ⟨hc1, hc2⟩ := (prod_active_iff A1 A2 c1 c2).mp hc
  obtain ⟨ha1, ha2⟩ :=
    bool_and_true (show (A1.admissible c1 && A2.admissible c2) = true from ha)
  simp [hop_prod_admissible, h1 c1 hc1 ha1, h2 c2 hc2 ha2]

/-- the converse, left component (the right side has an admissible class). -/
theorem hop_prod_correct_left (A1 A2 B1 B2 : ExecModel)
    (T1 : A1.Rep → B1.Raw) (T2 : A2.Rep → B2.Raw)
    (obs1 : B1.Outcome → A1.Outcome) (obs2 : B2.Outcome → A2.Outcome)
    (eq1 : A1.Outcome → A1.Outcome → Bool) (eq2 : A2.Outcome → A2.Outcome → Bool)
    (w2 : ∃ c2, activeClass A2 c2 ∧ A2.admissible c2 = true)
    (h : hopCorrect (prodModel A1 A2) (prodModel B1 B2) (prodT T1 T2)
      (prodObs obs1 obs2) (prodEq eq1 eq2)) :
    hopCorrect A1 B1 T1 obs1 eq1 := by
  rw [hopCorrect_iff_exact] at h ⊢
  intro c1 hc1 ha1
  obtain ⟨c2, hc2, ha2⟩ := w2
  have := h (c1, c2) ((prod_active_iff A1 A2 c1 c2).mpr ⟨hc1, hc2⟩)
    (by simp [prodModel, ha1, ha2])
  rw [hop_prod_admissible] at this
  exact (bool_and_true this).1

/-- the converse, right component. -/
theorem hop_prod_correct_right (A1 A2 B1 B2 : ExecModel)
    (T1 : A1.Rep → B1.Raw) (T2 : A2.Rep → B2.Raw)
    (obs1 : B1.Outcome → A1.Outcome) (obs2 : B2.Outcome → A2.Outcome)
    (eq1 : A1.Outcome → A1.Outcome → Bool) (eq2 : A2.Outcome → A2.Outcome → Bool)
    (w1 : ∃ c1, activeClass A1 c1 ∧ A1.admissible c1 = true)
    (h : hopCorrect (prodModel A1 A2) (prodModel B1 B2) (prodT T1 T2)
      (prodObs obs1 obs2) (prodEq eq1 eq2)) :
    hopCorrect A2 B2 T2 obs2 eq2 := by
  rw [hopCorrect_iff_exact] at h ⊢
  intro c2 hc2 ha2
  obtain ⟨c1, hc1, ha1⟩ := w1
  have := h (c1, c2) ((prod_active_iff A1 A2 c1 c2).mpr ⟨hc1, hc2⟩)
    (by simp [prodModel, ha1, ha2])
  rw [hop_prod_admissible] at this
  exact (bool_and_true this).2

/-! ## 5. Clocks and the resource residue -/

/-- a clock-indexed layer: carriers, quotient, admission, residue and
    representative are fixed; evaluation is indexed by `k : K`. -/
structure Fam (K : Type) where
  Raw : Type
  Class : Type
  Rep : Type
  Residue : Type
  Outcome : Type
  q : Raw → Class
  runRaw : K → Raw → Outcome
  runClass : K → Class → Outcome
  admissible : Class → Bool
  rho : Class → Option Residue
  sigma : Class → Option Rep

abbrev Clocked := Fam Nat

namespace Fam

/-- the layer at one clock. -/
def model {K : Type} (L : Fam K) (k : K) : ExecModel where
  Raw := L.Raw
  Class := L.Class
  Rep := L.Rep
  Residue := L.Residue
  Outcome := L.Outcome
  q := L.q
  evalRaw := L.runRaw k
  evalClass := L.runClass k
  admissible := L.admissible
  rho := L.rho
  sigma := L.sigma

def active {K : Type} (L : Fam K) (c : L.Class) : Prop := ∃ r, L.q r = c

/-- quotient factorization at every clock. -/
def qf {K : Type} (L : Fam K) : Prop := ∀ k r, L.runRaw k r = L.runClass k (L.q r)

theorem qf_iff {K : Type} (L : Fam K) :
    L.qf ↔ ∀ k, quotientFactorization (L.model k) := Iff.rfl

/-- a clock-free layer. -/
def const {K : Type} (M : ExecModel) : Fam K where
  Raw := M.Raw
  Class := M.Class
  Rep := M.Rep
  Residue := M.Residue
  Outcome := M.Outcome
  q := M.q
  runRaw := fun _ => M.evalRaw
  runClass := fun _ => M.evalClass
  admissible := M.admissible
  rho := M.rho
  sigma := M.sigma

/-- a layer given as one model plus its clock-indexed evaluators (a clock
    such as `fuel` or `steps` changes only `evalRaw`/`evalClass`). -/
def ofFamily {K : Type} (M0 : ExecModel) (run : K → M0.Raw → M0.Outcome)
    (runC : K → M0.Class → M0.Outcome) : Fam K where
  Raw := M0.Raw
  Class := M0.Class
  Rep := M0.Rep
  Residue := M0.Residue
  Outcome := M0.Outcome
  q := M0.q
  runRaw := run
  runClass := runC
  admissible := M0.admissible
  rho := M0.rho
  sigma := M0.sigma

/-- one input of an input-and-clock-indexed layer. -/
def input {I K : Type} (L : Fam (I × K)) (x : I) : Fam K where
  Raw := L.Raw
  Class := L.Class
  Rep := L.Rep
  Residue := L.Residue
  Outcome := L.Outcome
  q := L.q
  runRaw := fun k => L.runRaw (x, k)
  runClass := fun k => L.runClass (x, k)
  admissible := L.admissible
  rho := L.rho
  sigma := L.sigma

end Fam

/-- the residue of a clocked hop: a hop residue, or the target stopped by a
    resource limit (CakeML's "resource limit hit"), carrying its outcome. -/
inductive ClockResidue (O_A O_B R_B : Type) where
  | hop (r : HopResidue O_A O_B R_B)
  | resourceLimit (b : O_B)

def reclass {O_A O_B R_B : Type} (lim : O_B → Bool) :
    HopResidue O_A O_B R_B → ClockResidue O_A O_B R_B
  | .translationRefused => .hop .translationRefused
  | .targetRefused r => .hop (.targetRefused r)
  | .valueMismatch a b =>
      if lim b then .resourceLimit b else .hop (.valueMismatch a b)

/-- the hop at a clock pair: `hopModel` with mismatches on a resource-limit
    target outcome renamed to the resource residue. -/
def clockHopModel {KA KB : Type} (A : Fam KA) (B : Fam KB) (T : A.Rep → B.Raw)
    (obs : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (lim : B.Outcome → Bool) (kA : KA) (kB : KB) : ExecModel where
  Raw := A.Raw
  Class := A.Class
  Rep := B.Rep
  Residue := ClockResidue A.Outcome B.Outcome B.Residue
  Outcome := A.Outcome
  q := A.q
  evalRaw := A.runRaw kA
  evalClass := A.runClass kA
  admissible := (hopModel (A.model kA) (B.model kB) T obs eqA).admissible
  rho := fun c => ((hopModel (A.model kA) (B.model kB) T obs eqA).rho c).map (reclass lim)
  sigma := (hopModel (A.model kA) (B.model kB) T obs eqA).sigma

theorem clockHopModel_profile {KA KB : Type} (A : Fam KA) (B : Fam KB)
    (T : A.Rep → B.Raw) (obs : B.Outcome → A.Outcome)
    (eqA : A.Outcome → A.Outcome → Bool) (lim : B.Outcome → Bool) (kA : KA) (kB : KB)
    (hA : hasMSTNFProfile (A.model kA)) (hB : hasMSTNFProfile (B.model kB)) :
    hasMSTNFProfile (clockHopModel A B T obs eqA lim kA kB) := by
  have h := hopModel_profile (A.model kA) (B.model kB) T obs eqA hA hB
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  intro c hc ha hn
  apply h.2.2.1 c hc ha
  cases hr : (hopModel (A.model kA) (B.model kB) T obs eqA).rho c with
  | none => rfl
  | some r =>
      have : (clockHopModel A B T obs eqA lim kA kB).rho c = some (reclass lim r) := by
        simp [clockHopModel, hr]
      rw [this] at hn
      cases hn

/-- no residue, or only the resource residue. -/
def resourceOk {O_A O_B R_B : Type} : Option (ClockResidue O_A O_B R_B) → Prop
  | none => True
  | some (.hop _) => False
  | some (.resourceLimit _) => True

theorem clock_resourceOk_iff {KA KB : Type} (A : Fam KA) (B : Fam KB)
    (T : A.Rep → B.Raw) (obs : B.Outcome → A.Outcome)
    (eqA : A.Outcome → A.Outcome → Bool) (lim : B.Outcome → Bool)
    (kA : KA) (kB : KB) (c : A.Class) :
    resourceOk ((clockHopModel A B T obs eqA lim kA kB).rho c) ↔
      ∃ rep, A.sigma c = some rep ∧ B.admissible (B.q (T rep)) = true ∧
        (eqA (obs (B.runRaw kB (T rep))) (A.runClass kA c) = true ∨
          lim (B.runRaw kB (T rep)) = true) := by
  cases hs : A.sigma c with
  | none => simp [clockHopModel, hopModel, Fam.model, hs, resourceOk, reclass]
  | some rep =>
      cases ha : B.admissible (B.q (T rep)) <;>
      cases he : eqA (obs (B.runRaw kB (T rep))) (A.runClass kA c) <;>
      cases hl : lim (B.runRaw kB (T rep)) <;>
      simp [clockHopModel, hopModel, Fam.model, hs, ha, he, hl, resourceOk, reclass]

/-- CakeML's per-phase statement, MST-NF reading: on the classes satisfying
    `P`, for every source clock some target clock leaves no residue but the
    resource residue. -/
def clockCorrectOn {KA KB : Type} (A : Fam KA) (B : Fam KB) (T : A.Rep → B.Raw)
    (obs : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (lim : B.Outcome → Bool) (P : A.Class → Prop) : Prop :=
  ∀ c, A.active c → P c → ∀ kA, ∃ kB,
    resourceOk ((clockHopModel A B T obs eqA lim kA kB).rho c)

def clockHopCorrect {KA KB : Type} (A : Fam KA) (B : Fam KB) (T : A.Rep → B.Raw)
    (obs : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (lim : B.Outcome → Bool) : Prop :=
  clockCorrectOn A B T obs eqA lim (fun c => A.admissible c = true)

/-- the structural part of a hop as a layer: A's evaluation, B's
    representative, admission = translated and B-admitted. -/
def transSigma {KA KB : Type} (A : Fam KA) (B : Fam KB) (T : A.Rep → B.Raw)
    (c : A.Class) : Option B.Rep :=
  match A.sigma c with
  | none => none
  | some rep => if B.admissible (B.q (T rep)) then B.sigma (B.q (T rep)) else none

def transFam {KA KB : Type} (A : Fam KA) (B : Fam KB) (T : A.Rep → B.Raw) : Fam KA where
  Raw := A.Raw
  Class := A.Class
  Rep := B.Rep
  Residue := HopResidue A.Outcome B.Outcome B.Residue
  Outcome := A.Outcome
  q := A.q
  runRaw := A.runRaw
  runClass := A.runClass
  admissible := fun c => match A.sigma c with
    | none => false
    | some rep => B.admissible (B.q (T rep))
  rho := fun c => match A.sigma c with
    | none => some .translationRefused
    | some rep =>
        if B.admissible (B.q (T rep)) then none
        else some (.targetRefused (B.rho (B.q (T rep))))
  sigma := transSigma A B T

theorem transFam_profile {KA KB : Type} (A : Fam KA) (B : Fam KB)
    (T : A.Rep → B.Raw) (kA : KA) (kB : KB)
    (hA : hasMSTNFProfile (A.model kA)) (hB : hasMSTNFProfile (B.model kB)) :
    hasMSTNFProfile ((transFam A B T).model kA) := by
  refine ⟨fun r => hA.1 r, ?_, ?_, ?_⟩
  · intro c rep hs
    cases hA' : A.sigma c with
    | none => simp [Fam.model, transFam, transSigma, hA'] at hs
    | some r =>
        cases hb : B.admissible (B.q (T r)) <;>
          simp [Fam.model, transFam, transSigma, hA', hb] at hs ⊢
  · intro c _ ha
    cases hA' : A.sigma c with
    | none => simp [Fam.model, transFam, hA']
    | some r =>
        cases hb : B.admissible (B.q (T r)) <;>
          simp [Fam.model, transFam, hA', hb] at ha ⊢
  · intro c _ ha
    cases hA' : A.sigma c with
    | none => simp [Fam.model, transFam, hA'] at ha
    | some r =>
        cases hb : B.admissible (B.q (T r)) with
        | false => simp [Fam.model, transFam, hA', hb] at ha
        | true =>
            have hp := hB.2.2.2 (B.q (T r)) ⟨T r, rfl⟩ hb
            simp [Fam.model, transFam, transSigma, hA', hb]
            exact hp

/-- the resource outcomes of the composite: C's own, and those C reports
    back as B's. -/
def clockSeqLim {OB OC : Type} (obs23 : OC → OB) (limB : OB → Bool)
    (limC : OC → Bool) : OC → Bool :=
  fun o => limC o || limB (obs23 o)

/-- sequential composition of clocked hops (CakeML's phase composition):
    for every A clock a C clock, with the resource residue of C or of B. -/
theorem clock_hop_seq_correct {KA KB KC : Type} (A : Fam KA) (B : Fam KB) (C : Fam KC)
    (T12 : A.Rep → B.Raw) (obs12 : B.Outcome → A.Outcome)
    (eqA : A.Outcome → A.Outcome → Bool) (limB : B.Outcome → Bool)
    (T23 : B.Rep → C.Raw) (obs23 : C.Outcome → B.Outcome)
    (eqB : B.Outcome → B.Outcome → Bool) (limC : C.Outcome → Bool)
    (P : A.Class → Prop)
    (hAB : clockCorrectOn A B T12 obs12 eqA limB P)
    (hBC : clockHopCorrect B C T23 obs23 eqB limC)
    (hqB : B.qf)
    (heqB : ∀ x y, eqB x y = true → x = y) :
    clockCorrectOn (transFam A B T12) C T23 (fun o => obs12 (obs23 o)) eqA
      (clockSeqLim obs23 limB limC) P := by
  intro c hc hP kA
  obtain ⟨kB, hok1⟩ := hAB c hc hP kA
  obtain ⟨repA, hsA, haB, hv1⟩ :=
    (clock_resourceOk_iff A B T12 obs12 eqA limB kA kB c).mp hok1
  obtain ⟨kC, hok2⟩ := hBC (B.q (T12 repA)) ⟨T12 repA, rfl⟩ haB kB
  obtain ⟨repB, hsB, haC, hv2⟩ :=
    (clock_resourceOk_iff B C T23 obs23 eqB limC kB kC _).mp hok2
  refine ⟨kC, (clock_resourceOk_iff (transFam A B T12) C T23
    (fun o => obs12 (obs23 o)) eqA (clockSeqLim obs23 limB limC) kA kC c).mpr
    ⟨repB, ?_, haC, ?_⟩⟩
  · show transSigma A B T12 c = some repB
    simp [transSigma, hsA, haB, hsB]
  · show eqA (obs12 (obs23 (C.runRaw kC (T23 repB)))) (A.runClass kA c) = true ∨
      (limC (C.runRaw kC (T23 repB)) || limB (obs23 (C.runRaw kC (T23 repB)))) = true
    rcases hv2 with he | hl
    · have hv : obs23 (C.runRaw kC (T23 repB)) = B.runRaw kB (T12 repA) :=
        (heqB _ _ he).trans (hqB kB (T12 repA)).symm
      rw [hv]
      rcases hv1 with he1 | hl1
      · exact Or.inl he1
      · exact Or.inr (by rw [hl1]; simp)
    · exact Or.inr (by rw [hl]; simp)

/-- (1) is the clock-free, resource-free instance of (5). -/
theorem clock_const_iff (A B : ExecModel) (T : A.Rep → B.Raw)
    (obs : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool) :
    clockHopCorrect (Fam.const A : Clocked) (Fam.const B : Clocked) T obs eqA
        (fun _ => false) ↔ hopCorrect A B T obs eqA := by
  rw [hopCorrect_iff_exact]
  constructor
  · intro h c hc ha
    obtain ⟨_, hok⟩ := h c hc ha 0
    obtain ⟨rep, hs, hb, hv⟩ := (clock_resourceOk_iff _ _ _ _ _ _ _ _ c).mp hok
    refine (hop_admissible_iff A B T obs eqA c).mpr ⟨rep, hs, hb, ?_⟩
    rcases hv with he | hl
    · exact he
    · simp at hl
  · intro h c hc ha _
    obtain ⟨rep, hs, hb, he⟩ := (hop_admissible_iff A B T obs eqA c).mp (h c hc ha)
    exact ⟨0, (clock_resourceOk_iff _ _ _ _ _ _ _ _ c).mpr ⟨rep, hs, hb, Or.inl he⟩⟩

/-! ## 6. The bootstrap instance -/

/-- the chain's output on a source program: B's representative of the
    translated class, translated again. -/
def chainOut {KA KB KC : Type} (A : Fam KA) (B : Fam KB) (C : Fam KC)
    (T12 : A.Rep → B.Raw) (T23 : B.Rep → C.Raw) (p : A.Raw) : Option C.Raw :=
  (transSigma A B T12 (A.q p)).map T23

theorem transSigma_input {IA IB KA KB : Type} (A : Fam (IA × KA)) (B : Fam (IB × KB))
    (T : A.Rep → B.Raw) (x : IA) (y : IB) (c : A.Class) :
    transSigma (A.input x) (B.input y) T c = transSigma A B T c := by
  cases hs : A.sigma c <;> simp [transSigma, Fam.input, hs]

/-- CakeML's bootstrap shape: per-hop theorems on every admissible input,
    and the fixpoint evidence that `bin` is the chain's image of the
    compiler's source `p`, give: `bin` is admitted, and on every such input,
    for every source clock some target clock gives `p`'s outcome, or a named
    resource stop. -/
theorem bootstrap_instance {IA IB IC KA KB KC : Type}
    (A : Fam (IA × KA)) (B : Fam (IB × KB)) (C : Fam (IC × KC))
    (eAB : IA → IB) (eBC : IB → IC) (P : IA → Prop)
    (T12 : A.Rep → B.Raw) (obs12 : B.Outcome → A.Outcome)
    (eqA : A.Outcome → A.Outcome → Bool) (limB : B.Outcome → Bool)
    (T23 : B.Rep → C.Raw) (obs23 : C.Outcome → B.Outcome)
    (eqB : B.Outcome → B.Outcome → Bool) (limC : C.Outcome → Bool)
    (hAB : ∀ x, P x → clockHopCorrect (A.input x) (B.input (eAB x)) T12 obs12 eqA limB)
    (hBC : ∀ x, P x → clockHopCorrect (B.input (eAB x)) (C.input (eBC (eAB x))) T23 obs23 eqB limC)
    (hqB : B.qf)
    (heqB : ∀ x y, eqB x y = true → x = y)
    (p : A.Raw)
    (hadm : A.admissible (A.q p) = true)
    (bin : C.Raw)
    (hfix : chainOut A B C T12 T23 p = some bin) :
    ∀ x, P x → ∀ kA, ∃ kC, C.admissible (C.q bin) = true ∧
      (eqA (obs12 (obs23 (C.runRaw (eBC (eAB x), kC) bin)))
          (A.runClass (x, kA) (A.q p)) = true ∨
        limC (C.runRaw (eBC (eAB x), kC) bin) = true ∨
        limB (obs23 (C.runRaw (eBC (eAB x), kC) bin)) = true) := by
  intro x hx kA
  have hseq := clock_hop_seq_correct (A.input x) (B.input (eAB x))
    (C.input (eBC (eAB x))) T12 obs12 eqA limB T23 obs23 eqB limC
    (fun c => A.admissible c = true) (hAB x hx) (hBC x hx)
    (fun k r => hqB (eAB x, k) r) heqB
  obtain ⟨kC, hok⟩ := hseq (A.q p) ⟨p, rfl⟩ hadm kA
  obtain ⟨repB, hs, haC, hv⟩ := (clock_resourceOk_iff _ _ _ _ _ _ _ _ _).mp hok
  have hbin : T23 repB = bin := by
    have h' : (transSigma A B T12 (A.q p)).map T23 = some bin := hfix
    have hs' : transSigma A B T12 (A.q p) = some repB :=
      (transSigma_input A B T12 x (eAB x) (A.q p)).symm.trans hs
    rw [hs'] at h'
    simpa using h'
  subst hbin
  refine ⟨kC, haC, ?_⟩
  simp only [clockSeqLim, Bool.or_eq_true] at hv
  exact hv

end NfCompose

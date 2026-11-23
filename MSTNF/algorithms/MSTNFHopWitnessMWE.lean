import MSTNF.algorithms.MSTNFHopComposeMWE

/-!
Necessity of the hypotheses of the hop-composition laws of
`MSTNFHopComposeMWE`.

For each hypothesis of each law there is a model in which every other
hypothesis holds and the conclusion fails (`*_needs_*`): the direct
sequential law (`hAB`, `hBC`, `hqB`, `heqB`), the hop-of-a-hop law (`hBC`,
`hqB`, `heqB`), the `hopObsSeq` law (`h12`, `h23`, `hqB`), the product law
(`h1`, `h2`), the clocked sequential law (`hAB`, `hBC`, `hqB`, `heqB`) and the
bootstrap instance (`hadm`, `hfix`). `clock_lim_minimal` shows the composite
resource predicate `clockSeqLim` cannot be weakened. The witnesses are
finite models on `Unit`, `Bool` and `Nat`.
-/
namespace NfCompose
open MSTNecessityExecModelMWE

namespace HopWitness

def pt (o : Nat) : ExecModel where
  Raw := Unit
  Class := Unit
  Rep := Unit
  Residue := Unit
  Outcome := Nat
  q := fun _ => ()
  evalRaw := fun _ => o
  evalClass := fun _ => o
  admissible := fun _ => true
  rho := fun _ => none
  sigma := fun _ => some ()

theorem pt_profile (o : Nat) : hasMSTNFProfile (pt o) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _; rfl
  · intro _ _ _; rfl
  · intro _ _ h; simp [pt] at h
  · intro _ _ _ h; simp [pt] at h

/-- a point its own admission refuses (a representative is left in). -/
def ptOff (o : Nat) : ExecModel where
  Raw := Unit
  Class := Unit
  Rep := Unit
  Residue := Unit
  Outcome := Nat
  q := fun _ => ()
  evalRaw := fun _ => o
  evalClass := fun _ => o
  admissible := fun _ => false
  rho := fun _ => some ()
  sigma := fun _ => some ()

/-- evaluation does not factor through the class; the other three profile
    laws hold. -/
def badB : ExecModel where
  Raw := Unit
  Class := Unit
  Rep := Unit
  Residue := Unit
  Outcome := Nat
  q := fun _ => ()
  evalRaw := fun _ => 0
  evalClass := fun _ => 1
  admissible := fun _ => true
  rho := fun _ => none
  sigma := fun _ => some ()

theorem badB_other_laws :
    admissibilitySound badB ∧ residueTotality badB ∧ representativePrecision badB := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ _; rfl
  · intro _ _ h; simp [badB] at h
  · intro _ _ _ h; simp [badB] at h

theorem badB_not_qf : ¬ quotientFactorization badB :=
  fun h => absurd (show (0 : Nat) = 1 from h ()) (by decide)

/-- two programs with different outcomes. -/
def ptB : ExecModel where
  Raw := Bool
  Class := Bool
  Rep := Bool
  Residue := Unit
  Outcome := Nat
  q := fun b => b
  evalRaw := fun b => cond b 0 1
  evalClass := fun b => cond b 0 1
  admissible := fun _ => true
  rho := fun _ => none
  sigma := fun b => some b

def u : Unit → Unit := fun _ => ()
def tT : Unit → Bool := fun _ => true
def idN : Nat → Nat := fun o => o
def eqN : Nat → Nat → Bool := Nat.beq
def eqT : Nat → Nat → Bool := fun _ _ => true
def limF : Nat → Bool := fun _ => false
def lim7 : Nat → Bool := fun o => Nat.beq o 7

theorem eqN_sound : ∀ x y, eqN x y = true → x = y :=
  fun _ _ h => Nat.eq_of_beq_eq_true h

theorem eqT_unsound : ¬ ∀ x y, eqT x y = true → x = y :=
  fun h => absurd (h 0 1 rfl) (by decide)

theorem hopCorrect_of_all (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome) (eqA : M_A.Outcome → M_A.Outcome → Bool)
    (h : ∀ c, (hopModel M_A M_B T obs eqA).admissible c = true) :
    hopCorrect M_A M_B T obs eqA :=
  (hopCorrect_iff_exact M_A M_B T obs eqA).mpr fun c _ _ => h c

theorem not_hopCorrect_of (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome) (eqA : M_A.Outcome → M_A.Outcome → Bool)
    (c : M_A.Class) (hc : activeClass M_A c) (ha : M_A.admissible c = true)
    (hn : (hopModel M_A M_B T obs eqA).admissible c = false) :
    ¬ hopCorrect M_A M_B T obs eqA := by
  intro h
  have h' := (hopCorrect_iff_exact M_A M_B T obs eqA).mp h c hc ha
  rw [hn] at h'
  exact Bool.false_ne_true h'

theorem not_hopObsSeq_of (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome) (c : M_A.Class) (hc : activeClass M_A c)
    (ha : M_A.admissible c = true)
    (hn : hopSeqObs obs ((seqModel M_A M_B T).evalClass c) ≠ M_A.evalClass c) :
    ¬ hopObsSeq M_A M_B T obs :=
  fun h => let ⟨_, _, _, hv⟩ := h c hc ha; hn hv

theorem clock_of_all {KA KB : Type} (A : Fam KA) (B : Fam KB) (T : A.Rep → B.Raw)
    (obs : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (lim : B.Outcome → Bool) (P : A.Class → Prop) (kB : KB)
    (h : ∀ c kA, resourceOk ((clockHopModel A B T obs eqA lim kA kB).rho c)) :
    clockCorrectOn A B T obs eqA lim P :=
  fun c _ _ kA => ⟨kB, h c kA⟩

theorem not_clock_of {KA KB : Type} (A : Fam KA) (B : Fam KB) (T : A.Rep → B.Raw)
    (obs : B.Outcome → A.Outcome) (eqA : A.Outcome → A.Outcome → Bool)
    (lim : B.Outcome → Bool) (P : A.Class → Prop) (c : A.Class) (hc : A.active c)
    (hP : P c) (kA : KA)
    (hn : ∀ kB, ¬ resourceOk ((clockHopModel A B T obs eqA lim kA kB).rho c)) :
    ¬ clockCorrectOn A B T obs eqA lim P :=
  fun h => let ⟨kB, hk⟩ := h c hc hP kA; hn kB hk

/-! ### `hop_seq_correct_direct`: hAB, hBC, hqB, heqB -/

theorem direct_needs_hAB :
    hopCorrect (pt 1) (pt 1) u idN eqN ∧ quotientFactorization (pt 1) ∧
    (∀ x y, eqN x y = true → x = y) ∧
    ¬ hopCorrect (pt 0) (seqModel (pt 1) (pt 1) u) u
      (fun o => idN (hopSeqObs idN o)) eqN :=
  ⟨hopCorrect_of_all _ _ _ _ _ fun _ => rfl, (pt_profile 1).1, eqN_sound,
    not_hopCorrect_of _ _ _ _ _ () ⟨(), rfl⟩ rfl rfl⟩

theorem direct_needs_hBC :
    hopCorrect (pt 0) (pt 0) u idN eqN ∧ quotientFactorization (pt 0) ∧
    (∀ x y, eqN x y = true → x = y) ∧
    ¬ hopCorrect (pt 0) (seqModel (pt 0) (pt 1) u) u
      (fun o => idN (hopSeqObs idN o)) eqN :=
  ⟨hopCorrect_of_all _ _ _ _ _ fun _ => rfl, (pt_profile 0).1, eqN_sound,
    not_hopCorrect_of _ _ _ _ _ () ⟨(), rfl⟩ rfl rfl⟩

theorem direct_needs_hqB :
    hopCorrect (pt 0) badB u idN eqN ∧ hopCorrect badB (pt 1) u idN eqN ∧
    (∀ x y, eqN x y = true → x = y) ∧ ¬ quotientFactorization badB ∧
    ¬ hopCorrect (pt 0) (seqModel badB (pt 1) u) u
      (fun o => idN (hopSeqObs idN o)) eqN :=
  ⟨hopCorrect_of_all _ _ _ _ _ fun _ => rfl, hopCorrect_of_all _ _ _ _ _ fun _ => rfl,
    eqN_sound, badB_not_qf, not_hopCorrect_of _ _ _ _ _ () ⟨(), rfl⟩ rfl rfl⟩

theorem direct_needs_heqB :
    hopCorrect (pt 0) (pt 0) u idN eqN ∧ hopCorrect (pt 0) (pt 1) u idN eqT ∧
    quotientFactorization (pt 0) ∧ ¬ (∀ x y, eqT x y = true → x = y) ∧
    ¬ hopCorrect (pt 0) (seqModel (pt 0) (pt 1) u) u
      (fun o => idN (hopSeqObs idN o)) eqN :=
  ⟨hopCorrect_of_all _ _ _ _ _ fun _ => rfl, hopCorrect_of_all _ _ _ _ _ fun _ => rfl,
    (pt_profile 0).1, eqT_unsound, not_hopCorrect_of _ _ _ _ _ () ⟨(), rfl⟩ rfl rfl⟩

/-! ### `hop_seq_correct` (hop of a hop): hBC, hqB, heqB -/

theorem hopHop_needs_hBC :
    quotientFactorization (pt 0) ∧ (∀ x y, eqN x y = true → x = y) ∧
    ¬ hopCorrect (hopModel (pt 0) (pt 0) u idN eqN) (pt 1) u
      (fun o => idN (idN o)) eqN :=
  ⟨(pt_profile 0).1, eqN_sound, not_hopCorrect_of _ _ _ _ _ () ⟨(), rfl⟩ rfl rfl⟩

theorem hopHop_needs_hqB :
    hopCorrect badB (pt 1) u idN eqN ∧ (∀ x y, eqN x y = true → x = y) ∧
    ¬ quotientFactorization badB ∧
    ¬ hopCorrect (hopModel (pt 0) badB u idN eqN) (pt 1) u
      (fun o => idN (idN o)) eqN :=
  ⟨hopCorrect_of_all _ _ _ _ _ fun _ => rfl, eqN_sound, badB_not_qf,
    not_hopCorrect_of _ _ _ _ _ () ⟨(), rfl⟩ rfl rfl⟩

theorem hopHop_needs_heqB :
    hopCorrect (pt 0) (pt 1) u idN eqT ∧ quotientFactorization (pt 0) ∧
    ¬ (∀ x y, eqT x y = true → x = y) ∧
    ¬ hopCorrect (hopModel (pt 0) (pt 0) u idN eqN) (pt 1) u
      (fun o => idN (idN o)) eqN :=
  ⟨hopCorrect_of_all _ _ _ _ _ fun _ => rfl, (pt_profile 0).1, eqT_unsound,
    not_hopCorrect_of _ _ _ _ _ () ⟨(), rfl⟩ rfl rfl⟩

/-! ### `hopObsSeq_comp`: h12, h23, hqB -/

theorem obsSeq_needs_h12 :
    hopObsSeq (pt 1) (pt 1) u idN ∧ quotientFactorization (pt 1) ∧
    ¬ hopObsSeq (pt 0) (seqModel (pt 1) (pt 1) u) u (fun o => idN (hopSeqObs idN o)) :=
  ⟨fun _ _ _ => ⟨(), rfl, rfl, rfl⟩, (pt_profile 1).1,
    not_hopObsSeq_of _ _ _ _ () ⟨(), rfl⟩ rfl
      (fun h => absurd (show (1 : Nat) = 0 from h) (by decide))⟩

theorem obsSeq_needs_h23 :
    hopObsSeq (pt 0) (pt 0) u idN ∧ quotientFactorization (pt 0) ∧
    ¬ hopObsSeq (pt 0) (seqModel (pt 0) (pt 1) u) u (fun o => idN (hopSeqObs idN o)) :=
  ⟨fun _ _ _ => ⟨(), rfl, rfl, rfl⟩, (pt_profile 0).1,
    not_hopObsSeq_of _ _ _ _ () ⟨(), rfl⟩ rfl
      (fun h => absurd (show (1 : Nat) = 0 from h) (by decide))⟩

theorem obsSeq_needs_hqB :
    hopObsSeq (pt 0) badB u idN ∧ hopObsSeq badB (pt 1) u idN ∧
    ¬ quotientFactorization badB ∧
    ¬ hopObsSeq (pt 0) (seqModel badB (pt 1) u) u (fun o => idN (hopSeqObs idN o)) :=
  ⟨fun _ _ _ => ⟨(), rfl, rfl, rfl⟩, fun _ _ _ => ⟨(), rfl, rfl, rfl⟩, badB_not_qf,
    not_hopObsSeq_of _ _ _ _ () ⟨(), rfl⟩ rfl
      (fun h => absurd (show (1 : Nat) = 0 from h) (by decide))⟩

/-! ### `hop_prod_correct`: h1, h2 -/

theorem prod_needs_h1 :
    hopCorrect (pt 0) (pt 0) u idN eqN ∧
    ¬ hopCorrect (prodModel (pt 0) (pt 0)) (prodModel (pt 1) (pt 0)) (prodT u u)
      (prodObs idN idN) (prodEq eqN eqN) :=
  ⟨hopCorrect_of_all _ _ _ _ _ fun _ => rfl,
    not_hopCorrect_of _ _ _ _ _ ((), ()) ⟨((), ()), rfl⟩ rfl rfl⟩

theorem prod_needs_h2 :
    hopCorrect (pt 0) (pt 0) u idN eqN ∧
    ¬ hopCorrect (prodModel (pt 0) (pt 0)) (prodModel (pt 0) (pt 1)) (prodT u u)
      (prodObs idN idN) (prodEq eqN eqN) :=
  ⟨hopCorrect_of_all _ _ _ _ _ fun _ => rfl,
    not_hopCorrect_of _ _ _ _ _ ((), ()) ⟨((), ()), rfl⟩ rfl rfl⟩

/-! ### `clock_hop_seq_correct`: hAB, hBC, hqB, heqB; and the resource set -/

def cpt (o : Nat) : Clocked := Fam.const (pt o)
def cbadB : Clocked := Fam.const badB

theorem cpt_qf (o : Nat) : (cpt o).qf := by
  intro _ _; rfl

theorem cbadB_not_qf : ¬ cbadB.qf :=
  fun h => absurd (show (0 : Nat) = 1 from h 0 ()) (by decide)

theorem clock_needs_hAB :
    clockHopCorrect (cpt 1) (cpt 1) u idN eqN limF ∧ (cpt 1).qf ∧
    (∀ x y, eqN x y = true → x = y) ∧
    ¬ clockCorrectOn (transFam (cpt 0) (cpt 1) u) (cpt 1) u (fun o => idN (idN o)) eqN
      (clockSeqLim idN limF limF) (fun c => (cpt 0).admissible c = true) :=
  ⟨clock_of_all _ _ _ _ _ _ _ 0 fun _ _ => trivial, cpt_qf 1, eqN_sound,
    not_clock_of _ _ _ _ _ _ _ () ⟨(), rfl⟩ rfl 0 fun _ h => h⟩

theorem clock_needs_hBC :
    clockHopCorrect (cpt 0) (cpt 0) u idN eqN limF ∧ (cpt 0).qf ∧
    (∀ x y, eqN x y = true → x = y) ∧
    ¬ clockCorrectOn (transFam (cpt 0) (cpt 0) u) (cpt 1) u (fun o => idN (idN o)) eqN
      (clockSeqLim idN limF limF) (fun c => (cpt 0).admissible c = true) :=
  ⟨clock_of_all _ _ _ _ _ _ _ 0 fun _ _ => trivial, cpt_qf 0, eqN_sound,
    not_clock_of _ _ _ _ _ _ _ () ⟨(), rfl⟩ rfl 0 fun _ h => h⟩

theorem clock_needs_hqB :
    clockHopCorrect (cpt 0) cbadB u idN eqN limF ∧
    clockHopCorrect cbadB (cpt 1) u idN eqN limF ∧
    (∀ x y, eqN x y = true → x = y) ∧ ¬ cbadB.qf ∧
    ¬ clockCorrectOn (transFam (cpt 0) cbadB u) (cpt 1) u (fun o => idN (idN o)) eqN
      (clockSeqLim idN limF limF) (fun c => (cpt 0).admissible c = true) :=
  ⟨clock_of_all _ _ _ _ _ _ _ 0 fun _ _ => trivial,
    clock_of_all _ _ _ _ _ _ _ 0 fun _ _ => trivial, eqN_sound, cbadB_not_qf,
    not_clock_of _ _ _ _ _ _ _ () ⟨(), rfl⟩ rfl 0 fun _ h => h⟩

theorem clock_needs_heqB :
    clockHopCorrect (cpt 0) (cpt 0) u idN eqN limF ∧
    clockHopCorrect (cpt 0) (cpt 1) u idN eqT limF ∧
    (cpt 0).qf ∧ ¬ (∀ x y, eqT x y = true → x = y) ∧
    ¬ clockCorrectOn (transFam (cpt 0) (cpt 0) u) (cpt 1) u (fun o => idN (idN o)) eqN
      (clockSeqLim idN limF limF) (fun c => (cpt 0).admissible c = true) :=
  ⟨clock_of_all _ _ _ _ _ _ _ 0 fun _ _ => trivial,
    clock_of_all _ _ _ _ _ _ _ 0 fun _ _ => trivial, cpt_qf 0, eqT_unsound,
    not_clock_of _ _ _ _ _ _ _ () ⟨(), rfl⟩ rfl 0 fun _ h => h⟩

/-- the composite's resource set cannot drop B's: B stops by resource,
    C reports it faithfully, and with C's own resource set only the
    composite fails. -/
theorem clock_lim_minimal :
    clockHopCorrect (cpt 0) (cpt 7) u idN eqN lim7 ∧
    clockHopCorrect (cpt 7) (cpt 7) u idN eqN limF ∧ (cpt 7).qf ∧
    clockCorrectOn (transFam (cpt 0) (cpt 7) u) (cpt 7) u (fun o => idN (idN o)) eqN
      (clockSeqLim idN lim7 limF) (fun c => (cpt 0).admissible c = true) ∧
    ¬ clockCorrectOn (transFam (cpt 0) (cpt 7) u) (cpt 7) u (fun o => idN (idN o)) eqN
      limF (fun c => (cpt 0).admissible c = true) := by
  have h1 : clockHopCorrect (cpt 0) (cpt 7) u idN eqN lim7 :=
    clock_of_all _ _ _ _ _ _ _ 0 fun _ _ => trivial
  have h2 : clockHopCorrect (cpt 7) (cpt 7) u idN eqN limF :=
    clock_of_all _ _ _ _ _ _ _ 0 fun _ _ => trivial
  exact ⟨h1, h2, cpt_qf 7,
    clock_hop_seq_correct (cpt 0) (cpt 7) (cpt 7) u idN eqN lim7 u idN eqN limF
      (fun c => (cpt 0).admissible c = true) h1 h2 (cpt_qf 7) eqN_sound,
    not_clock_of _ _ _ _ _ _ _ () ⟨(), rfl⟩ rfl 0 fun _ h => h⟩

/-! ### `bootstrap_instance`: hadm, hfix -/

def bA : Fam (Unit × Nat) := Fam.const (ptOff 0)
def b1 : Fam (Unit × Nat) := Fam.const (pt 1)
def b0 : Fam (Unit × Nat) := Fam.const (pt 0)
def bC : Fam (Unit × Nat) := Fam.const ptB

theorem boot_needs_hadm :
    (∀ x, (fun _ : Unit => True) x →
      clockHopCorrect (bA.input x) (b1.input (u x)) u idN eqN limF) ∧
    (∀ x, (fun _ : Unit => True) x →
      clockHopCorrect (b1.input (u x)) (b1.input (u (u x))) u idN eqN limF) ∧
    b1.qf ∧ (∀ x y, eqN x y = true → x = y) ∧
    chainOut bA b1 b1 u u () = some () ∧
    ¬ bA.admissible (bA.q ()) = true ∧
    ¬ (∀ x, (fun _ : Unit => True) x → ∀ kA, ∃ kC, b1.admissible (b1.q ()) = true ∧
      (eqN (idN (idN (b1.runRaw (u (u x), kC) ()))) (bA.runClass (x, kA) (bA.q ())) = true ∨
        limF (b1.runRaw (u (u x), kC) ()) = true ∨
        limF (idN (b1.runRaw (u (u x), kC) ())) = true)) := by
  refine ⟨?_, ?_, ?_, eqN_sound, rfl, Bool.false_ne_true, ?_⟩
  · intro _ _ _ _ ha _
    exact (Bool.false_ne_true ha).elim
  · intro _ _
    exact clock_of_all _ _ _ _ _ _ _ 0 fun _ _ => trivial
  · intro _ _; rfl
  · intro h
    obtain ⟨kC, _, hk⟩ := h () trivial 0
    rcases hk with hk | hk | hk <;> exact Bool.false_ne_true hk

theorem boot_needs_hfix :
    (∀ x, (fun _ : Unit => True) x →
      clockHopCorrect (b0.input x) (b0.input (u x)) u idN eqN limF) ∧
    (∀ x, (fun _ : Unit => True) x →
      clockHopCorrect (b0.input (u x)) (bC.input (u (u x))) tT idN eqN limF) ∧
    b0.qf ∧ (∀ x y, eqN x y = true → x = y) ∧
    b0.admissible (b0.q ()) = true ∧
    ¬ chainOut b0 b0 bC u tT () = some false ∧
    ¬ (∀ x, (fun _ : Unit => True) x → ∀ kA, ∃ kC, bC.admissible (bC.q false) = true ∧
      (eqN (idN (idN (bC.runRaw (u (u x), kC) false))) (b0.runClass (x, kA) (b0.q ())) = true ∨
        limF (bC.runRaw (u (u x), kC) false) = true ∨
        limF (idN (bC.runRaw (u (u x), kC) false)) = true)) := by
  refine ⟨?_, ?_, ?_, eqN_sound, rfl, ?_, ?_⟩
  · intro _ _
    exact clock_of_all _ _ _ _ _ _ _ 0 fun _ _ => trivial
  · intro _ _
    exact clock_of_all _ _ _ _ _ _ _ 0 fun _ _ => trivial
  · intro _ _; rfl
  · intro h
    have h' : (some true : Option Bool) = some false := h
    cases h'
  · intro h
    obtain ⟨kC, _, hk⟩ := h () trivial 0
    rcases hk with hk | hk | hk <;> exact Bool.false_ne_true hk

end HopWitness

end NfCompose

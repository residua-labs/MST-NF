import MSTNF.algorithms.MSTNFRelationalHopMWE
import MSTNF.algorithms.MSTNFObservationMWE

/-!
Relational hops and the observation order, integrated. Semantic coarsening
works for every information class,
including quotient readings without an executable DecidableEq instance.
-/
namespace NfCompose.Observation
open MSTNecessityExecModelMWE

def Observes (A B : ExecModel) (obs : B.Outcome → A.Outcome)
    (p : Information A.Outcome) : A.Outcome → B.Outcome → Prop :=
  fun a b => agrees p (obs b) a

theorem relHopOn_coarsen (A B : ExecModel) (F : A.Rep → Option B.Raw)
    (obs : B.Outcome → A.Outcome) (p q : Information A.Outcome)
    (P : A.Class → Prop) (hpq : Below p q)
    (h : RelHopOn A B F (Observes A B obs q) P) :
    RelHopOn A B F (Observes A B obs p) P :=
  relHopOn_mono A B F _ _ P (fun a b e => hpq (obs b) a e) h

/-- Compatibility phrased on classes, without a chosen or decidable view. -/
def InfoCompatible {X Y : Type} (obs : Y → X)
    (p : Information X) (q : Information Y) : Prop :=
  ∀ x y, agrees q x y → agrees p (obs x) (obs y)

theorem infoCompatible_classOf {X Y : Type} (obs : Y → X)
    (p : Projection X) (q : Projection Y) :
    InfoCompatible obs (classOf p) (classOf q) ↔ Compatible obs p q := Iff.rfl

/-- Coarsening the requested outer reading or refining the available middle
    reading preserves compatibility, hence preserves composability. -/
theorem infoCompatible_variance {X Y : Type} (obs : Y → X)
    (p p' : Information X) (q q' : Information Y)
    (houter : Below p' p) (hinner : Below q q')
    (h : InfoCompatible obs p q) : InfoCompatible obs p' q' :=
  fun x y e => houter _ _ (h x y (hinner x y e))

theorem infoCompatible_comp {X Y Z : Type} (f : Y → X) (g : Z → Y)
    (p : Information X) (q : Information Y) (r : Information Z)
    (hf : InfoCompatible f p q) (hg : InfoCompatible g q r) :
    InfoCompatible (fun z => f (g z)) p r :=
  fun x y e => hf _ _ (hg x y e)

/-- Compose partial relational arrows at possibly non-decidable observations.
    Compatibility is exactly the permission to substitute the middle reading. -/
theorem relHopOn_observation_seq (A B C : ExecModel)
    (F : A.Rep → Option B.Raw) (G : B.Rep → Option C.Raw)
    (obsAB : B.Outcome → A.Outcome) (obsBC : C.Outcome → B.Outcome)
    (p : Information A.Outcome) (q : Information B.Outcome)
    (P : A.Class → Prop) (hcompat : InfoCompatible obsAB p q)
    (hqB : quotientFactorization B)
    (hAB : RelHopOn A B F (Observes A B obsAB p) P)
    (hBC : RelHopCorrect B C G (Observes B C obsBC q)) :
    RelHopOn A C (partialHopSeq B F G)
      (Observes A C (fun o => obsAB (obsBC o)) p) P :=
  relHopOn_comp A B C F G
    (Observes A B obsAB p) (Observes B C obsBC q)
    (Observes A C (fun o => obsAB (obsBC o)) p) P
    (fun _ _ _ hab hbc => (kernel p).iseqv.trans (hcompat _ _ hbc) hab)
    hqB hAB hBC

/-- Postcomposition can lose distinctions, never create new distinctions.
    The statement is order preservation; no meet-preservation is asserted. -/
theorem postcompose_coarser {O V W : Type} (f : O → V) (g : V → W) :
    Coarser (⟨W, fun o => g (f o)⟩ : Projection O) ⟨V, f⟩ :=
  fun _ _ e => congrArg g e

end NfCompose.Observation

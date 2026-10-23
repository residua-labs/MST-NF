-- Claims check: every entry of evidence/CLAIMS.json must resolve to a theorem in the shipped modules, with the
-- recorded statement hash and axiom set.
--
--   CLAIMS=evidence/CLAIMS.json lake env lean scripts/ClaimsCheck.lean        # check: prints one JSON line per theorem
--   EMIT="Name1,Name2" lake env lean scripts/ClaimsCheck.lean                # emit: statement hash, module, axioms
--
-- The statement hash is `Hfull` of the development's statement-fidelity tool: the hash of the theorem's type `Expr`
-- (universe parameters replaced by position, metadata erased, binder names and binder infos ignored, de Bruijn indices),
-- so it is invariant under renaming of bound variables and of the theorem. The hashing code below is copied from that tool.
import MSTNF.algorithms.MSTMinimalityRoleBasisMWE
import MSTNF.algorithms.MSTNF3Form4FormEquivMWE
import MSTNF.algorithms.MSTNF3FormMWE
import MSTNF.algorithms.MSTNF3FormOmegaForcedProbeMWE
import MSTNF.algorithms.MSTNFAlgorithmClassCoverageMWE
import MSTNF.algorithms.MSTNFCanonicalDecompositionMWE
import MSTNF.algorithms.MSTNFCompletenessRepresentationMWE
import MSTNF.algorithms.MSTNFConcreteAbstractEquivMWE
import MSTNF.algorithms.MSTNFExecutionNoFifthRoleMWE
import MSTNF.algorithms.MSTNFKernelConformanceMWE
import MSTNF.algorithms.MSTNFPartitionCompletenessMWE
import MSTNF.algorithms.MSTNFProfileDichotomyMWE
import MSTNF.algorithms.MSTNFQuotientBeforeExecutionNFMWE
import MSTNF.algorithms.MSTNFResidueAbsorptionWellFoundedMWE
import MSTNF.algorithms.MSTNFResidueTypologyMWE
import MSTNF.algorithms.MSTNFRunNFAbstractMWE
import MSTNF.algorithms.MSTNFStructuralAdvantageMWE
import MSTNF.algorithms.MSTNFT1BridgeClosureMWE
import MSTNF.algorithms.MSTNFVSoundnessConformanceMWE
import MSTNF.algorithms.MSTNecessityExecModelMWE
import MSTNF.algorithms.MSTNecessityRoleAblationMWE
import MSTNF.algorithms.MSTNoFifthRoleIntegrationMWE
import MSTNFDefsPred.MSTNFDefsPredMWE
import MSTNF.core.MSTNFObjectMWE
import MSTNF.core.MSTNFPredBridgeMWE
import MSTNF.l1.MSTGenericResidueSkeletonsMWE
import MSTNF.methodology.GenericResidueExhaustionSchemaMWE
import Lean
open Lean Meta

abbrev H2 := UInt64 × UInt64

def mix2 (h : H2) (x : UInt64) : H2 :=
  let t := (h.2 ^^^ x) * 0xff51afd7ed558ccd
  (mixHash h.1 x, t ^^^ (t >>> 33))

def comb (tag : UInt64) (xs : List H2) : H2 :=
  xs.foldl (fun acc h => mix2 (mix2 acc h.1) h.2) (tag * 0x9e3779b97f4a7c15 + 1, tag + 0x1234567)

def levelH : Level → H2
  | .zero => comb 21 []
  | .succ l => comb 22 [levelH l]
  | .max a b => comb 23 [levelH a, levelH b]
  | .imax a b => comb 24 [levelH a, levelH b]
  | .param n => comb 25 [(n.hash, 0)]
  | .mvar _ => comb 26 []

structure HSt where
  cache : Std.HashMap Expr H2 := {}
  occ : Std.HashMap FVarId Nat := {}
abbrev HM := StateM HSt

partial def hashE (pos : Std.HashMap FVarId Nat) (e : Expr) : HM H2 := do
  if let some h := (← get).cache[e]? then return h
  let h ← match e with
    | .bvar i => pure (comb 1 [((i : Nat).toUInt64, 0)])
    | .fvar id =>
      match pos[id]? with
      | some k => pure (comb 2 [(k.toUInt64, 0)])
      | none =>
        let s ← get
        match s.occ[id]? with
        | some k => pure (comb 3 [(k.toUInt64, 0)])
        | none =>
          let k := s.occ.size
          modify fun s => { s with occ := s.occ.insert id k }
          pure (comb 3 [(k.toUInt64, 0)])
    | .mvar _ => pure (comb 4 [])
    | .sort l => pure (comb 5 [levelH l])
    | .const n ls => pure (comb 6 ((n.hash, 0) :: ls.map levelH))
    | .app f a => do
      let hf ← hashE pos f
      let ha ← hashE pos a
      pure (comb 7 [hf, ha])
    | .lam _ t b _ => do
      let ht ← hashE pos t
      let hb ← hashE pos b
      pure (comb 8 [ht, hb])
    | .forallE _ t b _ => do
      let ht ← hashE pos t
      let hb ← hashE pos b
      pure (comb 9 [ht, hb])
    | .letE _ t v b _ => do
      let ht ← hashE pos t
      let hv ← hashE pos v
      let hb ← hashE pos b
      pure (comb 10 [ht, hv, hb])
    | .lit (.natVal n) => pure (comb 11 [(hash n, 0)])
    | .lit (.strVal s) => pure (comb 12 [(hash s, 0)])
    | .mdata _ b => hashE pos b
    | .proj s i b => do
      let hb ← hashE pos b
      pure (comb 13 [(s.hash, i.toUInt64), hb])
  modify fun s => { s with cache := s.cache.insert e h }
  return h

def hexH (h : H2) : String :=
  let p (x : UInt64) : String :=
    let s := (Nat.toDigits 16 x.toNat).asString
    "".pushn '0' (16 - s.length) ++ s
  p h.1 ++ p h.2

def hashFresh (pos : Std.HashMap FVarId Nat) (e : Expr) : H2 := (hashE pos e |>.run {}).1

def posInst (lps : List Name) (e : Expr) : Expr :=
  e.instantiateLevelParams lps (lps.mapIdx fun i _ => mkLevelParam (Name.mkSimple s!"_u{i}"))


open Lean Meta Elab

def shippedModules : List Name := [`MSTNF.algorithms.MSTMinimalityRoleBasisMWE, `MSTNF.algorithms.MSTNF3Form4FormEquivMWE, `MSTNF.algorithms.MSTNF3FormMWE, `MSTNF.algorithms.MSTNF3FormOmegaForcedProbeMWE, `MSTNF.algorithms.MSTNFAlgorithmClassCoverageMWE, `MSTNF.algorithms.MSTNFCanonicalDecompositionMWE, `MSTNF.algorithms.MSTNFCompletenessRepresentationMWE, `MSTNF.algorithms.MSTNFConcreteAbstractEquivMWE, `MSTNF.algorithms.MSTNFExecutionNoFifthRoleMWE, `MSTNF.algorithms.MSTNFKernelConformanceMWE, `MSTNF.algorithms.MSTNFPartitionCompletenessMWE, `MSTNF.algorithms.MSTNFProfileDichotomyMWE, `MSTNF.algorithms.MSTNFQuotientBeforeExecutionNFMWE, `MSTNF.algorithms.MSTNFResidueAbsorptionWellFoundedMWE, `MSTNF.algorithms.MSTNFResidueTypologyMWE, `MSTNF.algorithms.MSTNFRunNFAbstractMWE, `MSTNF.algorithms.MSTNFStructuralAdvantageMWE, `MSTNF.algorithms.MSTNFT1BridgeClosureMWE, `MSTNF.algorithms.MSTNFVSoundnessConformanceMWE, `MSTNF.algorithms.MSTNecessityExecModelMWE, `MSTNF.algorithms.MSTNecessityRoleAblationMWE, `MSTNF.algorithms.MSTNoFifthRoleIntegrationMWE, `MSTNFDefsPred.MSTNFDefsPredMWE, `MSTNF.core.MSTNFObjectMWE, `MSTNF.core.MSTNFPredBridgeMWE, `MSTNF.l1.MSTGenericResidueSkeletonsMWE, `MSTNF.methodology.GenericResidueExhaustionSchemaMWE]

def axiomsOf (n : Name) : CoreM (List String) := do
  let (_, s) := ((CollectAxioms.collect n).run (← getEnv)).run {}
  return (s.axioms.toList.map toString).toArray.qsort (· < ·) |>.toList

def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => ""

def stmtHash (ci : ConstantInfo) : String :=
  hexH (hashFresh {} (posInst ci.levelParams ci.type))

#eval show CoreM Unit from do
  let env ← getEnv
  let emit := (← IO.getEnv "EMIT").getD ""
  if emit != "" then
    for s in emit.splitOn "," do
      let n := s.toName
      match env.find? n with
      | none => IO.println (Json.mkObj [("name", s), ("found", false)]).compress
      | some ci =>
        let ax ← axiomsOf n
        IO.println (Json.mkObj [("name", s), ("found", true), ("kind", (if ci matches .thmInfo _ then "theorem" else "other")),
          ("module", modOf env n), ("statement_hash", stmtHash ci), ("axioms", toJson ax)]).compress
  else
    let path := (← IO.getEnv "CLAIMS").getD "evidence/CLAIMS.json"
    let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
    let claims := (j.getObjValD "claims").getArr?.toOption.getD #[]
    let mut bad := 0
    let mut total := 0
    for c in claims do
      let cid := (c.getObjValD "id").getStr?.toOption.getD ""
      for t in (c.getObjValD "theorems").getArr?.toOption.getD #[] do
        total := total + 1
        let nm := (t.getObjValD "name").getStr?.toOption.getD ""
        let wantMod := (t.getObjValD "module").getStr?.toOption.getD ""
        let wantHash := (t.getObjValD "statement_hash").getStr?.toOption.getD ""
        let wantAx := ((t.getObjValD "axioms").getArr?.toOption.getD #[]).toList.map (fun x => x.getStr?.toOption.getD "")
        let n := nm.toName
        let mut why : List String := []
        match env.find? n with
        | none => why := why ++ ["not found"]
        | some ci =>
          unless ci matches .thmInfo _ do why := why ++ ["not a theorem"]
          let m := modOf env n
          if m != wantMod then why := why ++ [s!"module {m} != {wantMod}"]
          unless shippedModules.any (fun x => x.toString == m) do why := why ++ ["module not shipped"]
          let h := stmtHash ci
          if h != wantHash then why := why ++ [s!"statement hash {h} != {wantHash}"]
          let ax ← axiomsOf n
          if ax != (wantAx.toArray.qsort (· < ·)).toList then why := why ++ [s!"axioms {ax} != {wantAx}"]
          for a in ax do
            unless ["propext", "Classical.choice", "Quot.sound"].contains a do why := why ++ [s!"axiom {a} not allowed"]
        if !why.isEmpty then bad := bad + 1
        IO.println (Json.mkObj [("claim", cid), ("theorem", nm), ("ok", why.isEmpty), ("why", toJson why)]).compress
    for d in (j.getObjValD "definitions").getArr?.toOption.getD #[] do
      total := total + 1
      let nm := (d.getObjValD "name").getStr?.toOption.getD ""
      let wantMod := (d.getObjValD "module").getStr?.toOption.getD ""
      let wantHash := (d.getObjValD "statement_hash").getStr?.toOption.getD ""
      let n := nm.toName
      let mut why : List String := []
      match env.find? n with
      | none => why := why ++ ["not found"]
      | some ci =>
        unless ci matches .defnInfo _ do why := why ++ ["not a definition"]
        if modOf env n != wantMod then why := why ++ ["module mismatch"]
        if stmtHash ci != wantHash then why := why ++ ["type hash mismatch"]
      if !why.isEmpty then bad := bad + 1
      IO.println (Json.mkObj [("claim", (d.getObjValD "id").getStr?.toOption.getD ""), ("definition", nm), ("ok", why.isEmpty), ("why", toJson why)]).compress
    IO.println (Json.mkObj [("summary", true), ("items_checked", total), ("failures", bad)]).compress

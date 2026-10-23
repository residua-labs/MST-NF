# MST-NF: rationale, results and scope

English · [中文](RATIONALE.zh-CN.md)

The detailed companion to the [README](../README.md): the object, the proved properties, the 3-form question, the Gödel-wall model, related structures, how to instantiate it, and where it came from. Every theorem named here is in this repository; see *Intents* in the README for axioms. Statements that are not theorems (history, research positions, analogies) are marked as such.

**A normal form for systems that decide. In an MST-NF model, every input falls in a class that is either admitted, with a representative, or refused, with a named residue, so no refusal is without a reason (`input_dichotomy`).**

## The four questions

Any system that takes inputs and decides answers four questions, usually without saying so. Examples are a compiler, a package manager, a CI gate, a proof checker, and an agent's action policy.

| | Question | Left implicit, it shows up as |
|---|---|---|
| **q** | When are two inputs the same thing? | wrong caches after a rename, dependency hell, "works on my machine" |
| **a** | What is allowed in? | admission rules scattered across `if` statements that nobody can state in full |
| **σ** | What is the canonical form of an admitted input? | many spellings of one thing; comparison and deduplication break |
| **ρ** | When an input is refused, what exactly is the reason? | inputs dropped or approximated silently; "something went wrong" |

MST-NF makes the four answers explicit as four roles and relates them as shown below.

## The object

In Lean the four roles are fields of one structure, `ExecModel` (`MSTNF/algorithms/MSTNecessityExecModelMWE`), exactly as declared:

```lean
structure ExecModel where
  Raw     : Type
  Class   : Type
  Rep     : Type
  Residue : Type
  Outcome : Type
  q         : Raw → Class
  evalRaw   : Raw → Outcome
  evalClass : Class → Outcome
  admissible : Class → Bool
  rho        : Class → Option Residue
  sigma      : Class → Option Rep
```

(`activeClass c` means some raw input `r` has `q r = c`.) Each role carries one obligation; their conjunction is `hasMSTNFProfile`.

| Role | Obligation (Lean name) | Statement |
|---|---|---|
| q | `quotientFactorization` | `evalRaw r = evalClass (q r)`: what the system does on an input depends only on its class |
| a | `admissibilitySound` | if a class has a representative, it is admissible |
| σ | `representativePrecision` | every active admissible class has a representative (`sigma c ≠ none`) |
| ρ | `residueTotality` | every active non-admissible class has a residue (`rho c ≠ none`) |

The project's mapping from its founding requirement to these obligations (recorded in a bridge note that is not included here) is: `q` ← the functional role "distinguish" (R1); `a` ← "constrain" (R2) and admissibility (Φ2a); `σ` ← "generate" (R3) and element-level precision (Φ2b); `ρ` ← honesty (Φ3) and recursive completeness (Φ5). The Lean files carry the tags R1, R2, Φ2b and Φ5; the mapping is the project's, not something proved here.

What the profile gives, and does not give. For every input, whose class is active: either its class is admissible and has a representative, or it is not admissible, has no representative, and has a residue. `sigma` is a function, so a class has one value, but nothing in the profile says which value; "canonical" is not a property the profile imposes. The profile does **not** say that at most one raw input per class is admitted; that separate safety condition (`AtMostOneAdmit`) is not one of the four roles. And `evalRaw` is only required to factor through classes: the model does not require an input's outcome to be a representative or a refusal, so tying outputs to `σ`/`ρ` is the instance's own obligation.

## Why it is a normal form: the mathematics

In general usage a normal form is a canonical representation; this repository does not claim that notion beyond the theorems listed below. MST-NF has the five properties in the table below, each tied to the listed theorems (`evidence/CLAIMS.json`). The properties are stated over three related models: the decision function `C : E → Option X` (`none` = refused), `ExecModel`, and `CoreObject`. The repository does not give one map between the three.

| Property | What the theorems say | Theorems (module) |
|---|---|---|
| **Completeness** | Every `C` has a faithful (q, a, σ, ρ) decomposition, constructed from `C` (the proofs are `rfl`: `q := C`, `σ := id`). Every input is admitted or rejected, exclusively (`canonicalA (q e) = !ρ e`), and ρ holds on every refused input. Here ρ is a Boolean refusal indicator; typed residues belong to `ExecModel`. | `completeness_theorem`, `canonical_decomposition_faithful`, `residue_totality`, `admitted_rejected_partition` (`MSTNFCompletenessRepresentationMWE`) |
| **Sufficiency** | In FDT form: a candidate role factors through the four-role profile **iff** it has no explicit diagnostic witness, i.e. no two objects with the same profile that it separates. A fifth role therefore cannot be asserted; it has to be exhibited, and an exhibited one is an explicit diagnostic witness (two objects with the same profile that the candidate separates), which is not a residue in the sense of `rho c ≠ none`. This holds inside the admissible role language of the module (its scope sentence). For the core execution language every role is represented (`noIndependentFifth_for_coreProfile`, a closed instance whose four roles are the four constructors and that holds by definition). Together with `completeness_theorem` (every decision function factors through q/a/σ/ρ), this is the sufficiency result. | `roleRepresentation_iff_noDiagnostic`, `noIndependentFifth_iff_noExplicitDiagnosticWitness`, `noIndependentFifth_iff_allRolesRepresented` (generic), `noIndependentFifth_for_coreProfile` (`MSTNFExecutionNoFifthRoleMWE`) |
| **Necessity** | For each role there is an `ExecModel` in which the other three role properties hold and that role's property fails. (In some of the countermodels one of the other three holds because its hypothesis is empty; the statement is the existence of the countermodel.) | `deleting_each_role_breaks_semantics` (`MSTNecessityRoleAblationMWE`) |
| **Minimality** | Two merged roles cannot both be independently diagnosed, so a basis that diagnoses all four independently has at least four role positions. This is minimality of diagnostic capacity, not of an encoding. The theorem's signature carries a `complete B` hypothesis that the proof does not use; the load-bearing hypothesis is independent diagnosability. | `standard_basis_is_minimal_independent_diagnostic_basis`, `fused_roles_lose_independent_diagnostics` (`MSTMinimalityRoleBasisMWE`) |
| **Uniqueness** | Any two kernel-exact decompositions identify the same inputs, and (when onto) are isomorphic. A valid decomposition never merges inputs `C` separates, so the canonical one is the coarsest. Two decision functions agree on every input iff their canonical forms are equal (a function-extensionality statement). | `kernel_exact_unique_up_to_map`, `kernel_exact_iso`, `canonical_is_coarsest`, `agree_iff_same_canonical` (`MSTNFCanonicalDecompositionMWE`) |

`MSTNoFifthRoleIntegrationMWE` covers only *dependent* candidates (entailed by the profile, so they have no deletion countermodel and adding them to the basis changes nothing). It is bookkeeping by unfolding the definition, not an independence result. `minimal_complete_basis` packages completeness; its minimality half is the proposition `True`, a cross-reference, so it is not cited as a proof of minimality.

Two consequences carry the practical weight:
- **Behaviour factors through identity.** For an `ExecModel` satisfying `quotientFactorization`, inputs in the same class get the same outcome (`sameClass_sameOutcome`).
- **Correctness has a closed form.** A `CoreObject` is exact if and only if its soundness residue and its completeness residue are both empty (`exact_iff_empty_residues`; it uses `Classical.choice`).

"Unique" in the table means: any two kernel-exact surjective quotients are isomorphic (`kernel_exact_iso`); whether MST-NF is the unique structure the founding requirement forces is a separate question, listed as open at the end. That the form lets one unfold a system into four parts with one proof shape is the project's practice, not a theorem here; conjunctive normal form in logic plays a similar role (an analogy only).

### "If four is minimal, why can σ and ρ be merged?"

They can be packed into one sum-typed classifier `Lambda : (c : Class) → {r // IsRep c r} ⊕ {e // IsResidue c e}`, the "3-form" `ExecModel3` (`MSTNF3FormMWE`). That does not contradict the minimality result (`standard_basis_is_minimal_independent_diagnostic_basis`), which is about independent diagnostics. The modules establish the following:

1. **Minimality is not "fewest components".** None of the four obligations can be dropped and each can fail while the other three hold (`deleting_each_role_breaks_semantics`); merged roles cannot both be independently diagnosed (`fused_roles_lose_independent_diagnostics`). Packing two roles into one type is a re-encoding, which the theory does not rule out.
2. **In the 3-form, three of the four obligations hold by typing.** `admissibilitySound_derived`, `residueTotality_derived` and `representativePrecision_derived` are case splits on `Lambda`; the 3-form profile `hasMSTNFProfile_3form` is only `quotientFactorization3`. A system that violates those three cannot be written as an `ExecModel3` (`admissibilitySound_derived`, `residueTotality_derived`, `representativePrecision_derived`).
3. **The 3-form and the 4-form are related by a forgetful map and a section.** `toExecModel` forgets the `IsRep`/`IsResidue` witnesses; `fromExecModel` fills them with trivial witnesses and needs the profile, all classes active, and a partition condition. `toExecModel_fromExecModel` (`toExecModel ∘ fromExecModel = id`), `hasMSTNFProfile_iff_3form_section` (under all classes active and `lambdaPartition`, a 4-form has the profile iff it is `toExecModel M3` for some 3-form with its profile) and `fromExecModel_toExecModel_admissible/sigma/rho` (operational round trip, pointwise on the three projections) are proved. The module's comments explain why a strict inverse is not available (several 3-forms differing in `IsRep`/`IsResidue` project to the same 4-form); no theorem states non-injectivity, and an earlier "bijection" wording is withdrawn in the module (`MSTNF3Form4FormEquivMWE`).
4. **The admission tag is forced; the merged classifier is not.** `tag_is_omega_forced` shows that any Boolean classifier with the same true-fibre as `admissible` equals `admissible` (uniqueness of the classifying map of the admission subobject at the Boolean level, by cases). `two_Lambdas_same_tag_distinct_witnesses` gives two `ExecModel3` with the same `admissible` and different `sigma true` (`MSTNF3FormOmegaForcedProbeMWE`). So uniqueness of the tag does not determine the merged classifier.

That the four-role form, keeping acceptance (σ) and refusal (ρ) symmetric and separately checkable, is *the* normal form is a design decision of the theory, supported by points 1–4, not a separate theorem.

## What the Gödel wall model proves

The project's research record separates two levels. At the object level the canonical strata coincide, per that record, with classical structures (an orthogonal factorization system for quotient canonicality, a subobject classifier for admission, a join-semilattice for the choice space). That coincidence is not established for the four-role object by theorems in this repository; here it is reported as the record's claim, and what follows from it is that the object level is regarded as redescription, not new mathematics. Its mechanical validation on a corpus (the record gives q matched on 94 of 105 specifications and σ on 71 of 71, at the tested sizes) checks an independently written Lean belief function against the spec's own gate using `native_decide`, i.e. Lean against the spec, not the spec against a real protocol. The corpus modules are not part of this repository.

At the meta level the record argues that applying MST-NF to its own residue-absorption process cannot reach a terminal basis, because a framework expressive enough to encode its own soundness cannot prove it (Gödel's second incompleteness theorem), so "this framework is sound" is always a residue outside it. What is in this repository is an abstract model of that argument, not Gödel's theorem:

```lean
structure GodelFramework where
  detected : List Nat
  selfSoundnessFiat : Nat
  godel2 : selfSoundnessFiat ∉ detected
```

`godel2` is a field: it is where Gödel's theorem would be applied in a concrete framework; it is not proved here. `godelSuccessor F` adds the fiat to `detected` and picks a fresh number as the next fiat, discharged by arithmetic (`fresh_not_in`). The theorems: `godelStep_no_terminal` (`¬ InBasis godelStep F`: no framework is terminal; the reason is that `godelSuccessor F` is a successor, which is the separate statement `godelStep_has_successor`), `godelStep_flip_not_wellFounded` (`¬ WellFounded (flip godelStep)`; uses `Classical.choice`), `T1_parametric_in_framework` (`∀ F, ¬ ReachesBasis godelStep F`) and `T1_closure` (a conjunction of: every level of an earlier toy ladder has a successor; the concrete facts `42 ∉ [40]`, `49 ∉ [40, 42]`, `52 ∉ [40, 42, 49]`; and `T1_parametric_in_framework`; axioms `propext`, `Quot.sound`). The numbers 40, 42, 49 and 52 label levels of the project's anti-fiat ladder; that every such level is the previous level's self-soundness fiat is an empirical observation recorded in the module, not a theorem. The proofs use no provability predicate or representability hypothesis, so this is a structural model of the regress; justifying `godel2` for a real framework needs the real theorem. The form quantified over every self-application operator needs Reynolds parametricity, which Lean 4 core lacks; it is a named boundary and is not claimed. The case of a framework too weak for Gödel's theorem is modelled by `WeakFramework` with a step relation that is constantly `False` (`weakStep_wellFounded`, `weak_horn_redescriptive_but_nonuniversal`); that a weak framework cannot encode its own self-application is a comment, not a theorem.

## Related structures

No theorem relates MST-NF to the following; these are comparisons in prose, from the project's schema analysis.

**Mazurkiewicz traces.** A trace monoid quotients words by an independence relation, so its classes play the role of `q`, and a representative per class (a normal form such as the lexicographic one) plays the role of `σ`. There is no admission predicate and no residue: the classifier is a total function into representatives. The MST-NF extension in the project's analysis is that the classifier's codomain is a sum, representative or residue, so failure is classified rather than absent. This repository proves nothing about trace congruences or independence relations.

**Abstract interpretation and Galois connections.** In abstract interpretation, the words soundness and completeness refer to an abstraction relative to a concrete semantics, expressed through an abstraction map and a concretisation map forming a Galois connection. In the `CoreObject`, `Sound` is `Fix ⊆ Adm` and `Complete` is `Adm ⊆ Fix` for the set of fixed points of a relation `D`; there is no abstraction map, no concretisation map and no insertion. The two vocabularies overlap in the words, not in a proved correspondence.

**Refinement types.** A refinement type is a base type with a predicate, and an operation is partial on the refined subset. The 3-form's `Sum {r // IsRep c r} {e // IsResidue c e}` uses subtypes in the same way, so the 4-form can look like "refinement type plus partial functions". In the 3-form the classifier is a total function into a sum and does not restrict a domain, which the project's analysis takes as the point of difference. This repository proves nothing relating the construction to any refinement-type system.

## Using it

To model a component as an `ExecModel`:
1. Name its raw inputs, its classes and `q`.
2. Name the admission test, the representative function `sigma` and the residue function `rho` (a closed vocabulary of residues is good practice; the structure does not require it).
3. Discharge the four obligations above.

Then `sameClass_sameOutcome` applies. `exact_iff_empty_residues` is stated for the separate `CoreObject` structure; there is no general map from an `ExecModel` to a `CoreObject` here.

Downstream runtimes that keep a no-Mathlib boundary can vendor `MSTNFDefsPred/` instead of the full theory. It has zero imports, it is the predicate form of the core object, and its faithfulness to the set form is established by the equivalence theorems of `MSTNFPredBridgeMWE` (for exactness, `exact_agrees`).

The table below is illustrative; only the abstract theory is formalized here.

| System | q: same thing | a: allowed in | σ: canonical form | ρ: named refusal |
|---|---|---|---|---|
| compiler | the program's meaning | the supported language fragment | the intermediate representation | unsupported construct, type error |
| package manager | content hash | repository policy | lock file | version conflict, rejected package |
| code merge | patch content | CI and review | merged tree | the specific rule that refused it |
| proof checker | the statement | kernel acceptance | the checked derivation | the specific kernel refusal |
| agent action policy | the requested action | the policy ceiling | the normalised action | the denied permission |

## Where it came from

History from the project's own notes. None of it is a theorem of this repository, and the source repositories are not published. MST-NF was not designed top-down. It started from one requirement, given by the project owner when building a description language for market narratives: the description must be objective, precise and honest; it must be pure reasoning, and statistical correctness, even 99.99%, is not accepted; it must be recursively complete; and whatever lies outside it is explicitly where a human decision begins. The notes extract six founding principles (classification precedes inference; a minimal admissible world; structure is prior to dynamics; canonical selection is unique or absent; residue is a structured measure of deviation; completeness is the termination of residue pressure) and one growth rule:

```
discover a residue → demand a witness → absorb it by a theorem if possible → otherwise expose it and open the minimal new layer
```

They describe the historical derivation as carried out under human guidance, with AI agents as implementers and reviewers (an author-is-not-the-verifier loop with Lean as the evaluator), and fourteen rounds of adversarial review for the paper. The chain they describe ends in a residue-exhaustion normal form with a staged structure and seven structured residues; the four-role formulation proved here is the execution-profile statement of the same line, and it is not claimed to be the direct output of that derivation. The abbreviation MST historically referred to Market Structure Theory, the domain where the mechanism was first studied; MST-NF reads Minimal Structure Theory (Normal Form), the name of the theory.

## For agents

These are research positions, not theorems of this repository. What this repository establishes is the class-level structure of the profile (`input_dichotomy`), which is what makes them checkable.

The project's classification theory distinguishes three cases for a determinate output: **Type 1**, evidence insufficiency (a unique answer exists, the evidence is missing); **Type 2**, structural plurality (several answers are valid, which is not a failure); **Type 3**, unsupported canonicalization (a determinate output where the structure does not warrant one), which is what is called hallucination in language models. The MST-NF obligations constrain the class level: a representative exists only for an admitted class (`admissibilitySound`), and every active class that is not admitted has a named residue (`residueTotality`). They do not by themselves constrain what a system outputs on an input (`evalRaw` only has to factor through classes), and whether the admission test admits only classes that warrant a unique reading is the instance's own obligation, stated as its `a` and checked against its residues. An agent built as an instance can still be wrong; the model gives only that its refusals carry residues (`input_dichotomy`).

On how agents improve, the same research line describes closed-world intelligence as reclassification-driven convergence: improving structure from fixed information by repeatedly reclassifying it under fixed principles until it stabilises; in MST-NF terms, reclassification is residue absorption. This is an operational definition, not a result proved here. The Residua project describes its components as MST-NF instances; that is a statement about Residua and is not checked in this repository.

## What is new, what is not, and what is open

- **Not new:** quotients and soundness/completeness vocabulary have long histories, and the object-level strata coincide, per the project's record, with classical structures; this repository does not claim new mathematics at the object level. The `CoreObject` states that monotonicity, idempotence, totality and fixedness are not assumed, so the object is not presented as a closure operator.
- **Established here:**
  - the four-role `ExecModel` with its obligations, and the statements in the table above, each with its stated scope;
  - the Gödel-wall model: no `GodelFramework` reaches a terminal basis (`T1_parametric_in_framework`), with Gödel's theorem entering as a field;
  - the use of the theory as the generating structure of a working system is the project's claim and is not checked here.
- **Open, and not claimed:**
  - whether a fresh automated run, given only the founding requirements, reproduces the same normal form;
  - whether those requirements are themselves minimal;
  - whether MST-NF is the unique structure satisfying them.

The exact theorem statements, their axioms and their scope are under *Intents*; the non-claims are under *What this does NOT claim*.

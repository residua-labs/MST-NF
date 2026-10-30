# MST-NF: Minimal Structure Theory Normal Form

English · [中文](README.zh-CN.md)

**A normal form for systems that decide. In an MST-NF model, every input falls in a class that is either admitted, with a representative, or refused, with a named residue, so no refusal is without a reason (`input_dichotomy`).**

*MST-NF: Minimal Structure Theory (Normal Form).* Lean 4 (v4.14.0, Mathlib v4.14.0); see *Trust boundary*.

## Why

Every system that takes inputs and decides answers four questions, usually without saying so. This is true of a compiler, a package manager, a CI gate, a proof checker, and an AI agent.

| | Question | When it is left implicit |
|---|---|---|
| **q** | When are two inputs the same thing? | stale caches, dependency hell, "works on my machine" |
| **a** | What is allowed in? | rules scattered across `if` statements that nobody can state in full |
| **σ** | What is the canonical form of an admitted input? | many spellings of one thing; comparison and deduplication break |
| **ρ** | If an input is refused, why exactly? | inputs dropped silently; "something went wrong" |

The worst of these failures is the silent one: a system that produces a confident answer where nothing warrants one. In a language model this is called hallucination. In any system it is a decision that cannot be checked.

MST-NF makes the four answers explicit as four roles. For precise models of a decision system, the following hold:
- **the four roles suffice** to represent any decision function `C : E → Option X` (`completeness_theorem`), and, inside the admissible role language, a candidate fifth role factors through the four-role profile unless an explicit diagnostic witness for it is exhibited (`roleRepresentation_iff_noDiagnostic`);
- **none is redundant**: for each role there is a model where the other three hold and it fails (`deleting_each_role_breaks_semantics`);
- **the decomposition is unique up to isomorphism among kernel-exact surjective quotients** (`kernel_exact_iso`), and coarsest among valid ones (`canonical_is_coarsest`).

So a system modelled this way can be unfolded into the same four parts and checked part by part, which is the project's practice, not a theorem here. For a core object, "is it correct?" has a closed form: it is exact if and only if its two residues are empty (`exact_iff_empty_residues`). Conjunctive normal form plays a similar role in logic (an analogy only).

## Why a normal form, and not a design

MST-NF was not designed top-down. In the project's history it started from one requirement, given by the project owner when building a description language for market narratives (the abbreviation MST historically referred to Market Structure Theory):
- the description must be objective, precise and honest;
- it must be pure reasoning, with no statistical tolerance (even 99.99% is not accepted);
- it must be recursively complete;
- anything outside it must be named as the point where human judgment begins.

The project's notes describe each step of the development as forced because the previous one fell short of that requirement, and the same rule applied every time: find the residue, demand a witness, absorb it by a theorem if possible, and otherwise name it and open the smallest new layer. Bridging the result to other domains showed that it was not specific to markets. The notes describe the historical derivation as carried out under human guidance, with AI agents working as implementers and reviewers; none of this history is a theorem of this repository, and the source repositories are not published.

The four roles correspond, in the project's mapping, to parts of that requirement:
- the quotient `q` and admission `a` correspond to the functional roles "distinguish" and "constrain";
- precision (an admitted input gets a representative) corresponds to `σ`;
- honesty and recursive completeness (a refused input gets a named residue, never silently dropped) correspond to `ρ`.

`σ` and `ρ` can be merged into one "outcome" role as an encoding. What the theory proves is about independent diagnosis: merged roles can no longer both be independently diagnosed (`fused_roles_lose_independent_diagnostics`). Taking the four-role form as the normal form, because it keeps acceptance and refusal symmetric, is a design decision supported by that result, not a separate theorem.

## Why for agents, by agents

**By agents:** AI agents took part in developing and formalising the theory, under human guidance and adversarial review (see above).

**For agents:** a decision is useful to others only if it can be checked. In an MST-NF model, a representative exists only for an admitted class (`representative_only_if_admitted`), and every active class that is not admitted carries a named residue (`input_dichotomy`). Whether an agent's actual outputs are tied to them is the instance's own obligation: the model requires only that outcomes depend on the class (`quotientFactorization`). Used that way, an agent can still be wrong; what the model gives is that every refusal in it carries a residue (`input_dichotomy`).

Two research positions sit next to this and are not theorems of this repository: that insight comes from reclassifying what is already known, which in MST-NF terms is residue absorption; and that, applied to its own process, the theory never closes. For the second there is a formal statement about an abstract model: no `GodelFramework` reaches a terminal basis (`T1_parametric_in_framework`). Gödel's second incompleteness theorem enters only as a field of that structure (`godel2`); it is not re-proved here.

## What is proved, and where to read more

Each statement named above resolves to a Lean 4 theorem in this repository (`evidence/claims_check.txt`); axioms and scope are under *Intents* and *What this does NOT claim*. The full argument, with every theorem named and the questions a skeptic would ask, is in [`docs/RATIONALE.md`](docs/RATIONALE.md).

Three questions about the founding requirement itself remain open, and are not claimed:
- whether an automated run from the requirement alone reproduces the same normal form;
- whether the requirement is minimal;
- whether MST-NF is the only structure it forces.

---

## The theory in one paragraph

MST-NF describes a decision system by four structural roles: a quotient **q**, an admissibility predicate **a**, a representative choice **σ** and a typed residue **ρ**. The Lean development defines the obligations of the four roles (`ExecModel`, `hasMSTNFProfile`) and proves the statements listed under *Intents*: every decision function has a four-part decomposition (`completeness_theorem`); no role is redundant (`deleting_each_role_breaks_semantics`); the roles are minimal as an independent diagnostic basis (`standard_basis_is_minimal_independent_diagnostic_basis`); two kernel-exact surjective quotients are isomorphic (`kernel_exact_iso`); and a core object is exact if and only if its two residues are empty (`exact_iff_empty_residues`). Everything is machine-checked against Lean 4.14.0 and Mathlib v4.14.0; this README states what that does and does not establish, and raw evidence is in [`evidence/`](evidence/).

## What is in the repository

27 modules (counts of theorems and definitions: `evidence/axiom_audit.txt`):

| Directory | Contents |
|---|---|
| `MSTNF/l1/`, `MSTNF/methodology/` | the generic residue skeleton and residue-exhaustion schema (set level) |
| `MSTNF/core/` | the MST-NF core object (set form, `CoreObject`, `Sound/Complete/Exact`) and the **authorization bridge** relating the predicate form to the set form |
| `MSTNFDefsPred/` | the zero-import, Mathlib-free predicate form of the core object (a vendorable projection; its faithfulness is certified by the bridge) |
| `MSTNF/algorithms/` | the execution model and role ablation, the diagnostic-basis modules, the no-fifth-role modules, the canonical decomposition, quotient-before-execution (QBE), partition and residue-typology modules, `runNF`, the per-input dichotomy, the 3-form modules (`MSTNF3Form*`) and the Gödel-wall model (`MSTNFResidueAbsorptionWellFoundedMWE`, `MSTNFT1BridgeClosureMWE`) |
| `MSTNF/algorithms/*Conformance*`, `MSTNFConcreteAbstractEquivMWE` | the Lean side of executed conformance: concrete finite fixtures and bridges between a computable Boolean mirror and the abstract definitions |

Why the conformance modules are here: `MSTNFConcreteAbstractEquivMWE` imports `MSTNFVSoundnessConformanceMWE` and `MSTNFKernelConformanceMWE`. They are included for that reason only. No other conformance module, no CRT/IET seam module, no application and no archived pre-NF module is included, because nothing in the modules above imports them.

Module names follow the directory layout (`MSTNF.algorithms.*`). Lean namespaces are the original ones. The questions a skeptic would ask, with the exact scope of each answer, are in [`docs/RATIONALE.md`](docs/RATIONALE.md).

## Intents

Generated from `evidence/CLAIMS.json`: every row is a claim that resolves to a theorem in this repository, with its statement hash and axioms checked by `scripts/ClaimsCheck.lean`.

| Theorem | Module | Axioms (`#print axioms`) |
|---|---|---|
| `completeness_theorem` — every decision function `C : E → Option X` has a faithful (q, a, σ) decomposition (by construction) | `MSTNF/algorithms/MSTNFCompletenessRepresentationMWE.lean` | none |
| `canonical_decomposition_faithful` — `C e = σ (q e)` for the canonical decomposition (by `rfl`) | `MSTNF/algorithms/MSTNFCompletenessRepresentationMWE.lean` | none |
| `admitted_rejected_partition` — admitted xor rejected: `a (q e) = !ρ e` | `MSTNF/algorithms/MSTNFCompletenessRepresentationMWE.lean` | propext |
| `residue_totality` — `C e = none` implies the refusal indicator ρ holds at `e` | `MSTNF/algorithms/MSTNFCompletenessRepresentationMWE.lean` | propext |
| `roleRepresentation_iff_noDiagnostic` — a candidate role factors through the profile iff it has no explicit diagnostic witness | `MSTNF/algorithms/MSTNFExecutionNoFifthRoleMWE.lean` | Classical.choice, Quot.sound, propext |
| `noIndependentFifth_iff_noExplicitDiagnosticWitness` — no independent fifth role iff no explicit diagnostic witness | `MSTNF/algorithms/MSTNFExecutionNoFifthRoleMWE.lean` | Classical.choice, Quot.sound, propext |
| `noIndependentFifth_iff_allRolesRepresented` — no independent fifth role iff every role is represented | `MSTNF/algorithms/MSTNFExecutionNoFifthRoleMWE.lean` | Classical.choice, Quot.sound, propext |
| `noIndependentFifth_for_coreProfile` — closed instance: the core execution roles are represented (holds by definition) | `MSTNF/algorithms/MSTNFExecutionNoFifthRoleMWE.lean` | none |
| `profileWithFifth_iff_profile` — adding a dependent fifth role does not change the profile | `MSTNF/algorithms/MSTNoFifthRoleIntegrationMWE.lean` | none |
| `no_independent_deletion_countermodel_for_dependent_fifth` — a dependent fifth role has no deletion countermodel | `MSTNF/algorithms/MSTNoFifthRoleIntegrationMWE.lean` | none |
| `extended_basis_complete` — the basis extended by a dependent fifth role is complete | `MSTNF/algorithms/MSTNoFifthRoleIntegrationMWE.lean` | none |
| `execModel_with_all_roles_has_mstnf_profile` — the four role properties give the MST-NF execution profile | `MSTNF/algorithms/MSTNecessityExecModelMWE.lean` | none |
| `deleting_each_role_breaks_semantics` — for each role, a model satisfying the other three and failing it | `MSTNF/algorithms/MSTNecessityRoleAblationMWE.lean` | propext |
| `standard_basis_is_minimal_independent_diagnostic_basis` — a basis diagnosing all four roles independently has at least four role positions | `MSTNF/algorithms/MSTMinimalityRoleBasisMWE.lean` | none |
| `fused_roles_lose_independent_diagnostics` — two merged roles cannot both be independently diagnosed | `MSTNF/algorithms/MSTMinimalityRoleBasisMWE.lean` | none |
| `noninjective_simulation_requires_role_fusion` — a non-injective simulation fuses two roles | `MSTNF/algorithms/MSTMinimalityRoleBasisMWE.lean` | Classical.choice, Quot.sound, propext |
| `kernel_exact_unique_up_to_map` — kernel-exact quotients identify the same inputs | `MSTNF/algorithms/MSTNFCanonicalDecompositionMWE.lean` | propext |
| `kernel_exact_iso` — two kernel-exact surjective quotients are isomorphic | `MSTNF/algorithms/MSTNFCanonicalDecompositionMWE.lean` | Classical.choice |
| `canonical_is_coarsest` — a valid decomposition never merges inputs the function separates | `MSTNF/algorithms/MSTNFCanonicalDecompositionMWE.lean` | none |
| `agree_iff_same_canonical` — functions agree on every input iff their canonical forms are equal | `MSTNF/algorithms/MSTNFCanonicalDecompositionMWE.lean` | Quot.sound |
| `sameClass_sameOutcome` — given `quotientFactorization`, same class implies same outcome | `MSTNF/algorithms/MSTNecessityExecModelMWE.lean` | none |
| `exact_iff_empty_residues` — a core object is exact iff its soundness and completeness residues are empty | `MSTNF/core/MSTNFObjectMWE.lean` | Classical.choice, Quot.sound, propext |
| `exact_agrees` — predicate-form exactness agrees with the set form | `MSTNF/core/MSTNFPredBridgeMWE.lean` | Quot.sound, propext |
| `minimal_complete_basis` — completeness half only; its minimality half is the proposition `True` | `MSTNF/algorithms/MSTNFCompletenessRepresentationMWE.lean` | none |
| `input_dichotomy` — under the profile, each input's class is admitted with a representative, or refused with a residue and no representative | `MSTNF/algorithms/MSTNFProfileDichotomyMWE.lean` | none |
| `representative_only_if_admitted` — under the profile, an input's class has a representative only if it is admitted | `MSTNF/algorithms/MSTNFProfileDichotomyMWE.lean` | none |
| `admissibilitySound_derived` — in the 3-form, `admissibilitySound` holds by typing | `MSTNF/algorithms/MSTNF3FormMWE.lean` | none |
| `residueTotality_derived` — in the 3-form, `residueTotality` holds by typing | `MSTNF/algorithms/MSTNF3FormMWE.lean` | none |
| `representativePrecision_derived` — in the 3-form, `representativePrecision` holds by typing | `MSTNF/algorithms/MSTNF3FormMWE.lean` | none |
| `toExecModel_fromExecModel` — `toExecModel ∘ fromExecModel = id` on profile models (all classes active, λ-partitioned) | `MSTNF/algorithms/MSTNF3Form4FormEquivMWE.lean` | Quot.sound |
| `hasMSTNFProfile_iff_3form_section` — under all classes active and lambdaPartition, a 4-form has the profile iff it is the projection of a 3-form with its profile | `MSTNF/algorithms/MSTNF3Form4FormEquivMWE.lean` | Quot.sound |
| `fromExecModel_toExecModel_admissible` — operational round trip on `admissible` | `MSTNF/algorithms/MSTNF3Form4FormEquivMWE.lean` | none |
| `fromExecModel_toExecModel_sigma` — operational round trip on `sigma` | `MSTNF/algorithms/MSTNF3Form4FormEquivMWE.lean` | none |
| `fromExecModel_toExecModel_rho` — operational round trip on `rho` | `MSTNF/algorithms/MSTNF3Form4FormEquivMWE.lean` | none |
| `tag_is_omega_forced` — a Boolean classifier with the same true-fibre as `admissible` equals `admissible` | `MSTNF/algorithms/MSTNF3FormOmegaForcedProbeMWE.lean` | Quot.sound, propext |
| `two_Lambdas_same_tag_distinct_witnesses` — two 3-forms with the same `admissible` and different `sigma true` | `MSTNF/algorithms/MSTNF3FormOmegaForcedProbeMWE.lean` | Quot.sound |
| `godelStep_no_terminal` — no `GodelFramework` is terminal (`¬ InBasis godelStep F`) | `MSTNF/algorithms/MSTNFResidueAbsorptionWellFoundedMWE.lean` | Quot.sound, propext |
| `godelStep_flip_not_wellFounded` — the successor relation is not well-founded | `MSTNF/algorithms/MSTNFResidueAbsorptionWellFoundedMWE.lean` | Quot.sound, propext |
| `T1_parametric_in_framework` — no `GodelFramework` reaches a terminal basis | `MSTNF/algorithms/MSTNFT1BridgeClosureMWE.lean` | Quot.sound, propext |
| `T1_closure` — conjunction of the Gödel-wall facts for the model | `MSTNF/algorithms/MSTNFT1BridgeClosureMWE.lean` | Quot.sound, propext |
| `antiFiatChain_each_detects_prior_fiat` — the next level's fiat is not in the previous level's detected list (decide on concrete data) | `MSTNF/algorithms/MSTNFT1BridgeClosureMWE.lean` | Quot.sound, propext |
| `weakStep_wellFounded` — the weak-framework step relation is well-founded (it is constantly false) | `MSTNF/algorithms/MSTNFResidueAbsorptionWellFoundedMWE.lean` | none |
| `weak_horn_redescriptive_but_nonuniversal` — for the constantly-False step relation: all residues represented and the flipped step is well-founded (non-universality is a comment, not a theorem) | `MSTNF/algorithms/MSTNFResidueAbsorptionWellFoundedMWE.lean` | none |
| `mstnf_backend_le_classic` — QBE counting bound: attempts after quotienting ≤ attempts without | `MSTNF/algorithms/MSTNFQuotientBeforeExecutionNFMWE.lean` | propext |
| `v_concrete_eq_abstract_on_all_fixtures` — V bridge: concrete mirror equals abstract definition on all fixtures | `MSTNF/algorithms/MSTNFConcreteAbstractEquivMWE.lean` | none |
| `core_concrete_eq_abstract_on_all_fixtures` — core bridge on all fixtures | `MSTNF/algorithms/MSTNFConcreteAbstractEquivMWE.lean` | none |
| `residue_concrete_eq_abstract_on_all_fixtures` — residue bridge on all fixtures | `MSTNF/algorithms/MSTNFConcreteAbstractEquivMWE.lean` | none |

Source: `evidence/intent_axioms.txt` (`lake env lean scripts/PrintAxioms.lean`) and `evidence/claims_check.txt`.

## Trust boundary

* **Toolchain:** `leanprover/lean4:v4.14.0` and Mathlib `v4.14.0` (rev `4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84`, pinned in `lake-manifest.json`). `MSTNFDefsPred` imports nothing.
* **Axiom profile** (`scripts/AxiomAudit.lean` over all 526 theorems, `evidence/axiom_audit.txt`): no user `axiom` declaration, no `sorry`, no `native_decide` (`Lean.ofReduceBool`); 404 theorems use no axiom, 63 use `propext`, 33 use `propext` and `Quot.sound`, 7 use `Quot.sound`, and **19 use `Classical.choice`** (16 with `propext` and `Quot.sound`, 2 alone, 1 with `Quot.sound`) (`evidence/axiom_audit.txt`).
* **`native_decide`:** none in this repository. The development source of `MSTNFConcreteAbstractEquivMWE` originally used `native_decide` for three bridge theorems; the development repository now uses `decide`, so the kernel checks them, statements unchanged (`evidence/native_decide.txt`).
* **Kernel re-checks** (`evidence/`):
  * `lean4checker` (tag `v4.14.0`, commit `bee437b`) replays every constant of each of the 27 modules into a fresh environment with the Lean kernel: **27/27 pass** (`evidence/kernel_replay_per_module.txt`). `--fresh` replays (all imported constants, Mathlib included, into an empty environment) of `MSTNFConcreteAbstractEquivMWE`, `MSTNFT1BridgeClosureMWE`, `MSTNF3Form4FormEquivMWE` exit 0. The `--fresh` replay of `MSTNF3FormOmegaForcedProbeMWE` (which imports all of `Mathlib.Tactic`) aborts with a kernel deterministic timeout, a resource limit and not a type error; the per-module replay and the Nanoda check of that module pass. This uses the *same* kernel; it detects environment tampering and non-replayable declarations, it is not a second kernel.
  * **Nanoda** (`nanoda_lib` `v0.3.2`, commit `66cca78`), an independent Rust implementation of the kernel, checks an export of the 1077 theorem and definition constants of the 27 modules and all their dependencies: **`Checked 3908 declarations with no errors`**, with only `propext`, `Classical.choice`, `Quot.sound` permitted (`evidence/nanoda/`). The exporter is `lean4export` (format 2.0.0) with a small patch (qualifying `HashMap`) to compile on Lean 4.14.0.
  * Negative control: the earlier version of `MSTNFConcreteAbstractEquivMWE` (with `native_decide`) is rejected by both tools (`lean4checker`: `unknown declaration …_nativeDecide_1`; Nanoda: `unpermitted axiom "Lean.ofReduceBool"`).
* **Claims gate** (`evidence/CLAIMS.json`, `evidence/rcc/claims_*`): the registry lists the property sentences of the README and `docs/RATIONALE.md` (English and Chinese) with the theorem each cites, and the checker confirms that every cited theorem exists here with the recorded statement hash and allowed axioms. It does not check that a sentence says no more than its theorem; that review is in `evidence/audit/`. The RCC executable returns **Closed** on the claims graph. An independent review of each claim against its theorem is recorded in `evidence/audit/`.
* **RCC closure verdicts on the intents** (`evidence/rcc/`): the intents were also run through the RCC executable over the obligation graph *intent theorem → hypotheses → producers*. Non-vacuity reading (a producer showing the hypothesis is satisfiable): **11/11 Closed**. Strict reading (a producer must be generic): **7 Closed, 4 Await**.

## What this does NOT claim

* **Not a claim that Lean 4.14.0, Mathlib, or the kernel are correct.** Nanoda re-checks the kernel's judgments with a second implementation; both implement the same type theory, and neither checks that a statement says what its prose says. The claims gate checks that each property sentence names theorems whose statements are pinned; it does not replace reading them.
* **The export is of the 1077 constants of this repository and their dependencies**, produced by an exporter patched to run on Lean 4.14.0; a defect in exporter or checker is outside what is verified here.
* **Sufficiency is bounded.** The no-fifth-role statement holds inside the admissible role language of its module. Its closed instance (`noIndependentFifth_for_coreProfile`) holds by definition, and `MSTNoFifthRoleIntegrationMWE` covers only candidates the profile already entails. Neither proves that no future theory could add an independent dimension.
* **Minimality is relative.** It is minimality of independent diagnostic capacity, not of an arbitrary encoding. The theorem's signature carries a `complete B` hypothesis that its proof does not use.
* **The profile is not a safety guarantee.** `hasMSTNFProfile` does not imply at most one admitted raw input per class (`AtMostOneAdmit`, a separate condition), and it does not tie a system's outputs to representatives or residues.
* **Conditional and model-specific statements.** `sameClass_sameOutcome` needs `quotientFactorization`; the exactness theorem is about `CoreObject`, the completeness statements about decision functions `C : E → Option X`, and the profile statements about `ExecModel`. This repository gives no single map between these three models.
* **The Gödel-wall result is about an abstract model.** Gödel's theorem enters as the field `godel2` of `GodelFramework` and is not re-proved; the form quantified over every self-application operator is not claimed; the weak-framework case is a constantly-false step relation.
* **Fixtures are finite.** The conformance and concrete↔abstract theorems check only finite fixtures. They do not say a runtime implementation is correct. The Python and OCaml adapters named in some module comments are not part of this repository.
* **The RCC verdicts are consistency evidence, not independent proof.** The extractor and instance data were produced by the same party as the theory; reproducing them needs the RCC library, which this repository does not contain.
* **History and research positions are not theorems.** The origin story, the hallucination taxonomy, reclassification as convergence, the claim that the form lets any system be unfolded into four parts with one proof shape, and the statements about Residua are the project's, and none is checked here.
* **Applications are out of scope** (market-structure, Chanlun, DeFi, CRT/IET seam modules, auto-growth) as are earlier pre-NF formulations.
* **`closure_claim = 0`.** Nothing here says MST-NF, or any system built on it, is closed.

## Reproduce

```sh
# install elan: https://github.com/leanprover/elan
lake exe cache get                # Mathlib oleans (optional; otherwise Mathlib builds from source)
lake build                        # builds MSTNFDefsPred and MSTNF; expect exit 0
lake env lean scripts/PrintAxioms.lean   # axioms of the intents
lake env lean scripts/AxiomAudit.lean    # all theorems: user axioms, sorry, native_decide, Classical.choice
CLAIMS=evidence/CLAIMS.json lake env lean scripts/ClaimsCheck.lean   # every claim resolves; expect failures = 0
# kernel replay (same kernel, detects environment tampering):
git clone --branch v4.14.0 https://github.com/leanprover/lean4checker && (cd lean4checker && lake build)
for m in $(cat scripts/modules.txt); do lake env lean4checker/.lake/build/bin/lean4checker "$m"; done
# independent kernel (Nanoda): see evidence/nanoda/README.md
sha256sum -c MANIFEST.sha256      # content-addressed manifest
```

(On some macOS versions the compiled `lake exe cache get` / `lean4checker` binaries abort in `dyld`; run them interpreted, e.g. `lake env lean --run lean4checker/Main.lean <module>`.)

## Provenance

Sources are the development repository at the commits recorded in `provenance/SOURCE.md`, with the blob of every source file. Published files equal their sources byte for byte except for rewritten `import` lines (`import X` becomes `import MSTNF.X`). Nothing is edited at publication time: comment scrubs and the `native_decide` to `decide` change were made in the development repository before publication.

## Manifest

`MANIFEST.sha256` lists `sha256  path` for every file in the repository except itself.

## License

Apache-2.0. See `LICENSE` and `NOTICE`.

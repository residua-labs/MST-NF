MST-NF claims delta: 288 entries, OK 248, OVERCLAIM 40, OPEN 0

Read-only judgment of the files now in `the publication tree` (README.md 196 lines, README.zh-CN.md 116, docs/RATIONALE.md 161, docs/RATIONALE.zh-CN.md 161) against `evidence/CLAIMS.json` (schema `mstnf-claims/1`). Entry universe: 143 `claims[].anchors` plus 145 `other_property_sentences`. The four definition anchors on `residueTotality` and `representativePrecision` are already inside those 145 (`D0071`, `D0072`, `D0108`, `D0109`) and are not counted again. `quotientFactorization`, `admissibilitySound`, and `hasMSTNFProfile` have empty anchor lists.

This lane did not run `lake`, `scripts/ClaimsCheck.lean`, or RCC, and it did not remeasure the axiom audit, the Nanoda line, or the kernel replay. `gate.errors` in the file is `[]`. `unit_kinds` in the file is rationale 264, theorem 117, nonclaim 94, hedged 11, evidence 18, pointer 7, definition 4, comparison 11. An OK on an evidence sentence means the sentence reports a named file. It does not mean this lane reproduced the count.

A shared sentence registered on several claims is one verdict per anchor. The 40 OVERCLAIM entries are 24 wordings. OPEN is 0: every judged sentence either stays inside its theorem or its kind, or the gap is named below. The earlier 44-objection file is unchanged.

## Focus 1. `input_dichotomy` (C17)

`input_dichotomy` (`MSTNFProfileDichotomyMWE.lean:19-21`), under `hasMSTNFProfile`, for every raw `r`:

`(admissible (q r) = true ∧ sigma (q r) ≠ none) ∨ (admissible (q r) = false ∧ sigma (q r) = none ∧ rho (q r) ≠ none)`.

The proof builds `activeClass` as `⟨r, rfl⟩`, so the quantifier over inputs does not need a separate active-class hypothesis. The module comment says the sentence "no refusal is without a reason" resolves to this theorem, and that the theorem says nothing about `evalRaw` or `AtMostOneAdmit`. `representative_only_if_admitted` is the contrapositive `sigma (q r) ≠ none → admissible (q r) = true`.

OK, both languages: the headline (C17.A00, C17.A05, C17.A08, C17.A10); the representative/residue sentence (C17.A01, C17.A06); the intents rows (C17.A03, C17.A04). "Named residue" and "reason" are the document's words for `rho ≠ none` (some residue, not a closed vocabulary). The next README sentence says tying outputs to representatives or residues is the instance's obligation and the model requires only `quotientFactorization` (`N0075` / the Chinese object-section sentence quoted in Focus 6). `N0028` / `N0062` say the same limit.

OVERCLAIM, trace, 2 entries (C17.A02 English README, C17.A07 Chinese README):

"Used that way, an agent can still be wrong, but its answers are traceable to an admission it can be held to, and every refusal in the model has a name (`input_dichotomy`)."

Chinese: "这样使用时，agent 依然可能出错，但它的答案可以追溯到一次可以被追责的准入，模型里的每一次拒绝都有名字（`input_dichotomy`）。"

The refusal half matches the second disjunct (`rho ≠ none`). Traceability of answers is not a conjunct. The module comment says the theorem says nothing about the outcome `evalRaw`. "Used that way" points at the previous hedge; the traceability clause is still asserted, and the citation is `input_dichotomy`.

## Focus 2. Sufficiency (C03, C04, C05) and the completeness glue (C01)

`roleRepresentation_iff_noDiagnostic` (`MSTNFExecutionNoFifthRoleMWE.lean:117-123`) is `RoleProfileRepresentation r ↔ ¬ ExplicitDiagnosticWitness r`. `ExplicitDiagnosticWitness` (`:47-51`) is two objects with the same profile and asymmetric `sem`. `NoIndependentFifthRole` is `¬ ∃ r, IsExecutionRole r ∧ ¬ RoleProfileRepresentation r`. The module header scopes the claim to a Φ-exec admissible role language, and states it as a conditional: if every execution role is represented, then there is no independent fifth. The intents rows for the three iff theorems match those statements, including the scope words "inside the admissible role language" on the sufficiency cell. `noIndependentFifth_for_coreProfile` (`:221-224`) is the closed instance: four constructors, `IsExecutionRole := True`, `profile := id`, proof by `rfl` after unfolding. The intents row says "holds by definition". C05 (`profileWithFifth_iff_profile`, `no_independent_deletion_countermodel_for_dependent_fifth`, `extended_basis_complete`) is the dependent fifth the profile already entails. Those intents rows are English-only and match. `N0024`/`N0025` and `N0056`/`N0057` bound the result to that language and say it does not prove that no future theory could add a dimension.

OVERCLAIM, exhibit, 4 entries. The same why-bullet is an anchor of C01 and of C03, in both languages (C01.A00, C01.A04, C03.A00, C03.A04):

"no independent fifth role can be exhibited inside the admissible role language (`roleRepresentation_iff_noDiagnostic`)."

Chinese: "在可容许角色语言之内，无法给出独立的第五个角色（`roleRepresentation_iff_noDiagnostic`）。"

The cited theorem is the per-role biconditional with `ExplicitDiagnosticWitness`. Exhibiting that witness is how independence is stated. The bullet states a ban on exhibiting a fifth, drops the header's hypothesis that every role is represented, and cites the per-role iff for that ban. The first half of the same bullet, four roles suffice for any `C` via `completeness_theorem`, matches the existential (`q := C`, `σ := id`, proofs `rfl`) and is not the defect.

OVERCLAIM, residue-name, 6 entries. The sufficiency cell is an anchor of C01, C03, and C04, in both languages (C01.A07, C01.A09, C03.A05, C03.A06, C04.A03, C04.A04). The iff clause matches: a candidate factors through the profile iff there are no two objects with the same profile that it separates; a fifth cannot be asserted and has to be exhibited; the core instance holds by definition. Then:

"an exhibited one is a concrete named residue."

Chinese: "被给出的那个，就是一个具体的具名残差。"

`ExplicitDiagnosticWitness` is two objects and a role predicate. A residue in this document is `rho c ≠ none` (`residueTotality`). The exhibited witness is not a residue.

OVERCLAIM, iso-surj, 16 entries, one gap. `kernel_exact_iso` (`MSTNFCanonicalDecompositionMWE.lean:317-322`) is: if both quotients are kernel-exact and both are `Function.Surjective`, then there is a bijection `f` with `f ∘ q₁ = q₂`. The construction uses `Surjective.choose`. The intents row states "two kernel-exact surjective quotients are isomorphic" and is OK (C10.A02). The uniqueness cell states "when onto" and is OK. These sentences drop surjectivity:

- Why-bullet, C10.A00, C10.A03, C11.A00, C11.A02: "the decomposition is unique for a given `C`, up to isomorphism (`kernel_exact_iso`)." Chinese: "分解是唯一的（在同构意义下，`kernel_exact_iso`）。" The coarsest half of the same bullet cites `canonical_is_coarsest` and matches that theorem (a valid decomposition does not merge inputs `C` separates).
- One-paragraph summary, C01.A01, C01.A05, C07.A01, C07.A04, C08.A01, C08.A06, C10.A01, C10.A04, C14.A01, C14.A04: "the canonical decomposition is unique up to isomorphism (`kernel_exact_iso`)." The other clauses of that paragraph match their theorems. `canonicalQ = C` is not shown surjective, so the iso theorem does not apply to it as a bare citation of uniqueness.
- C10.A06, C10.A08: "'Unique' in the table is uniqueness of the decomposition for a given `C` (`kernel_exact_iso`)." The next clause, that uniqueness of MST-NF as the structure forced by the founding requirement is open, matches the open-question hedges.

## Focus 3. 3-form (C18–C21) and the Gödel-wall model (C22, C23)

C18 matches. `admissibilitySound_derived`, `residueTotality_derived`, and `representativePrecision_derived` are case splits on `Lambda` for every `ExecModel3`, and `hasMSTNFProfile_3form` is `quotientFactorization3`. "By typing" matches those proofs. `tag_is_omega_forced` (`MSTNF3FormOmegaForcedProbeMWE.lean:75-80`) is: `χ : Class → Bool` with `χ c = true ↔ admissible c = true` gives `χ = admissible`, by `funext` and cases. The rationale gloss "uniqueness of the classifying map of the admission subobject at the Boolean level, by cases" stays inside that statement. "At the Boolean level" and "by cases" keep it off a topos universal property. `two_Lambdas_same_tag_distinct_witnesses` is the pair with `sigma true = some 0` and `some 1`. The sentence that the four-role form is the normal form as a design decision, not a separate theorem, is `N0080` / `N0119` and matches its nonclaim kind. The displayed `ExecModel` order in the rationale is admissible, then rho, then sigma, as declared.

`toExecModel_fromExecModel` (`MSTNF3Form4FormEquivMWE.lean:524-527`) is equality under `hasMSTNFProfile`, all classes active, and `lambdaPartition`. The intents row C19.A00 states those hypotheses and is OK. The three round-trip rows (C19.A02, C19.A03, C19.A04) say "operational round trip" on one projection. Each theorem assumes `hasMSTNFProfile_3form` and all classes of the `toExecModel` image active, and concludes a pointwise equation. The label does not state an unconditional equality. OK.

OVERCLAIM, iff-hyp, 3 entries. `hasMSTNFProfile_iff_3form_section` (`:587-590`) is the iff under `∀ c, activeClass M c` and `lambdaPartition M`. C19.A01: "a 4-form has the profile iff it is the projection of a 3-form with its profile." Both hypotheses are absent from that row. C19.A05 and C19.A06 are the rationale sentence that glosses `toExecModel ∘ fromExecModel = id` and the same unconditional iff. The previous sentence of the same numbered item (rationale only, quoted in Focus 6) says `fromExecModel` needs the profile, all classes active, and a partition condition. That sentence is not part of the anchor. The anchor as registered states the identity and the iff without those hypotheses. The following sentence, that no theorem states non-injectivity and the bijection wording is withdrawn, is `N0078` / `N0116` and is OK.

`godel2` is the field `selfSoundnessFiat ∉ detected` (`MSTNFResidueAbsorptionWellFoundedMWE.lean:86-89`). `N0007`, `N0029`, `N0041`, `N0063`, `N0084`, `N0123` say it is a field and is not re-proved. Those match.

`InBasis step k := ∀ k', ¬ step k k'` (`:59-60`). `godelStep_no_terminal` (`:141-144`) is `¬ InBasis godelStep F`, proved by applying the basis hypothesis to `godelSuccessor F`. `godelStep_has_successor` (`:137-139`) is `∃ F', godelStep F F'` and is not in C22's theorem list. `godelStep_flip_not_wellFounded` (`:172-173`) is `¬ WellFounded (flip godelStep)` and the intents row names `Classical.choice`. That row is OK. `T1_parametric_in_framework` is `∀ F, ¬ ReachesBasis godelStep F`. C22.A00, C22.A03, C22.A06, C22.A08, C22.A10 match it. `T1_closure` (`MSTNFT1BridgeClosureMWE.lean:195-203`) is the conjunction of `∀ n, ∃ F', godelStep (metaLevelToFramework n) F'`, the three non-memberships below, and `T1_parametric_in_framework`. It does not contain `¬ WellFounded`. C22.A04 ("conjunction of the Gödel-wall facts for the model") does not add that conjunct. OK as a label of that conjunction. The rationale paragraph states the conjuncts `42 ∉ [40]`, `49 ∉ [40, 42]`, `52 ∉ [40, 42, 49]` and says the ladder numbers are an empirical observation, not a theorem. Those clauses match. `UniformInD_LeanCoreUnformalizable` is defined as `True` (`:161-168`); the rationale does not cite it, and it says the uniform-in-D form is a named boundary and is not claimed (`N0029`).

OVERCLAIM, successor, 3 entries (C22.A01, and the rationale paragraphs C22.A07, C22.A09). Intents: "`godelStep_no_terminal` — every `GodelFramework` has a successor." The rationale repeats "`godelStep_no_terminal` (every framework has a successor)" / "每个框架都有后继". The statement is `¬ InBasis`. The existential is the unlisted theorem `godelStep_has_successor`. The proof exhibits `godelSuccessor`, so the gloss is the reason the negation holds, and it is attributed to the other statement.

OVERCLAIM, antifiat, 1 entry, English intents only (C22.A05): "`antiFiatChain_each_detects_prior_fiat` — each ladder level detects the previous fiat." The theorem (`MSTNFT1BridgeClosureMWE.lean:112-116`) is `f_42.selfSoundnessFiat ∉ f_40.detected ∧ f_49.selfSoundnessFiat ∉ f_42.detected ∧ f_52.selfSoundnessFiat ∉ f_49.detected`, closed by `decide`. That is the new fiat outside the previous `detected` list. `f_40.detected = []`, `f_42.detected = [40]`, `f_49.detected = [40, 42]`, `f_52.detected = [40, 42, 49]`, so the data also has the other membership, and the module comment records that membership as an empirical observation. The theorem does not prove it, and these four values are not a `godelStep` chain (`godelSuccessor` sets the next fiat to `listMax + 1`). The rationale says the non-memberships, and says the "previous level's self-soundness fiat" reading is not a theorem (`N0085` / `N0124`). Chinese has no intents table (`README.zh-CN.md` says that section is English-only), so this wording is not in the Chinese file.

OVERCLAIM, weakhorn, 1 entry, English intents only (C23.A01): "`weak_horn_redescriptive_but_nonuniversal` — the weak-framework case seals but is non-universal (model-level)." The theorem (`MSTNFResidueAbsorptionWellFoundedMWE.lean:274-276`) is `AllResiduesRepresented weakStep ∧ WellFounded (flip weakStep)`, with `weakStep := fun _ _ => False` (`:257-258`). Non-universality, and "cannot encode its own self-application", is the comment at `:269-273`. The rationale says that half is a comment, not a theorem (C23.A02, C23.A03). `N0029` / `N0063` say the weak-framework case is a constantly-false step. Those are OK. `weakStep_wellFounded` as "constantly false" (C23.A00) matches.

## Focus 4. `nonclaim` and `hedged`

The gate document says a positive sentence that contains a negation word can be classified `nonclaim`, and that the reviewer judges meaning. These assert a property and stay inside a definition or a theorem, so the verdict is OK and the kind label is the heuristic the document describes:

- `N0074` / `N0111`: the per-input dichotomy (admitted with a representative, or not admissible, no representative, and a residue). Content matches `input_dichotomy`. "Not" is why the kind is nonclaim.
- `N0099` / `N0139`: "a representative exists only for an admitted class (`admissibilitySound`), and every active class that is not admitted has a named residue (`residueTotality`)." Both match the definitions (`sigma c = some rep → admissible c = true`; active and `admissible = false` implies `rho ≠ none`). `N0100` / `N0140` then say this does not constrain `evalRaw`.
- `N0004` / `N0038`: the speech act is that a founding requirement corresponds to `ρ`. The parenthesis "a refused input gets a named residue, never silently dropped" is that requirement's wording. It is the `ρ` question, not a theorem about `evalRaw`.

`N0081`–`N0086` and `N0120`–`N0125` report the project's record (redescription, corpus sizes, Gödel II as the record's argument) and say the coincidence is not a theorem here, that `godel2` is a field, and that the ladder membership is an empirical observation. Comparison entries `C0087`–`C0091` and `C0126`–`C0131` stay inside "proves nothing" / schema comparison. The old open items on Mazurkiewicz traces, Galois connections, and refinement types are that prose. Hedged open questions (`H0010`, `H0044`, `H0045`, `H0102`, `H0103`, `H0143`, `H0144`) ask whether the requirement is minimal and whether MST-NF is the unique such structure. They do not assert either.

OVERCLAIM, self-grounded, 2 entries (`H0096`, `H0136`), kind `hedged`:

"MST-NF reads Minimal Structure Theory (Normal Form), a general, self-grounded minimal semantic model."

Chinese: "MST-NF 读作 Minimal Structure Theory (Normal Form)，一个通用的、自奠基的最小语义模型。"

The historical expansion of the abbreviation is a hedge. The appositive asserts generality, self-groundedness, and minimality. No theorem in the registry is that claim, and the same section lists whether the requirements are minimal, and whether MST-NF is the unique structure satisfying them, as open (`H0102`, `H0103`).

## Focus 5. Chinese against English

No Chinese sentence on the focus items is stronger than its English counterpart. The exhibit bullet, the named-residue clause, the surjectivity omission, the traceability sentence, the unconditional 3-form iff in the rationale, the successor gloss, and the self-grounded appositive are parallel. Chinese is weaker where `README.zh-CN.md` leaves the intents table in English only: the anti-fiat "detects the previous fiat" row and the weak-horn "non-universal" row have no Chinese anchor. C05, C06, C24, and C25 intents rows are English-only; their Chinese absence is the parity the README states, and those English rows match their theorems. One Chinese limit is registered more weakly than English: the object-section `evalRaw` sentence is rationale-only in Chinese and nonclaim `N0075` in English (Focus 6). The wording is the same limit.

## Focus 6. Gate misses

The mechanism says a unit with no lexicon hit is `rationale` and, by construction, states no property. These sentences state a property, are not among the 288 entries, and are only in `rationale_sentences`. Quoted in full:

1. Traceability, same gap as C17.A02, with no theorem name. `docs/RATIONALE.md`: "An agent built as an instance can still be wrong; its answers are traceable to an admission it can be held to." `docs/RATIONALE.zh-CN.md`: "作为实例构建的 agent 依然可能出错；它的答案可以追溯到一次可以被追责的准入。"
2. Converse of C18, content matches (the three derived obligations hold for every `ExecModel3`, so a system that violates them is not an `ExecModel3`). English: "A system that violates those three cannot be written as an `ExecModel3`." Chinese: "违反这三条的系统，无法写成 `ExecModel3`。"
3. True limit on `sigma`. English: "`sigma` is a function, so a class has one value, but nothing in the profile says which value; \"canonical\" is not a property the profile imposes." Chinese: "`sigma` 是函数，所以一个类只有一个值，但 profile 没有说是哪个值；\"规范\"不是 profile 强加的性质。" The σ question-row ("What is the canonical form of an admitted input?") is a question in that table, not this assertion.
4. True limit, English rationale copy only. "The profile does **not** say that at most one raw input per class is admitted; that separate safety condition (`AtMostOneAdmit`) is not one of the four roles." The Chinese twin is registered (`N0112`). `admissibilitySound`'s comment says the at-most-one condition is the separate `AtMostOneAdmit`.
5. Definition restatement with no definition anchor. English: "| a | `admissibilitySound` | if a class has a representative, it is admissible |". Chinese: "| a | `admissibilitySound` | 如果一个类有代表元，它就是被接受的 |". The definition is `∀ c rep, sigma c = some rep → admissible c = true`. `D:admissibilitySound` has no anchors. The `σ` and `ρ` rows of the same table are the definition anchors and match.
6. Glossary biconditional, not attached to `agree_iff_same_canonical`. English: "A normal form is a canonical representation: every object of a kind has one, and two objects are equivalent exactly when their normal forms agree." Chinese: "范式是一种规范表示：同一种类的每个对象都有一个，两个对象等价，当且仅当它们的范式一致。" Read as the meaning of the phrase, it cites no theorem. The agreement theorem is about two decision functions `C`, and the iso theorem needs surjectivity.
7. Chinese-only registration gap for a limit English registers as `N0075`. "另外，`evalRaw` 只被要求通过类分解：模型并不要求一个输入的结果是代表元或拒绝，所以把输出与 `σ`/`ρ` 绑定，是具体实例自己的义务。" Content matches `quotientFactorization` (`evalRaw r = evalClass (q r)`) and the C17 module comment.

OVERCLAIM, coverage, 2 entries (`E0019`, `E0051`): "every sentence in the README and `docs/RATIONALE.md` (English and Chinese) that states a property resolves to a claim, and every claim resolves to a theorem here with a matching statement hash and allowed axioms." The sentences in this section state properties and do not resolve to a claim. The hash half is a report of `evidence/CLAIMS.json` and `scripts/ClaimsCheck.lean`; this lane did not re-run that check, so this verdict does not confirm the hashes.

No other property sentence in the four files was found outside the registry. Directory-table phrases such as "authorization bridge" are the C15 scope note; `exact_agrees` is `ExactP ↔ Exact (toSet C)`.

## What the rewrite brought inside the theorems

These earlier gaps are now stated at the size of the theorem or the kind, and their entries are OK: completeness proofs named as `rfl` with `q := C` and `σ := id`, and `ρ` named as a Boolean; `complete B` named as unused on `standard_basis_is_minimal_independent_diagnostic_basis`; "canonical" not asserted of `sigma` (Focus 6 item 3); closure-operator presentation withdrawn (`CoreObject` does not assume monotonicity, idempotence, totality, or fixedness); 3-form bijection wording withdrawn; `ExecModel` display matches the declaration; `godel2` stated as a field; redescription, corpus figures, and "not new" attributed to the record; Mazurkiewicz, Galois, and refinement-type paragraphs say the repository proves nothing about them.

## Ledger

288 lines. OVERCLAIM names the defect code from the sections above. OK is the verdict that the anchor says no more than its theorem or its kind.

C01.A00 OVERCLAIM exhibit [en] README.md §Why
C01.A01 OVERCLAIM iso-surj [en] README.md §The theory in one paragraph
C01.A02 OK [en] README.md §Intents
C01.A03 OK [en] README.md §Intents
C01.A04 OVERCLAIM exhibit [zh] README.zh-CN.md §为什么
C01.A05 OVERCLAIM iso-surj [zh] README.zh-CN.md §一段话说明理论
C01.A06 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C01.A07 OVERCLAIM residue-name [en] RATIONALE.md §Why it is a normal form: the mathematics
C01.A08 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C01.A09 OVERCLAIM residue-name [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C02.A00 OK [en] README.md §Intents
C02.A01 OK [en] README.md §Intents
C02.A02 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C02.A03 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C03.A00 OVERCLAIM exhibit [en] README.md §Why
C03.A01 OK [en] README.md §Intents
C03.A02 OK [en] README.md §Intents
C03.A03 OK [en] README.md §Intents
C03.A04 OVERCLAIM exhibit [zh] README.zh-CN.md §为什么
C03.A05 OVERCLAIM residue-name [en] RATIONALE.md §Why it is a normal form: the mathematics
C03.A06 OVERCLAIM residue-name [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C04.A00 OK [en] README.md §Intents
C04.A01 OK [en] README.md §What this does NOT claim
C04.A02 OK [zh] README.zh-CN.md §本仓库不宣称什么
C04.A03 OVERCLAIM residue-name [en] RATIONALE.md §Why it is a normal form: the mathematics
C04.A04 OVERCLAIM residue-name [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C05.A00 OK [en] README.md §Intents
C05.A01 OK [en] README.md §Intents
C05.A02 OK [en] README.md §Intents
C06.A00 OK [en] README.md §Intents
C07.A00 OK [en] README.md §Why
C07.A01 OVERCLAIM iso-surj [en] README.md §The theory in one paragraph
C07.A02 OK [en] README.md §Intents
C07.A03 OK [zh] README.zh-CN.md §为什么
C07.A04 OVERCLAIM iso-surj [zh] README.zh-CN.md §一段话说明理论
C07.A05 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C07.A06 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C07.A07 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C07.A08 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C08.A00 OK [en] README.md §Why a normal form, and not a design
C08.A01 OVERCLAIM iso-surj [en] README.md §The theory in one paragraph
C08.A02 OK [en] README.md §Intents
C08.A03 OK [en] README.md §Intents
C08.A04 OK [en] README.md §Intents
C08.A05 OK [zh] README.zh-CN.md §为什么是范式，而不是设计
C08.A06 OVERCLAIM iso-surj [zh] README.zh-CN.md §一段话说明理论
C08.A07 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C08.A08 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C08.A09 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C08.A10 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C08.A11 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C08.A12 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C09.A00 OK [en] README.md §Intents
C09.A01 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C09.A02 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C10.A00 OVERCLAIM iso-surj [en] README.md §Why
C10.A01 OVERCLAIM iso-surj [en] README.md §The theory in one paragraph
C10.A02 OK [en] README.md §Intents
C10.A03 OVERCLAIM iso-surj [zh] README.zh-CN.md §为什么
C10.A04 OVERCLAIM iso-surj [zh] README.zh-CN.md §一段话说明理论
C10.A05 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C10.A06 OVERCLAIM iso-surj [en] RATIONALE.md §Why it is a normal form: the mathematics
C10.A07 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C10.A08 OVERCLAIM iso-surj [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C11.A00 OVERCLAIM iso-surj [en] README.md §Why
C11.A01 OK [en] README.md §Intents
C11.A02 OVERCLAIM iso-surj [zh] README.zh-CN.md §为什么
C11.A03 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C11.A04 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C12.A00 OK [en] README.md §Intents
C12.A01 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C12.A02 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C13.A00 OK [en] README.md §Intents
C13.A01 OK [en] README.md §What this does NOT claim
C13.A02 OK [zh] README.zh-CN.md §本仓库不宣称什么
C13.A03 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C13.A04 OK [en] RATIONALE.md §Using it
C13.A05 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C13.A06 OK [zh] RATIONALE.zh-CN.md §如何使用
C14.A00 OK [en] README.md §Why
C14.A01 OVERCLAIM iso-surj [en] README.md §The theory in one paragraph
C14.A02 OK [en] README.md §Intents
C14.A03 OK [zh] README.zh-CN.md §为什么
C14.A04 OVERCLAIM iso-surj [zh] README.zh-CN.md §一段话说明理论
C14.A05 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C14.A06 OK [en] RATIONALE.md §Using it
C14.A07 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C14.A08 OK [zh] RATIONALE.zh-CN.md §如何使用
C15.A00 OK [en] README.md §Intents
C15.A01 OK [en] RATIONALE.md §Using it
C15.A02 OK [zh] RATIONALE.zh-CN.md §如何使用
C16.A00 OK [en] README.md §Intents
C16.A01 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C16.A02 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C17.A00 OK [en] README.md §MST-NF
C17.A01 OK [en] README.md §Why for agents, by agents
C17.A02 OVERCLAIM trace [en] README.md §Why for agents, by agents
C17.A03 OK [en] README.md §Intents
C17.A04 OK [en] README.md §Intents
C17.A05 OK [zh] README.zh-CN.md §MST-NF
C17.A06 OK [zh] README.zh-CN.md §为什么是 for agents, by agents
C17.A07 OVERCLAIM trace [zh] README.zh-CN.md §为什么是 for agents, by agents
C17.A08 OK [en] RATIONALE.md §MST-NF: rationale, results and scope
C17.A09 OK [en] RATIONALE.md §For agents
C17.A10 OK [zh] RATIONALE.zh-CN.md §MST-NF：理由、结果与范围
C17.A11 OK [zh] RATIONALE.zh-CN.md §面向 agents
C18.A00 OK [en] README.md §Intents
C18.A01 OK [en] README.md §Intents
C18.A02 OK [en] README.md §Intents
C18.A03 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C18.A04 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C19.A00 OK [en] README.md §Intents
C19.A01 OVERCLAIM iff-hyp [en] README.md §Intents
C19.A02 OK [en] README.md §Intents
C19.A03 OK [en] README.md §Intents
C19.A04 OK [en] README.md §Intents
C19.A05 OVERCLAIM iff-hyp [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C19.A06 OVERCLAIM iff-hyp [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C20.A00 OK [en] README.md §Intents
C20.A01 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C20.A02 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C21.A00 OK [en] README.md §Intents
C21.A01 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C21.A02 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C22.A00 OK [en] README.md §Why for agents, by agents
C22.A01 OVERCLAIM successor [en] README.md §Intents
C22.A02 OK [en] README.md §Intents
C22.A03 OK [en] README.md §Intents
C22.A04 OK [en] README.md §Intents
C22.A05 OVERCLAIM antifiat [en] README.md §Intents
C22.A06 OK [zh] README.zh-CN.md §为什么是 for agents, by agents
C22.A07 OVERCLAIM successor [en] RATIONALE.md §What the Gödel wall model proves
C22.A08 OK [en] RATIONALE.md §What is new, what is not, and what is open
C22.A09 OVERCLAIM successor [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
C22.A10 OK [zh] RATIONALE.zh-CN.md §什么是新的，什么不是，什么是未决的
C23.A00 OK [en] README.md §Intents
C23.A01 OVERCLAIM weakhorn [en] README.md §Intents
C23.A02 OK [en] RATIONALE.md §What the Gödel wall model proves
C23.A03 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
C24.A00 OK [en] README.md §Intents
C25.A00 OK [en] README.md §Intents
C25.A01 OK [en] README.md §Intents
C25.A02 OK [en] README.md §Intents
N0001 OK [en] README.md §Why
H0002 OK [en] README.md §Why a normal form, and not a design
N0003 OK [en] README.md §Why a normal form, and not a design
N0004 OK [en] README.md §Why a normal form, and not a design
N0005 OK [en] README.md §Why a normal form, and not a design
N0006 OK [en] README.md §Why for agents, by agents
N0007 OK [en] README.md §Why for agents, by agents
E0008 OK [en] README.md §What is proved, and where to read more
P0009 OK [en] README.md §What is proved, and where to read more
H0010 OK [en] README.md §What is proved, and where to read more
N0011 OK [en] README.md §The theory in one paragraph
E0012 OK [en] README.md §What is in the repository
N0013 OK [en] README.md §What is in the repository
P0014 OK [en] README.md §What is in the repository
E0015 OK [en] README.md §Intents
E0016 OK [en] README.md §Trust boundary
E0017 OK [en] README.md §Trust boundary
E0018 OK [en] README.md §Trust boundary
E0019 OVERCLAIM coverage [en] README.md §Trust boundary
E0020 OK [en] README.md §Trust boundary
E0021 OK [en] README.md §Trust boundary
N0022 OK [en] README.md §What this does NOT claim
N0023 OK [en] README.md §What this does NOT claim
N0024 OK [en] README.md §What this does NOT claim
N0025 OK [en] README.md §What this does NOT claim
N0026 OK [en] README.md §What this does NOT claim
N0027 OK [en] README.md §What this does NOT claim
N0028 OK [en] README.md §What this does NOT claim
N0029 OK [en] README.md §What this does NOT claim
N0030 OK [en] README.md §What this does NOT claim
N0031 OK [en] README.md §What this does NOT claim
N0032 OK [en] README.md §What this does NOT claim
N0033 OK [en] README.md §What this does NOT claim
N0034 OK [zh] README.zh-CN.md §为什么
N0035 OK [zh] README.zh-CN.md §为什么
N0036 OK [zh] README.zh-CN.md §为什么是范式，而不是设计
N0037 OK [zh] README.zh-CN.md §为什么是范式，而不是设计
N0038 OK [zh] README.zh-CN.md §为什么是范式，而不是设计
N0039 OK [zh] README.zh-CN.md §为什么是范式，而不是设计
N0040 OK [zh] README.zh-CN.md §为什么是 for agents, by agents
N0041 OK [zh] README.zh-CN.md §为什么是 for agents, by agents
E0042 OK [zh] README.zh-CN.md §证明了什么，详情在哪里
P0043 OK [zh] README.zh-CN.md §证明了什么，详情在哪里
H0044 OK [zh] README.zh-CN.md §证明了什么，详情在哪里
H0045 OK [zh] README.zh-CN.md §证明了什么，详情在哪里
N0046 OK [zh] README.zh-CN.md §一段话说明理论
N0047 OK [zh] README.zh-CN.md §仓库内容、Intents、清单与许可
E0048 OK [zh] README.zh-CN.md §信任边界
E0049 OK [zh] README.zh-CN.md §信任边界
E0050 OK [zh] README.zh-CN.md §信任边界
E0051 OVERCLAIM coverage [zh] README.zh-CN.md §信任边界
E0052 OK [zh] README.zh-CN.md §信任边界
E0053 OK [zh] README.zh-CN.md §信任边界
N0054 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0055 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0056 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0057 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0058 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0059 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0060 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0061 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0062 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0063 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0064 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0065 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0066 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0067 OK [zh] README.zh-CN.md §本仓库不宣称什么
P0068 OK [en] RATIONALE.md §MST-NF: rationale, results and scope
P0069 OK [en] RATIONALE.md §MST-NF: rationale, results and scope
N0070 OK [en] RATIONALE.md §MST-NF: rationale, results and scope
D0071 OK [en] RATIONALE.md §The object
D0072 OK [en] RATIONALE.md §The object
N0073 OK [en] RATIONALE.md §The object
N0074 OK [en] RATIONALE.md §The object
N0075 OK [en] RATIONALE.md §The object
E0076 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
N0077 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
N0078 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
N0079 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
N0080 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
N0081 OK [en] RATIONALE.md §What the Gödel wall model proves
N0082 OK [en] RATIONALE.md §What the Gödel wall model proves
N0083 OK [en] RATIONALE.md §What the Gödel wall model proves
N0084 OK [en] RATIONALE.md §What the Gödel wall model proves
N0085 OK [en] RATIONALE.md §What the Gödel wall model proves
N0086 OK [en] RATIONALE.md §What the Gödel wall model proves
C0087 OK [en] RATIONALE.md §Related structures
C0088 OK [en] RATIONALE.md §Related structures
C0089 OK [en] RATIONALE.md §Related structures
C0090 OK [en] RATIONALE.md §Related structures
C0091 OK [en] RATIONALE.md §Related structures
N0092 OK [en] RATIONALE.md §Where it came from
N0093 OK [en] RATIONALE.md §Where it came from
H0094 OK [en] RATIONALE.md §Where it came from
N0095 OK [en] RATIONALE.md §Where it came from
H0096 OVERCLAIM self-grounded [en] RATIONALE.md §Where it came from
N0097 OK [en] RATIONALE.md §For agents
N0098 OK [en] RATIONALE.md §For agents
N0099 OK [en] RATIONALE.md §For agents
N0100 OK [en] RATIONALE.md §For agents
N0101 OK [en] RATIONALE.md §For agents
H0102 OK [en] RATIONALE.md §What is new, what is not, and what is open
H0103 OK [en] RATIONALE.md §What is new, what is not, and what is open
N0104 OK [en] RATIONALE.md §What is new, what is not, and what is open
P0105 OK [zh] RATIONALE.zh-CN.md §MST-NF：理由、结果与范围
P0106 OK [zh] RATIONALE.zh-CN.md §MST-NF：理由、结果与范围
N0107 OK [zh] RATIONALE.zh-CN.md §MST-NF：理由、结果与范围
D0108 OK [zh] RATIONALE.zh-CN.md §对象
D0109 OK [zh] RATIONALE.zh-CN.md §对象
N0110 OK [zh] RATIONALE.zh-CN.md §对象
N0111 OK [zh] RATIONALE.zh-CN.md §对象
N0112 OK [zh] RATIONALE.zh-CN.md §对象
E0113 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
N0114 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
N0115 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
N0116 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
N0117 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
N0118 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
N0119 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
N0120 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
N0121 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
N0122 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
N0123 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
N0124 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
N0125 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
C0126 OK [zh] RATIONALE.zh-CN.md §相关结构
C0127 OK [zh] RATIONALE.zh-CN.md §相关结构
C0128 OK [zh] RATIONALE.zh-CN.md §相关结构
C0129 OK [zh] RATIONALE.zh-CN.md §相关结构
C0130 OK [zh] RATIONALE.zh-CN.md §相关结构
C0131 OK [zh] RATIONALE.zh-CN.md §相关结构
N0132 OK [zh] RATIONALE.zh-CN.md §它的来历
N0133 OK [zh] RATIONALE.zh-CN.md §它的来历
N0134 OK [zh] RATIONALE.zh-CN.md §它的来历
N0135 OK [zh] RATIONALE.zh-CN.md §它的来历
H0136 OVERCLAIM self-grounded [zh] RATIONALE.zh-CN.md §它的来历
N0137 OK [zh] RATIONALE.zh-CN.md §面向 agents
N0138 OK [zh] RATIONALE.zh-CN.md §面向 agents
N0139 OK [zh] RATIONALE.zh-CN.md §面向 agents
N0140 OK [zh] RATIONALE.zh-CN.md §面向 agents
N0141 OK [zh] RATIONALE.zh-CN.md §面向 agents
N0142 OK [zh] RATIONALE.zh-CN.md §什么是新的，什么不是，什么是未决的
H0143 OK [zh] RATIONALE.zh-CN.md §什么是新的，什么不是，什么是未决的
H0144 OK [zh] RATIONALE.zh-CN.md §什么是新的，什么不是，什么是未决的
N0145 OK [zh] RATIONALE.zh-CN.md §什么是新的，什么不是，什么是未决的

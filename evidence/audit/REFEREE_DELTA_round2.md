MST-NF claims delta2: 299 entries, OK 299, OVERCLAIM 0, OPEN 0

Second pass on the files now in `the publication tree`. Entry universe: 147 `claims[].anchors` plus 152 `other_property_sentences` (nonclaim 99, evidence 20, comparison 11, hedged 9, pointer 7, definition 6). The six definition anchors are those six `other_property_sentences` (`D0073`–`D0075`, `D0113`–`D0115`), not a further count. `gate.errors` in the file is `[]`. `unit_kinds` is rationale 255, theorem 121, nonclaim 99, hedged 9, evidence 20, pointer 7, definition 6, comparison 11.

The inbox says the Lean sources are unchanged since round 1. This lane re-read the four prose files and `evidence/CLAIMS.json`. It did not re-run `lake`, `ClaimsCheck`, or RCC, and it did not remeasure the axiom audit, Nanoda, or the kernel replay. An OK on an evidence sentence means the sentence reports a named file or the checker's contract. It does not mean this lane reproduced the count. Theorem statements cited below are the ones read from the published modules in round 1.

Round 1's 40 OVERCLAIM entries were 24 wordings. Each wording was rewritten. None of the old wordings remain. OPEN is 0.

## The 24 wordings

exhibit. The why-bullet (C01.A00, C01.A04, C03.A00, C03.A04) now says that, inside the admissible role language, a candidate fifth role factors through the four-role profile unless an explicit diagnostic witness for it is exhibited (`roleRepresentation_iff_noDiagnostic`). That is the per-role biconditional: `RoleProfileRepresentation r ↔ ¬ ExplicitDiagnosticWitness r`, and the witness is two objects with the same profile and asymmetric `sem`. The module header scopes that language to the q/a/ρ/σ profile. The bullet no longer says a fifth cannot be exhibited.

residue-name. The sufficiency cell (C01.A07, C01.A09, C03.A05, C03.A06, C04.A03, C04.A04) says an exhibited candidate is an explicit diagnostic witness, two objects with the same profile that the candidate separates, and that this is not a residue in the sense of `rho c ≠ none`. The iff clause, the scope sentence, and the core instance holding by definition are unchanged and still match.

iso-surj. `kernel_exact_iso` is an isomorphism of two kernel-exact surjective quotients. The why-bullet (C10.A00, C11.A00) says unique up to isomorphism among kernel-exact surjective quotients. The Chinese why-bullet (C10.A03, C11.A02) says two kernel-exact surjective quotients are the same in the sense of isomorphism, and cites `kernel_exact_iso`. The one-paragraph summary says two kernel-exact surjective quotients are isomorphic. The table gloss (C10.A06, C10.A08) says the same. The uniqueness cell still says "when onto". The coarsest half still cites `canonical_is_coarsest`.

trace. README C17.A02 / C17.A07: "what the model gives is that every refusal in it carries a residue (`input_dichotomy`)." Rationale C17.A10 / C17.A13: "the model gives only that its refusals carry residues (`input_dichotomy`)." "Its" binds to the model. `input_dichotomy` is the class split under `hasMSTNFProfile`: admitted with `sigma ≠ none`, or refused with `sigma = none` and `rho ≠ none`. "Carries a residue" is the `rho ≠ none` half. The traceability clause is gone. The headline and the module comment still match, and the surrounding sentences still leave `evalRaw` to the instance (`N0080`, `N0029`).

iff-hyp. C19.A01 states the iff under all classes active and `lambdaPartition`, which is the hypothesis list of `hasMSTNFProfile_iff_3form_section` (`hasMSTNFProfile` is the left side of that iff, not a further hypothesis). C19.A05 and C19.A06 put the same two hypotheses on the iff parenthesis. The parenthesis `` `toExecModel ∘ fromExecModel = id` `` does not repeat hypotheses. The previous sentence of the same numbered item says `fromExecModel` needs the profile, all classes active, and a partition condition, and those are the hypotheses of `toExecModel_fromExecModel`. The intents row C19.A00 states them. The round-trip rows remain labels of the pointwise theorems. OK.

successor. C22.A01 glosses `godelStep_no_terminal` as `¬ InBasis godelStep F`. C22.A07 and C22.A09 say the reason is that `godelSuccessor F` is a successor, and that this existential is the separate statement `godelStep_has_successor`. "Every level of an earlier toy ladder has a successor" is the conjunct `∀ n, ∃ F', godelStep (metaLevelToFramework n) F'` inside `T1_closure`, not a gloss of `¬ InBasis`. The three non-memberships and `T1_parametric_in_framework` are stated as in the theorem. `¬ WellFounded` stays on its own row.

antifiat. C22.A05: "the next level's fiat is not in the previous level's detected list (decide on concrete data)." The theorem is `42 ∉ [40]`, `49 ∉ [40, 42]`, `52 ∉ [40, 42, 49]`, by `decide`. The rationale still calls the other direction an empirical observation.

weakhorn. C23.A01: for the constantly-False step, all residues represented and the flipped step well-founded, and non-universality is a comment, not a theorem. That matches `AllResiduesRepresented weakStep ∧ WellFounded (flip weakStep)` with `weakStep := fun _ _ => False`, and the comment at the theorem.

self-grounded. The appositive is gone. The sentence is "MST-NF reads Minimal Structure Theory (Normal Form), the name of the theory," and the Chinese twin "这是该理论的名称." Both are rationale, not property entries. They name the abbreviation. The minimality and uniqueness questions stay open (`H0107`, `H0108`, `H0150`, `H0151`).

coverage. E0019 / E0052 say the registry lists the property sentences with the theorem each cites, and the checker confirms that every cited theorem exists with the recorded statement hash and allowed axioms. E0020 / E0053 say the checker does not check that a sentence says no more than its theorem. That matches `docs/CLAIMS_GATE_MECHANISM.md`. This lane did not re-run the checker, so the hash half is not reconfirmed. The sentences no longer say every property sentence resolves to a claim. The lexicon misses below are the remainder; they do not make E0019 assert a theorem.

C18. The converse is now its own anchor (C18.A04, C18.A06) and names `admissibilitySound_derived`, `residueTotality_derived`, and `representativePrecision_derived`. Those three hold for every `ExecModel3` by cases on `Lambda`, so a system that violates them is not an `ExecModel3`.

N0081 / N0120 hedge the glossary: a normal form, in general usage, is a canonical representation, and the repository does not claim that notion beyond the theorems listed below.

Registered former misses, content unchanged and inside the definition or the limit: `admissibilitySound` table row (`D0073`, `D0113`); "canonical is not a property the profile imposes" (`N0078`, `N0118`); at most one admitted raw input per class is `AtMostOneAdmit` (`N0079`, `N0119`, and `N0029` / `N0064`). `representativePrecision` and `residueTotality` rows still match `sigma c ≠ none` and `rho c ≠ none` on active classes.

## Chinese

No Chinese sentence is stronger than its English counterpart. The exhibit, residue-name, surjectivity, refusal-carries-residue, successor, and 3-form hypothesis wordings are parallel. Chinese "在同构意义下是同一个" is the isomorphism claim, cited to `kernel_exact_iso`, not an unstated equality. The intents table is still English-only, so C05, C06, C23's weak-horn row, C24, and C25 have no Chinese anchor. The anti-fiat row is English-only; the Chinese rationale states the non-memberships.

## Gate misses

These state a property and are not among the 299 entries. They sit in `rationale_sentences`.

1. Chinese object-section limit, English twin registered as `N0080`. "另外，`evalRaw` 只被要求通过类分解：模型并不要求一个输入的结果是代表元或拒绝，所以把输出与 `σ`/`ρ` 绑定，是具体实例自己的义务。" Content matches `quotientFactorization` (`evalRaw r = evalClass (q r)`) and the C17 module comment. Not stronger than the English sentence.

2. Closed vocabulary, both languages. "Name the admission test, the representative function `sigma` and the residue function `rho` (a closed vocabulary of residues is good practice; the structure does not require it)." Chinese: "命名准入测试、代表元函数 `sigma` 和残差函数 `rho`（残差词表是封闭的是好的实践；结构本身并不要求）。" `residueTotality` is `rho c ≠ none` for an active non-admissible class. A closed vocabulary is not a conjunct.

3. Founding-requirement correspondence for `σ`, both languages. The `ρ` twin is registered (`N0004`, `N0039`). These are not: "precision (an admitted input gets a representative) corresponds to `σ`" and "精准（被接受的输入有代表元）对应 `σ`。" The speech act is the correspondence. The parenthesis is the requirement's wording. It does not carry the active-class hypothesis of `representativePrecision`.

4. Comparison-section definition, both languages, while the neighboring "proves nothing" sentences are `comparison` entries. "In the `CoreObject`, `Sound` is `Fix ⊆ Adm` and `Complete` is `Adm ⊆ Fix` for the set of fixed points of a relation `D`; there is no abstraction map, no concretisation map and no insertion." Chinese: "在 `CoreObject` 里，`Sound` 是 `Fix ⊆ Adm`，`Complete` 是 `Adm ⊆ Fix`，其中 `Fix` 是关系 `D` 的不动点集；这里没有抽象映射，没有具体化映射，也没有 Galois 插入。" The two inclusions match the definitions. The sentence does not state a Galois connection.

The sentence that the canonical strata coincide with an orthogonal factorization system, a subobject classifier, and a join-semilattice is rationale and is qualified by "per that record." The next sentence is registered and says that coincidence is not established by theorems in this repository. The "name of the theory" sentence is not a property claim.

## Ledger

299 lines. Each is OK: the anchor says no more than its theorem or its stated kind.

C01.A00 OK [en] README.md §Why
C01.A01 OK [en] README.md §The theory in one paragraph
C01.A02 OK [en] README.md §Intents
C01.A03 OK [en] README.md §Intents
C01.A04 OK [zh] README.zh-CN.md §为什么
C01.A05 OK [zh] README.zh-CN.md §一段话说明理论
C01.A06 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C01.A07 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C01.A08 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C01.A09 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C02.A00 OK [en] README.md §Intents
C02.A01 OK [en] README.md §Intents
C02.A02 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C02.A03 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C03.A00 OK [en] README.md §Why
C03.A01 OK [en] README.md §Intents
C03.A02 OK [en] README.md §Intents
C03.A03 OK [en] README.md §Intents
C03.A04 OK [zh] README.zh-CN.md §为什么
C03.A05 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C03.A06 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C04.A00 OK [en] README.md §Intents
C04.A01 OK [en] README.md §What this does NOT claim
C04.A02 OK [zh] README.zh-CN.md §本仓库不宣称什么
C04.A03 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C04.A04 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C05.A00 OK [en] README.md §Intents
C05.A01 OK [en] README.md §Intents
C05.A02 OK [en] README.md §Intents
C06.A00 OK [en] README.md §Intents
C07.A00 OK [en] README.md §Why
C07.A01 OK [en] README.md §The theory in one paragraph
C07.A02 OK [en] README.md §Intents
C07.A03 OK [zh] README.zh-CN.md §为什么
C07.A04 OK [zh] README.zh-CN.md §一段话说明理论
C07.A05 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C07.A06 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C07.A07 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C07.A08 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C08.A00 OK [en] README.md §Why a normal form, and not a design
C08.A01 OK [en] README.md §The theory in one paragraph
C08.A02 OK [en] README.md §Intents
C08.A03 OK [en] README.md §Intents
C08.A04 OK [en] README.md §Intents
C08.A05 OK [zh] README.zh-CN.md §为什么是范式，而不是设计
C08.A06 OK [zh] README.zh-CN.md §一段话说明理论
C08.A07 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C08.A08 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C08.A09 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C08.A10 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C08.A11 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C08.A12 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C09.A00 OK [en] README.md §Intents
C09.A01 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C09.A02 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C10.A00 OK [en] README.md §Why
C10.A01 OK [en] README.md §The theory in one paragraph
C10.A02 OK [en] README.md §Intents
C10.A03 OK [zh] README.zh-CN.md §为什么
C10.A04 OK [zh] README.zh-CN.md §一段话说明理论
C10.A05 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C10.A06 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
C10.A07 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C10.A08 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
C11.A00 OK [en] README.md §Why
C11.A01 OK [en] README.md §Intents
C11.A02 OK [zh] README.zh-CN.md §为什么
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
C14.A01 OK [en] README.md §The theory in one paragraph
C14.A02 OK [en] README.md §Intents
C14.A03 OK [zh] README.zh-CN.md §为什么
C14.A04 OK [zh] README.zh-CN.md §一段话说明理论
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
C17.A02 OK [en] README.md §Why for agents, by agents
C17.A03 OK [en] README.md §Intents
C17.A04 OK [en] README.md §Intents
C17.A05 OK [zh] README.zh-CN.md §MST-NF
C17.A06 OK [zh] README.zh-CN.md §为什么是 for agents, by agents
C17.A07 OK [zh] README.zh-CN.md §为什么是 for agents, by agents
C17.A08 OK [en] RATIONALE.md §MST-NF: rationale, results and scope
C17.A09 OK [en] RATIONALE.md §For agents
C17.A10 OK [en] RATIONALE.md §For agents
C17.A11 OK [zh] RATIONALE.zh-CN.md §MST-NF：理由、结果与范围
C17.A12 OK [zh] RATIONALE.zh-CN.md §面向 agents
C17.A13 OK [zh] RATIONALE.zh-CN.md §面向 agents
C18.A00 OK [en] README.md §Intents
C18.A01 OK [en] README.md §Intents
C18.A02 OK [en] README.md §Intents
C18.A03 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C18.A04 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C18.A05 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C18.A06 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C19.A00 OK [en] README.md §Intents
C19.A01 OK [en] README.md §Intents
C19.A02 OK [en] README.md §Intents
C19.A03 OK [en] README.md §Intents
C19.A04 OK [en] README.md §Intents
C19.A05 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C19.A06 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C20.A00 OK [en] README.md §Intents
C20.A01 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C20.A02 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C21.A00 OK [en] README.md §Intents
C21.A01 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
C21.A02 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
C22.A00 OK [en] README.md §Why for agents, by agents
C22.A01 OK [en] README.md §Intents
C22.A02 OK [en] README.md §Intents
C22.A03 OK [en] README.md §Intents
C22.A04 OK [en] README.md §Intents
C22.A05 OK [en] README.md §Intents
C22.A06 OK [zh] README.zh-CN.md §为什么是 for agents, by agents
C22.A07 OK [en] RATIONALE.md §What the Gödel wall model proves
C22.A08 OK [en] RATIONALE.md §What is new, what is not, and what is open
C22.A09 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
C22.A10 OK [zh] RATIONALE.zh-CN.md §什么是新的，什么不是，什么是未决的
C23.A00 OK [en] README.md §Intents
C23.A01 OK [en] README.md §Intents
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
E0019 OK [en] README.md §Trust boundary
E0020 OK [en] README.md §Trust boundary
E0021 OK [en] README.md §Trust boundary
E0022 OK [en] README.md §Trust boundary
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
N0034 OK [en] README.md §What this does NOT claim
N0035 OK [zh] README.zh-CN.md §为什么
N0036 OK [zh] README.zh-CN.md §为什么
N0037 OK [zh] README.zh-CN.md §为什么是范式，而不是设计
N0038 OK [zh] README.zh-CN.md §为什么是范式，而不是设计
N0039 OK [zh] README.zh-CN.md §为什么是范式，而不是设计
N0040 OK [zh] README.zh-CN.md §为什么是范式，而不是设计
N0041 OK [zh] README.zh-CN.md §为什么是 for agents, by agents
N0042 OK [zh] README.zh-CN.md §为什么是 for agents, by agents
E0043 OK [zh] README.zh-CN.md §证明了什么，详情在哪里
P0044 OK [zh] README.zh-CN.md §证明了什么，详情在哪里
H0045 OK [zh] README.zh-CN.md §证明了什么，详情在哪里
H0046 OK [zh] README.zh-CN.md §证明了什么，详情在哪里
N0047 OK [zh] README.zh-CN.md §一段话说明理论
N0048 OK [zh] README.zh-CN.md §仓库内容、Intents、清单与许可
E0049 OK [zh] README.zh-CN.md §信任边界
E0050 OK [zh] README.zh-CN.md §信任边界
E0051 OK [zh] README.zh-CN.md §信任边界
E0052 OK [zh] README.zh-CN.md §信任边界
E0053 OK [zh] README.zh-CN.md §信任边界
E0054 OK [zh] README.zh-CN.md §信任边界
E0055 OK [zh] README.zh-CN.md §信任边界
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
N0068 OK [zh] README.zh-CN.md §本仓库不宣称什么
N0069 OK [zh] README.zh-CN.md §本仓库不宣称什么
P0070 OK [en] RATIONALE.md §MST-NF: rationale, results and scope
P0071 OK [en] RATIONALE.md §MST-NF: rationale, results and scope
N0072 OK [en] RATIONALE.md §MST-NF: rationale, results and scope
D0073 OK [en] RATIONALE.md §The object
D0074 OK [en] RATIONALE.md §The object
D0075 OK [en] RATIONALE.md §The object
N0076 OK [en] RATIONALE.md §The object
N0077 OK [en] RATIONALE.md §The object
N0078 OK [en] RATIONALE.md §The object
N0079 OK [en] RATIONALE.md §The object
N0080 OK [en] RATIONALE.md §The object
N0081 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
E0082 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
N0083 OK [en] RATIONALE.md §Why it is a normal form: the mathematics
N0084 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
N0085 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
N0086 OK [en] RATIONALE.md §"If four is minimal, why can σ and ρ be merged?"
N0087 OK [en] RATIONALE.md §What the Gödel wall model proves
N0088 OK [en] RATIONALE.md §What the Gödel wall model proves
N0089 OK [en] RATIONALE.md §What the Gödel wall model proves
N0090 OK [en] RATIONALE.md §What the Gödel wall model proves
N0091 OK [en] RATIONALE.md §What the Gödel wall model proves
N0092 OK [en] RATIONALE.md §What the Gödel wall model proves
C0093 OK [en] RATIONALE.md §Related structures
C0094 OK [en] RATIONALE.md §Related structures
C0095 OK [en] RATIONALE.md §Related structures
C0096 OK [en] RATIONALE.md §Related structures
C0097 OK [en] RATIONALE.md §Related structures
N0098 OK [en] RATIONALE.md §Where it came from
N0099 OK [en] RATIONALE.md §Where it came from
H0100 OK [en] RATIONALE.md §Where it came from
N0101 OK [en] RATIONALE.md §Where it came from
N0102 OK [en] RATIONALE.md §For agents
N0103 OK [en] RATIONALE.md §For agents
N0104 OK [en] RATIONALE.md §For agents
N0105 OK [en] RATIONALE.md §For agents
N0106 OK [en] RATIONALE.md §For agents
H0107 OK [en] RATIONALE.md §What is new, what is not, and what is open
H0108 OK [en] RATIONALE.md §What is new, what is not, and what is open
N0109 OK [en] RATIONALE.md §What is new, what is not, and what is open
P0110 OK [zh] RATIONALE.zh-CN.md §MST-NF：理由、结果与范围
P0111 OK [zh] RATIONALE.zh-CN.md §MST-NF：理由、结果与范围
N0112 OK [zh] RATIONALE.zh-CN.md §MST-NF：理由、结果与范围
D0113 OK [zh] RATIONALE.zh-CN.md §对象
D0114 OK [zh] RATIONALE.zh-CN.md §对象
D0115 OK [zh] RATIONALE.zh-CN.md §对象
N0116 OK [zh] RATIONALE.zh-CN.md §对象
N0117 OK [zh] RATIONALE.zh-CN.md §对象
N0118 OK [zh] RATIONALE.zh-CN.md §对象
N0119 OK [zh] RATIONALE.zh-CN.md §对象
N0120 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
E0121 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
N0122 OK [zh] RATIONALE.zh-CN.md §为什么它是范式：数学
N0123 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
N0124 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
N0125 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
N0126 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
N0127 OK [zh] RATIONALE.zh-CN.md §"如果四个是最小的，为什么 σ 和 ρ 可以合并？"
N0128 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
N0129 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
N0130 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
N0131 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
N0132 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
N0133 OK [zh] RATIONALE.zh-CN.md §哥德尔墙模型证明了什么
C0134 OK [zh] RATIONALE.zh-CN.md §相关结构
C0135 OK [zh] RATIONALE.zh-CN.md §相关结构
C0136 OK [zh] RATIONALE.zh-CN.md §相关结构
C0137 OK [zh] RATIONALE.zh-CN.md §相关结构
C0138 OK [zh] RATIONALE.zh-CN.md §相关结构
C0139 OK [zh] RATIONALE.zh-CN.md §相关结构
N0140 OK [zh] RATIONALE.zh-CN.md §它的来历
N0141 OK [zh] RATIONALE.zh-CN.md §它的来历
N0142 OK [zh] RATIONALE.zh-CN.md §它的来历
N0143 OK [zh] RATIONALE.zh-CN.md §它的来历
N0144 OK [zh] RATIONALE.zh-CN.md §面向 agents
N0145 OK [zh] RATIONALE.zh-CN.md §面向 agents
N0146 OK [zh] RATIONALE.zh-CN.md §面向 agents
N0147 OK [zh] RATIONALE.zh-CN.md §面向 agents
N0148 OK [zh] RATIONALE.zh-CN.md §面向 agents
N0149 OK [zh] RATIONALE.zh-CN.md §什么是新的，什么不是，什么是未决的
H0150 OK [zh] RATIONALE.zh-CN.md §什么是新的，什么不是，什么是未决的
H0151 OK [zh] RATIONALE.zh-CN.md §什么是新的，什么不是，什么是未决的
N0152 OK [zh] RATIONALE.zh-CN.md §什么是新的，什么不是，什么是未决的

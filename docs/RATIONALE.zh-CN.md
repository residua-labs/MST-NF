# MST-NF：理由、结果与范围

[English](RATIONALE.md) · **中文**

这是 [README](../README.zh-CN.md) 的详细配套文档：对象、已证明的性质、3-form 问题、哥德尔墙模型、相关结构、如何实例化，以及它的来历。这里点名的每一条定理都在本仓库中；公理见 README 的 *Intents*。不是定理的陈述（历史、研究立场、类比）都有明确标注。

**一个"做决定的系统"的范式。在 MST-NF 模型里，每个输入所属的类，要么被接受并带有代表元，要么被拒绝并带有具名的残差，所以没有哪一次拒绝是没有理由的（`input_dichotomy`）。**

## 四个问题

任何接收输入、做出决定的系统，都在暗中回答四个问题，比如编译器、包管理器、CI 门禁、证明检查器，以及 agent 的行动策略。

| | 问题 | 隐式回答时的表现 |
|---|---|---|
| **q** | 两个输入什么时候算"同一个东西"？ | 重命名后缓存出错、依赖地狱、"在我机器上能跑" |
| **a** | 什么可以进来？ | 准入规则散落在各处的 `if` 里，没有人能完整说清楚 |
| **σ** | 被接受的输入，它的规范形式是什么？ | 同一个东西有多种写法，比较和去重出错 |
| **ρ** | 被拒绝时，具体原因是什么？ | 输入被悄悄丢掉或被近似；"出了点问题" |

MST-NF 把这四个答案显式化为四个角色，并如下所示地把它们联系起来。

## 对象

在 Lean 里，四个角色是同一个结构 `ExecModel`（`MSTNF/algorithms/MSTNecessityExecModelMWE`）的字段，和声明完全一致：

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

（`activeClass c` 表示存在某个原始输入 `r` 使得 `q r = c`。）每个角色带一条义务；它们的合取就是 `hasMSTNFProfile`。

| 角色 | 义务（Lean 名） | 陈述 |
|---|---|---|
| q | `quotientFactorization` | `evalRaw r = evalClass (q r)`：系统在一个输入上做什么，只取决于它的类 |
| a | `admissibilitySound` | 如果一个类有代表元，它就是被接受的 |
| σ | `representativePrecision` | 每个活跃的被接受的类都有代表元（`sigma c ≠ none`） |
| ρ | `residueTotality` | 每个活跃的未被接受的类都有残差（`rho c ≠ none`） |

项目从它的奠基要求到这些义务的对应关系（记录在一份本仓库未包含的桥接笔记里）是：`q` ← 功能角色"区分"（R1）；`a` ← "约束"（R2）与可容许性（Φ2a）；`σ` ← "生成"（R3）与元素级精准（Φ2b）；`ρ` ← 诚实（Φ3）与递归完备（Φ5）。Lean 文件里带有的标记是 R1、R2、Φ2b 和 Φ5；这个对应关系是项目的，不是这里证明的。

profile 给了什么，没给什么。对每个输入（它的类是活跃的）：要么它的类是被接受的并且有代表元，要么它不被接受、没有代表元、并且有残差。`sigma` 是函数，所以一个类只有一个值，但 profile 没有说是哪个值；"规范"不是 profile 强加的性质。profile **不**说每个类至多有一个原始输入被接受；那个单独的安全条件（`AtMostOneAdmit`）不属于四个角色。另外，`evalRaw` 只被要求通过类分解：模型并不要求一个输入的结果是代表元或拒绝，所以把输出与 `σ`/`ρ` 绑定，是具体实例自己的义务。

## 为什么它是范式：数学

一般意义上，范式是一种规范表示；本仓库对这一概念的断言，不超出下面所列的定理。MST-NF 有下表中的五个性质，每个都对应所列的定理（`evidence/CLAIMS.json`）。这些性质是针对三个相关的模型陈述的：决策函数 `C : E → Option X`（`none` = 拒绝）、`ExecModel` 和 `CoreObject`。本仓库没有给出这三者之间的统一映射。

| 性质 | 定理说了什么 | 定理（模块） |
|---|---|---|
| **完备性（Completeness）** | 每个 `C` 都有忠实的 (q, a, σ, ρ) 分解，由 `C` 构造得到（证明是 `rfl`：`q := C`，`σ := id`）。每个输入要么被接受要么被拒绝，二者互斥（`canonicalA (q e) = !ρ e`），并且 ρ 在每个被拒绝的输入上成立。这里的 ρ 是布尔的拒绝指示；有类型的残差属于 `ExecModel`。 | `completeness_theorem`、`canonical_decomposition_faithful`、`residue_totality`、`admitted_rejected_partition`（`MSTNFCompletenessRepresentationMWE`） |
| **充分性（Sufficiency）** | FDT 形式：一个候选角色能通过四角色 profile 分解，**当且仅当**它没有显式诊断见证，即不存在两个 profile 相同、而它能区分的对象。所以第五个角色不能凭空宣称，必须被给出；被给出的那个，是一个显式诊断见证（两个 profile 相同、而候选角色能区分的对象），它不是 `rho c ≠ none` 意义上的残差。这在该模块的可容许角色语言之内成立（模块自己的范围语句）。对核心执行语言，每个角色都被表示（`noIndependentFifth_for_coreProfile`，一个封闭的实例：四个角色就是四个构造子，按定义成立）。与 `completeness_theorem`（每个决策函数都通过 q/a/σ/ρ 分解）一起，这就是充分性的结果。 | `roleRepresentation_iff_noDiagnostic`、`noIndependentFifth_iff_noExplicitDiagnosticWitness`、`noIndependentFifth_iff_allRolesRepresented`（泛型）、`noIndependentFifth_for_coreProfile`（`MSTNFExecutionNoFifthRoleMWE`） |
| **必要性（Necessity）** | 对每个角色，都存在一个 `ExecModel`，其余三个角色性质成立，而该角色的性质不成立。（在部分反模型里，其余三个之一成立是因为它的假设为空；陈述的是反模型的存在。） | `deleting_each_role_breaks_semantics`（`MSTNecessityRoleAblationMWE`） |
| **最小性（Minimality）** | 被合并的两个角色不能同时被独立诊断，所以能独立诊断全部四个角色的基，至少有四个角色位置。这是诊断能力的最小性，不是编码的最小性。该定理的签名里带有一个 `complete B` 假设，证明并未使用它；起承重作用的假设是可独立诊断性。 | `standard_basis_is_minimal_independent_diagnostic_basis`、`fused_roles_lose_independent_diagnostics`（`MSTMinimalityRoleBasisMWE`） |
| **唯一性（Uniqueness）** | 任何两个 kernel-exact 的分解，识别的是同一批输入，并且（在满射时）同构。合法分解从不合并 `C` 区分开的输入，所以规范分解是最粗的。两个决策函数在每个输入上一致，当且仅当它们的规范形式相等（这是一个函数外延性的陈述）。 | `kernel_exact_unique_up_to_map`、`kernel_exact_iso`、`canonical_is_coarsest`、`agree_iff_same_canonical`（`MSTNFCanonicalDecompositionMWE`） |

`MSTNoFifthRoleIntegrationMWE` 只覆盖*依赖的*候选（被 profile 蕴含，所以没有删除反模型，把它们加进基也不改变任何东西）。它是展开定义得到的簿记，不是独立性结果。`minimal_complete_basis` 打包的是完备性；它的最小性一半是命题 `True`，只是一个交叉引用，所以不把它当作最小性的证明来引用。

两个后果承载了实际的分量：
- **行为通过身份分解。** 对满足 `quotientFactorization` 的 `ExecModel`，同一个类里的输入得到相同的结果（`sameClass_sameOutcome`）。
- **正确性有封闭形式：**一个 `CoreObject` 是 exact 的，当且仅当它的可靠性残差与完备性残差都为空（`exact_iff_empty_residues`；它用到了 `Classical.choice`）。

表中的"唯一"指的是：任何两个 kernel-exact 且满射的商是同构的（`kernel_exact_iso`）；MST-NF 是否是奠基要求所逼出的唯一结构，是另一个问题，列在最后的未决项里。至于这个形式可以让人把系统展开成四个部分、并用同一种证明形状，那是项目的实践，不是这里的定理；逻辑里的合取范式扮演类似的角色（仅是类比）。

### "如果四个是最小的，为什么 σ 和 ρ 可以合并？"

它们可以被打包成一个带和类型的分类器 `Lambda : (c : Class) → {r // IsRep c r} ⊕ {e // IsResidue c e}`，即"3-form" `ExecModel3`（`MSTNF3FormMWE`）。这与最小性结果（`standard_basis_is_minimal_independent_diagnostic_basis`）并不矛盾，后者讲的是独立诊断。模块确立了：

1. **最小性不是"组件数最少"。** 四条义务一个都不能丢，并且每一条都可以在其余三条成立时失败（`deleting_each_role_breaks_semantics`）；合并的角色不能同时被独立诊断（`fused_roles_lose_independent_diagnostics`）。把两个角色打包进一个类型是重新编码，理论并不排除这一点。
2. **在 3-form 里，四条义务中有三条由类型保证：**`admissibilitySound_derived`、`residueTotality_derived`、`representativePrecision_derived` 是对 `Lambda` 的分情况讨论；3-form 的 profile `hasMSTNFProfile_3form` 只是 `quotientFactorization3`。违反这三条的系统，无法写成 `ExecModel3`（`admissibilitySound_derived`、`residueTotality_derived`、`representativePrecision_derived`）。
3. **3-form 与 4-form 之间是遗忘映射加截面。** `toExecModel` 遗忘 `IsRep`/`IsResidue` 见证；`fromExecModel` 用平凡见证填充它们，并需要 profile、所有类活跃、以及一个划分条件。已证明：`toExecModel_fromExecModel`（`toExecModel ∘ fromExecModel = id`）、`hasMSTNFProfile_iff_3form_section`（在所有类活跃且满足 `lambdaPartition` 时，一个 4-form 具有 profile，当且仅当它是某个具有其 profile 的 3-form 的 `toExecModel`），以及 `fromExecModel_toExecModel_admissible/sigma/rho`（操作意义上的往返，在三个投影上逐点成立）。模块的注释解释了为什么没有严格逆（多个在 `IsRep`/`IsResidue` 上不同的 3-form 投影到同一个 4-form）；没有定理陈述"非单射"，模块里也撤回了较早的"双射"说法（`MSTNF3Form4FormEquivMWE`）。
4. **准入标签是被强制的；合并后的分类器不是。** `tag_is_omega_forced` 表明，任何与 `admissible` 具有相同真纤维的布尔分类器都等于 `admissible`（在布尔层面，准入子对象的分类映射是唯一的，按情况证明）。`two_Lambdas_same_tag_distinct_witnesses` 给出两个 `ExecModel3`，`admissible` 相同、`sigma true` 不同（`MSTNF3FormOmegaForcedProbeMWE`）。所以标签的唯一性并不决定合并后的分类器。

四角色形式让接受（σ）与拒绝（ρ）保持对称且可以分别检查，把它当作*那个*范式，是理论的一个设计决定，由第 1–4 点支持，而不是一条单独的定理。

## 哥德尔墙模型证明了什么

项目的研究记录区分两个层面。在对象层，规范分层与一些经典结构一致（按该记录：商的规范性对应正交分解系统，准入对应子对象分类子，选择空间对应连接半格）。对四角色对象而言，这种一致并没有在本仓库里被定理确立；这里只是把它作为该记录的主张来报告，由此得到的是：对象层被视为重新描述，而不是新数学。它在语料上的机械验证（记录给出 q 在 105 个规格中匹配 94 个，σ 在 71 个中匹配 71 个，在被测试的规模上）是用 `native_decide` 把一个独立编写的 Lean belief 函数与规格自己的门禁对照检查，即 Lean 对照规格，而不是规格对照真实协议。语料模块不属于本仓库。

在元层，记录论证：把 MST-NF 应用到它自己的残差吸收过程上，不可能到达终止基，因为一个足够有表达力、能编码自身可靠性的框架无法证明它（哥德尔第二不完备定理），所以"这个框架是可靠的"永远是它之外的一个残差。本仓库里有的是这一论证的一个抽象模型，不是哥德尔定理本身：

```lean
structure GodelFramework where
  detected : List Nat
  selfSoundnessFiat : Nat
  godel2 : selfSoundnessFiat ∉ detected
```

`godel2` 是一个字段：在具体框架里，哥德尔定理会在这里被应用；它没有在这里被证明。`godelSuccessor F` 把 fiat 加进 `detected`，并选一个新的数作为下一个 fiat，由算术得到（`fresh_not_in`）。定理有：`godelStep_no_terminal`（`¬ InBasis godelStep F`：没有框架是终止的；原因是 `godelSuccessor F` 是一个后继，这是另一条陈述 `godelStep_has_successor`）、`godelStep_flip_not_wellFounded`（`¬ WellFounded (flip godelStep)`；用到了 `Classical.choice`）、`T1_parametric_in_framework`（`∀ F, ¬ ReachesBasis godelStep F`）和 `T1_closure`（一个合取：早先玩具阶梯的每一层都有后继；具体事实 `42 ∉ [40]`、`49 ∉ [40, 42]`、`52 ∉ [40, 42, 49]`；以及 `T1_parametric_in_framework`；公理 `propext`、`Quot.sound`）。数字 40、42、49、52 标记项目的 anti-fiat 阶梯的层；"每一层都是上一层的自身可靠性 fiat"是模块里记录的经验观察，不是定理。这些证明没有使用可证性谓词或可表示性假设，所以这是对该回归的结构性模型；要为真实框架论证 `godel2`，需要真正的定理。对每个自应用算子都成立的形式需要 Reynolds 参数性，而 Lean 4 core 没有它；这是一个被命名的边界，不作宣称。对"弱到哥德尔定理不适用的框架"这一情形，用 `WeakFramework` 建模，其步关系恒为 `False`（`weakStep_wellFounded`、`weak_horn_redescriptive_but_nonuniversal`）；弱框架无法编码自身的自应用，这是注释，不是定理。

## 相关结构

没有任何定理把 MST-NF 与下列结构联系起来；以下是来自项目 schema 分析的散文式比较。

**Mazurkiewicz 迹。** 迹幺半群用一个独立性关系对字做商，所以它的类扮演 `q` 的角色，每个类取一个代表元（例如字典序范式）扮演 `σ` 的角色。它没有准入谓词，也没有残差：分类器是一个到代表元的全函数。项目分析里 MST-NF 的扩展在于分类器的值域是和类型，要么是代表元，要么是残差，于是失败被分类而不是缺席。本仓库对迹同余或独立性关系没有证明任何东西。

**抽象解释与 Galois 连接。** 在抽象解释里，"可靠性与完备性"这两个词指的是抽象相对于具体语义的关系，通过构成 Galois 连接的抽象映射与具体化映射来表达。在 `CoreObject` 里，`Sound` 是 `Fix ⊆ Adm`，`Complete` 是 `Adm ⊆ Fix`，其中 `Fix` 是关系 `D` 的不动点集；这里没有抽象映射，没有具体化映射，也没有 Galois 插入。两套词汇只在用词上重叠，没有被证明的对应。

**精化类型（refinement types）。** 精化类型是带谓词的基类型，运算在被精化的子集上是部分的。3-form 的 `Sum {r // IsRep c r} {e // IsResidue c e}` 以同样的方式使用子类型，所以 4-form 看上去像"精化类型加部分函数"。在 3-form 里，分类器是到和类型的全函数，不限制定义域，项目分析把这当作区别所在。本仓库没有证明这一构造与任何精化类型系统的关系。

## 如何使用

把一个组件建模为 `ExecModel`：
1. 命名它的原始输入、类和 `q`。
2. 命名准入测试、代表元函数 `sigma` 和残差函数 `rho`（残差词表是封闭的是好的实践；结构本身并不要求）。
3. 满足上面的四条义务。

之后 `sameClass_sameOutcome` 适用。`exact_iff_empty_residues` 针对单独的 `CoreObject` 结构；这里没有从 `ExecModel` 到 `CoreObject` 的通用映射。

要保持"无 Mathlib"边界的下游运行时，可以只引入 `MSTNFDefsPred/` 而不引入整个理论。它零导入，是 core object 的谓词形式，它对集合形式的忠实性由 `MSTNFPredBridgeMWE` 的等价定理确立（exactness 部分见 `exact_agrees`）。

下表只是示意；本仓库只形式化了抽象理论。

| 系统 | q：同一个东西 | a：允许进入 | σ：规范形式 | ρ：具名的拒绝 |
|---|---|---|---|---|
| 编译器 | 程序的含义 | 支持的语言子集 | 中间表示 | 不支持的构造、类型错误 |
| 包管理器 | 内容哈希 | 仓库策略 | 锁文件 | 版本冲突、被拒绝的包 |
| 代码合并 | patch 内容 | CI 与评审 | 合并后的树 | 拒绝它的具体规则 |
| 证明检查器 | 命题 | 内核接受 | 被检查的推导 | 具体的内核拒绝 |
| agent 行动策略 | 被请求的动作 | 策略上限 | 规范化后的动作 | 被拒绝的权限 |

## 它的来历

以下历史来自项目自己的笔记；其中没有一条是本仓库的定理，源仓库也未公开。MST-NF 不是自上而下设计出来的。它起源于项目所有者在构建一门市场叙述描述语言时给出的一条要求：描述必须客观、精准、诚实；必须是纯推理，统计上的正确，哪怕是 99.99%，也不接受；必须递归完备；超出它的部分，必须明确标出：这里开始由人来决定。笔记从中提取了六条奠基原则（分类先于推断；最小可容许世界；结构先于动力学；规范选择要么唯一要么不存在；残差是偏差的结构化度量；完备性是残差压力的终止），以及一条生长规则：

```
发现残差 → 要求见证 → 能用定理吸收就吸收 → 否则暴露它并开出最小的新层
```

笔记把历史上的推导描述为在人的引导下进行，AI agents 担任实现者和评审者（作者不是验证者的循环，以 Lean 为评价器），论文经历了十四轮对抗评审。笔记描述的链条终止于一个残差穷尽的范式，带有分阶段的结构和七个结构化残差；本仓库证明的四角色形式，是同一条路线的执行 profile 陈述，并不声称它是那段推导的直接产物。缩写 MST 在历史上指 Market Structure Theory（市场结构理论），也就是机制最初被研究的领域；MST-NF 读作 Minimal Structure Theory (Normal Form)，这是该理论的名称。

## 面向 agents

以下是研究立场，不是本仓库的定理。本仓库确立的，是 profile 在类层面的结构（`input_dichotomy`），正是它让这些立场可以被检查。

项目的分类理论对"一个确定的输出"区分三种情形：**Type 1**，证据不足（存在唯一答案，但证据缺失）；**Type 2**，结构性多元（有多个有效答案，这并不是失败）；**Type 3**，无依据的规范化（在结构不支持的地方给出确定输出），也就是语言模型里所说的幻觉。MST-NF 的义务约束的是类这一层：只有被接受的类才有代表元（`admissibilitySound`），每个活跃但未被接受的类都有具名残差（`residueTotality`）。它们本身并不约束系统在某个输入上输出什么（`evalRaw` 只需要通过类分解），而准入测试是否只接受那些有依据得到唯一读法的类，是具体实例自己的义务，体现为它的 `a`，并对照它的残差来检查。作为实例构建的 agent 依然可能出错；模型只提供：它的拒绝都带有残差（`input_dichotomy`）。

关于 agent 如何进步，同一条研究路线把封闭世界的智能描述为"由重分类驱动的收敛"：在固定原则下对固定信息反复重分类，直到稳定，从而改进结构；用 MST-NF 的话说，重分类就是残差吸收。这是一个操作性定义，不是这里证明的结果。Residua 项目把自己的组件描述为 MST-NF 实例；这是关于 Residua 的陈述，在本仓库中没有被检查。

## 什么是新的，什么不是，什么是未决的

- **不是新的：**商以及可靠性/完备性的词汇有悠久的历史，并且按项目记录，对象层的分层与经典结构一致；本仓库不宣称在对象层有新数学。`CoreObject` 明确说单调性、幂等性、全性和不动性都不被假设，所以这个对象不被表述为闭包算子。
- **本仓库确立的：**
  - 带有义务的四角色 `ExecModel`，以及上表中的各陈述，各自带有其范围；
  - 哥德尔墙模型：没有 `GodelFramework` 能到达终止基（`T1_parametric_in_framework`），哥德尔定理以字段的形式进入；
  - 把该理论用作一个运行中系统的生成结构，是项目的主张，这里没有检查。
- **未决，不作宣称：**
  - 只从奠基要求出发，自动化地重跑一遍，能否得到同一个范式；
  - 这些要求本身是否最小；
  - MST-NF 是否是满足它们的唯一结构。

确切的定理陈述、公理和范围见 *Intents*；未作的宣称见 *What this does NOT claim*。

# MST-NF

[English](README.md) · **中文**

**一个"做决定的系统"的范式。在 MST-NF 模型里，每个输入所属的类，要么被接受并带有代表元（representative），要么被拒绝并带有具名的残差（residue），所以没有哪一次拒绝是没有理由的（`input_dichotomy`）。**

*MST-NF：Minimal Structure Theory (Normal Form)。* Lean 4（v4.14.0，Mathlib v4.14.0）；见*信任边界*。

## 为什么

任何接收输入、做出决定的系统，都在暗中回答四个问题，比如编译器、包管理器、CI 门禁、证明检查器，以及 AI agent。

| | 问题 | 隐式回答时的表现 |
|---|---|---|
| **q** | 两个输入什么时候算"同一个东西"？ | 缓存失效、依赖地狱、"在我机器上能跑" |
| **a** | 什么可以进来？ | 规则散落在各处的 `if` 里，没有人能完整说清楚 |
| **σ** | 被接受的输入，它的规范形式是什么？ | 同一个东西有多种写法，比较和去重出错 |
| **ρ** | 被拒绝时，具体原因是什么？ | 输入被悄悄丢掉；报错只有"出了点问题" |

其中最糟的是悄无声息的那种：系统在没有任何依据的地方，给出一个笃定的答案。在语言模型里，这叫幻觉；在任何系统里，这都是一个无法被检查的决定。

MST-NF 把这四个答案显式化为四个角色。针对"决策系统"的几个精确模型，下列各项成立：
- **四个角色足够**表示任何决策函数 `C : E → Option X`（`completeness_theorem`），并且在可容许角色语言之内，一个候选的第五角色都能通过四角色 profile 分解，除非给出它的显式诊断见证（`roleRepresentation_iff_noDiagnostic`）；
- **没有哪一个是多余的**：对每个角色，都存在一个模型，其余三个成立而它不成立（`deleting_each_role_breaks_semantics`）；
- 两个 kernel-exact 且满射的商，**在同构意义下是同一个**（`kernel_exact_iso`），并且在所有合法分解中最粗（`canonical_is_coarsest`）。

所以，按这种方式建模的系统，可以展开成同样的四个部分，逐个检查；这是项目的实践，不是本仓库里的定理。对一个 core object，"它对不对"有封闭形式：当且仅当它的两类残差都为空，它才是 exact 的（`exact_iff_empty_residues`）。合取范式在逻辑里扮演类似的角色（仅是类比）。

## 为什么是范式，而不是设计

MST-NF 不是自上而下设计出来的。在项目的历史里，它起源于项目所有者在构建一门市场叙述描述语言时给出的一条要求（缩写 MST 在历史上指 Market Structure Theory，市场结构理论）：
- 描述必须客观、精准、诚实；
- 必须是纯推理，不容许任何统计上的容差（哪怕是 99.99% 也不接受）；
- 必须递归完备；
- 超出它的部分，必须明确标出：这里开始由人来判断。

项目笔记把开发的每一步都描述为"因为上一步达不到这条要求而被逼出来"，并且每一次用的都是同一条规则：找到残差，要求见证，能用定理吸收就吸收，否则给它命名，并开出最小的新层。把结果和其他领域搭桥时，发现它并不只关乎市场。笔记把这段历史上的推导描述为在人的引导下进行，AI agents 担任实现者和评审者；这段历史没有一条是本仓库的定理，其源仓库也未公开。

在项目自己的对应关系里，四个角色对应那条要求的各个部分：
- 商 `q` 与准入 `a`，对应功能角色"区分"（distinguish）与"约束"（constrain）；
- 精准（被接受的输入有代表元）对应 `σ`；
- 诚实与递归完备（被拒绝的输入有具名残差，绝不悄悄丢掉）对应 `ρ`。

作为一种编码，`σ` 和 `ρ` 可以合并成一个"结果"角色。理论证明的是关于独立诊断的事：合并后的角色不能再同时被独立诊断（`fused_roles_lose_independent_diagnostics`）。把四角色形式当作范式，是因为它让接受与拒绝保持对称；这是由该结果支持的设计决定，而不是一条单独的定理。

## 为什么是 for agents, by agents

**By agents：**AI agents 在人的引导和对抗评审下，参与了这个理论的开发和形式化（见上文）。

**For agents：**一个决定，只有能被检查，对别人才有用。在 MST-NF 模型里，只有被接受的类才有代表元（`representative_only_if_admitted`），每一个活跃（active）但未被接受的类都带有具名残差（`input_dichotomy`）。agent 的实际输出是否与它们绑定，是具体实例自己的义务：模型只要求结果取决于类（`quotientFactorization`）。这样使用时，agent 依然可能出错；模型提供的是：其中每一次拒绝都带有残差（`input_dichotomy`）。

旁边还有两个研究立场，它们不是本仓库的定理：洞见来自对已知信息的重分类，用 MST-NF 的话说，重分类就是残差吸收；以及，把该理论用在它自己的过程上，它永不封闭。对于后者，有一个关于抽象模型的形式陈述：没有任何 `GodelFramework` 能到达终止基（`T1_parametric_in_framework`）。哥德尔第二不完备定理只是以该结构的一个字段（`godel2`）进入，本仓库并没有重新证明它。

## 证明了什么，详情在哪里

上文点名的每一条陈述，都对应本仓库里的一条 Lean 4 定理（`evidence/claims_check.txt`）；公理和适用范围见 *Intents* 和 *What this does NOT claim*。完整的论证、每一条定理名，以及怀疑者会问的问题，见 [`docs/RATIONALE.md`](docs/RATIONALE.md)（中文：[`docs/RATIONALE.zh-CN.md`](docs/RATIONALE.zh-CN.md)）。

关于那条最初的要求本身，有三个问题仍未解决，本仓库不作宣称：
- 只从这条要求出发，自动化地重跑一遍，能否得到同一个范式；
- 这条要求本身是否最小；
- MST-NF 是否是它唯一能逼出的结构。

---

## 一段话说明理论

MST-NF 用四个结构角色来描述一个决策系统：商 **q**、准入谓词 **a**、代表元选择 **σ** 和有类型的残差 **ρ**。Lean 开发中定义了四个角色的义务（`ExecModel`、`hasMSTNFProfile`），并证明了 *Intents* 中列出的陈述：每个决策函数都有四部分分解（`completeness_theorem`）；没有哪个角色是多余的（`deleting_each_role_breaks_semantics`）；这四个角色作为独立诊断基是最小的（`standard_basis_is_minimal_independent_diagnostic_basis`）；两个 kernel-exact 且满射的商是同构的（`kernel_exact_iso`）；一个 core object 是 exact 的，当且仅当它的两类残差都为空（`exact_iff_empty_residues`）。全部内容都针对 Lean 4.14.0 与 Mathlib v4.14.0 做了机器检查；本 README 说明这一点确立了什么、没有确立什么；原始证据见 [`evidence/`](evidence/)。

## 仓库内容、Intents、清单与许可

"仓库内容"、"Intents"（定理表）、"来源"、"清单"和"许可"这几节只提供英文版，见 [README.md](README.md)。其余各节的中文翻译如下。

## 信任边界

* **工具链：**`leanprover/lean4:v4.14.0` 与 Mathlib `v4.14.0`（rev `4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84`，固定在 `lake-manifest.json` 中）。`MSTNFDefsPred` 不导入任何东西。
* **公理画像**（`scripts/AxiomAudit.lean` 覆盖全部 525 条定理，`evidence/axiom_audit.txt`）：没有用户 `axiom` 声明，没有 `sorry`，没有 `native_decide`（`Lean.ofReduceBool`）；399 条定理不使用任何公理，63 条使用 `propext`，30 条使用 `propext` 和 `Quot.sound`，6 条使用 `Quot.sound`，**27 条使用 `Classical.choice`**（22 条同时使用 `propext` 和 `Quot.sound`，4 条单独使用，1 条同时使用 `Quot.sound`）（`evidence/axiom_audit.txt`）。
* **`native_decide`：**本仓库中没有。`MSTNFConcreteAbstractEquivMWE` 的开发源码最初对三条桥接定理使用 `native_decide`；开发仓库现已改用 `decide`，因此由内核检查，陈述不变（`evidence/native_decide.txt`）。
* **内核复核**（`evidence/`）：
  * `lean4checker`（标签 `v4.14.0`，提交 `bee437b`）把这 27 个模块的每个常量重放到全新环境中，使用 Lean 内核：**27/27 通过**（`evidence/kernel_replay_per_module.txt`）。对 `MSTNFConcreteAbstractEquivMWE`、`MSTNFT1BridgeClosureMWE`、`MSTNF3Form4FormEquivMWE` 的 `--fresh` 重放（把它导入的全部常量，包括 Mathlib，重放到空环境中）退出码为 0。 对 `MSTNF3FormOmegaForcedProbeMWE`（它导入整个 `Mathlib.Tactic`）的 `--fresh` 重放因内核确定性超时（kernel deterministic timeout）而中止；这是资源上限，不是类型错误，对该模块的逐模块重放与 Nanoda 检查均通过。 它使用的是*同一个*内核；它能发现环境篡改和不可重放的声明，但它不是第二个内核。
  * **Nanoda**（`nanoda_lib` `v0.3.2`，提交 `66cca78`）是独立的 Rust 内核实现，它检查这 27 个模块的 1077 个定理和定义常量及其全部依赖的导出：**`Checked 3908 declarations with no errors`**（无错误），只允许 `propext`、`Classical.choice`、`Quot.sound`（`evidence/nanoda/`）。导出器是 `lean4export`（格式 2.0.0），带一个小补丁（限定 `HashMap`）以便在 Lean 4.14.0 上编译。
  * 反例对照：较早版本的 `MSTNFConcreteAbstractEquivMWE`（含 `native_decide`）被两个工具拒绝（`lean4checker`：`unknown declaration …_nativeDecide_1`；Nanoda：`unpermitted axiom "Lean.ofReduceBool"`）。
* **断言闸门**（`evidence/CLAIMS.json`，`evidence/rcc/claims_*`）：注册表列出 README 与 `docs/RATIONALE.md`（英文和中文）中陈述性质的句子及其引用的定理；检查程序确认每条被引用的定理都存在于本仓库，且陈述哈希与允许的公理与记录一致。它不检查句子是否不超出其定理；那一评审记录在 `evidence/audit/`。RCC 可执行程序对该断言图的结果是 **Closed**。对每条断言与其定理的独立评审记录在 `evidence/audit/`。
* **对 intents 的 RCC 闭合判定**（`evidence/rcc/`）：这些 intents 还在"intent 定理 → 假设 → 生产者"的义务图上运行过 RCC 可执行程序。非空洞读法（存在一个生产者表明假设可满足）：**11/11 Closed**。严格读法（生产者必须是泛型的）：**7 个 Closed，4 个 Await**。

## 本仓库不宣称什么

* **不宣称 Lean 4.14.0、Mathlib 或内核是正确的。**Nanoda 用第二个实现复核了内核的判定；两者实现的是同一套类型论，也都不检查一个陈述是否表达了它的文字描述。断言闸门只检查每个陈述性质的句子点名了陈述已被固定的定理；它不能代替人去读这些定理。
* **导出范围**是本仓库的 1077 个常量及其依赖，由一个为在 Lean 4.14.0 上运行而打过补丁的导出器生成；导出器或检查器自身的缺陷不在这里验证的范围内。
* **充分性是有边界的。**无第五角色的陈述，在其模块的可容许角色语言之内成立。它的封闭实例（`noIndependentFifth_for_coreProfile`）按定义成立，`MSTNoFifthRoleIntegrationMWE` 只覆盖 profile 已经蕴含的候选。两者都不证明将来不会有理论加入一个独立维度。
* **最小性是相对的。**它是独立诊断能力的最小性，不是任意编码的最小性。该定理的签名里有一个 `complete B` 假设，证明并没有使用它。
* **profile 不是安全性保证。**`hasMSTNFProfile` 并不蕴含每个类至多有一个原始输入被接受（`AtMostOneAdmit`，一个单独的条件），也不把系统的输出与代表元或残差绑定。
* **有条件的、针对特定模型的陈述。**`sameClass_sameOutcome` 需要 `quotientFactorization`；exactness 定理针对 `CoreObject`，完备性陈述针对决策函数 `C : E → Option X`，profile 陈述针对 `ExecModel`。本仓库没有给出这三个模型之间的单一映射。
* **哥德尔墙结果针对的是抽象模型。**哥德尔定理以 `GodelFramework` 的字段 `godel2` 进入，没有被重新证明；对每个自应用算子都成立的形式不作宣称；弱框架的情形是一个恒为假的步关系。
* **fixture 是有限的。**conformance 和 concrete↔abstract 定理检查的是有限 fixture，并不说明某个运行时实现是正确的。一些模块注释中提到的 Python 与 OCaml 适配器不属于本仓库。
* **RCC 判定是一致性证据，不是独立证明。**提取器与实例数据由与该理论相同的一方产生；复现它们需要 RCC 库，本仓库不含它。
* **历史与研究立场不是定理。**起源故事、幻觉分类、"重分类即收敛"、"这个形式让任何系统都能展开成四个部分并用同一种证明形状"的说法，以及关于 Residua 的陈述，都是项目自己的，这里没有一条被检查。
* **应用不在范围内**（市场结构、缠论、DeFi、CRT/IET 接缝模块、自动生长），较早的 pre-NF 表述也不在范围内。
* **`closure_claim = 0`。**这里没有任何内容说 MST-NF 或基于它构建的任何系统是"闭合的"。

## 复现

```sh
# 安装 elan: https://github.com/leanprover/elan
lake exe cache get                # Mathlib oleans（可选；否则 Mathlib 从源码构建）
lake build                        # 构建 MSTNFDefsPred 和 MSTNF；预期退出码 0
lake env lean scripts/PrintAxioms.lean   # 各 intents 的公理
lake env lean scripts/AxiomAudit.lean    # 全部定理：用户公理、sorry、native_decide、Classical.choice
CLAIMS=evidence/CLAIMS.json lake env lean scripts/ClaimsCheck.lean   # 每条断言都能解析；预期 failures = 0
# 内核重放（同一个内核，能发现环境篡改）：
git clone --branch v4.14.0 https://github.com/leanprover/lean4checker && (cd lean4checker && lake build)
for m in $(cat scripts/modules.txt); do lake env lean4checker/.lake/build/bin/lean4checker "$m"; done
# 独立内核（Nanoda）：见 evidence/nanoda/README.md
sha256sum -c MANIFEST.sha256      # 内容寻址清单
```

（在某些 macOS 版本上，编译好的 `lake exe cache get` / `lean4checker` 二进制会在 `dyld` 中中止；可以解释执行，例如 `lake env lean --run lean4checker/Main.lean <模块>`。）

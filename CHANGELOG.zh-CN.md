# 更新日志

本仓库的每一次发布，按时间倒序。日期为 UTC；每条注明它在 `main` 上的提交。声明编号见 `evidence/CLAIMS.json`。

## 2026-11-26：关系型 hop、观察序、运行时结果
提交 `a0500ee`、`e40d3f1`。`MSTNF/algorithms/` 新增模块：`MSTNFRelationalHopMWE`、`MSTNFForwardBackwardMWE`、`MSTNFRuntimeRefinementMWE`、`MSTNFObservationMWE`、`MSTNFObservationHopMWE`、`MSTNFObservationRuntimeMWE`。
- C50 ExecModel 上的关系型 hop：以结果关系表述的正确性、它的组合、布尔桥。
- C51 对全部结果的前向正确性，在目标确定时给出后向方向。
- C52 运行时结果把值、拒绝原因和资源上限区分开。
- C53 观察序：投影按商构成信息类的格。
- C54 hop 正确性可以迁移到更粗的观察类。
- C55 观察者可以提升到完整的运行时结果。
共 58 条定理；等式组合律 `hop_seq_correct` 作为关系型组合律的特例推出。没有新增 `Classical.choice`。

## 2026-11-24：资源充分性
提交 `76d15f0`、`2d7a7de`。`MSTNFResourceAdequateMWE`。
- C49 带时钟 hop 的资源充分性（H-progress）：精确形式更强，两种形式都能经可行域像条件顺序组合，见证给出 H-witness 的形状。

## 2026-11-24：组合、hop 与递归
提交 `e2f0640`、`65e0cfd`、`996f353`、`921f434`。ExecModel 上的和、积、顺序与至多一次组合（`MSTNFComposition*`）；hop 正确性、它的组合以及递归组合律（`MSTNFHop*`、`MSTNFRecComposeMWE`）；审计、声明检查和公理清单扩展到这些模块。

## 2026-11-22：R2
提交 `3aee6a2`。活跃类剖面、定律 P1 至 P9、PreKey 与 Reason 两层、有限实例、Cedar 桥（`MSTNF/r2/`）。

## 2026-10-30：choice 普查
提交 `11afc15`、`780f25b`、`559f693`、`9cf3fda`。P1-B 分解改为在内核商上陈述；从 6 个声明中去掉附带的 `Classical.choice`（其余 19 个 choice 定理列在公理普查中）。

## 2026-10-24：1.0
提交 `a142e6a`、`1ee4043`。决策系统的四角色规范形（Lean 4.14.0）。

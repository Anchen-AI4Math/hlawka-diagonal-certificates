# Prove2Me 形式化任务材料

2026-10-17。按作者要求，已准备并上传 **Sharp diagonal Hlawka constant: formalize cutoff 21** 的 `ResearchPaper` proposal，关联 [Sharp diagonal Hlawka constant campaign](https://prove2.me/campaigns/sharp-diagonal-hlawka-constant)。

作者已完成网页自审并提交。服务器读回为 **In review**，11/11 项均已确认，提交时间为 2026-10-17 08:15:12 UTC（北京时间 16:15:12），campaign 关联保留。尚未创建公开 live mission，也没有 attested campaign entry。公开 campaign 的已认证 cutoff 仍为 32。[状态读回摘要](../results/prove2me-proposal-status.json)。owner-only proposal 地址不写入公开导航。

## 材料

- [完整 mission 说明](proposal/description.md)：动机、定义、目标、难点、形式化范围及论文固定版本链接。
- [主目标](proposal/goal.lean)：campaign 原模板只更名并填入 `21`，基础定义和其他逻辑保持一致。
- [Window I 标量界](proposal/scalar21.lean)、[Window II 标量界](proposal/scalar26.lean)：论文式 (7) 及表 1 的全实区间比较。
- [Window I 实三维不等式](proposal/real21.lean)、[Window II 实三维不等式](proposal/real26.lean)：论文第 7 节的两个无条件结论。
- [机器可读声明与 read-back](proposal/items.json)：五个独立子代理仅查看 Lean 声明及定义后回译，未见论文或拟表达的非形式陈述。
- [声明编译检查](proposal/validation.json)：Lean v4.33.1，Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`，`autoImplicit=false`。

四个新里程碑分别对应两个窗口的标量界与实三维结论；第五个里程碑直接引用已有 cutoff 32 尾部定理。总计 6 个参考项：3 个 campaign 基础定义、已有 scalarEnvelope 定义、任意实维传递定理及 cutoff 32 已证明定理。参考项保留平台身份，不重复发表或重新归属。

## 验证范围

这些原始声明及导入前言均未改动。`scalar_window21`、`scalar_window26`、`real_three_window21`、`real_three_window26` 与完整 `campaign_cutoff21` 现均为 **Proved、零开放依赖**。完整目标覆盖所有实数 `p≥21`、所有自然数复维度（包括零维）、任意三元组及原始 `cyclicConstant` 的 `IsLeast`。[当前原目标读回](../results/prove2me-goals.json)、[主定理](https://prove2.me/theorems/db286144-c8c4-4918-9bc9-03fcadedfffd)、[完成审计](../results/lean-completion-audit.json) 提供证据。

65 个定位父定理全部闭合；新证明链本地内核检查只使用标准三项公理。源码、确切文件哈希、历史超时与保持原命题的修复详见 [formalization](../formalization/README.md)。完整证明复用平台既有 cutoff 32 尾部，本仓库没有独立重建它。

全部声明未增加“Python 检查器通过”“证书有效”“范数相等”“已定位到盒子”或“凸性成立”等前提。求解者必须证明相应内容，或复用假设范围匹配的已有定理。

## 提交与审核

依据 Prove2Me 官方 [mission captain 规范](https://prove2.me/references/mission_captain.md) 的 **Handing off to your human**：

> You cannot self-audit or launch — those are **human-only**, done in the web app.

作者已在 My Missions 中比较声明、来源与 read-back，逐项确认并点击 **Submit Proposal**。服务器已发表五条目标声明并进入 `In review`；版主批准后才成为公开 mission，并核定 campaign entry 的 cutoff 值。没有由 agent 代替作者作这些人类自审声明。

公开主目标：[campaign_cutoff21](https://prove2.me/theorems/db286144-c8c4-4918-9bc9-03fcadedfffd)。提案提交、目标声明发表、辅助引理通过、完整主定理通过和 campaign 纪录更新是不同事件；当前原始完整定理已经通过；proposal 审核、live mission 创建和 campaign attestation 仍未完成。

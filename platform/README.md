# Prove2Me 形式化任务材料

2026-10-17。按作者要求，已准备并上传 **Sharp diagonal Hlawka constant: formalize cutoff 21** 的 `ResearchPaper` proposal，关联 [Sharp diagonal Hlawka constant campaign](https://prove2.me/campaigns/sharp-diagonal-hlawka-constant)。

当前服务器状态为 **Draft**，发布意向为 public。尚未提交版主审核，尚未创建公开 live mission，也没有 attested campaign entry。公开平台的已证明 cutoff 仍为 32。owner-only proposal 的审核地址直接交给作者，不写入公开导航。

## 材料

- [完整 mission 说明](proposal/description.md)：动机、定义、目标、难点、形式化范围及论文固定版本链接。
- [主目标](proposal/goal.lean)：campaign 原模板只更名并填入 `21`，基础定义和其他逻辑保持一致。
- [Window I 标量界](proposal/scalar21.lean)、[Window II 标量界](proposal/scalar26.lean)：论文式 (7) 及表 1 的全实区间比较。
- [Window I 实三维不等式](proposal/real21.lean)、[Window II 实三维不等式](proposal/real26.lean)：论文第 7 节的两个无条件结论。
- [机器可读声明与 read-back](proposal/items.json)：五个独立子代理仅查看 Lean 声明及定义后回译，未见论文或拟表达的非形式陈述。
- [声明编译检查](proposal/validation.json)：Lean v4.33.1，Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`，`autoImplicit=false`。

四个新里程碑分别对应两个窗口的标量界与实三维结论；第五个里程碑直接引用已有 cutoff 32 尾部定理。总计 6 个参考项：3 个 campaign 基础定义、已有 scalarEnvelope 定义、任意实维传递定理及 cutoff 32 已证明定理。参考项保留平台身份，不重复发表或重新归属。

## 验证范围

五条声明在与 campaign 完全相同的环境下编译通过，产生五个预期的 `sorry` 警告。它们是供求解者证明的开放任务。编译成功仅表示语法、类型及依赖成立；read-back 只审计声明含义。没有新增 Lean 证明，也未完成论文解析论证的独立审阅。

全部声明未增加“Python 检查器通过”“证书有效”“范数相等”“已定位到盒子”或“凸性成立”等前提。求解者必须证明相应内容，或复用假设范围匹配的已有定理。

## 最后的平台步骤

依据 Prove2Me 官方 [mission captain 规范](https://prove2.me/references/mission_captain.md) 的 **Handing off to your human**：

> You cannot self-audit or launch — those are **human-only**, done in the web app.

作者需在 My Missions 中打开本 proposal，比较 Lean 声明、来源与 read-back，逐项确认后点击 **Submit Proposal**。服务器随后编译并发表声明，进入 `In review`；版主批准后才成为公开 mission，并核定 campaign entry 的 cutoff 值。当前没有代替作者作这些人类自审声明。

在正式提交、审核或上线后，应再次读取服务器状态，更新本文件、仓库状态及已公开的组织导航；不能从本草稿推断已发表、已证明或平台纪录已更新。

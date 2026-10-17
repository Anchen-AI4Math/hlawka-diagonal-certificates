# Lean 工作交接：保留完整 cutoff 21 目标

完成标准是原始 [campaign_cutoff21](https://prove2.me/theorems/db286144-c8c4-4918-9bc9-03fcadedfffd) 的准确声明为 `Proved` 且开放依赖为零。范围包括每个实数 `p≥21`、所有自然数维度（含零维）、任意复向量三元组，以及原始 `cyclicConstant` 的 `IsLeast`。不能以部分结果代替。

## 本地数学链已接通

[完整新证明链](../results/lean-full-window-build.json) 为 PASS，记录 639 个源码哈希和 601 项公理检查，公理只有 `propext`、`Classical.choice`、`Quot.sound`。`Theorems/` 镜像导入实际证明，没有用 `sorry` 代替依赖。

- `CoarseFailure21/26` 从任意严格实三维反例完成归一化、定向与粗定位；不要求输入非零、等范数或预先定向。
- `Localized21/26` 全部 256 段、768 个根界整数幂证书通过；从实际原始范数推出十轮收缩、范数 cap、pair/offsum floors，局部输入不再是抽象 `Facts`。
- `GroupedGeometry/Curvature/Convexity/Nonneg` 完成实际范数 cap 下的 Hessian、沿线凸性、同时置换轨道平均及非负性，两组域覆盖 `[21,377/16]`、`[377/16,32]`。
- `RealWindows` 证明两个原始无条件实三维窗口。`ComplexBridge` 完成任意有限复维度传递与最小性，包含零维。
- `FullWindow.campaign_cutoff21_from_tail` 证明准确的最终结论，显式输入平台既有 cutoff 32 尾部。该尾部在平台已 Proved，本仓库没有独立重建其完整证明。

这些已通过的数学步骤不是当前缺口。原始 `sources/*.lean` 保持字节不变；改编与归属记录于 [Foundation provenance](../formalization/Hlawka21/Foundation/provenance.json)。

## 平台闭合与最终证据

**原始完整主目标已完成：`Proved`、零开放依赖。** 两个原始标量窗口、两个原始无条件实三维窗口均为 `Proved`、零开放依赖；[全目标读回](../results/prove2me-goals.json) 核对原始声明与导入前言未改变。

实际反例归约、分段定位、曲率、凸性、对称平均和所有有限复维度的最小性传递均已通过。65 个定位父定理覆盖原 256 段，全部平台闭合。原始 16 段及 8 段大包的超时仍保留为历史；四段方案中另有 4 个父目标通过 8 个更小子区间和同一父命题的拼接证明闭合。没有重复上传相同失败文件或修改目标范围。

本地精确文件检查与平台接受记录分别保留：[65 份原文件](../results/lean-domain-blocks-build.json)、[父目标闭合](../results/prove2me-domain-blocks.json)、[子证书](../results/prove2me-domain-children.json)、[修复证明](../results/prove2me-domain-repairs.json)。修复后采用的源文件也独立经过本地内核检查。

两个窗口的接口检查使用 41、24 个显式证书参数；可逆标识符替换核对其证明体与服务器文件一致。这些接口检查是条件性检查，不能单独替代实际 `RealWindows` 无条件证明；后者及全部定位证书已分别核验。可选逐文件镜像导入实际证明；已停止并移除重复展开全部证明的慢速聚合镜像，没有以 `sorry` 或新公理替代。

[主目标记录](../results/prove2me-root.json) 中 `SKETCH_ACCEPTED` 是历史提交判决；其依赖闭合后，当前原始定理已 `Proved`、零开放依赖，无需为改变历史标签重复提交。[完成审计](../results/lean-completion-audit.json) 核对原始目标、精确源文件、完整区间覆盖、全部依赖及数值回放。完整平台证明使用已有 `campaign_cutoff32`；未声称独立重建尾部或完成独立解析审阅。

## 环境和操作约束

固定 Lean v4.33.1 / Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`，`autoImplicit=false`。复现命令见 [formalization/README.md](../formalization/README.md)。默认检查重新执行；`--reuse` 仅复用同环境和同源码哈希的 PASS。Windows 上限制并发进程，避免全库同时构建。

每次提交验证精确文件哈希，异步任务轮询原句柄；观察超时不是服务器终态。不要因本地 PASS 提升完整平台状态，不修改原始目标假设以缩小范围。论文 proposal、live mission、campaign attestation 与证明状态分别记录。

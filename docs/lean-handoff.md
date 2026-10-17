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

## 平台闭合与当前缺口

两个原始标量窗口和原先 32 个辅助定理已获平台接受。新增的任意反例粗定位两个窗口、两组公共解析域非负性、通用复数最小性传递均读回 Proved、零开放依赖。见 [反例归约](../results/prove2me-failure.json)、[公共分析与传递](../results/prove2me-analytic-assembly.json)。

单段实际范数定位 `actual_localize21_slab000` 也已 ACCEPTED，读回 Proved、零开放依赖：[记录](../results/prove2me-localization.json)。因此平台有限算术路线可行，不能把编译超时理解为数学反例。

首批 16 段打包和随后 8 段打包的前三个提交均超出服务器 300 秒限时。保留 ERROR 历史，不重复上传原文件。8 段方案共 33 份，本地批量检查已中止并保留 11 个精确文件 PASS；不能称为全部通过或“固定剩余 36 项”。

首个 4 段组合已在平台 Proved、零开放依赖；当前逐批核验和提交 4 段一组的实际范数定位，只导出公共解析域所需的显式有理界，不导入解析定理。`domain-blocks.json` 检查所有 256 段恰好覆盖一次且端点无缝；其本地精确文件检查与平台判决必须分别读取，不能从已生成源文件推断通过。复杂证明不能藏入 Definition 文件绕过平台限制。

全部 65 份原始四段文件已通过精确本地检查。个别平台超时保持原父声明，通过两个更小子区间独立证明再组合修复；三个初始超时块已全部修复。两个窗口的组合层已使用 41、24 个显式证书参数通过检查，证明体可逆替换回最终服务器文件；这项条件接口检查不改变已通过的无条件 `RealWindows` 证明。重复编译 65 个边界包装的聚合 API 已停止并移除；可选镜像仍导入各自的实际证明。平台只有在对应完整覆盖全部闭合后才提交原窗口。

原始 real_three_window21 已 Proved、零开放依赖；real_three_window26 和最终主目标尚未闭合，见 [原目标读回](../results/prove2me-goals.json)。后续须将完整 `[21,32]` 的闭合证书与公共解析定理、任意反例归约连接，再通过已闭合的复数桥接与 cutoff 32 尾部关闭原始主目标。`prepare_real_window_platform_proofs.py` 已接入 65 份四段定位及两组已闭合解析定理；原始主目标组合已获 SKETCH_ACCEPTED，目前仅原始 real_three_window26 依赖待闭合，见 [主目标记录](../results/prove2me-root.json)。

## 环境和操作约束

固定 Lean v4.33.1 / Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`，`autoImplicit=false`。复现命令见 [formalization/README.md](../formalization/README.md)。默认检查重新执行；`--reuse` 仅复用同环境和同源码哈希的 PASS。Windows 上限制并发进程，避免全库同时构建。

每次提交验证精确文件哈希，异步任务轮询原句柄；观察超时不是服务器终态。不要因本地 PASS 提升完整平台状态，不修改原始目标假设以缩小范围。论文 proposal、live mission、campaign attestation 与证明状态分别记录。

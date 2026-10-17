# Lean 工作交接：保留完整 cutoff 21 目标

当前目标是完成原始全维复数 `campaign_cutoff21`，并通过 Prove2Me。其断言对每个实数 `p≥21`、所有自然数维度 `n`，`cyclicConstant p` 是统一最小 Hlawka 常数，包含 `n=0`、零向量和不等 singleton 范数。主目标仍为 `Open`，不能以本文列出的部分结果替代完成。

## 已核验的当前边界

- [scalar_window21](https://prove2.me/theorems/2b5def5c-82ab-4480-bbcb-1d11f05b7cbe)、[scalar_window26](https://prove2.me/theorems/bfa2ef01-7ed9-4ac2-93ec-ace2d0624fda)：均 `ACCEPTED` / `Proved`，开放叶子均为零。五条原始声明与上传版本逐项比较一致。
- 两个实三维窗口与主目标仍 `Open`，见 [原目标读回](../results/prove2me-goals.json)。Proposal 为 `In review`，live mission 尚未创建，campaign 正式已证明 cutoff 仍为 32。
- 27 个辅助证明已获平台 `ACCEPTED`，包括两阶段 LP、实际范数的粗定位连接、残差、解析上界、envelope 与 16 个标量下界区间。
- [标量构建](../results/lean-scalar-build.json)：两个完整实区间，256 段、768 个整数幂证书。其 Bernoulli 路线已接回原始标量声明。
- [收缩构建](../results/lean-contraction-build.json)：256 段十轮条件收缩全部通过。此结果仍以显式 `Facts` 和初始 singleton 下界为前提，不是无条件实三维 Hlawka 结论。
- 原始参考 `sources/*.lean` 未改动；这里只重用并编译了需要的通用部分，没有声称独立重建完整 cutoff 32 尾部。

## 下一段证明链

1. **归一化与定向。** `sources/coarse32.lean` 中 `scaled_failure`、`signed_conflict`、`oriented_core` 给出可参考的结构。新窗口常数必须使用原 profile。`CoarseConnection21/26` 已从真实范数、归一化、定向 loss 和线性 failure 条件推出粗盒子，但尚需从任意反例建立这些条件。
2. **实际范数的收缩。** `ContractionFacts.facts_of` 已证明实际 `lpNorm` 数据到通用 `Facts` 的连接，给定每段根界、预算和 refined tail。`RefinedTail` 已证明两个窗口的实际 pair 范数尾项，Window I 明确保留总范数 cap。剩余每段三类根界可用 `ContractionCore.le_rpow_of_pow_le` / `rpow_le_of_pow_le` 变成整数幂比较，再调用 `Window21/Slab*.lean` 与 `Window26/Slab*.lean`。
3. **范数 cap 下的 Hessian。** `sources/convex_box32.lean` 前约 425 行包含通用微分和 residual 极小点工具；其中 `normHessian_lower_generic` 使用较弱坐标盒范数估计，需要改为本文的实际 singleton cap `U`、总范数 cap `A`。`normHessian_upper_canceled` 已参数化主坐标与尾坐标。不要把硬编码 cutoff 32 的凸盒定理直接当作新窗口定理使用。
4. **几何与曲率。** 保留 pair 主坐标 floor `J` 和 offsum floor `W0`，证明径向系数差的 shape 界及 Young 组合。`PairResidual.matrix_pair_residual_bound` 的六项顺序为 `(k,i)=(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)`。Window I 系数为 `(7/4+2η/L)^2`；Window II 的证书使用 16。还需把该矩阵估计与实际 residual 分解接起来。
5. **凸域和平均。** 使用 norm 次水平集及线性 floors；`N0+N1+N2=3` 只用于推导，不保留为凸域约束。证明置换不变性、平均的 cyclic 参数范围与 deficit 非负，再关闭两个无条件实三维目标。
6. **全维复数和最优性。** 复用已证明的 `real_bound_of_fin_three`、cyclic sharpness 和 cutoff 32 尾部；必要时提取 `sources/solution32.lean` 的通用 circle-transfer 论证。最终核验全维主目标实际 `Proved` 且无开放依赖。

## 已定位的同环境基础定义

- [BoxHessian](https://prove2.me/theorems/67a497f7-8a7d-4f4f-acfa-d289c97ffb1a)：`deficitHessian`。
- [BoxConvexity](https://prove2.me/theorems/149cc404-d435-4c1c-a983-20fc6a0ef285)：`deficitSlope`。
- [ComplexTransfer](https://prove2.me/theorems/1cf7bb14-a189-4df6-b9d5-0fd9d8e16714)：seven-vector power deficit 与 circle projection。通用维数传递定理 ID 为 `9face38e-b769-47bf-99b7-b0ab3a1f86bc`；复数 cyclic lower obstruction ID 为 `ac90dc0a-6fc9-4328-bd21-da91445892b9`。

这些是原项目的定义与定理，保留来源和署名；使用时核对其当前状态、环境及假设。它们不是新窗口已完成的证据。

## 构建与提交约束

固定 Lean v4.33.1 / Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。完整复现命令在 [formalization/README.md](../formalization/README.md)。默认重放不信任已提交报告；`--reuse` 是显式缓存选项。

本地 `Theorems/` 文件导入实际已编译的证明，没有用 `sorry` 代替依赖。平台提交前须检查确切文件哈希；每个已提交异步句柄应继续轮询，不因观察超时而重复上传。Windows 上逐个构建 theorem mirror，避免同时打开过多 Lean 文件映射。

两条旧的 if 形式粗定位目标曾触发平台目标类型检查的语法错误；等价的“对角界与非对角界分开”表述已被接受，旧条目可逆退休并保留历史。原始五条 mission 声明没有因此改变。

# Cutoff 21 的 Lean 形式化

这里保存实际证明。主目标仍是：对每个实数 `p≥21`，`cyclicConstant p` 是所有有限复维度的统一最小 Hlawka 常数。当前只完成部分辅助引理，没有关闭该主目标。

环境与 Prove2Me campaign 相同：Lean **v4.33.1**，Mathlib **0df444a360eaa60ab8c11dca51a86af692955474**，`autoImplicit=false`。

| 已证明部分 | 源文件 | 范围 |
|---|---|---|
| 两个窗口的精确粗定位 | [Coarse21](Hlawka21/Coarse21.lean)、[Coarse26](Hlawka21/Coarse26.lean) | 四组 LP 蕴含，合计 72 个线性结论；从明确列出的有理线性前提证明结论 |
| 扰动能量估计 | [Residual](Hlawka21/Residual.lean) | 任意有限指标集，含 `rho=0`；证明系数 `3+7*rho+4*rho²` 及其有理放宽 |
| 六个 pair 残差的矩阵估计 | [PairResidual](Hlawka21/PairResidual.lean) | 从九个任意实矩阵分量与六个有界 theta 系数，证明论文式 (34) 的能量界 |

以上六个辅助定理均已获 Prove2Me `ACCEPTED`。所有公开定理 ID 及验证句柄见 [服务器验证记录](../results/prove2me-auxiliary.json)。每个记录对应 [platform](platform/) 中一个独立、完整的 `theorem solution` 文件；[编译报告](../results/lean-auxiliary-build.json) 保存确切文件哈希和公理审计结果，全部仅依赖 `propext`、`Classical.choice`、`Quot.sound`。

LP 生成器读取原始 profile 与对偶证书，用其选择线性前提，再由 Lean 的 `linarith` 构造内核可检查的证明；证书和外部数值求解器不是公理。当前仍需从原始范数问题证明这些 LP 前提。残差矩阵估计也未代替完整 Hessian、凸性与平均论证。

首次构建：

```powershell
cd formalization
lake update
lake exe cache get
lake build
```

回到仓库根目录，重新生成并检查平台提交文件：

```powershell
python scripts/generate_coarse_lean.py
python scripts/prepare_platform_proofs.py
python scripts/check_lean_proofs.py
```

检查器优先使用已安装的固定版本工具链，并核对 Mathlib revision。当前机器曾使用同一固定版本的隔离构建目录 `.test-tmp/prove2me/lean`；该缓存不提交到仓库。编译报告是当前环境中的构建记录，不是独立复验。

完整剩余工作见 [下一步](../docs/next-steps.md)。平台五个开放目标仍在 [任务材料](../platform/README.md) 中；其中声明的 `sorry` 占位不能作为证明使用。

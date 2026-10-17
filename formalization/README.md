# Cutoff 21 的 Lean 形式化

这里保存实际证明。主目标仍是：对每个实数 `p≥21`，`cyclicConstant p` 是所有有限复维度的统一最小 Hlawka 常数。两个原始标量里程碑已关闭；两个实三维窗口及该全维主目标仍未关闭。

环境与 Prove2Me campaign 相同：Lean **v4.33.1**，Mathlib **0df444a360eaa60ab8c11dca51a86af692955474**，`autoImplicit=false`。

| 已证明部分 | 源文件 | 范围 |
|---|---|---|
| 原始标量里程碑 `[21,26]`、`[26,32]` | [Window I](platform/Sol_scalar_window21.lean)、[Window II](platform/Sol_scalar_window26.lean) | 两条原始声明未改动，均获平台 `ACCEPTED` / `Proved`，开放依赖为零 |
| 标量下界、上界与 envelope | [FixedWitness](Hlawka21/FixedWitness.lean)、[CyclicUpper](Hlawka21/CyclicUpper.lean)、[Envelope](Hlawka21/Envelope.lean) | 全实区间；256 段合计 768 个整数幂证书；[证明说明](../docs/lean-scalar.md) |
| 两个窗口的精确粗定位 | [Coarse21](Hlawka21/Coarse21.lean)、[Coarse26](Hlawka21/Coarse26.lean) | 四组 LP 蕴含，合计 72 个线性结论；从明确列出的有理线性前提证明结论 |
| 原始范数到粗盒子的连接 | [Window I](Hlawka21/CoarseConnection21.lean)、[Window II](Hlawka21/CoarseConnection26.lean) | 从已归一化、已定向的真实范数数据，经两个 LP 阶段和半尾项估计得到坐标盒；两条平台表述均已接受 |
| 实际 pair 范数的精化尾项 | [Tail](Hlawka21/Tail.lean)、[RefinedTail](Hlawka21/RefinedTail.lean) | 包含零主坐标；Window I 的裁剪明确使用总范数上界 |
| 256 段十轮条件收缩 | [通用步骤](Hlawka21/ContractionRounds.lean)、[范数桥接](Hlawka21/ContractionFacts.lean) | 全部逐段内核检查；尚需组合每段根界与预算，接成无条件定位，再完成 Hessian 和平均论证 |
| 扰动能量估计 | [Residual](Hlawka21/Residual.lean) | 任意有限指标集，含 `rho=0`；证明系数 `3+7*rho+4*rho²` 及其有理放宽 |
| 六个 pair 残差的矩阵估计 | [PairResidual](Hlawka21/PairResidual.lean) | 从九个任意实矩阵分量与六个有界 theta 系数，证明论文式 (34) 的能量界 |

27 个辅助定理均已获 Prove2Me `ACCEPTED`，另有两个原始标量里程碑获 `ACCEPTED` / `Proved`。见 [辅助记录](../results/prove2me-auxiliary.json)、[里程碑记录](../results/prove2me-milestones.json) 和 [五个原目标的服务器读回](../results/prove2me-goals.json)。两个平台未接受的旧粗定位表述已可逆退休，并链接到等价且已接受的对角/非对角分开表述；历史记录保留。

每个接受记录对应 [platform](platform/) 中的完整 `theorem solution` 文件。[辅助编译报告](../results/lean-auxiliary-build.json) 与 [里程碑编译报告](../results/lean-milestone-build.json) 保存确切文件哈希，公理均只有 `propext`、`Classical.choice`、`Quot.sound`。本地 `Theorems/` 镜像导入实际已编译证明，没有用 `sorry` 声明代替平台依赖。

LP 生成器读取原始 profile 与对偶证书，用其选择线性前提，再由 Lean 的 `linarith` 构造内核可检查的证明；证书和外部数值求解器不是公理。当前仍需从任意反例完成归一化和定向，并将收缩、Hessian、凸域和平均过程接起来。条件收缩和残差矩阵估计均未代替完整实三维证明。

首次构建：

```powershell
cd formalization
lake update
lake exe cache get
lake build
```

回到仓库根目录，完整重放新增有限证书：

```powershell
python scripts/check_contractor_lean.py --jobs 2
python scripts/check_scalar_lower_lean.py --jobs 2
```

重新生成并检查全部平台证明及原始标量里程碑：

```powershell
python scripts/prepare_platform_proofs.py
python scripts/prepare_analytic_platform_proofs.py
python scripts/prepare_scalar_platform_proofs.py
python scripts/check_lean_proofs.py --jobs 2
python scripts/build_theorem_mirrors.py
python scripts/check_lean_proofs.py --manifest formalization/platform/mission-proofs.json --output results/lean-milestone-build.json --jobs 2
```

这些检查器默认重新执行本地检查；`--reuse` 是显式复用匹配哈希的既有记录，不是独立复验。检查器优先使用已安装的固定版本工具链，并核对 Mathlib revision。当前机器曾使用同一固定版本的隔离构建目录 `.test-tmp/prove2me/lean`；缓存不提交。Windows 上应限制同时运行的 Lean 进程数，镜像构建脚本逐个调度。

完整剩余工作见 [下一步](../docs/next-steps.md)。原始五个目标中只有两个标量目标已证明；另三个仍为开放任务。[任务材料](../platform/README.md) 的声明占位只描述目标，不能作为证明使用。

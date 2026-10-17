# Cutoff 21 的 Lean 形式化

持续目标是原始 `campaign_cutoff21`：对每个实数 `p≥21`，`cyclicConstant p` 是所有有限复维度的统一最小 Hlawka 常数，包含 `n=0`、零向量和不等范数三元组。**完整平台主目标仍未关闭。**

固定环境：Lean **v4.33.1**，Mathlib **0df444a360eaa60ab8c11dca51a86af692955474**，`autoImplicit=false`。

| 证明部分 | 当前证据 |
|---|---|
| 两个原始标量里程碑 | 平台 `Proved`，开放依赖为零；[原目标读回](../results/prove2me-goals.json) |
| 任意严格实三维反例到粗盒子 | 两个平台定理 `Proved`，开放依赖为零；[完整证明与记录](../results/prove2me-failure.json)；输入没有归一化、定向、非零或等范数假设 |
| 256 段实际范数定位 | [全部 PASS](../results/lean-localization-build.json)，含 768 个根界整数幂证书、十轮收缩和线性 pair/offsum floors；不再以抽象 `Facts` 为输入 |
| 范数 cap 下的 Hessian、凸性与对称平均 | [两组域构建报告](../results/lean-geometry-build.json)；参数区间 `[21,377/16]`、`[377/16,32]`；两组公共域定理已获平台接受 |
| 两个原始无条件实三维窗口 | [RealWindows](Hlawka21/RealWindows.lean) 已本地内核检查；平台原目标仍 `Open` |
| 任意有限复维度传递及最小性 | [通用桥接](Hlawka21/ComplexBridge.lean) 本地通过且平台 `Proved`、开放依赖为零；[平台记录](../results/prove2me-analytic-assembly.json) |
| 全范围最终拼接 | [FullWindow](Hlawka21/FullWindow.lean) 本地证明准确的 cutoff 21 结论，显式输入既有 cutoff 32 尾部；[639 个源码哈希、601 项公理检查](../results/lean-full-window-build.json)；尾部未独立重建，原始平台主目标组合已获 `SKETCH_ACCEPTED`，仍有两个实三维窗口依赖 |

目前 59 个辅助定理获平台 `ACCEPTED`，另有两个原始标量里程碑 `Proved`。计数与新增证书的异步状态分别见 [status.json](../status.json)、[原辅助记录](../results/prove2me-auxiliary.json)、[任意反例归约](../results/prove2me-failure.json)、[公共解析及传递](../results/prove2me-analytic-assembly.json)、[紧凑证书](../results/prove2me-real-pieces.json)。这不表示原始全维主目标已经通过。

## 平台提交为何拆分

最初 16 份自包含大文件均在本地通过，但首批 3 份约 500 KB 的文件触发了平台 300 秒超时，见 [本地精确文件检查](../results/lean-real-platform-build.json) 和 [服务器记录](../results/prove2me-real-chunks.json)。保留这些记录，不能把超时改写为已接受。

公共 Hessian、凸性和平均论证已提取为两条闭合的平台定理。第二版有限证书各覆盖至多 8 段，共 33 份、无缝覆盖原 256 段，但首批三个提交也触发了 300 秒超时；[批量本地检查](../results/lean-real-pieces-build.json) 已中止并保留 11 个精确文件通过记录。因此 33 不是固定剩余定理数，也不能据此估计完成时间。

不导入解析定理的单段实际范数定位已获平台 `ACCEPTED`，读回 `Proved`、零开放依赖：[精确文件通过](../results/lean-localization-platform-build.json)，[平台异步任务](../results/prove2me-localization.json)。65 份四段组合无缝覆盖全部 256 段，原始提交文件已[全部通过本地精确检查](../results/lean-domain-blocks-build.json)。平台仍逐批验收这些定位定理；部分超时块通过更小子区间证明修复，不能称为所有原始文件均获平台接受。所有版本仍使用原始 `lpNorm`，没有把目标改成数值有效性谓词，也没有修改原始五个 mission 声明。

## 复现

首次安装依赖：

```powershell
cd formalization
lake update
lake exe cache get
cd ..
```

固定版本工具链与 Mathlib revision 由检查器再次核对。先复核有限证书，再核验组装；Windows 上限制同时运行的 Lean 进程数：

```powershell
python scripts/check_contractor_lean.py --jobs 2
python scripts/check_scalar_lower_lean.py --jobs 2
python scripts/check_localization_lean.py --jobs 2
python scripts/check_real_chunks_lean.py --jobs 2
python scripts/check_full_window_lean.py
```

`check_full_window_lean.py` 使用实际本地证明，检查两个原始实三维声明、全维复数最小性传递和显式尾部接口，公理只有 `propext`、`Classical.choice`、`Quot.sound`。本地 `Theorems/` 镜像导入实际证明，没有用 `sorry` 或外加公理代替平台依赖。

检查准确的紧凑提交文件：

```powershell
python scripts/prepare_group_domain_platform_proofs.py
python scripts/prepare_transfer_platform_proof.py
python scripts/prepare_domain_block_platform_proofs.py
python scripts/build_theorem_mirrors.py --manifest formalization/platform/domain-block-proofs.json
python scripts/check_lean_proofs.py --manifest formalization/platform/analytic-assembly-proofs.json --output results/lean-analytic-assembly-build.json --jobs 2
python scripts/check_lean_proofs.py --manifest formalization/platform/domain-block-proofs.json --output results/lean-domain-blocks-build.json --jobs 2
python scripts/prepare_real_window_platform_proofs.py
python scripts/check_lean_proofs.py --manifest formalization/platform/real-window-proofs.json --output results/lean-real-window-platform-build.json --jobs 1
python scripts/prepare_root_platform_proof.py
python scripts/check_lean_proofs.py --manifest formalization/platform/root-assembly-check.json --output results/lean-root-assembly-build.json --jobs 1
```

四段 API 镜像把真实局部证明在本地合并编译一次，再由各个 `Theorems/` 模块导入；没有开放声明、外加公理或平台 Definition 中隐藏的复杂证明。`--keys` 可明确选择少数代表块，报告会记录选择；只有整份清单全部 PASS 才表示整批精确文件通过。

个别四段文件仍触发服务器限时，分别用 `prepare_domain_block_repair.py <parent_key>` 拆成两个忠实子区间。原父声明、256 段覆盖及最终目标保持不变。子证明闭合后，用新的短区间组合证明修复父目标；旧超时提交保留为历史，不重复上传同一文件。[子证明检查](../results/lean-domain-children-build.json)、[子证明平台任务](../results/prove2me-domain-children.json)、[修复源码清单](platform/domain-repair-proofs.json)。

`root-assembly-check.json` 检查与最终组合相同的证明体，显式输入 cutoff 32 尾部。最终 `Sol_campaign_cutoff21.lean` 改为导入平台已闭合的尾部，由服务器检查；当前 [组合判决](../results/prove2me-root.json) 为 `SKETCH_ACCEPTED`，不能称为无开放依赖的完整证明。

这些检查器默认执行新检查；`--reuse` 只显式复用同一工具链和 Mathlib 下、文件哈希一致的既有 PASS，不是独立复验。`--lean-threads` 可限制每个 Lean 进程的线程数。当前机器使用过相同固定版本的隔离目录 `.test-tmp/prove2me/lean`；缓存不提交。

原始 `sources/*.lean` 保持不改。原作者及平台贡献者的来源、许可与改编哈希见 [Foundation provenance](Hlawka21/Foundation/provenance.json) 和 [来源声明](../sources/NOTICE.md)。进一步工作见 [下一步](../docs/next-steps.md)。

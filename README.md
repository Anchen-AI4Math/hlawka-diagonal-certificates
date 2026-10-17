# Sharp diagonal Hlawka：cutoff 127/4 的计算机辅助证明

独立、私有的研究仓库。[完整证明稿](docs/proof-127-over-4.md) 给出把指数截断从 **32 推进到 127/4 = 31.75** 的计算机辅助论证，结论针对任意有限维复向量的统一最优常数。

**已完成：** 新窗口 `[31.75,32]` 的完整解析链、有限数值证书，以及 Arb 和纯有理数两种算术后端复核。解析链包括包络、正规化、粗定位、收缩、盒内凸性、对称平均、三维到任意维归约、实到复传递和最优性。尾部 `p≥32` 引用平台已有接受结果。

**当前状态：完整证明稿已写出并完成作者自审，待独立审阅。** 本仓库没有新增 Lean 证明、没有向 Prove2Me 提交结果，也没有更新平台纪录。两个算术后端共享数学条件与验证流程，不代表两份独立端到端证明。`sources/*.lean` 是只读参考快照，未在此重新编译。

2026-10-17 查询的 [Prove2Me campaign](https://prove2.me/campaigns/sharp-diagonal-hlawka-constant) 显示 cutoff 32 于 2026-10-16 完成。这里的 32 是指数阈值，不是 Hlawka 常数的数值。

## 复核

本次使用 Python 3.14。在项目根，无第三方依赖的复核命令为：

```powershell
python -S scripts/verify.py --backend rational --precision 256 --output results/verification-rational.json
python -S scripts/negative_controls.py --backend rational
```

`-S` 禁用 site 包加载。纯有理后端使用整数、Fraction、有限泰勒和及显式余项界，[正确性说明](docs/rational-arithmetic.md)。Arb 对照复核：

```powershell
python -m pip install --target .deps -r requirements.txt
python scripts/verify.py
python scripts/verify.py --precision 256 --output results/verification-256.json
python scripts/negative_controls.py
python scripts/check_arithmetic.py
```

Arb 后端只使用 Python 标准库和 `python-flint`；NumPy/SciPy 仅用于产生候选数据，验证阶段不调用优化器。

重生成：

```powershell
$env:PYTHONPATH='.deps'
python scripts/scout.py
python scripts/coarse_lp.py
python scripts/generate.py
python scripts/verify.py
```

| 数值义务 | 覆盖 | 证书 |
|---|---|---|
| `scalarEnvelope(p, 0.3854) < K_p`，`0.448 p < K_p` | 1124 个闭区间，无间隙覆盖全部实数 p | [scalar.json](certificates/scalar.json) |
| `K_p ≤ p/2` | 96 个 `(p,t)` 矩形，`1/2 ≤ t ≤ 2` | [cyclic-upper.json](certificates/cyclic-upper.json) |
| 粗定位的线性推论 | 36 份精确有理数对偶证明 | [coarse.json](certificates/coarse.json) |
| 逐轮坐标收缩 | 16 段，每段六轮，按前一轮结果推进 | [contractor.json](certificates/contractor.json) |
| 原最终盒子的曲率条件 | 全部 `[31.75,32]` | [验证结果](results/verification.json) |

最终盒子保持为：对角项 `[-1.065,-0.625]`，非对角项 `[0.849,1.121]`。最紧的收缩边界仍有约 `0.001763` 的余量。Arb 192/256 位、纯有理数 256 位均通过；53 项算术交叉检查通过，两种后端各拒绝全部五种故意损坏的证书。数值 PASS 的范围是有限计算条件，解析部分另见正文。

阅读 [完整证明](docs/proof-127-over-4.md)、[作者自审清单](docs/self-audit.md)、[研究状态](status.json)、[下一步](docs/next-steps.md)。早期 [数值笔记](docs/numerical-note.md) 保留为历史记录。浮点探索在 [scout.json](results/scout.json)，不能用作证明。

本仓库按用户要求保持私有。组织公开主页及 research-index 不登记它；未来明确获准公开后，再按 `AGENTS.md` 同步导航。

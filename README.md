# Sharp diagonal Hlawka：数值证书

独立、私有的数值研究仓库。当前候选是把指数截断从 **32 推进到 127/4 = 31.75**。

**已完成：** 对整个实数区间 `[31.75, 32]`，用 Arb 区间算术和精确有理数线性对偶证书验证了新窗口所需的标量包络、循环常数上下界、粗定位、坐标收缩和固定盒子的曲率数值条件。

**尚未完成：** 新窗口的完整数学归约仍需独立审阅；本仓库没有新增 Lean 证明、没有向 Prove2Me 提交结果，也没有更新平台纪录。`sources/*.lean` 仅为已经接受的公开证明的只读参考快照，未在此重新编译。

2026-10-17 查询的 [Prove2Me campaign](https://prove2.me/campaigns/sharp-diagonal-hlawka-constant) 显示 cutoff 32 于 2026-10-16 完成。这里的 32 是指数阈值，不是 Hlawka 常数的数值。

## 复核

Python 3.14，在项目根运行：

```powershell
python -m pip install --target .deps -r requirements.txt
python scripts/verify.py
python scripts/negative_controls.py
```

验证器只使用 Python 标准库和 `python-flint`；NumPy/SciPy 仅用于产生候选数据，验证阶段不调用优化器。

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

最终盒子保持为：对角项 `[-1.065,-0.625]`，非对角项 `[0.849,1.121]`。最紧的收缩边界仍有约 `0.001763` 的余量。所有证书在 192 位和 256 位精度下通过；这属于同一验证器的不同精度复核，不是独立实现的复验。五种故意损坏证书的测试全部被拒绝。

阅读 [推导及信任边界](docs/numerical-note.md)、[研究状态](status.json)、[下一步](docs/next-steps.md)。浮点探索在 [scout.json](results/scout.json)，不能用作证明。

本仓库按用户要求保持私有。组织公开主页及 research-index 不登记它；未来明确获准公开后，再按 `AGENTS.md` 同步导航。

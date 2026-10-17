# Sharp diagonal Hlawka：cutoff 26 的计算机辅助证明

独立、私有的研究仓库。当前 [证明稿](docs/proof-26.md) 将此前的 **31.75 推进到 26**，结论针对所有实数 `p≥26`、任意有限维复向量的统一最优 Hlawka 常数。

关键改进是保留定位反例时已经得到的单项及总和范数上界，在它们与坐标盒子的凸交集上证明亏损函数凸。这显著收紧正 Hessian 项的估计。96 个 p 段分别使用自己的盒子与范数上界，覆盖整个 `[26,32]`；尾部 `p≥32` 引用已有接受结果。

**当前状态：完整计算机辅助证明稿已完成作者自审，待独立审阅。** Arb 192/256 位和纯有理数 256 位均通过新窗口的全部有限证书。没有新增 Lean 证明、平台提交或平台纪录更新；两个后端共享数学条件和检查流程，不代表两份独立端到端证明。

2026-10-17 查询的 [Prove2Me campaign](https://prove2.me/campaigns/sharp-diagonal-hlawka-constant) 仍显示最佳形式化 cutoff 为 32。这里的 26、31.75、32 都是指数 p 的阈值，不是最优常数 K_p 的数值。

## 复核 cutoff 26

本次使用 Python 3.14。在项目根，无第三方依赖的复核命令为：

```powershell
python -S scripts/verify.py --backend rational --precision 256 --profile profiles/cutoff26.json --directory certificates/cutoff26 --output results/cutoff26-rational.json
python -S scripts/negative_controls.py --backend rational --profile profiles/cutoff26.json --directory certificates/cutoff26 --output results/cutoff26-negative-rational.json
```

`-S` 禁用 site 包加载。纯有理后端使用整数、Fraction、有限泰勒和及显式余项界，[正确性说明](docs/rational-arithmetic.md)。Arb 对照复核：

```powershell
python -m pip install --target .deps -r requirements.txt
python scripts/verify.py --profile profiles/cutoff26.json --directory certificates/cutoff26 --output results/cutoff26-arb.json
python scripts/verify.py --precision 256 --profile profiles/cutoff26.json --directory certificates/cutoff26 --output results/cutoff26-arb-256.json
python scripts/negative_controls.py --profile profiles/cutoff26.json --directory certificates/cutoff26 --output results/cutoff26-negative-arb.json
python scripts/check_arithmetic.py
```

Arb 后端只使用 Python 标准库和 `python-flint`；NumPy/SciPy 仅用于产生候选数据，验证阶段不调用优化器。

重生成：

```powershell
$env:PYTHONPATH='.deps'
python scripts/generate_window.py --profile profiles/cutoff26.json --output certificates/cutoff26
```

| 数值义务 | 覆盖 | 证书 |
|---|---|---|
| `E_p(0.394)<K_p`，`0.443p<K_p` | 2699 个闭区间，无间隙覆盖全部实数 p | [scalar.json](certificates/cutoff26/scalar.json) |
| `K_p≤p/2` | 672 个 `(p,t)` 矩形 | [cyclic-upper.json](certificates/cutoff26/cyclic-upper.json) |
| 粗定位 | 36 份精确有理数对偶证明 | [coarse.json](certificates/cutoff26/coarse.json) |
| 收缩、范数上界与坐标盒子 | 96 段，每段十轮 | [contractor.json](certificates/cutoff26/contractor.json) |
| 凸域曲率 | 全部 `[26,32]`，每段重算几何常数 | [Arb 结果](results/cutoff26-arb.json)、[纯有理结果](results/cutoff26-rational.json) |

两类无量纲曲率余量的最小下端约为 **0.3200**、**0.2675**。两种后端各拒绝七种故意损坏的输入，包括错误盒子与失败的曲率配置。原有 53 项算术交叉检查仍适用于未改动的算术内核。数值 PASS 的范围是有限计算条件，解析论证见正文。

## 基础稿与状态

[cutoff 31.75 基础稿](docs/proof-127-over-4.md) 中的加权凸性、正规化、收缩、降维和复数传递引理被新稿明确引用；新的凸域、曲率系数和平均参数范围在新稿中证明。旧证书保留在 `certificates/` 顶层，仍可用不带 profile 的 `python scripts/verify.py` 复核；本次回归检查通过，见 [baseline-regression.json](results/baseline-regression.json)。

另见 [作者自审](docs/self-audit.md)、[研究状态](status.json)、[下一步](docs/next-steps.md)。下载的 `sources/*.lean` 保持原字节，未重新编译。浮点探索不能作为证明；本仓库尚未证明 26 是最优阈值。

本仓库按用户要求保持私有。组织公开主页及 research-index 不登记它；未来明确获准公开后，再按 `AGENTS.md` 同步导航。

# Sharp diagonal Hlawka：cutoff 21 的计算机辅助证明

**论文：** [A computer-assisted sharp diagonal Hlawka inequality for real exponents p ≥ 21（PDF）](paper/main.pdf) · [LaTeX 源码](paper/main.tex) · [构建与复现](paper/README.md)。

**作者：徐宇轩（Yuxuan Xu），武汉大学计算机学院。** 论文为 AI 辅助研究预印本，明确披露辅助范围，并致谢既有证明与平台贡献者。

本仓库的完整论文将此前的 **26 推进到 21**，结论针对所有实数 `p≥21`、任意有限维复向量的统一最优 Hlawka 常数。论文独立展开 `[21,32]` 的解析归约及有限证书论证；`p≥32` 引用已有接受结果。仓库中的进展为 31.75 → 26 → 21。

本轮改进包括：用总范数上界裁剪 pair 尾坐标；把已推导的 pair 主坐标下界与非对角总和下界保留为凸域上的线性约束；把 pair 误差的统一系数 16 改成更小的有理系数。新证书覆盖 `[21,26]`，接上既有稿的 `[26,32]`，尾部 `p≥32` 引用平台已有接受结果。

**当前状态：完整计算机辅助证明稿已完成作者自审，待独立审阅。** Arb 192/256 位和纯有理数 256 位均通过新窗口的全部有限证书。没有新增 Lean 证明、平台提交或平台纪录更新；两个后端共享数学条件和检查流程，不代表两份独立端到端证明。

2026-10-17 查询的 [Prove2Me campaign](https://prove2.me/campaigns/sharp-diagonal-hlawka-constant) 仍显示最佳形式化 cutoff 为 32。这里的 21、26、31.75、32 都是指数 p 的阈值，不是最优常数 K_p 的数值。

## 复核新窗口 [21,26]

**一条命令复核论文的全部新窗口 `[21,32]`：**

```powershell
python -S scripts/replay_release.py
```

该命令使用纯标准库有理区间后端，复核两个窗口、15 项损坏证书拒绝检查及 11 个引用源文件哈希，生成 [发布复核报告](results/release-replay.json)。它不重新编译已有 Lean 尾部，也不代替独立数学审阅。

本次使用 Python 3.14。在项目根，无第三方依赖的复核命令为：

```powershell
python -S scripts/verify.py --backend rational --precision 256 --profile profiles/cutoff21.json --directory certificates/cutoff21 --output results/cutoff21-rational.json
python -S scripts/negative_controls.py --backend rational --profile profiles/cutoff21.json --directory certificates/cutoff21 --output results/cutoff21-negative-rational.json
```

`-S` 禁用 site 包加载。纯有理后端使用整数、Fraction、有限泰勒和及显式余项界，[正确性说明](docs/rational-arithmetic.md)。Arb 对照复核：

```powershell
python -m pip install --target .deps -r requirements.txt
python scripts/verify.py --profile profiles/cutoff21.json --directory certificates/cutoff21 --output results/cutoff21-arb.json
python scripts/verify.py --precision 256 --profile profiles/cutoff21.json --directory certificates/cutoff21 --output results/cutoff21-arb-256.json
python scripts/negative_controls.py --profile profiles/cutoff21.json --directory certificates/cutoff21 --output results/cutoff21-negative-arb.json
python scripts/check_arithmetic.py
```

Arb 后端只使用 Python 标准库和 `python-flint`；NumPy/SciPy 仅用于产生候选数据，验证阶段不调用优化器。

重生成：

```powershell
$env:PYTHONPATH='.deps'
python scripts/generate_window.py --profile profiles/cutoff21.json --output certificates/cutoff21
```

| 数值义务 | 覆盖 | 证书 |
|---|---|---|
| `E_p(0.4044)<K_p`，`0.4368p<K_p` | 2355 个闭区间，无间隙覆盖全部实数 p | [scalar.json](certificates/cutoff21/scalar.json) |
| `K_p≤p/2` | 960 个 `(p,t)` 矩形 | [cyclic-upper.json](certificates/cutoff21/cyclic-upper.json) |
| 粗定位 | 36 份精确有理数对偶证明 | [coarse.json](certificates/cutoff21/coarse.json) |
| 收缩、范数上界与坐标盒子 | 160 段，每段十轮 | [contractor.json](certificates/cutoff21/contractor.json) |
| 凸域曲率 | 全部 `[21,26]`，每段重算几何常数 | [Arb 结果](results/cutoff21-arb.json)、[纯有理结果](results/cutoff21-rational.json) |

两类无量纲曲率余量的最小下端约为 **0.3913**、**0.3217**。两种后端各拒绝八种故意损坏的输入，包括错误盒子、失败的曲率配置及未经证明的过小尾误差。原有 53 项算术交叉检查仍适用于未改动的算术内核。数值 PASS 的范围是有限计算条件，解析论证见正文。

## 基础稿与状态

[cutoff 31.75 基础稿](docs/proof-127-over-4.md) 中的通用解析引理，以及 [cutoff 26 稿](docs/proof-26.md) 的范数约束方法被新稿明确引用。区间依次为 `[21,26]`、`[26,32]`、平台已有结果 `[32,∞)`，端点相接无缺口。

cutoff 26 的原证书保留并通过本轮 [回归检查](results/cutoff26-regression.json)。重新复核整个数值范围时，还需运行 `python scripts/verify.py --profile profiles/cutoff26.json --directory certificates/cutoff26 --output results/cutoff26-arb.json`，纯有理后端命令见其证明稿。最初的证书保留在 `certificates/` 顶层，可不带 profile 运行检查。

另见 [作者自审](docs/self-audit.md)、[研究状态](status.json)、[下一步](docs/next-steps.md)。下载的 `sources/*.lean` 保持原字节，未重新编译。浮点探索不能作为证明；本仓库尚未证明 21 是最优阈值。

按作者 2026-10-17 的指示，本仓库以论文预印本和可复核数据包公开发布；不代表期刊发表。项目材料采用 [Apache-2.0](LICENSE)，第三方材料保留原作者归属与许可，详见 [NOTICE](NOTICE) 和 [来源声明](sources/NOTICE.md)。可使用 [CITATION.cff](CITATION.cff) 引用。

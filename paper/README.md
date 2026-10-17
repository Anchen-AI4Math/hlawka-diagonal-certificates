# 论文与复现

**A computer-assisted sharp diagonal Hlawka inequality for real exponents p ≥ 21**

徐宇轩 / Yuxuan Xu，武汉大学计算机学院 / School of Computer Science, Wuhan University。

2026-10-17，v1 研究预印本。[阅读 PDF](main.pdf) · [LaTeX 源码](main.tex)。v1 发布时尚无新增 Lean 验证；后续进展见 [形式化状态](../formalization/README.md)。尚未独立审阅或期刊投稿，没有声称 21 为最优阈值。

论文包含问题定义、主定理、全维归约、标量包络、定向和精确 LP 定位、十轮收缩、保留范数及线性约束的凸域、Hessian 估计、对称平均、最优性、有限证书规格及有理算术附录。`[21,32]` 的论证在正文中连贯给出，`[32,∞)` 明确引用已有接受结果。

## 构建

在 `paper` 目录，有 Tectonic 时运行：

```sh
tectonic main.tex
```

也可以使用完整 TeX Live 的 `latexmk -pdf main.tex`，或连续两次 `pdflatex main.tex`。本文不需要外部 BibTeX 数据库、shell escape 或中文字体。PDF 使用英文姓名，中文姓名与作者指定的单位保存在本说明及引用元数据。

本次实际使用 Tectonic 0.17.0+20260731。构建结果、文件摘要和排版检查见 [build.json](build.json)。输出 PDF 的时间元数据可能导致不同机器构建时字节不同，不应要求 PDF 哈希跨构建一致。

## 证书复现

回到仓库根目录运行：

```sh
python -S scripts/replay_release.py
```

仅使用 Python 标准库，依次验证 `[21,26]` 与 `[26,32]`、15 个故意损坏输入及引用文件完整性。本次使用 Python 3.14。结果在 [release-replay.json](../results/release-replay.json)，其中记录脚本、profile 与证书的 SHA-256；PDF 自身不能替代这些输入。

Arb 后端是另一个算术实现，但两者共享数学建模和验证控制流程。完整信任范围见论文第 8 节与 [status.json](../status.json)。

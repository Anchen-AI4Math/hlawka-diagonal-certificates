# 标量界的 Lean 证明路线

原论文用区间算术验证两组标量比较。新增 Lean 证明采用更简单的端点证书与 Bernoulli 传递，保持原来的定义、参数和全实区间结论。源码与公理审计以 [formalization](../formalization/README.md) 和相应构建记录为准；这些标量结果本身不证明全维 Hlawka 主目标。

## 上界

写 `A=A_p(t)`、`B=B_p(t)`、`a=3^(1/p)`、`b=2^(1/p)`。当 `21≤p≤32` 时，Lean 证明

$$
1+\frac{.69}{p}+\frac{.69^2}{2p^2}\le b\le1+\frac1p,
\qquad 1+\frac1p\le a\le3.
$$

下界使用 `log 2≥.69`、`log 3≥1` 和指数函数的二次 Taylor 下界；`b≤1+1/p` 来自 Bernoulli 不等式。已证明的半尾项估计给出 `B≤2+10^-5`，而 `A≥max(b,t)`。分 `t≤b` 和 `b≤t` 两种情况，得到

$$
2(p-1)A+\frac23a(2-t)\ge2p+10^{-3}>pB.
$$

此外 `A≥1+1/64`，所以循环比值分母为正。整理上式并取上确界，得到整个 `[21,32]` 上的 `K_p≤p/2`。这一步不使用原来 960 个上界矩形。见 [CyclicUpper.lean](../formalization/Hlawka21/CyclicUpper.lean)。

## Envelope 比线性阈值小

每个窗口令 `m` 为左端点，`q,c` 为原 profile 参数，置 `d=(1-q)/(2c)`。一次精确有理数整数幂比较证明

$$
\frac{1+q^m}{2}<(1-d/m)^m.
$$

对任意实数 `p≥m`，Bernoulli 不等式给出

$$
(1-d/m)^m\le(1-d/p)^p,
\qquad q^p\le q^m.
$$

取正的 `p` 次根，得到 `((1+q^p)/2)^(1/p)<1-d/p`；分母为正后整理即为 `E_p(q)<cp`。这个结果对所有更大的实指数成立，强于只在窗口内作比较。见 [Envelope.lean](../formalization/Hlawka21/Envelope.lean)。接上 `cp<K_p` 才得到原任务的 `E_p(q)<K_p`。

## 固定有理循环见证

Window I 使用 `t=17/20`，Window II 使用 `t=87/100`。沿用原 contractor 的 160 与 96 个闭区间边界，只使用其覆盖信息；新的标量证书另存，不覆盖原证书。

在每段 `[α,β]`，写 `α=m/k`，选择有理数 `Z,A_*,a_*`。Lean 检查三个整数幂不等式

$$
t^m\le Z^k,\qquad (2+Z)^k\le A_*^m,\qquad3^k\le a_*^m.
$$

由此得到 `t^α≤Z`、`t^α+2≤A_*^α`、`3≤a_*^α`。Bernoulli 给出整个实区间上的上界

$$
A_p(t)\le1+\frac\alpha p(A_*-1),\qquad
3^{1/p}\le1+\frac\alpha p(a_*-1).
$$

再用 `B_p(t)≥2`。置 `d=2-t`、`H=3(A_*-1)-d(a_*-1)`，只需精确验证

$$
H\ge0,\qquad
3-d+\frac\alpha\beta H-6c\alpha(A_*-1)>0.
$$

这推出 `cp<R_p(t)≤K_p`，覆盖整个闭区间，不只是端点。见 [FixedWitness.lean](../formalization/Hlawka21/FixedWitness.lean)。256 段合计 768 个整数幂证书；每 16 段共享一个模块，再通过有限二分覆盖接回两个原始标量里程碑。

候选有理数由 Decimal 向上取整产生，生成器不受信任。每个被采用的值还需通过精确 Fraction 预检查及 Lean 内核的整数幂检查。构建入口为 `python scripts/check_scalar_lower_lean.py`；完整性与实际通过状态见 [标量构建记录](../results/lean-scalar-build.json) 和 [平台记录](../results/prove2me-auxiliary.json)。

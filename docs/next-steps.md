# 下一步

当前持续目标是完成 cutoff 21 的 Lean 形式化并通过 Prove2Me。作者已在网页完成 proposal 自审与提交，服务器为 `In review`，campaign 关联保留；版主审核与数学证明验证分别跟踪。

1. **已完成两个原始标量里程碑**：全实区间上的 `cp<Kp≤p/2`、`scalarEnvelope p q<Kp` 均已获平台 `ACCEPTED` / `Proved`，开放依赖为零。共 27 个辅助定理通过。见 [证明路线](lean-scalar.md)、[平台里程碑记录](../results/prove2me-milestones.json) 和 [原目标状态](../results/prove2me-goals.json)。不要重新把标量界当作未完成任务。
2. 从任意实三维反例完成反射、归一化和定向，再调用已证明的 `CoarseConnection21/26`。实际范数到两阶段 LP、半尾项到粗坐标盒的连接已完成；任意反例到这些假设的连接仍需完成。数值 PASS 不能直接作为 Lean 前提。
3. 256 个 slab 的十轮**条件收缩**已全部在 Lean 通过。补齐每段根界和预算的组合，使用 `ContractionFacts`、`RefinedTail` 接回实际范数，得到 singleton 上界、pair 主坐标和非对角总和下界。保留 `sources/*.lean` 原文件不改。
4. 完成范数上界约束下的 Hessian 下界、径向系数差、pair 残差、凸域不变性与平均论证，分别关闭两个实三维目标。域内保留范数次水平集和已推导的线性不等式，不保留非凸的 `S=3` 等式约束。已有矩阵残差能量估计可以复用。
5. 接回任意实维、复数传递、cyclic 最优性和既有 `p≥32` 尾部，证明原始全维主目标。最终须核验原始 `campaign_cutoff21` 为 `Proved`、开放依赖为零，且声明保持任意有限复维度、实数指数、零维与不等范数三元组的范围；两个标量目标或条件收缩通过不等于完成。
6. 完整论文及解析归约仍待独立审阅。两个算术后端共享模型和检查流程，不能称为独立端到端证明。21 尚不是已证明的最优阈值；进一步降低 cutoff 是独立研究方向，不能替代当前形式化目标。

公开论文见 [paper/main.pdf](../paper/main.pdf)，精确状态见 [status.json](../status.json)。论文预印本公开和 Prove2Me 提案提交不表示期刊发表。

下一轮代码与证据入口见 [Lean 工作交接](lean-handoff.md)。

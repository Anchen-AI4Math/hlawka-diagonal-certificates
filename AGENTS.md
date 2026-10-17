# AI4Math 工作区

## 本仓库当前范围

- 用户于 2026-10-17 明确要求整理完整论文、推送后公开本仓库，覆盖此前的私有偏好。公开发布后按下方约定同步组织导航；不得发布凭证、无关私人资料或推断平台已接受新阈值。
- 论文署名为徐宇轩（Yuxuan Xu），武汉大学计算机学院。主论文为 `paper/main.tex` 与 `paper/main.pdf`；修改数学内容后复核其与证书的对应，重新编译 PDF。公开不等于期刊发表或独立审阅。
- 用户要求优先推进数值证书，暂不急做 Lean；除非后续改变要求，不提交平台证明或启动大规模 Lean 工作。
- 用户随后于 2026-10-17 明确要求把论文交到 Prove2Me、创建 mission 并关联 campaign。已授权准备和上传相关 proposal；正式 goal 采用 campaign 原模板并将 cutoff 填为 21。平台当前规定 proposal 的自审确认与 Submit Proposal 由用户在网页完成，审核通过才成为公开 mission/campaign entry。声明中的 `by sorry` 表示开放任务；声明编译与独立 read-back 不等于证明验证。
- 当前持续目标已由用户明确改为“完成 Lean 形式化，Prove2Me 平台通过”，覆盖此前暂缓 Lean 的偏好。可以编写、编译和提交真实证明及必要的辅助定理；最终仍须核对 cutoff 21 原目标与全部依赖的实际通过状态，不能用声明编译或尚有开放子引理的 sketch 代替完成。
- 先读 `status.json`、`docs/proof-21.md`、`docs/self-audit.md` 和 `docs/next-steps.md`。`docs/proof-26.md` 与 `docs/proof-127-over-4.md` 为新稿依赖；证书分别保存在 `certificates/cutoff21/`、`certificates/cutoff26/` 与顶层，不覆盖旧结果。严格区分数值义务、解析归约、独立审阅、Lean 验证和发表状态。
- `sources/*.lean` 是参考下载，保留不改；新数值证书放在 `certificates/`，验证器放在 `scripts/`。生成器可用浮点搜索，接受证书必须通过区间或精确有理数验证。

<!-- ai4math-maintenance:start -->
## AI4Math 入口自动维护（默认收尾工作）

- 用户已要求：新增/发布/重命名/迁移/暂停公开 AI4Math 课题或仓库，以及有证据支持的研究状态变化后，主动同步组织主页 `Anchen-AI4Math/.github/profile/README.md` 与研究总目录 `Anchen-AI4Math/research-index` 的 `README.md`、`catalog.json`，无需再次提醒。普通修改无导航或状态变化时不提交空变更。
- **个人主页不更新**：不要修改 `Anchen0823/Anchen0823`、个人简介或个人置顶；个人主页仅保留用户自行设置的组织链接。
- 执行前读取完整维护约定：`https://github.com/Anchen-AI4Math/research-index/blob/main/MAINTENANCE.md`（可用 `gh api repos/Anchen-AI4Math/research-index/contents/MAINTENANCE.md` 获取），并遵守当前任务更具体的约束。
- 只登记已公开或本次已获准公开发布的信息；不因此自动创建公开仓库、改变可见性或迁移所有权。源材料未公开时只记录本地待办，不发布私有资料。
- 总目录收录完整课题与独立仓库；组织主页维护简洁研究入口。新工作区课题先更新其 `missions/index.json` 和状态文件，再同步已公开的版本。只读取当前课题与导航所需资料，不全量扫描其他任务。
- 发布前读取最新内容及 SHA，保留他人编辑；分别记录研究、验证和发表状态，链接证据，不夸大结论。发布后核验远端；分支保护需要 PR 时按仓库独立建 PR，报告待合并状态，不绕过保护。
- 新建 AI4Math 仓库时，把本节写入其根 `AGENTS.md`，让后续独立打开的 agent 也能发现约定。
- 本规则由执行任务的 agent 在收尾时触发；无运行中的 agent 时不是后台同步服务。网络或权限阻塞时明确报告未完成项。
<!-- ai4math-maintenance:end -->

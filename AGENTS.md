# AI4Math 工作区

## 本仓库当前范围

- 本仓库为用户明确选择的私有研究仓库，不向公开目录发布其名称、内容或状态。
- 用户要求优先推进数值证书，暂不急做 Lean；除非后续改变要求，不提交平台证明或启动大规模 Lean 工作。
- 先读 `status.json`、`docs/numerical-note.md` 和 `docs/next-steps.md`。严格区分数值义务、解析归约、独立审阅、Lean 验证和发表状态。
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

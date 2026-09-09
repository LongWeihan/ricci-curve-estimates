# 简明数学表述独立审核

日期：2026-09-09。审核者：Astra 代理 formalization_prompt_research；未参与本轮蓝图/UI措辞编辑。本审核是独立 AI 语义审核，不是外部人类同行评审。

**结论：通过，本轮未发现需修复的数学条件损失或双语歧义。** 审核仅覆盖相对 HEAD `a37e827f81fcf9be10268145eaee10e821c6c190` 的表达变更；已有 Lean 数学正确性证据依相同源码哈希继承。未运行 Lake，未修改蓝图、UI、报告、Lean 源码或看板。

## 绑定版本

| 文件 | SHA-256 |
|---|---|
| `blueprint/blueprint.json` | `e5f208da45b9c2cccadccda88f6a71b85d339228d1615329c772cb23027cebe8` |
| `website-template/zh-CN-blueprint.json` | `f31199b3553c7a308257d041134a4d4c46f0cd9c9553c866c08ee7ff770855bc` |
| `website-template/ui.json` | `a6f6988ec920b7c1bd1c67395d30a2c350dd36902122a6f6f2634ecdef5fbe35` |

以上为最后一次顶层字段调整后的版本，替代本轮先前 EN/ZH 临时冻结哈希。

## 结构与公式核对

通过只读 JSON 比较逐一检查两个版本的 22 个节点：相对 HEAD，节点 id、标题、kind、math_statement、Lean 模块/文件/声明映射、dependencies 及 source_references 均逐项完全相同。节点次序未变，62 条精选声明映射完整保持。中英文的数学公式、节点身份、映射、依赖及引用标识相互一致。此次机械比较是静态完整性证据，不冒充重新编译或新的公理检查。

节点改动集中于 explanation、contribution.detail 与 scope_caveats。顶层 scope、dependency_semantics 及两条来源 role 亦已阅读：scope 保留“已有光滑浸入闭曲线流”与“静态一维因子度量”；图的边明确为组织阐述所选取的前置结果，未声称等于完整 Lean import 图；Perelman 来源定位和上游蓝图的证明规划定位准确且双语同义。

## 逐节点语义核对

下列每项均已对照 EN、ZH 新旧文本及保持不变的数学公式，结论均为通过。

| 节点 | 保持的条件与结论 |
|---|---|
| `flow_input` | 保留已有光滑浸入周期解、within 时间方程与内点演化条件。 |
| `curve_geometry` | 实际演化度量、固定有效图册、周期一及允许自交均保留。 |
| `speed_evolution` | 速度律由流方程和混合协变导数推出。 |
| `connection_variation` | 固定空间点求联络时间导数后用 g(t) 降指标；度量变分另算。 |
| `curvature_evolution` | P 明确为空间投影，时空投影额外分量仍说明；q PDE 从输入流推导。 |
| `spatial_kato` | 由度量 Cauchy–Schwarz 与已导出的正则性证明 q 梯度界，涵盖零点。 |
| `ambient_error` | B,K,D 为实际度量范数下张量评估界；低层输入与后续构造分开。 |
| `regularized_pde` | ε>0 公式未变；条件标量引理输入由几何根关闭。 |
| `moving_integrals` | 联合光滑、周期消通量、密度吸收及固定 ε 控制保持；未宣称 Θ 的 a.e. 导数。 |
| `interior_comparison` | 内点微分加闭连续；初始端点不要求经典导数或负时间延拓。 |
| `epsilon_limit` | 先比较再在两端取极限；Θ 局部 AC 仍是另待证明的接口。 |
| `actual_curve_estimate` | 仅输入实际流与环境界，微分及积分估计由它们推出。 |
| `length_energy` | 统一下界覆盖 [a,b] 上所有环境点的所有单位向量；不加权式另需 B≥0。 |
| `compact_tensor_bounds` | 从紧致基底构造多线性评估界；无需因子紧致。 |
| `product_metric` | WithLp 2 模型与普通 max 范数产品区分，几何使用真实 g,h 纤维度量。 |
| `one_dimensional_flatness` | 实际一维曲率消零；Ricci 先作为场恒零，再求协变导数。 |
| `product_curvature_ricci` | 图册开放域上的 Γ/导数分裂，符号桥与实际纤维等距仍明确。 |
| `product_covricci` | 对有效函数芽的低阶 Ricci 分裂求导；分裂本身为证明结论。 |
| `product_ricci_flow` | 保留 joint within 平滑与时间静态因子；允许外部索引变化。 |
| `product_tensor_bounds` | 同一 B,K,D 由投影不增范数继承；低层输入与最终紧致构造区分。 |
| `uniform_product_estimate` | 常数先于全部静态度量、曲线与初值；正尺度无下界/正则性要求；已有解和初值界显式。 |
| `scaled_factor_application` | 真实正尺度度量构造、全时间区间应用；不在零尺度造度量，不提供图册/ramp/存在性。 |

## 重点判断

`length_energy` 英文 “all ambient unit vectors over [a,b]” 仍量化整个环境，而非仅曲线上单位切向量；中文进一步明写每点所有单位向量。这与既有公开根的 uniform ambient Ricci lower bound 一致，没有缩窄为沿曲线假设。不加权 B≥0 条件保留。

`uniform_product_estimate` 公式是简写，完整量词顺序由随附说明明确：先 ∃B,C，再量化所有静态度量、曲线和初值界。已有光滑浸入周期解和共同初值界仍作为输入。该顺序也涵盖整个度量族，而非在每个 λ 之后重新取常数。尺度可任意小但严格正；因子在 Ricci 时间内静态。

纯空间联络与原时空路线的差别保留在 connection_variation、curvature_evolution 及顶层符号记号中。q PDE 与 Kato 不被移作几何根的输入。条件分析引理仍明确自己的输入边界，几何根负责证明。ε_limit 的英文 “remains a separate result” 与 moving_integrals 明确 “requires a further theorem” 及最终范围条款合读，不是声称已经证明 Θ 的局部 AC/a.e.；中文同样明确尚需另证。

## UI 与双语一致性

已读取 ui.json 两种语言的全部显示字符串。首页范围保留实际已有流、演化度量、紧致基底常数独立于静态一维因子，以及比较后去正则化。导出声明目录仍与数学阐述区分，原文类型和源码保留其语言；没有将精选映射数包装成完成百分比。导航、标签和范围说明双语同义，没有增加数学结论或人类审稿认可。`development` 字符串仅是“PDF待加入”的预览分支文案；是否启用该分支属于另行网站构建验收，本审核未把其存在误判为当前报告缺失。

本轮更直接的措辞未改变数学模块范围、流存在性输入、零曲率处理方式、端点策略或实际产品几何要求。可以在上述哈希上继承既有数学审核，并将本记录作为本轮表达变更的独立语义证据。

语言标签追加核对：当前 UI 仅新增 EN `language_label: Language` / ZH `language_label: 语言`，并将 `switch_language` 改为 `Language: switch to Chinese` / `语言：切换至英文`。去除新增键并恢复原切换文字后，重建 JSON 的 SHA-256 与先前已审核 UI `1c2e4721bc9c065581b416152e2fa35048bd32f31f733cb77a06074875b9cd69` 完全一致。标签和无障碍提示双语同义；其余数学 UI 文字及两份蓝图未变，数学复核结论保持。

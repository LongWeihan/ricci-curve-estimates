# 几何定义与流方程独立语义审核

日期：2026-09-09。只读静态审核；本报告没有自行运行编译或可达公理检查。代码版本 SHA-256：

| 文件（相对 outputs/poincare-curve-control） | SHA-256 |
|---|---|
| CurveControl/Geometry/Basic.lean | ba910982435615287ee972ec2ac8ad5509988aa9a1e02d8f5f81019268040d6f |
| CurveControl/Geometry/Flow.lean | 8255b92a801170d496a7fc5fae5d86ecceb6349c9d8de7930e62a3cfd7265a02 |

## 结论与验收建议

未发现语义错误。Basic 的 v,S,H,q,k,hε,L,Θ,Θε,E 均直接从真实 metric/curve 和上游协变微分定义构造；Flow 是实际光滑、闭合、浸入曲线族及曲线缩短 PDE 的输入规范，没有目标速度、曲率或积分估计字段。

对看板现有“几何定义与流方程规范验收”节点（定义及基础性质编译、文献语义核对、无隐藏目标估计），当前范围足够进入验收：本静态语义审核支持该节点；仍须主代理取得相同版本实际编译与可达公理证据后才可标记 verified。此建议不表示 SpatialCurve 的正交性、速度演化、曲率演化或任何后续节点已完成。

Flow 必须与上游 `IsRicciFlowOn g J` 联合使用，不能把独立 `IsCurveShorteningFlowOn` 宣称成完整 Ricci 环境。根估计还须加入有限时间区间/环境张量界或紧性，不是定义节点的欠缺。

## 实际切向量与 chart 识别

Basic 的 `curveVelocity` 复用上游 moving-foot 定义：在 x 固定后，对局部曲线 y↦extChartAt I (γ x)(γ y) 求导，得到 T_{γ x}M 的模型坐标。不是对随 x 变化的 chart 一起求导。

`covDerivAlong` 正确对 `chartFieldCoord (γ x) γ W` 求导，再加 Γ(cₓ,W)。不能改成裸 `deriv W`，因为即使 Lean 的各 tangent fiber 底层都是 E，沿不同点的 E 数值仍需 tangent bundle trivialization 转换。当前代码已经保留这一转换。

连接依据见上游 `Ch02/CovDerivAlongCurve.lean`：

- `chartFieldCoord_self`：基点自身的 fiber trivialization 为恒等，因此公式里的 `W x` 确实等于该 chart 的坐标。
- `hasDerivAt_extChartAt_comp` 与 `chartFieldCoord_curveVelocity_eq`：导数按 `tangentCoordChange` 变换，支持任意包含该点的有效 chart。
- `HasCovDerivAlongAt`：局部 chart source、真实曲线导数、真实坐标场导数以及 Christoffel 公式。
- Basic 的 `covDerivAlong_eq_of_hasCovDeriv` 对这一真实 predicate 的实例直接识别 totalized 值。

Christoffel contraction 来自 metric 的 chart Christoffel 系数，不是独立任意 Γ。由此曲率定义 `(1/v) ∇ₓ((1/v)cₓ)` 是 ∇ₛS。当前没有额外证明完整 chart-change 协变恒等式；它复用上游规范作为定义接口。后续若接抽象 Levi–Civita connection 或 spacetime curvature，要明确使用/证明相应 bridge，而不能仅凭两个 E 类型相同就改写。

无需假设 γ 的全像落在一个 chart；每个基点只需局部 chart。平滑曲线自动局部留在 chart source。Flow 的联合 `ContMDiffOn` 足以在合法 time slice 提取空间平滑性，空间方向是 ℝ 全域，故端点 t 的空间微分不受时间边界影响。

## 自交、闭合、参数及正则性

- γ:ℝ→M 与 period-one 描述 ℝ/ℤ 上闭曲线的 lift。平滑+周期使所有空间导数周期，不需要全局 injectivity 或 embedding。
- 向量场 W 是依赖参数 x 的 `∀ x, TangentSpace I (γ x)`，因此 γ(x₁)=γ(x₂) 时仍允许 W(x₁)≠W(x₂)。curvatureVector 也可依赖不同分支，self-intersections 没有被排除。
- v=√g(cₓ,cₓ)；非零 cₓ 给 v>0，S 的单位性质正确。曲线族浸入明确要求此非零性。
- q 与平方根、正则化的基础性质数学正确；新增 Θε 与 E 均采用真实弧长权重 v，而不是 dx。
- Bochner/interval 积分和 `deriv` 是 totalized 定义。单独 Basic 允许不可积或不可微输入，不意味着其 junk 值具有几何意义。联合 Flow 的平滑与浸入，加 g 的真实光滑性，应在后续层证明可积性与微分识别。当前注释明确了这一边界。

## 时间 within 方程

Flow 方程对时间曲线 s↦c(s,x) 在 t 的同一基点 c(t,x) chart 使用 `HasDerivWithinAt ... J t`，右侧 curvatureVector 是该同一 tangent fiber 的值。因此左、右两边识别正确，并未漏一个 chart differential。

t 在 interior J 时，`hasDerivAt_timeChart` 从 neighborhood 条件得到经典导数；`timeVelocity_eq_curvatureVector` 再取 deriv，语义正确。端点不声称任意全域 c 的经典 deriv 等于 H，避免了错误的区间外延拓假设。

任意 J 上 `HasDerivWithinAt` 在孤立点可能不唯一/退化。这不构成本局部 predicate 错误，但完整 Ricci 流不能仅用该 predicate。上游 `IsRicciFlowOn` 已明确 `J.OrdConnected`、`J.Nontrivial`、空间时间联合 metric 光滑与 within Ricci 方程；配合它时，J 是非退化实区间，端点的相应单侧导数有通常意义。紧闭子区间上的联合平滑提供分析层所需正则性。

`IsCurveShorteningFlowOn` 是光滑已存在的输入，没有存在或延拓结论；既不要求 tangentially reparametrized flow，也不允许额外切向速度。这与固定参数 PDE cₜ=H 的目标一致。

## 后续必须保持的明确边界

根定理应传入真实 `IsRicciFlowOn g J` 与 `IsCurveShorteningFlowOn g c J`，从它们推导目标估计。还需证明空间 `HasCovDerivAlongAt` 实例、空间导数与时间导数交换、joint smoothness 下 metric/connection 演化，以及产品圆常数统一。不得把这些变成定义字段后称其自然获得。


## 最终定义版本复核与实际证据（2026-09-09）

本节更新首轮仅静态的证据状态。Basic 版本未变；上表 Flow 版本已更新到最终编译版本 8255b92a801170d496a7fc5fae5d86ecceb6349c9d8de7930e62a3cfd7265a02。

已独立读取并核对 `outputs/poincare-curve-control/verification/CurveControl-Geometry-Basic.json` 与 `CurveControl-Geometry-Flow.json` 以及 Flow log。文件 hash 与当前源码一致；Lean 4.32.1、mathlib 520045ab14e26149ee970e2e617ca04b09bde5d6；Basic 的 23 个公开声明、Flow 的 5 个公开声明全部有 axioms 输出，compile exit=0，extra_axioms=[]，只包含 propext/Classical.choice/Quot.sound。

Flow 的改动仅消除 metric 名字歧义、冗余 typeclass 参数并 `include hc`，没有改变其实际几何前提。另由现有 `run_lean.py env lean --stdin` 成功加载编译模块并对四个导出定理执行 `#check`（exit 0）；输出逐个确认 `speed_pos`、`tangent_unit`、`hasDerivAt_timeChart`、`timeVelocity_eq_curvatureVector` 均明确含 `(hc : IsCurveShorteningFlowOn g c J)`。两个时间导数声明仍明确要求 `t ∈ interior J`。没有因 section variable elaboration 而遗漏真实 flow 前提。

**最终建议：几何定义与流方程规范节点符合其现有验收范围，可由主代理标记 verified。** 这是定义节点的结论，不代表曲率演化或积分估计节点完成。

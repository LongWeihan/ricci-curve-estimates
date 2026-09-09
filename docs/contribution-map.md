# 贡献与接入地图

署名：GPT-6 Astra（AI 模型）与 Juii-hang Leung（龙维汉）；更新日期：2026-09-09。本文区分数学来源、已有 Lean 基础设施、本项目新增声明及当前交付边界；不主张新的数学发现，也不推断任何团队的内部需求。

本次完成的主链，是从**真实 Ricci 流及真实光滑浸入闭曲线收缩流**出发，得到长度、曲率能量及总曲率的估计。曲线族的统一初值传播、任意静态一维因子的实际产品几何、环境常数存在性和正尺度索引统一主定理均已完成。冻结核心已通过构建、公理检查及独立 Astra 语义复核；本审阅版另含实际缩放应用。当前完整覆盖和可复现版本以 [发布记录](../verification/release-check.json) 实际绑定的源码与运行结果为准。

## 来源及直接依赖

| 层次 | 固定来源 | 实际复用内容 |
|---|---|---|
| Lean / mathlib | Lean 4.32.1；mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6` | 流形、切丛、模型变换、Fréchet/within 微分、有限维线性代数、积分换序与参数积分、FTC、指数比较等通用基础。我们没有重建这些基础，也没有把 mathlib 描述为已包含整条目标曲线估计。 |
| frenzymath 几何库 | [Poincare-Conjecture，固定提交 bb91a091f0b968f8bbe8d861e025a88d82b161be](https://github.com/frenzymath/Poincare-Conjecture/tree/bb91a091f0b968f8bbe8d861e025a88d82b161be) | `formalized-sources/DoCarmo` 的真实 RiemannianMetric、canonical Levi–Civita、chart Gram/Christoffel/curvature、诱导与产品度量；`formalized-sources/MorganTian` 的沿曲线协变导数、Ricci 与协变 Ricci、时变度量及 Ricci 流坐标接口。 |
| 数学目标 | 同提交的 `PoincareConjecture/blueprint/src/chapters/curve-shrinking-estimates.tex` | 给出分解与目标陈述；相关标签在冻结蓝图中标记 `notready`，不是现成 Lean 定理可直接导入。 |
| 修正后的数学路线 | [Morgan–Tian，2015-12-02 修正](https://arxiv.org/html/1512.00699)，Lemma 0.1–0.4 | 漏掉联络时间导数会损失线性曲率误差；总曲率最终常数必须同时依赖初始总曲率与初始长度。本实现保留这一修正。 |

本项目的 [lakefile.lean](../lakefile.lean) 直接引用本机固定 mathlib checkout 与 MorganTianLib 源目录；MorganTianLib 再直接依赖同源 DoCarmoLib。新证明位于 `CurveControl/`，并非修改上游蓝图后把其标记视为证明。冻结 frenzymath 上游 archive 根目录实际带有 Apache-2.0 LICENSE；此前选择性抽取遗漏该文件，导致旧版文档误写“未发现”。本版纠正这一记录，保留 [geometry-LICENSE.txt](../third_party/licenses/geometry-LICENSE.txt) 与 [mathlib-LICENSE.txt](../third_party/licenses/mathlib-LICENSE.txt)。项目根 [LICENSE](../LICENSE) 为 Apache-2.0；构建文档使用的 KaTeX 0.16.22 另保留 MIT [许可证](../third_party/katex/LICENSE) 和 [来源记录](../third_party/katex/SOURCE.json)。准确归属见 [NOTICE](../NOTICE)。

## 从蓝图标签到实际声明

下表的行号是上述冻结 TeX 的位置。Lean 文件链接均指向本项目新增文件。

| 冻结蓝图标签 | 本项目接入段 | 对照关系与边界 |
|---|---|---|
| `lem:curve-flow-speed-and-tangent-evolution`（16） | [SpeedEvolution](../CurveControl/Geometry/SpeedEvolution.lean)、[CurveEvolution](../CurveControl/Geometry/CurveEvolution.lean)、[LengthEstimates](../CurveControl/Geometry/LengthEstimates.lean) | 证明真实速度/单位切向量演化及移动弧长密度；不是把速度律存成待用户提供的结论字段。 |
| `lem:space-time-metric-connection`（49） | [MovingMetric](../CurveControl/Geometry/MovingMetric.lean)、[RicciConnectionVariation](../CurveControl/Geometry/RicciConnectionVariation.lean)、[EvolvingConnection](../CurveControl/Geometry/EvolvingConnection.lean) | **路线适配**：使用纯空间时变联络及其变分；未字面构造蓝图的时空度量及所有时空联络声明。 |
| `thm:curve-flow-curvature-evolution`（753） | [CurvatureEvolution](../CurveControl/Geometry/CurvatureEvolution.lean)：`IsCurveShorteningFlowOn.hasDerivAt_curvatureSq_time` | 从同一个实际 g,c 推出修正后 q 时间演化；已关闭联络变分、chart germ、高阶协变正则性与曲率符号桥。 |
| `lem:regularized-curve-curvature-inequality`（808） | [RegularizedPDE](../CurveControl/Analysis/RegularizedPDE.lean)：`deriv_regularizedNorm_le`；[CurveEstimates](../CurveControl/Geometry/CurveEstimates.lean) 关闭实际几何输入 | 从 q PDE、真实 Kato 与 ε>0 推出 hε 的不等式；条件分析引理与实际 flow 根明确分层。 |
| `lem:curve-flow-length-total-curvature-evolution`（843） | LengthEstimates；[CurveEstimateAssembly](../CurveControl/Analysis/CurveEstimateAssembly.lean)：`ScalarCurveHypotheses.regularized_deriv_le` | 实际证明 L 与 Θε 的内点导数和积分控制。**没有宣称已字面证明未正则化 Θ 局部 AC 及其 a.e. 微分不等式。** |
| `lem:coupled-length-curvature-comparison`（880） | CurveEstimateAssembly：`regularized_comparison`；[InteriorComparison](../CurveControl/Analysis/InteriorComparison.lean) | 对固定 ε 的光滑量做内点微分、闭端点连续比较；不是蓝图中任意 AC 函数的同名 a.e. 版本。 |
| `thm:curve-flow-length-total-curvature-bounds`（905） | CurveEstimates：`IsCurveShorteningFlowOn.curve_estimate`、`curve_family_estimate`、`curve_family_uniform_estimate` | **实际终值目标已接入**；先比较 Θε，再 ε→0。相同指数系数控制任意索引族，初值界单列。 |
| `lem:product-circle-parallel-geometry`（82）及最终辅助圆尺度统一 | [OneDimensionalCurvature](../CurveControl/Geometry/OneDimensionalCurvature.lean)、[ProductModel](../CurveControl/Geometry/ProductModel.lean)、[ProductL2Connection](../CurveControl/Geometry/ProductL2Connection.lean) 等 | 一维 canonical curvature/Ric/covRic 为零，真实 L2 产品模型、Γ/Rm/Ric/∇Ric 分裂、产品 Ricci 流及最终正尺度统一根均已实现；见 UniformProductEstimates。没有宣称 ramp 全部平行几何或 ramp 全局存在已经实现。 |

## 新增证明与适配的数学内容

**纯空间联络。** 设 X=cₓ、v=|X|、S=X/v、H=DₛS、q=|H|²、P=DₛH+qS。用固定有效空间 chart 计算，再经切丛读回识别 intrinsic 向量；不对随脚点更换的裸坐标表达直接求导。新增证明把上游时变度量与联络 API 接成实际沿曲线公式，包括

```text
∂t〈V,W〉 = −2 Ric(V,W) + 〈DtV,W〉 + 〈V,DtW〉,
〈(∂t∇)(S,S),H〉 = −2(∇S Ric)(S,H) + (∇H Ric)(S,S),
q_t = Dₛ²q − 2|P|² + 2q²
      + 4q Ric(S,S) − 2Ric(H,H) + 2rm(H,S,H,S)
      − 4(∇S Ric)(S,H) + 2(∇H Ric)(S,S).
```

`rm` 的槽顺序和上游 do Carmo 曲率符号经过显式转换；空间 P 也没有被当成时空正交投影。与 Morgan–Tian 时空写法的纸面等价性核对见 [spatial-connection-route](spatial-connection-route.md)，实际 Lean 根审核见 [curvature-root-semantic-review](curvature-root-semantic-review.md)。这是证明路线与库接口的适配，不是重新发现该数学估计。

**端点。** [Flow](../CurveControl/Geometry/Flow.lean) 的真实曲线流条件以 `HasDerivWithinAt … J t` 表达时间方程。高阶演化在 `interior J` 上证明；闭区间连续性负责初值与终点传递。不把初值端点擅自当成有双侧高阶导数的内点，也不要求流提前延拓到负时间。

**完整积分链。** 正则化量 hε=√(q+ε²)，ds=v dx。新增分析文件把 mathlib 的参数积分/FTC/比较工具具体用于这组移动密度：证明积分可积性与换微分的正则性条件；由真实闭曲线周期性消去扩散通量；处理 hεq 与 k³；得到 Θε+L 的统一 ε 比较。最后使用 [RegularizedIntegral](../CurveControl/Analysis/RegularizedIntegral.lean) 的

```text
0 ≤ Θε(t) − Θ(t) ≤ ε L(t)
```

传递已证明的两端估计。不交换极限与时间导数，不要求用户提供 domination、扩散积分为零、Θ 的导数或最终比较。蓝图的 AC/a.e. 节点若有下游需要，仍需另行提供；当前替代路线已足以推出其最终全局界。

**真实产品而非范数伪实例。** 上游提供 `DCProductMetric`，本项目证明其坐标连接与曲率分裂，并将模型经连续线性等价变为 `WithLp 2 (E × F)`。ProductModelCoordinates 与 ProductL2Connection 实际证明 Gram、Γ、∂Γ、chart Rm 的运输，未给 max 范数 E×F 安装虚假的 InnerProductSpace，也未假定 LC 自然性。一维平坦性由维数一、曲率反对称及向量共线证明，不是 flatness 输入。最终尺度统一路线是从 base 张量界直接继承，不能用辅助圆 injectivity radius 给出会随 λ 退化的替代常数。

## 数学团队可以直接接入的接口

给定真实 `IsRicciFlowOn g J`、`IsCurveShorteningFlowOn g c J`、a≤b、[a,b]⊆J，以及真实环境张量界 `AmbientBounds.UniformTensorBoundsOn g J B K D`，已经验收的 `IsCurveShorteningFlowOn.curve_estimate` 输出

```text
L(t) ≤ L(a) exp(B(t−a)),
Θ(t)+L(t) ≤ (Θ(a)+L(a)) exp(C(t−a)),
C = max(6B+2K, 6D)/2 + B,       a ≤ t ≤ b.
```

Θ 单独的同一右侧界由 L≥0 得到。`IsCurveShorteningFlowOn.curvatureEnergy_integral_le`（位于 LengthEstimates） 提供实际曲率能量 E(t)=∫k²ds 的时间积分控制，可接下游 good-time 选择。

`curve_family_uniform_estimate` 对任意索引 i 使用同一 B,K,D：若 Lᵢ(a)≤L₀、Θᵢ(a)+Lᵢ(a)≤Q₀，则上式右侧分别换成 L₀、Q₀。若输入是 Θᵢ(a)≤Θ₀，可取 Q₀=Θ₀+L₀。此接口不需要索引空间正则性，也没有声称已从任意紧致参数族自动提取初始界。

以下仍是合法上游输入或后续范围：

- 给定光滑 Ricci 流及光滑浸入闭曲线流的存在；本模块不证明短时存在、延拓、奇性或有限消失本身。
- 闭曲线以周期一的 ℝ 参数化表达；从其他圆参数/已有流对象接入时须提供相应表示和实际流条件。
- 产品应用中，提供真正一维流形及实际光滑 RiemannianMetric。未构造具体 `AddCircle ℝ/λℤ` 图册；新增应用模块已从供给的真实 h₀ 构造全部 λ>0 的 λ²h₀。
- 初始长度及总曲率的统一界；多边形/ramp 逼近与这些初始界的构造属于蓝图更前段。
- 显式环境张量界仍可作为低层 `curve_estimate` 的复用接口；紧致基底最终根已在内部构造这些界，并证明向一维产品继承。

## 证据和当前状态的读法

本次文档读取时，`verification/CurveControl-Geometry-CurveEstimates.json` 与当前源码 hash 一致，9/9 公开声明编译及公理检查通过；对应独立语义审核已记录实际 flow 根不存在遗留目标 PDE/Kato 假设。`ProductL2Connection` 同样为 8/8，通过且无额外公理，SHA-256 为 `9be9087732efdf3460adfe8397d542a8941e2fe64504b649550de9f293c8559b`。

`CompactAmbientBounds.exists_uniformTensorBoundsOn` 已从紧致 M 上真实 smooth metric family 构造 B,K,D；`ProductIntrinsicCurvature`、`ProductCovRicci`、`ProductAmbientBounds` 与 `ProductFlow` 已关闭实际产品张量及流方程。`UniformProductEstimates` 的两个最终声明为：

- `exists_uniform_static_product_family_estimate`：先选 B,C，再量化任意外部索引、因子度量、曲线族和初始 L₀,Θ₀。
- `exists_uniform_positive_scale_product_estimate`：显式 λ>0 版本，不要求尺度有统一正下界，也不要求 λ 方向连续或光滑。

其结论是 `Lλ,i(t)≤L₀ exp(B(t−a))` 与 `Θλ,i(t)≤(Θ₀+L₀) exp(C(t−a))`；最终输入只有真实紧致基底 Ricci 流、静态一维因子度量、已存在的实际曲线流和共同初值界。不存在用户另行提供张量分裂、q PDE、Kato、积分求导或比较结论的假设。

最终源码 SHA-256 为 `b0ab134707b559ef04f8288f19987e5d6cd4e201caf7c1cc3d115d349d975bda`，对应逐文件记录为 9/9 声明通过。整库构建与环境级全部声明检查见 [release-check.json](../verification/release-check.json)；独立语义验收见 [最终统一估计审核](final-uniformity-semantic-review.md)。本版包含新增缩放应用，当前覆盖范围以该发布记录实际绑定的源码及运行结果为准，不沿用历史声明统计。独立代理复核不等于外部人类同行评审。

本贡献的单位是具体定义、证明、模型运输与整链集成，而非新数学发现；更不等同于整个庞加莱猜想形式化完成。


## 审阅版新增的实际缩放应用

[StaticFactorApplication.lean](../CurveControl/Examples/StaticFactorApplication.lean) 在冻结几何/分析核心之上新增应用层。`CurveControl.Examples.StaticFactorApplication.scaledFactorMetric` 从真实 h₀ 与 λ>0 实际构造 λ²h₀，证明正定、光滑和所需度量结构；`scaledFactorMetric_inner` 与 `scaledFactorMetric_norm` 分别证明双线性形式乘 λ²、切向量长度乘 λ。`scaledProduct_isRicciFlow` 由基底方程与一维性推出实际产品 Ricci 流。

`exists_scaledFactor_curve_bounds` 在 h₀、曲线及初值界之前选择 B,C，证明同时对所有正尺度和曲线成立的指数界；`exists_scaledFactor_fullInterval_bounds` 再以 b−a 统一整个闭时间区间。该应用已实际编译并通过独立 Astra 语义复核；本版整库覆盖仍以 [release-check.json](../verification/release-check.json) 的真实运行记录为准。它不构造圆图册、ramp 或解存在性。

审阅入口见 [英文报告](../paper/curve-estimates.pdf)、[蓝图](../website/index.html)、[接入指南](integration-guide.md) 和 [复现说明](reproduction.md)。作者信息待提供，独立 AI 复核不等于外部人类同行评审；详见 [AUTHORS](../AUTHORS.md)。

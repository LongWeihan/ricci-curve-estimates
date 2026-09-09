# 新增几何演化组件独立语义审核

日期：2026-09-09。范围：SpatialCurve、MovingMetric、EvolvingConnection、CurveEvolution 四文件，只读审核数学陈述、实际定义及证明体；没有修改代码或看板。

## 结论

四份组件在各自显式假设下语义正确，未发现漏掉 ∂ₜΓ 或 metric variation 的问题，也未发现用 totalized derivative 规避实际正则性的根结论。SpatialCurve 与 MovingMetric 已处理实际流形数据；EvolvingConnection 与 CurveEvolution 是真实 Fréchet 导数构成的坐标分析层。

`CurveEvolution.normal_evolution` 保留了正确的 +A(S,S)，但其 `hspeed` 仍是待由实际曲线几何证明的输入；Γ、v、a 与真实 Levi–Civita、速度、q+Ric(S,S) 的识别尚未在该文件中完成。因此这些结果有实质进展，却不能据此验收完整平方曲率演化节点。

主代理报告这四份已编译。本文主要提供独立语义审核；审核时在正式 `verification/` 下尚未找到这四份的 JSON/log，故不额外声称已独立核对它们全部公开声明的可达公理结果。

## 精确版本

以下为读取时 SHA-256，相对 `outputs/poincare-curve-control/CurveControl/Geometry/`：

| 文件 | SHA-256 |
|---|---|
| SpatialCurve.lean | dfc704a1cab50343214ffeb98549d32f6da30d6dd3536b8ef4d95fa4d844991b |
| MovingMetric.lean | 5b3df85812ad95884569265dbdc04c15dbfe8049c755d172ca2b3bb504bd4866 |
| EvolvingConnection.lean | 3998702f4353518a0300c6ccfc9530601c95b13960ccee64725f8d8d261f1299 |
| CurveEvolution.lean | 314c6ac9490268e35b4625c4f8b643aab4adda1f0f07bb6871573d89fc3fc19e |

## 1. SpatialCurve：actual regularity 已有关键闭合

行 20–30 从实际 manifold smoothness/continuity 得 moving-foot chart 的光滑性与局部 source membership。没有假设整条曲线落在单 chart。

行 43 的 `contDiffAt_chartFieldCoord_velocity` 用真实 chart transition bridge 将 velocity field 的固定 chart 表示等同于该固定 chart 曲线的导数，然后从 smooth γ 推出该场光滑。它没有把不同点的 E fiber 数值当作同一个无须转换的坐标，也没有对任意选择的 moving chart 裸求导。这是排除 derivative junk 的实质桥梁。

行 60 的 `hasCovDerivAlongAt_velocity` 给实际协变加速度；行 72 的 speed 空间导数从 metric compatibility+正速度+sqrt 链式法则得到。它不是时间速度演化，调用时不可混用 x 导数与 t 导数。

行 104 的 unit tangent 实际协变可微性由 inverse speed 的可微性与向量场乘积法则推出；只需点处非零，因为可微速度的连续性给局部非零。

行 119 的 `curvatureVector_orthogonal_of_contMDiff` 最终只假设 smooth γ 与 immersion；此前条件版 `curvatureVector_orthogonal` 所需的 hS 已真正构造。所有 y 非零的假设比点态更强，但符合 smooth immersed closed flow 的每个 time slice，且用于直接对全域单位恒等式求导。没有把正交性或目标估计当输入。

尚需将 `IsCurveShorteningFlowOn.smooth` 的时间切片抽出成全域空间 `ContMDiff γ`；这是普通 slice regularity 桥。周期性对这些局部性质无要求，积分节点再使用。

## 2. MovingMetric：明确保留 g 变化项

行 14 的 diagonal lemma 明确假设 F 在 (t,t) 的联合 Fréchet 可微性；不是从两个 partial derivative 单独存在错误推出 diagonal derivative。方向 (1,1)=(1,0)+(0,1) 给出两项相加。

行 38 的联合 metric pairing 可微性从 `IsSmoothMetricFamilyOn` 的真实 chart Gram entries 联合光滑、曲线实际 chart 导数以及 V,W 的 tangent-bundle coordinates 推出。证明中 chart 固定在 γ(t)，g 的时间变量与 γ/V/W 的参数变量先分开，随后取对角线。

行 90 的 `hasDerivAt_movingMetricInner` 接受 `IsMetricVariationOn`，它指定固定点和固定 tangent vectors 的真实 metric 时间导数，不是待证明的移动曲线平方范数公式。其结论是

    d/dt g(t)(V,V) = h(V,V)+2g(t)(DₜV,V).

其中 Dₜ 取当时 g(t) 的沿曲线协变导数。行 110 的 Ricci specialization 由真实 `IsRicciFlowOn` 得 −2Ric(V,V)，metric variation 修正明确存在。

所有结论限制 t∈interior J，正确避免了任意区间外函数值决定经典导数的问题。此结果可用于 X 与 H，但必须给出对应沿时间曲线的实际 `HasCovDerivAlongAt` 及其值的几何计算；任意数值 DV 不能凭空传入。

## 3. EvolvingConnection：真实 ∂ₜΓ 与交换式

坐标 Γ 是连续双线性映射值函数。`covDerivAlong` 定义为 dV+Γ(du,V)。行 28 的展开包括四项：V 的二阶导数、Γ 的导数、u 的二阶导数及 V 的一阶导数。u,V 的 C² 与 Γ 的可微性足以保证它们是真实导数。

行 71 的 commutator 由二阶导数对称及线性代数消项证明；无需 torsion-free。行 92 对 mixed velocity 才显式要求 Γ 对两个向量变量对称。没有把 Schwarz symmetry 或 commutator 结论作为公理化输入。

时间空间专用部分正确区分：

- `coefficients Γ u p = Γ(p.time,u(p))`，沿曲线后的实际系数。
- `curvature Γ t x X Y Z` 只对 Γ(t,·) 求空间导数，为 R(X,Y)Z 的正向 convention。
- `timeVariation Γ t x = fderiv (s↦Γ(s,x)) t 1`，固定空间点的真实时间偏导。
- 联合可微性提供 spatial/time slice 与总导数的拆分，不将沿 c 的总导数误当成 ∂ₜΓ。

行 172 的式子是

    DₜDₓV−DₓDₜV = R(uₜ,uₓ)V + (∂ₜΓ)(uₓ,V).

符号和因子正确。此处 Γ 可以是任意 sufficiently regular connection coefficients，尚未证明它来自给定 metric。最后需要取 Γ 为实际 g(t) 的固定 chart Christoffel contraction，并证明它的 timeVariation 符合 Ricci connection variation；这是独立桥，不是此通用交换引理的缺陷。

## 4. CurveEvolution：germ、非零与所需正则性

`tangent=uₓ/v`、`normal=Dₛ(tangent)` 不是独立给定向量场；内部 S,H 的 C³/C² 正则性分别从 u∈C⁴、v∈C³、Γ∈C²、v(p)≠0 推出。Γ 的实值含义以及 v 为真实速度暂时并未加入，因此这些名字在通用层只在后续识别后具有“单位/法向”的几何含义。

行 69 的 `tangent_evolution` 从 inverse-speed 链式法则、torsion-free mixed velocity 与 cₜ=H germ 推出 DₜS=DₛH+aS。`hflow` 必须是邻域相等，才可对其空间导数作替换；当前实际使用 `=ᶠ[𝓝 p]`，没有误用单点相等。点处 hspeed 足够，因为这里只求一次时间导数。

行 129 的 arclength commutator 是

    DₜDₛV = DₛDₜV + aDₛV + R(uₜ,S)V + (∂ₜΓ)(S,V).

v⁻¹ 时间变化的 a 项和显式 ∂ₜΓ 项都保留。v 只需非零而不需正数，对这一坐标代数恒等式充分；真实速度的正性由几何实例给出。

行 170 的 `normal_evolution` 要对 tangent evolution 再作空间微分，因此正确提升 hflow、hspeed、torsion symmetry 为邻域条件。`hflow.eventually_nhds` 提供每个邻近点的 flow germ，`hv.continuousAt.eventually_ne` 提供局部非零，而 `hu.eventually`、`hv.eventually` 提供邻域所需 regularity。没有只凭 p 点方程就对两边求导。

得到

    DₜH = Dₛ²H + 2aH + (Dₛa)S + R(H,S)S + (∂ₜΓ)(S,S),

与独立纸面推导一致；尤其 2a、曲率参数顺序及 ∂ₜΓ 的正号正确。

## 5. 目前最关键的几何连接缺口

以下均应由真实 g,c 的输入证明，不能提升为最终根假设：

1. 固定局部 chart 的 u=chart(c) 与 Basic 的 moving-foot velocity/unit tangent/curvature 的转换；保留 fiber trivialization，允许自交，不要求整条曲线一个坐标域。
2. v 取实际 metric speed，证明其 joint C³、局部正性；a 取 q+Ric(S,S)，证明所需微分性。
3. 由真实 `Flow.equation` 在内点得 chart hflow germ；由实际速度几何推导 hspeed germ。**CurveEvolution 接受 hspeed，故它本身没有证明速度演化。**
4. Γ 是实际 Levi–Civita，证明联合光滑、无挠性及 actual curvature identification。
5. 将 `timeVariation` 识别为 A=∂ₜ∇，证明 g(A(S,S),H)=−2(∇_S Ric)(S,H)+(∇_H Ric)(S,S)。不能仅给 Γ 的导数一个新名字便当作修正项已经闭合。
6. 将 normal evolution 和 MovingMetric 的真实 −2Ric(H,H) 合并；再从 spatial norm decomposition 得完整 q 演化。此处仍需 Psp 的实际定义与 Kato/空间内积恒等式。

## 验收建议

四文件作为各自表述的局部组件，独立语义审核通过。可保存为真实子引理进展。Basic+Flow 的“定义规范”节点可独立验收；速度/曲率演化节点还须完成上述根连接及最终声明的编译、公理检查。不能因 `normal_evolution` 的名字或已编译状态而跳过其 hspeed 与实际 Γ 接入前提。

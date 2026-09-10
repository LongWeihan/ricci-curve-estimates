# CurvatureEvolution：实际几何根独立语义审核

2026-09-09。只读源代码、依赖和验证证据，未修改 Lean 或看板。

冻结对象：`CurveControl/Geometry/CurvatureEvolution.lean`，SHA-256 `036bd50e689616d79ba89130aedf81dc8c5c588e1a25946af913cfe2263adb14`，608 行。对应 verification JSON 记录 31 个公开声明（30 个 theorem 加一个 def），31/31 打印，compile exit 0，extra_axioms=[]。这些是父代理真实编译及公理检查证据；本文提供独立语义判断。

## 结论与范围

审核通过：`IsCurveShorteningFlowOn.hasDerivAt_curvatureSq_time` 是真实 Ricci 流及真实浸入曲线流的内点曲率平方演化根。除环境 manifold/typeclass、实际 `hc`、实际 `hflow`、`t ∈ interior J` 和空间点 `x`，没有附加速度律、曲率 PDE、Kato、联络变分、混合导数或 H 的协变可微性假设。此前条件几何链中的正则性与 germ 缺口在此文件均已关闭。

可据此验收曲率演化节点。本文件本身尚不证明积分比较最终根；需要后续 CurveEstimates 把此等式和实际 ambient bound、Kato、速度律、闭端点连续性接入已审核标量链。λ 产品常数统一仍属独立交付范围。

## 1. 实际几何及局部图册桥

第 32–69 行从实际 `chartFieldCoord`、`covDerivAlong` 接入 upstream chart-covariant Levi-Civita 导数。这里固定空间 chart α，再读取沿 c 的切向量；并非对随脚点任意切换的裸坐标表达求导。

`eventually_interior_chart_at` 用真实 joint smooth/continuous family 和 chart source 开性给出邻域。每次从向量场表达识别导数，都提供有效图册邻域上的 `EventuallyEq`，不是仅一点相等。因而 `chart_covSpace_eq`、`chart_covTime_eq`、`chart_covArc_eq` 对函数 germ 求导合法。只要求当前脚点在某张图中，不要求整条闭曲线或整族落在一个全局 chart，自交也不受排斥。

实际 S 的表达由速度和空间方向 fderiv 得到；`chartCurvature_eq_normal` 再把 H=v⁻¹DₓS 识别为解析 `normal`。使用 hc 的 immersed 保证实际速度严格正，不依赖总化逆在零点给出的伪公式。

## 2. H、DsH 及实际导数正则性

`contDiffAt_chartCurvatureField` 使用流方程将固定图册 H 表达识别为真正的时间方向 fderiv(u)。由于 c joint smooth，这个表达内点光滑。这里使用允许作输入的 cₜ=H，没有把目标 Hₜ 演化作为输入，也没有从 H=H 的循环定义获得正则性。

随后构造 H 的实际时间、空间 `HasCovDerivAlongAt`。`contDiffAt_normal_in_chart` 通过已证明的 H/normal germ 等式转移光滑性；真实 Γ joint C²、v>0 得到 `covArcNormal` C²，再通过一阶及二阶 arc bridge 获得实际 DsH 的协变可微性。`arcDeriv_arcDeriv_curvatureSq_closed` 因此真正关闭了此前 CurvatureGradient 中 hD/hDD 两个输入，不再把它们交给根调用者。

## 3. 速度、联络及向量演化

令 a=q+Ric(S,S)。`fderiv_curveSpeed_time` 从已证明的真实速度 HasDerivAt 和 joint 可微性，通过导数唯一性得 vₜ=−av。`differentiableAt_curveSpeedDecay` 把实际 a 在邻域上写成 −vₜ/v，故 a 可微。它没有反过来假设 a 的目标公式。

`normal_evolution_in_chart` 提供解析引擎的全部输入：u C⁴、v C³、Γ C²、v≠0、Γ 无挠性，和在开邻域成立的真实流方程及真实速度律。因此解析中间引理虽有 hcsf/hspeed，最终实际几何声明没有遗留这些假设。

所得向量式为

    Dt H = Ds²H + 2aH + (Ds a)S + R⁺(H,S)S + A(S,S),
    A = ∂t Γ（固定空间坐标，非沿 c 的 Γ 总导数）.

`curvatureVector_evolution_canonicalChart` 用固定 chart 的时间、一阶和二阶空间桥回到实际脚点切空间。最后取 α=c(t,x) 仅用于该点坐标读取恒等；之前所有求导都在固定 α 的邻域内完成，故没有漏掉图册变化项。

## 4. lowering 与曲率符号

`timeVariation_pairing_canonical` 调用已审核的真实 RicciConnectionVariation 定理，恢复 canonical foot，并证明 inverse tangent readback 等于恒等。输出确为

    g(A(S,S),H) = −2(∇S Ric)(S,H) + (∇H Ric)(S,S).

`AmbientBounds.covRic` 的第一个向量槽是导数方向。这里 lowering 是 g·(∂tΓ)，不是 ∂t(gΓ)，故不应在这个步骤再添加 gₜΓ。真实 gₜ 的贡献由另一条 moving-metric 乘积律独立提供。

第 89–103 行 `chartCurvature_pairing_canonical` 关闭了先前审核指出的符号桥：upstream `curvatureFormAt_chartFrame` 明确有负号，代表 do Carmo R⁻=−R⁺；再用真实 Levi-Civita 四阶曲率末二槽反对称，证明

    g(R⁺(H,S)S,H) = curvatureFormAt(H,S,H,S).

因此最终 +2 AmbientBounds.rm(H,S,H,S) 正确。代码没有直接认同两个反号的曲率算子。

## 5. 最终 qₜ 的逐项来源

`hasDerivAt_curvatureSq_time_covariant` 首先从真实 moving metric 得

    qₜ = −2Ric(H,H) + 2g(DtH,H).

再代入向量式、g(S,H)=0，以及实际空间恒等式

    q_ss = 2|DsH|² + 2g(Ds²H,H),
    Psp = DsH+qS,  |DsH|² = |Psp|²+q².

恰得到根输出

    qₜ = q_ss − 2|Psp|² + 2q²
          +4q Ric(S,S) −2Ric(H,H) +2rm(H,S,H,S)
          −4(∇S Ric)(S,H) +2(∇H Ric)(S,S).

其中 +4q² 来自 2g(2aH,H)，与替换空间耗散产生的 −2q² 合并为 +2q²；(Ds a)S 由真正的 H⊥S 消去。无遗漏的 metric variation 或 ∂tΓ 项。

## 6. 文献与纯空间路线一致性

重新核对 [第 19.2 节更正，Lemma 0.2](https://arxiv.org/html/1512.00699)。该文使用 g(t)+dt² 时空联络，本实现是此前独立推导并审核的纯空间联络适配，保留全部修正，并非直接照搬其投影符号。修正导致线性 k 误差，后续总曲率控制因此要依赖初始长度。

以下为本审核的独立转换：置 α=RicSS、β=RicSH、δ=RicHH、T=∂t。时空投影 P̂=Psp+βT，故 |P̂|²=|Psp|²+β²；同时

    R̂(H,S,H,S)=rm(H,S,H,S)−αδ+β²,
    R̂(T,S,H,S)=−(∇S Ric)(S,H)+(∇H Ric)(S,S).

代入文献式，投影 −2β² 与曲率 +2β² 抵消，−2αδ 与显式 +2αδ 抵消，剩余导 Ricci 项合并为根声明的 −4/+2。代码明确采用 `normalCurvatureGradient` 的空间 P，没有把它当成时空非水平投影。

从实际 tensor bounds，修正误差可继续界为 (6B+2K)q+6D√q。此文件不预设环境界，故局部演化结论比最终有界估计所需条件更弱。

## 7. 时间边界和验收限制

本根只宣称 interior J 中的经典导数；这与固定图册开邻域以及高阶导数交换要求一致。没有声称 t=初值的双侧导数。已审核的闭时间连续性加内点比较接口可承担后续初值传递，不能将本根的 interior 条件擅自改写成 t∈J。

光滑浸入流存在仍为输入；未承诺存在、延拓或奇性控制。SigmaCompact、T2、有限正维、Boundaryless 等条件用于已选上游几何框架，对目标闭流形适用。总曲率在 H=0 不可微的问题需由正则化积分极限处理，本根仅涉及光滑 q，不涉及非法的 √q 时间导数。

独立运行检查补充：`#check @hasDerivAt_curvatureSq_time` 与 `#check @normal_evolution_in_chart` 成功，确认编译声明实际保留 hc/hflow 而不带额外目标条件；根声明 `#print axioms` 仅 propext、Classical.choice、Quot.sound，运行 exit 0。

## 8. 追加：CurveEstimates 实际最终根连接

冻结 SHA-256 `62e5710472d74a673e671bf3331ed904b4db4b09a102e9f3d05e7dba19802751`。已完整只读审核源文件，语义通过；本追加初写时父代理的全公开声明验证 JSON 尚未落盘，不能用本文替代该编译/公理证据。

`scalarCurveHypotheses_of_squaredPDE` 是明确的条件适配器，其 hqPDE 没有被伪装为无条件。真正 `curve_estimate` 中调用 `curvatureSq_time_le`，后者使用本次冻结的实际 q 时间导数根、真实投影平方、实际 TensorBoundsAt，完全关闭 hqPDE。

其余 scalar fields 逐项来自真实几何：q/v joint 内点光滑；actual within 初值 PDE 与 uniqueDiffOn_ricciTime 给闭矩形连续；q≥0 及浸入给 v>0；closed 给 period 1；单位 S 与实际 Ricci 张量界给 |r|≤B；SpeedEvolution 给 density；实际 mixed covariant derivative 构造后调用真实 metric Kato。P 是实际 normalCurvatureGradient 的 g(t) 范数，平方用 metricInner_self_nonneg 消去 sqrt，没有引入虚构耗散函数。

`Icc a b ⊆ J` 与 a≤b 足以让每个 t∈Ioo a b 属于 interior J：其证明直接用 Icc 在内点为邻域，合法且不额外要求 J 开。a=b 时无内点演化需求，闭端点最终结论由连续比较退化为等式。B,K,D 的非负性从 a∈J、真实脚点 c(a,0) 上的 tensor bounds 取得，并未假设任意空时间集合中的全称界能产生实数非负性。

常数 A=max(6B+2K,6D)，C=A/2+B。error 上界从绝对值界先取单边，再分别用 q≥0、sqrt(q)≥0 吸收到 A(q+sqrtq)，方向正确。scalar chain 的 hε PDE 产生 A/2 的线性及常数项，加 moving density 后比较 Θε+L，因此 C 必须是 A/2+B，源码与该值一致。最后 `simpa` 仅展开实际 weightedCurvature/totalCurvature/curveLength/curvature 的定义，不更换积分权重；输出为

    L(t) ≤ L(a) exp(B(t−a)),
    Θ(t)+L(t) ≤ (Θ(a)+L(a)) exp(C(t−a)).

Θ 本身无需端点或零曲率点经典导数：已审核标量根使用固定 ε>0 正则化、移动弧长积分、内点导数/闭连续比较和 ε→0，不交换极限与导数，也没有用户提供 domination、积分可积性、flux cancellation 或比较结论的假设。

`curve_family_estimate` 对任意索引 i 逐条调用同一个 actual root，B,K,D 不依赖 i。`curve_family_uniform_estimate` 仅增加允许的统一初始数据 L(a)≤L₀ 与 Θ(a)+L(a)≤Q₀，利用 exp>0 传播。Q₀ 是初始“总曲率加长度”上界，而非 Θ 单独上界；若给初始 Θ≤Θ₀，可取 Q₀=Θ₀+L₀。索引无需拓扑或正则性；这是对给定初值统一界更一般的接口，没有声称从紧致参数族自动提取这些界。

验收建议：同 hash 的严格编译和全公开公理检查完成后，可以结合先前 Analysis 文件证据及本独立语义审核验收 curvature、regularization、integration、comparison 四个节点。此建议不包含完整 uniformity 节点：真实任意一维产品张量/联络拆分及环境紧致性导出 B,K,D 的存在还须另外完成。当前 UniformTensorBoundsOn 是合法真实 ambient tensor bound 输入，而非已知目标曲率 PDE 的隐藏包装。

CurveEstimates 独立编译声明检查补充：`#check @IsCurveShorteningFlowOn.curve_estimate`、`#check @curve_family_uniform_estimate` 成功，实际声明恰为上述 hc/hflow、闭区间、真实 tensor bounds（族版本另有初始界）；`#print axioms curve_family_uniform_estimate` 仅 propext、Classical.choice、Quot.sound，运行 exit 0。全文件所有公开声明审计仍以父代理同 hash JSON 为准。

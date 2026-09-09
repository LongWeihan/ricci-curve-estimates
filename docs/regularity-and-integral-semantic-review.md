# 正则性、真实联络变分与积分组件独立语义审核

日期：2026-09-09。只读逐条核对冻结源码、必要上游定义与编译证据，未修改源码、未统一 build。使用现有 Lean runner 加载模块，对 4 个关键声明 `#check` 成功（exit 0）。

## 总结论与边界

五个文件在各自显式前提下独立语义审核通过，未发现端点导数、周期性、domination、二阶链式法则或 Ricci 联络变分的符号错误。

CurveRegularity 与 RicciConnectionVariation 是真实 g/c 的几何推论；SmoothIntegral 是从 joint regularity 自动建立积分技术条件的分析桥；RegularizedPDE、IntegralEstimates 是有条件分析定理，必须由真实曲率演化给出其 PDE/Kato/密度前提。不能因为后两者已编译就验收根曲率或整个曲线族估计。

## 冻结版本与证据

相对 `outputs/poincare-curve-control/CurveControl/`：

| 文件 | SHA-256 |
|---|---|
| Analysis/SmoothIntegral.lean | 1d5e76244c2432774910741e146fead17d000e4e0953babafcac393626259194 |
| Geometry/CurveRegularity.lean | f601fdfdf3e5e1eba5f439306914f33d9abfdaa01047d1bfcbaa80c8104d6003 |
| Geometry/RicciConnectionVariation.lean | 1e6aed39247d16e9a39f9185da6eddb29e3411d41d341bae03833101a2baba32 |
| Analysis/RegularizedPDE.lean | 46950b243b4bbca7165efe3afda60526fb9ac0d99333b1b6e1ad9fd22eadeb2e |
| Analysis/IntegralEstimates.lean | e43d4c71e0c0b5c0b0daae52934f7cc75a76ed8c014fec88377ac8e95a7a6b22 |

已读取 verification JSON：RegularizedPDE 5/5、IntegralEstimates 9/9、CurveRegularity 33/33 公开声明均有真实扫描结果，compile exit 0、extra_axioms=[]，source hash 与上表一致。其余两文件本次有模块加载与关键声明 #check，完整公开公理审计仍由主代理保存；不把一次 #check 冒充全部声明扫描。

实际 #check 确认以下导出接口的前提没有被 section elaboration 遗漏：

- `IsCurveShorteningFlowOn.contDiffWithinAt_curvatureSq`：hc、真实 smooth metric family hg、UniqueDiffOn J、p.time∈J。
- `continuousOn_regularizedCurvature_rectangle`：上述前提加 ε>0、Icc a b⊆J。
- `deriv_chartChristoffelBilin_lower_intrinsic`：真实 IsRicciFlowOn、内点时间、有效 chart target；没有任意 connection variation 输入。
- `hasDerivAt_weightedIntegral_of_contDiffOn`：仅 open U、t∈U、f/v 联合 C¹；没有额外 domination 参数。

## 1. SmoothIntegral：支配条件已由 compact rectangle 实际构造

`continuousOn_weightedIntegral_of_rectangle` 从 f,v 在 Icc a b×Icc 0 1 的连续性得到乘积范数在紧矩形上的上界 M，用空间常数函数 M 作可积支配。这是对实际 integrand 的 bound，并非从不存在的全域 uniform bound 推断。Lebesgue restricted Ioc 0 1 与 interval integral 端点 null-set 规范相容。

`movingWeightData_of_rectangle` 对实际 fₜv+fvₜ 的 norm 在同一紧矩形上取 M，另外从连续 slices 得可测、积分可积与 derivative measurable 条件。输入的 derivative 是真实 HasDerivAt，不是整个积分导数的同义改写。

`movingWeightData_of_contDiffOn` 先从 open U 中包含 t 的 neighborhood 取闭时间区间 Icc a b⊂U，再用联合 C¹ 得连续的实际 partial time derivative 与其 slice HasDerivAt。矩形边界 a,b 仍位于 open U 内，所以在这些辅助矩形端点要求经典导数合法，不是在原 flow 的初值之外加条件。

`hasDerivAt_weightedIntegral_of_contDiffOn` 最终不需要调用者另外给可积支配。Classical.choice 仅选择由紧性证明存在的数据，没有把结论变成 oracle。

对于 hε：每次 ε>0 固定后使用此桥，支配常数可以依赖 ε、该条曲线与所选紧时间邻域。最终估计的 ambient 常数必须 ε 独立；这里的技术支配常数不进入最终指数，因而无需 ε-uniform domination。

## 2. CurveRegularity：within 初值链合法

### 内点与端点严格区分

内点路线将实际速度平方识别为 fixed-chart 的 spatial directional derivative norm，将 q 识别为 time directional derivative norm。这使用 cₜ=H 的真实 PDE，只用于得到 regularity，没有假设 q 演化。

端点路线改用 `fderivWithin`，并明确加入 `UniqueDiffOn ℝ J`。`uniqueDiffOn_ricciTime` 从真实 Ricci 时间集合的 convex/ordConnected 与 nontrivial 得非空内部，再推出唯一 within differentiation；不是把单点时间域视为有唯一时间导数。

`contDiffWithinAt_chartDirectionalNormSqWithin` 对 J×univ 使用 hJ.prod uniqueDiffOn_univ，以真实 within smoothness 得 directional within derivative 的 smoothness。chart target 邻域由连续性取得，没有在目标 chart 外做几何推理。

### 将端点 PDE 变换到任意合法固定 chart

`hasDerivWithinAt_timeChart_in_chart` 使用固定 chart transition 的 HasFDerivAt，与原 Flow.equation 的 within derivative 复合。eventual equality 只在 nhdsWithin J 内要求，并另证明基点相等。没有把 within neighborhood 偷换成完整 neighborhood。

`chartCurvature_eq_timeFDerivWithin` 将上述导数与 joint within derivative 沿 (s,x) slice 的导数比较；hJ 保证它们唯一，因此 H 的 fixed-chart coordinates 等于 fderivWithin 的时间方向值。这在包含的时间端点成立，不依赖任意区间外 c 的值。

空间方向的 `chartVelocity_eq_spatialFDerivWithin` 不要求 hJ：固定 t∈J 的空间 slice 是全 ℝ，任何有效 joint derivative 的 spatial restriction 必须等于该真实 slice derivative；代码实际组合到 univ 并用经典 derivative uniqueness，数学正确。

由此 v、q、hε 在整个 J×ℝ 上 within smooth；v 的 sqrt 用 immersion 保证正，hε 的 sqrt 用 ε>0 保证正，q=0 没有被排除。随后限制到任意 Icc a b⊆J 的紧矩形，得真正 closed-rectangle continuity，满足积分比较初值需求。

### 周期性与 H 的连续性措辞

periodic_deriv 对 totalized derivative 也成立，因为函数平移恒等式与导数平移规则在不可微点仍一致。γ(x+1)=γ(x) 使 moving-foot anchor 本身相同，因此 X、S、H 的 E-valued periodic 表述合法；没有把不同脚点的 fiber 数值强行同一。

不过不能由该 periodic theorem 宣称“任意 moving-foot E-valued H 在全域连续”：选定 chart 可能跳变。正确连续性是 H 作为 pullback tangent-bundle section 的连续性，或其固定有效 chart 坐标的局部连续性。本文件实际导出的是 q、v、hε 的 scalar continuity/smoothness；已足以供 L、Θε 积分，不需要额外假设 raw E-valued H 连续。

H 在固定 chart 中的 within smooth coordinates 可以从 H=cₜ 的上述桥导出；未单独导出这种 vector-section regularity 定理不影响现有 scalar 结论，但更高协变微分的根连接仍要明确办理。

## 3. RicciConnectionVariation：标号、符号与 lowering

已核对上游 `ScalarTraceEvolution.lean` 的真实定义：`chartCovRicciOnE r i j` 是 ∇_r Ric_{ij}，第一个索引为导数方向；最后两个索引对称。当前

    ricciVariationCoef(i,j,k)
      = −Σ_l g^{kl}(∇_i Ric_{lj}+∇_j Ric_{li}−∇_l Ric_{ij})

与 Ricci-flow ∂ₜΓ^k_{ij} 正确一致。前两项把 l 放在 Ric 的第一个 slot，只是 Ric 对称性，不是错把 l 当 derivative direction。

`hasDerivAt_chartChristoffel_ricci` 由真实 hg.smooth、Ricci metric variation 和上游已证明 coefficient variation 推得；α,y 固定，时间仅在内点。`hasDerivAt_chartChristoffelBilin_ricci` 将 scalar coefficients 重构成真正 CLM derivative，避免只有系数名而无实际双线性导数的缺口。

lowering 步骤用 actual chartGramMatrix×chartInvGramMatrix=Id。合法 chart target 保证 baseSet 与逆矩阵性质；不是默认 basis 对 g 正交。得到

    g_{ak}(∂ₜΓ)^k_{ij}=−∇_i Ric_{aj}−∇_j Ric_{ai}+∇_a Ric_{ij}.

`ricciVariationBilin_lower_basis` 再用 actual tangent trivialization inverse 与 chart basis metric 配对。`deriv_chartChristoffelBilin_lower_intrinsic` 通过三个 slot 的线性逐基扩展到任意 U,V,W：

    g(A(U,V),W)=−(∇_U Ric)(V,W)−(∇_V Ric)(U,W)+(∇_W Ric)(U,V).

所有 U,V,W 均先经同一个合法 fixed-chart readback R 进入实际 tangent fiber，covRicciAt 用真实 canonical Levi–Civita 及其已有证明。没有手动假设 arbitrary trilinear form 等于 ∇Ric。

本式是“先求 ∂ₜΓ，再用当时 g lowering”，不是“对 gΓ 整体求时间导数”；因此此处不应再加 −2Ric 的 product term。−2Ric(H,H) 属 q 的 metric time derivative，已由 MovingMetric 单独提供。把 U=V=S、W=H 后，乘 2 的 contribution 正确为 −4∇S Ric(S,H)+2∇H Ric(S,S)。

`EvolvingConnection.timeVariation` 定义成 `fderiv` slice applied to 1，而本文件有 `deriv`/HasDerivAt；最后连接要用真实 derivative identification（标准 definitional/hasDerivAt bridge）保持系数场为同一个 actual Γ。

## 4. RegularizedPDE：有条件分析，实际链式法则正确

两个 spatial chain rules 使用实际 q′、v 与 arcDeriv，二阶公式为

    Dₛ²hε=(Dₛ²q)/(2hε)−(Dₛq)²/(4hε³).

v 的空间变化已经包含在 Dₛ²q 中，不缺 v′ 项。所需 q 全域可微/非负用于先得到空间函数恒等式，点处 q′ 可微、v 可微正值用于再求导，条件充分。

`regularized_kato_cancellation` 与 `regularized_pde_algebra` 明确把 Kato 和 q PDE 当作 scalar analysis 输入，代数中 hε>0、q≤hε²、A≥0 的使用正确。尤其负 gradient 项的方向为 −P²/hε≤−(Dₛq)²/(4hε³)，确实是所需取消方向。

`deriv_regularizedNorm_le` 接真实 time derivative 后得到 hε PDE。它是完整**条件分析**定理，不是已从真实 g,c 导出 q PDE；根 curvature 尚未闭合时不得将其标成独立几何结果。

## 5. IntegralEstimates：density/cubic 与周期 FTC

MovingWeightData 的字段只包装局部 integrand 导数、可测性、可积支配，不把整个 integral derivative 作为字段。SmoothIntegral 现在可以从实际 scalar joint regularity 构造这类数据，因此最终几何调用无需外部 domination 假设。

cubic cancellation √q³−hεq≤0 正确，允许任意 ε，因为只用 hε≥√q；需要 ε>0 的 division/PDE 部分已在 RegularizedPDE 层处理。regularized density inequality 保留 +C L forcing，未误删 Morgan–Tian 修正引入的长度依赖。

`deriv_length_le` 输出 BL−∫qds，负 energy 没有丢失。`deriv_regularizedTotal_le` 对实际 arcDeriv²hε 的 weighted diffusion 通过 FTC 消项：flux derivative 的 integrability、实际 differentiability 与端点 flux equality 均为明确输入，零积分是结论。它没有直接假设 diffusion integral=0。

这些 theorem 的 hevol/hpde 是合理分析前提；真实 speed theorem 已可提供 hevol，未来真实 q 演化+Kato+RegularizedPDE 提供 hpde。相关 integrability/flux endpoint 要由 CurveRegularity 的 smooth periodic scalar 及正 v 派生，不能要求用户额外假设它们。当前各文件分工语义一致。

## 6. 对根交付状态的建议

本批确实解决两项技术连接：端点 scalar continuity 不再依赖区间外延拓；积分 domination 不再需要独立几何假设。真实 Ricci 联络变分及 arbitrary-vector intrinsic lowering 也已建立。

仍需从同一真实 g,c 的 curvatureVector，完整接上 coordinate normal evolution、intrinsic curvature term、MovingMetric 与 spatial projection norm decomposition，得到最终 q PDE；再串联上述分析结论及 ε 极限、共同初值族界和产品因子常数。该根依赖未闭合前，不验收 curvature 根节点或完整曲线族模块。

# 速度、弧长密度与切向量演化：独立语义验收审核

日期：2026-09-09。对冻结源码只读审核；并使用既有 Lean runner 成功加载 SpeedEvolution 的编译模块，对两个最终定理执行 `#check`，exit 0。全公开声明可达公理扫描由主代理另执行，本报告不把 `#check` 当作该扫描。

## 结论

**arclength 节点语义验收通过；同版本全公开声明公理检查通过后可标记 verified。** 当前 SpeedEvolution 已从真实光滑浸入曲线缩短流与真实 Ricci flow 推出速度密度及单位切向量时间演化；没有把速度演化、mixed derivative 相等或曲率正交性留作最终定理的外部前提。

时间限制为 `t ∈ interior J`，这是合理且充分的证明接口：最终分析在闭子区间上使用连续性、在开区间上使用导数。新 InteriorComparison 已无初值导数要求。初始时刻依然需要从光滑输入证明 L、Θε 等连续性，但不需要把流方程在区间外延拓。

## 精确版本

相对 `outputs/poincare-curve-control/CurveControl/Geometry/`：

| 文件 | SHA-256 |
|---|---|
| SpeedEvolution.lean | a7f20002fa6b9bb61bc1c87dde5ff42a2c4152e8af21dce1d592ebe524566766 |
| ChartBridge.lean | d596420944d25d466852646a92b74f076bb630e84cc991de58daf22395a7dbe1 |
| CurvatureGradient.lean | 29e58787a59a6de0714dbd81af684e5d5ea927537a383101254841a6d99d79d5 |

## 1. SpeedEvolution 的根前提与计算

`IsCurveShorteningFlowOn.hasDerivAt_curveSpeed_time` 的已编译声明经实际 `#check` 确认：前提为真实 `hc : IsCurveShorteningFlowOn g c J`、`hflow : IsRicciFlowOn g J`、`t ∈ interior J` 及通常流形 typeclass；没有 hspeed、hDt、hDx 或目标积分界外部参数。结论为

    ∂ₜv = −(q+Ric(S,S))v.

由于模块中的 ds 由固定参数的正密度 v dx 定义，这就是弧长密度演化。若后续要额外包装成测度微分 notation，应复用这一定理，不必为当前节点构造新 measure-valued derivative。

证明链具体核对：

- 由真实 v 与 S 定义恢复 X=vS，∇ₓS=vH。
- 从已经证明的 ⟨H,S⟩=0 进行 metric-compatible 空间微分，得 ⟨∇ₓH,X⟩=−v²q。
- `exists_mixed_covDeriv` 用 joint smooth c 的实际固定 chart 二阶导数与上游 `hasCovDerivAlongAt_fst_snd_symm` 构造共同值 D。该上游结果确实通过 Schwarz symmetry 与 Christoffel symmetry 推导 mixed covariant derivatives 相等；不把相等作为假设。
- 在固定时刻 t，对所有空间 y 用真实 flow PDE 将时间 velocity field 替换成 curvature field。这是整条空间函数相等，足以对空间协变导数替换，不是单点相等后非法求导。
- MovingMetric 给 ∂ₜ|X|²=−2Ric(X,X)+2⟨DₜX,X⟩。正速度允许 sqrt 链式法则与约分，得到速度式，符号正确。

辅助 `hasDerivAt_time_curveSpeed_of_mixed` 保留两个 genuine covariant derivative predicates 是合理分层，因为最终真实 flow 定理已构造它们；不再构成根前提缺口。

`IsCurveShorteningFlowOn.hasCovDerivAt_unitTangent_time` 也经实际 `#check` 确认只有 hc、hflow、interior-time 前提。由 v⁻¹ 的真实导数和 X 的实际协变导数，得

    DₜS = v⁻¹∇ₓH+(q+RicSS)S = DₛH+(q+RicSS)S.

这里 Dₜ 是在当时 g(t) 下沿时间曲线的空间协变导数；不能与 g+dt² 的时空度量相容导数混用。公式已符合采用的纯空间路线。

## 2. ChartBridge：真实 joint smooth 与初值边界

`contMDiff_curve` 对任何 t∈J 提取全域空间平滑性，包括初始时间；由 product 上的 ContMDiffOn 沿固定时间 slice 复合得到，不要求 t 是内点。

`contMDiffAt_family` 及 `contDiffAt_chartCurveFamily` 则正确要求时间内点，再把 within smoothness 升级为完整邻域上的联合 smoothness。固定 chart α 只需包含当前 c(t,x)；连续性自动给局部 source neighborhood，没有全球 chart 也不要求曲线嵌入。

空间 velocity 与 fderiv(...)(0,1) 的桥使用 tangent-bundle coordinates。时间 curvature 与 fderiv(...)(1,0) 的桥显式包含 `tangentCoordChange I (c t x) α (c t x)`，没有把不同 chart 的 E 数值直接认作相等。

端点处没有错误声称 chartCurveFamily 的全域经典导数；初值仅提取空间 regularity。这与 Flow 的 within PDE 相容，也覆盖 self-intersections。

## 3. CurvatureGradient：真实 spatial P 与 Kato

`covArcDeriv=(1/v)covDerivAlong`；`normalCurvatureGradient=DₛH+qS`。后者是空间投影 Psp，明确不同于时空投影 P̂。定理依次证明：

    Dₛq=2⟨DₛH,H⟩=2⟨Psp,H⟩,
    (Dₛq)²≤4q|Psp|²,
    ⟨DₛH,S⟩=−q,
    |DₛH|²=|Psp|²+q²,
    ⟨Psp,S⟩=0.

Cauchy–Schwarz 来自实际 metric positivity，不是抽象任意 pairing 的未经证明条件。Kato 的 hD 是真实曲率场的 `HasCovDerivAlongAt`，没有 scalar gradient inequality 或目标 Kato 前提。

对实际内点 flow，SpeedEvolution 的 `exists_mixed_covDeriv` 已能提供 H 的协变导数，再用 `covDerivAlong_eq_of_hasCovDeriv` 改写为 hD 的 self-valued 形式。当前 CurvatureGradient 尚未提供这一 convenience wrapper，但语义上条件已可从实际输入获得。

最后 `arcDeriv_arcDeriv_curvatureSq` 从 genuine hD（全空间函数）及 hDD 推出

    Dₛ²q=2|DₛH|²+2⟨Dₛ²H,H⟩.

要求全域 hD 是为了先建立一阶函数恒等式再求导，条件充分；hDD 的实际获得仍需更高协变 regularity 的桥。它不是弧长节点验收所需的额外内容，也不能据此提前验收完整 q 演化。无需对 k=√q 在 q=0 处求导，q 和 hε 路线保持零曲率点合法。

## 4. 验收范围与下游调用

当前 arclength 节点接受的是实际速度、密度与 S 演化恒等式，而非最终 L 或 Θ 估计；该范围已满足。下游可直接调用 hc 的两个 root methods，不需要自行提供速度演化假设。若坐标版 CurveEvolution 需要 hspeed germ，应由该速度定理在所有邻近内点应用，并用 ChartBridge 同步 chart representation；不能继续把 hspeed 当最终外部输入。

尚未完成的 curvature root、∂ₜΓ 的 Ricci 识别、q 演化、hε PDE、移动积分和 λ 产品界，各自仍按相应节点验收。

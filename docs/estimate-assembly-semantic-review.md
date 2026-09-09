# 长度根估计、标量整链与环境张量界：独立语义审核

日期：2026-09-09。只读审核四个冻结文件及必要的上游定义/分析依赖；未修改源码或看板、未统一 build。

## 结论

四个文件均在其显式假设下语义审核通过。LengthEstimates 是从真实 hc+hflow 出发的长度及 curvature-energy 几何根结果；CurveEstimateAssembly 是从原始 scalar q PDE/Kato/density 输入出发的完整分析整链，**仍不是完整几何根定理**。AmbientBounds 证明真实 metric 范数下的环境张量评估与误差吸收；RicciTraceProduct 证明给定真实线性等距及曲率分裂时的 trace 代数，不自行构造 product geometry。

指数 `C=A/2+B`、energy 的权重/符号、初值端点处理、ε 极限顺序均正确。暂不建议凭本批增加整体交付节点；还需真实 q 演化闭合与产品/统一常数的几何实现。

## 冻结版本与实际证据

相对 `outputs/poincare-curve-control/CurveControl/`：

| 文件 | SHA-256 |
|---|---|
| Geometry/LengthEstimates.lean | ca3c30b9aae5e51cf1dcb4838fff60d61acf935760aceb08b7dfcb3a5f795689 |
| Analysis/CurveEstimateAssembly.lean | 8aef8045d2288b8dff7f81fc4250e466843b5e6a4d10a44d71974565b9aeab3c |
| Geometry/AmbientBounds.lean | 2763cd5ad3889aa71cb10bffc3954a8c87457aa5fbebe045ed89e378419535f7 |
| Geometry/RicciTraceProduct.lean | a16511a14e2a96d2114fb4b1e455f8412eb62c0be709d65192f0350e60d62264 |

已独立读取 verification JSON，四份 source hash 与当前源码一致，compile exit=0、extra_axioms=[]；公开声明扫描分别为 12/12、11/11、19/19、2/2。

另使用既有 Lean runner 成功 `#check` 三个已编译关键声明（exit 0）：actual `curveLength_le_exp`、actual `curvatureEnergy_integral_le`、scalar `ScalarCurveHypotheses.curve_estimate`。前两个明确保留真实 hc、hflow、区间条件与环境 Ricci 下界；最后一个明确保留整个 ScalarCurveHypotheses，未把其 PDE 前提在对外陈述中消失。

## 1. LengthEstimates：真实 L 与 energy 根

`lengthRate` 定义为实际 −(q+RicSS)v 的周期积分，不是独立输入的导数值。`hasDerivAt_curveLength` 从实际 joint C¹ 与既有 SpeedEvolution 的速度导数得到它就是 L′。

`intervalIntegrable_lengthDensity` 通过真实 v 的连续时间偏导表示 density，因此没有额外假设 Ricci-pairing 的可积性，也没有使用未证明的 density bound。

`lengthRate_le_growth_sub_energy` 只需环境的单位向量 Ricci 下界 −B≤Ric(V,V)。单位 S 是 hc 已证明的真实单位切向量；v≥0 保证积分不等式方向，得到

    L′≤BL−E， E=∫q ds≥0.

对 length growth 和 weighted energy 允许任意实数 B 是正确的；正指数的 integrating factor 比较不要求 B≥0。无权 energy 的推导额外要求 B≥0，与权重比较所需条件一致。

### 时间端点

假设 Icc a b⊆J 且 a≤b。对 t∈Ioo a b，Icc a b 包含 t 的邻域，故 t∈interior J；代码明确证明这个包含。闭区间 L 和 E 的连续性由 CurveRegularity 的端点 within smoothness 与 SmoothIntegral 得到。只有开区间要求经典/右导数，不要求 a 或 b 可微。

a=b 时加权/无权积分皆为 0，length 等式退化正确。不会因 t=b 处缺少经典导数而排除合法 smooth endpoint。

### Energy 权重与常数

加权式为

    ∫ₐᵇ e^(−B(t−a)) E(t)dt ≤ L(a)−e^(−B(b−a))L(b).

这是对 e^(−B(t−a))L(t) 的导数估计，负号与起点平移均正确。

无权式为

    ∫ₐᵇ E(t)dt ≤ e^(B(b−a))L(a)−L(b).

它不是错误的 `L(a)−e^(−BΔ)L(b)` 无权界；代码正确利用 B≥0、E≥0 放大权重。E 的时间可积性由闭区间连续性提供，不额外要求 L′ 可积。该根有真实 Perelman good-time 能量输入价值。

## 2. CurveEstimateAssembly：完整但有条件的标量整链

`ScalarCurveHypotheses` 明确记录原始 q,v,r,P 的 regularity、nonnegativity/positivity、空间周期性、环境 r 上界及以下三个数学前提：

    vₜ=−(q+r)v,
    (Dₛq)²≤4qP²,
    qₜ≤Dₛ²q−2P²+2q²+A(q+√q).

这是允许的分析层接口，不是实际 curve flow input。最终实际几何 root 必须从同一个 g,c 构造这些字段；不能把这个结构直接改名当作已经完成 Ricci 曲线模块。

### 常数方向

正则化 hε=√(q+ε²) 由原始 q PDE+Kato 得

    (hε)ₜ≤Dₛ²hε+k³+(A/2)(hε+1).

密度项 −hεq 与 k³ 抵消后，r 的绝对值界给

    Θε′≤(A/2+B)Θε+(A/2)L.

L′≤BL，相加得到

    (Θε+L)′≤(A/2+B)(Θε+L).

所以最终指数 C=A/2+B，没有误用 A+B，也没有多加一次 A/2。A、B 的非负性在结构中明确，环境构造应取 A=max(6B+2K,6D)。

### 正则性、周期与积分条件

q,v 的 smoothness 只在 open time strip 上要求；closed rectangle continuity 用于初值和最终时刻。q_periodic/v_periodic 也只需内点，因为消 diffusion 在求导的那些时刻执行，端点不求导。

P 不需额外连续/可积性：它只在点态 Kato/PDE 中出现，正则化时被消去，未进入任何被积分的 expression；这是合理弱化，不是漏条件。

r 也没有单独 smoothness 假设。含 r 的 integrand 通过已给 density equation 改写为实际 vₜ 的连续组合，因此可积性被证明，而非从仅有 r 有界直接推断所有导数正规。

代码从 joint smooth hε/v 自动产生 MovingWeightData，从真实空间 smooth periodic fields 导出 flux endpoint equality，再由 FTC 消去 Dₛ²hε 的移动密度积分。因此调用者不需额外 domination 或 zero-diffusion-integral 假设。

### ε→0

`regularized_comparison` 对任意 ε>0 使用同一个 A/2+B。`curve_estimate` 随后调用 RegularizedIntegral 的实际误差界

    0≤Θε−Θ≤εL

及两端积分极限，把已经证明的比较过极限。没有交换 ε 极限与时间导数，也不要求未正则化 Θ 处处可微。初值只用 q、v 的闭矩形连续性与非负性，不需要初值时间导数。

结构未显式要求 a≤b，但最终量化 t∈Icc a b：空区间结论自然为空；非空时证明中恢复合法初值 a∈Icc a b。它不造成合法时间范围的漏洞。

## 3. AmbientBounds：实际范数与真实 tensor 评估

`metricNorm` 是 √g(v,v)，没有使用固定 model-space 内积。因此由 unit S 得 norm(S)=1，由实际 H 得 norm(H)=k，所有 contractions 的 bound 真正是 evolving g 的 multilinear bound。

`covRic` 与 `rm` 使用 canonical Levi–Civita 与真实 covRicciAt/curvatureFormAt，不允许用户提供任意代数张量冒充环境曲率。`TensorBoundsAt` 的字段只给这些真实张量的环境大小，并要求 B,K,D≥0；没有曲线演化或积分结论字段。

所得 curvature error 为

    |quadratic terms|≤(6B+2K)q,
    |covariant Ricci terms|≤6Dk.

coefficients 与 scalar CurvatureError/Assembly 一致。`curve_evaluations` 仅需点态非零 velocity 来保证 S 单位；对于任意给定 H 向量环境张量估计本来就成立，不需要在这个 tensor-evaluation lemma 中额外证明 H 的高阶正则性。

### 必须明确的曲率符号 bridge

已实际读取上游定义：

- do Carmo `AffineConnection.curvature` 使用 R⁻(X,Y)Z=D_YD_XZ−D_XD_YZ+D_[X,Y]Z。
- `curvatureFormAt g X Y Z W=⟨R⁻(X,Y)Z,W⟩`。
- EvolvingConnection 的 coordinate curvature 使用 R⁺=−R⁻。

因此当前

    AmbientBounds.rm(H,S,H,S)=⟨R⁻(H,S)H,S⟩
                            =⟨R⁺(H,S)S,H⟩,

这里同时使用算子负号与末二 metric slots 的反对称性，两者抵消。故 `+2 rm(H,S,H,S)` 与所需 q evolution contraction 一致；没有发现错误号。但最终 intrinsic/coordinate root bridge 必须显式体现这个变换，不能直接宣称 R⁺ 算子等于上游 R⁻ 算子。绝对值环境估计本身对整体符号不敏感，不能用它掩盖演化恒等式的错误符号。

### 常数存在的边界

`UniformTensorBoundsOn` 是给定 B,K,D 的真实全空间/时间 tensor bound。该文件没有从 compact smooth ambient 自动构造这些常数，源码也明确如此。最终如果承诺“常数仅依赖 compact ambient flow、存在有限统一常数”，仍须证明相应 compactness/continuity lemma；当前环境输入不是隐藏目标估计，但不能把它当已完成常数存在性证明。

## 4. RicciTraceProduct：正确的等距 trace 代数

`ricciForm_isometry` 用真正 LinearIsometryEquiv 把正交基映到正交基，按实际 ricciForm 的 trace 定义逐项替换，结论正确。这里只要求 curvature-form compatibility，不要求无意义的坐标 basis 正交。

`ricciForm_product` 使用 WithLp 2(E×F)，而不是普通 product 的 sup norm。通过两因子正交基的直和、再经 e.symm 映回 V，将 trace 拆为两段；另一因子在对应纯基向量方向为零，利用 algebraic curvature 的零槽性质消去。得到 Ricci 是两个因子 Ricci 之和，系数没有维数或 2 的遗漏。

这是 product geometry 的代数子引理。实际应用必须给：

1. tangent fibers 上由真实 metric 安装的 inner-product/norm 实例；不能偶然使用 model norm。
2. 实际 product tangent metric 的线性等距同构 e。
3. canonical curvature 的真实 splitting theorem。

这些条件尚不是该文件的结论；保留作代数引理输入合理，但不能将它直接计成真实乘积 Ricci tensor splitting 已完成。

## 后续最短闭合清单

已有实际 LengthEstimates 可以直接交给下游调用；total-curvature 的 scalar chain 也已完整。剩余关键工作集中在真实 q evolution / chart-intrinsic sign bridge、实际 Psp/Kato 实例打包、ambient bounds 存在与产品一维因子的统一继承，以及最终按 a,λ 的几何 root 实例化。完成这些前，报告应明确区分“实际长度根已证明”与“总曲率条件分析链已证明”。

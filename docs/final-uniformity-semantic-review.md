# 最终产品统一估计：独立语义审核

日期：2026-09-09。审核者 curve_control_specification。只读冻结 Lean 源码、既有依赖及验证证据；未更改数学文件、运行统一构建或写看板。

**结论：通过，无需修复。** 本批实际 intrinsic Rm、Ric、∇Ric 产品拆分和真实产品 Ricci 流已关闭前次产品审核的全部几何接入缺口。两个最终存在性统一估计根不再要求 tensor bounds、任何 splitting、qPDE、Kato、积分正则性或目标比较假设。结合此前实际曲率/分析链审核及另一代理对 CompactAmbientBounds 的独立审核，可验收 uniformity；完整范围按“给定光滑浸入闭曲线流存在、任意供给的真实一维静态因子及其度量”实现。

## 冻结版本与证据

|文件|SHA-256|公开声明审计|
|---|---|---|
|ProductIntrinsicCurvature|`9ca3f8637ead329026f92bf5195b3fdffbe9aa02e2598cfaf6ade9c236e744a7`|9/9|
|ProductAmbientBounds|`c31c78db179ba1c35c28a743a92fbd77c1b361015545f0332036f86b763055e9`|6/6|
|ProductCovRicci|`d2ca15f00afde27cda82869329513b267f2de3b86a94a93a56c1f62f4adcb82a`|15/15|
|ProductFlow|`5c7a1ce694187e4548bebb6d18b990e4ba51eb933afac877fb91953ade5d238f`|14/14|
|UniformProductEstimates|`b0ab134707b559ef04f8288f19987e5d6cd4e201caf7c1cc3d115d349d975bda`|9/9|

本次读到五份同 hash JSON，compile exit 0，extra_axioms=[]。已读 release-check.json：full_build_in_this_run=true、build_exit_code=0、axiom_audit_exit_code=0，757 声明，43 数学模块加 CurveControl 根，允许且仅见 propext、Classical.choice、Quot.sound。上述为父代理真实统一构建和环境审计证据；本文补充独立语义判断。

## 1. 真实纤维内积与曲率/Ricci 拆分

ProductIntrinsicCurvature 的 productTangentEquiv 仅是线性等价。productTangentIsometry 在源 product fiber、目标两因子 fiber 分别安装由 productL2Metric、g、h 给出的真实 RiemannianBundle 内积实例，再由已经证明的 metricInner split 构造 isometryOfInner。这关闭了“用模型范数的连续线性等价冒充实际等距”的风险：其等距性依赖实际 g,h，不依赖未经证明的模型范数相等。

产品 L² 模型维数由 WithLp 线性等价及 finrank_prod 得到，正维来自 base，不存在把产品维数误置为一维的假设。因子一维仅在后面的消零步骤使用。

canonicalCurvatureFormAt_eq_chart 明确保留 upstream 的负号。将产品及两因子 chartCurvature split 与实际 metricInner split 组合后，负号分配得到 intrinsic 四张量 sum；未将 do Carmo R⁻ 与 chart R⁺ 直接认同。ricciTensorAt_productL2 通过真实 fiber isometry 调用正交基 trace 定理，因此无维数系数、trace normalization 或 basis norm 漏项。

ProductAmbientBounds 的 ambientRm_eq_canonical 使用真实 extendVector 及 pointwise tensor independence 识别两套 curvature package。随后全部四槽的 ambient Rm split 与 Ricci split 都是 actual roots。第二因子在 finrank=1 时由已证明的实际曲率/Ricci 为零消除；投影度量范数由 g⊕h 的平方和给出≤，利用 B/K≥0 相乘，保留相同 base B,K。不存在随 h 或半径退化的乘法常数。

## 2. ∇Ric 的最后接入

ProductCovRicci 的 covBilinDerivative 定义为真实 fderiv A 在方向 U 上评估 V,W，减去 A(Γ(U,V),W) 与 A(V,Γ(U,W))。导数方向在第一个槽；两条负号是 covariant 双线性 tensor 的正确联络修正。

解析 fderiv_bilin_split 要求 actual coefficient fields 可微和开邻域上的 lower-order splitting。证明沿 y+rU 求导，并用 EventuallyEq 和导数唯一性。这些解析假设不含 ∇Ric splitting 本身。covBilinDerivative_split 再加一点上真实 Γ split 足够，因为这里只需要对 A 求导，不对 Γ 求导。

几何层 chartRicciBilin 是真实 chartRicciCoefOnE 的有限和 CLM 包装，不是新供给的 tensor。系数光滑来自 actual g；两次有限基线性扩展证明其对任意 V,W 与真实 RicciTensorAt（inverse trivialization readback）相同。fderiv 与 coefficient partialDeriv 的基评估经过 actual HasFDerivAt 唯一性证明。covBilinDerivative_chartRicci_basis 给 ∂Ric−ΓRic−ΓRic；三次线性扩展用真实 covRicciAt 三槽线性性质接回 AmbientBounds.covRic，保留正确导数方向。

最终 covRic_productL2 先在任意有效 product chart target 上，由已证 intrinsic Ricci split 和真实 inverse tangent readback 得 coefficient split；chart target 开性再给用于求导的 germ。Γ split 则来自已证 productL2 connection。调用解析定理并回到 canonical foot 后，三向量 U,V,W 完全任意；没有 flatness、split 或导 Ricci 正则性额外根假设。

静态一维 h 的 ∇Ric=0 由真实 Ricci field 全局恒零再求导的既有定理取得，不是从一点 Ricci=0 误推导数=0。与实际投影范数≤和 D≥0 合并，得到同一 D，最后完整 TensorBoundsAt / UniformTensorBoundsOn 由内部证明提供。

## 3. 产品的真实 Ricci 流状态

ProductFlow 中水平 tangent pullback trivialization 与普通 tangent trivialization 的坐标表达先在真实 baseSet 内证明相同。metricFamily_coordinates 因此读取 hg 的真正 joint within 平滑双线性 section。

contMDiffOn_timePullbackForm 对固定 smooth map f 证明时空 pullback 双线性形式的平滑性：使用真实 mfderiv(f) 的 tangent coordinates 与 g 的两槽组合，并保留 source/target trivialization baseSet 邻域。无需 f 浸入，因为该辅助结果仅是双线性形式；最终产品正定性由先前真实 product metric 构造保证。

产品两投影在 L² 模型下 smooth；base family pullback 与 static h pullback 相加，逐向量确认等于 productL2Metric，故 isSmoothMetricFamilyOn_productL2 确实 joint smooth within 时间集，不是仅每个时间 slice 光滑。

hasDerivWithinAt_productL2Metric_of_ricciFlow 固定 p,u,v，实际投影只依赖模型与 p，不随 t 变化；h 是静态，所以时间导数只剩 base hg.equation 给的 −2Ric_g。isRicciFlowOn_productL2_oneDimensional 再用真实 Ricci split 和一维 Ricci=0 得正确 product RHS，且继承 ordConnected/nontrivial。端点使用 HasDerivWithinAt T，而非伪造双侧导数。最终没有把 product 已是 Ricci flow 当作输入。

## 4. 最终常数量词和调用闭合

两个核心根是 exists_uniform_static_product_family_estimate 与 exists_uniform_positive_scale_product_estimate。其显式次序是

    给定 compact base M、base g(t) Ricci flow、闭时间区间、真实一维 factor 模型，
    ∃ B C≥0，∀ 外部索引/曲线索引、所有静态 factor metrics h、所有 curves c，
    若 c 是实际光滑浸入闭曲线流且有统一初值 L₀,Θ₀，则给出全族估计。

特别 ∃B C 在 ∀h、∀c、∀L₀、∀Θ₀ 之前。虽然 factor manifold/typeclass 是定理上下文参数，证明选取见证只调用 compact_base_uniform_coefficients I hg，即只依赖 base metric family 和时间区间；没有读取 factor 几何数据、h、λ、曲线、初始长度或初始总曲率。CompactAmbientBounds 的已独立审核根提供实际 Rm/Ric/∇Ric 有限 bounds，源码接口与调用完全匹配。

C=max(6B+2R,6D)/2+B，非负性真实证明。产品原封保留 B,R,D，先证明 product flow，再调用此前已验收 curve_family_uniform_estimate。对每个 ℓ,i，初始 Θ+L 的界由两个允许的初值界相加。最后通过实际 L(t)≥0 从 Θ(t)+L(t) 控制得到 Θ(t) 控制：

    L(t) ≤ L₀ exp(B(t−a)),
    Θ(t) ≤ (Θ₀+L₀) exp(C(t−a)).

初值系数包含长度，符合修正需求。没有声称可用 Θ₀ 单独乘指数。对空索引量词合法；非空族的非负初始界由实际量自动约束，不需另列非负假设。

positive_scale 根取索引 {λ:ℝ // 0<λ}，整个 h_λ 任意供给，常数在选择整个 h_λ 前已经确定。因此没有 λ 下界、无 λ 连续性或 λ 导数假设，可用于 λ→0 的估计。该根不定义 h_λ=λ²h₀；它提供更一般接口，合法供给的缩放圆度量族是其实例。若外部项目要求具体 AddCircle 对象/缩放等式，其构造属于调用方，不应在交付说明中声称本模块已经定义该对象。h_λ 只能随外部 λ 变化，不能随 Ricci 时间 t 变化。

## 5. 验收意见及范围界限

建议验收 uniformity；无需修复上述五文件。此前 curvature/regularization/integration/comparison 已通过，本次关闭最后产品 tensor 和时间 flow 缺口。结合 CompactAmbientBounds 的独立审核和全库机械证据，现有数学模块达到约定的曲线族一致长度与总曲率估计范围。

光滑浸入闭曲线流存在仍作合法输入，未证明解存在/延拓；未证明整个有限消失定理或庞加莱猜想。结论可供有限消失路线后续调用。产品改为合法 L² 模型保持相同点集、atlas 及真实几何，只是适配上游 Hilbert 模型要求。不存在以度量模型替代原目标或缩小为全局坐标曲线的范围变化。

独立稳定导入检查：本代理另行运行 import UniformProductEstimates、三个实际 #check（covRic_productL2、isRicciFlowOn_productL2_oneDimensional、exists_uniform_positive_scale_product_estimate），exit 0；声明的输入顺序与上述源码审核一致。最终正尺度根 #print axioms 仅 propext、Classical.choice、Quot.sound。未执行重复全库构建。

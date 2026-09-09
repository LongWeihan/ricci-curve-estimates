# StaticFactorApplication 独立只读语义审核

结论：通过本次语义审核，未发现应阻止验收的定义替换、隐藏目标假设或量词错误。此结论是对真实缩放静态一维因子的估计应用的审核，不是具体圆、ramp 或曲线流存在性的证明。

## 版本与证据

- 审核文件：`outputs/poincare-curve-control/CurveControl/Examples/StaticFactorApplication.lean`。
- 独立复核 SHA256：`4f282888c9e432a824dd6bed822e73359fb6c70623a44cd7049edc9987e4b141`，与交审版本一致。
- 已读取正式编译及 olean 日志 `work/lean-start/static-factor-application-compile.log`、`work/lean-start/static-factor-application-olean.log`；两份日志均列出全部 7 个声明的可达公理，均仅为 `propext`、`Classical.choice`、`Quot.sound`，无错误或 warning。父代理/实现代理提供的 exit 0 和 olean ready 记录与日志内容一致。本次审核没有重建代码，也没有将已有编译记录表述为本审核新运行的编译。
- 只读追踪了 `UniformProductEstimates.lean`、`ProductFlow.lean`、`Flow.lean` 及上游 `isVonNBounded_of_posDef`、`IsRicciFlowOn` 定义。

## 缩放度量结构

`scaledFactorMetric h₀ ℓ` 的底层双线性形式实际定义为 `ℓ.val ^ 2 • h₀.inner p`。正尺度通过子类型 `{r : ℝ // 0 < r}` 保证，故平方严格为正；对称性直接由 `h₀.symm`，严格正定性由平方正与 `h₀.pos` 的乘积证明。`isVonNBounded` 并非一个调用者给出的额外界，而是应用已证明的有限维正定型 coercivity 定理，得到每个切空间中 `{v | q v v < 1}` 的 von Neumann 有界性。上游证明在单位球面上取正最小值再推得范数控制；这保证实际度量结构合法，不宣称此辅助有界常数在尺度趋零时保持统一。

光滑性由真实光滑度量截面 `h₀.contMDiff` 的常数标量乘法 `const_smul_section` 给出，未把缩放后光滑性作为假设。此处每个固定尺度的空间光滑性已足够；最终估计不需要曲线族或因子度量对尺度参数连续/可微。

`scaledFactorMetric_inner` 是结构定义的逐向量等式，`scaledFactorMetric_norm` 使用实际 `AmbientBounds.metricNorm = sqrt(metricInner v v)`、`sqrt_mul` 和正尺度下 `sqrt(ℓ²)=ℓ`。因此范数缩放为 ℓ 而非 ℓ²，且不是另行引入的抽象范数。没有包含退化尺度 ℓ = 0。

## 静态性与真实产品 Ricci 流

`scaledFactorMetric_static` 只证明固定尺度度量族在时间上恒定且光滑，这一表述正确。静态度量在一般维数并不自动是 Ricci 流；后续 `scaledProduct_isRicciFlow` 显式要求 `finrank ℝ F = 1`，并调用已证明的 `isRicciFlowOn_productL2_oneDimensional`。

该依赖的证明实际组合产品度量的时间导数、真实 `ricciTensorAt_productL2` 分裂以及一维 Ricci 消失，构造 `IsRicciFlowOn` 的光滑与 within 方程字段；没有要求调用者供应产品 Ricci 流结论。时间端点仍使用 within 导数。底层 `IsRicciFlowOn` 本身包含时间集非平凡条件，故虽然外层另写 `a ≤ b`，不能把本定理解释为独立提供单点时间集上的非退化流。

## 最终量词与统一界

`exists_scaledFactor_curve_bounds` 和 `exists_scaledFactor_fullInterval_bounds` 的 `∃ B C, ... ∀ h₀ ι c ...` 顺序正确。常数位于整个度量 h₀、所有正尺度、曲线指标、曲线族以及共同初值界之前。它们可依赖给定的紧致基底流和闭时间区间；固定的一维模型/流形位于外围类型参数中。证明进一步核实常数实际来自 `compact_base_uniform_coefficients I hg`，通过基底张量统一界和一维产品张量界转移，未从 h₀、尺度或曲线重新选取常数。

调用链是真实的：缩放应用 → `exists_uniform_positive_scale_product_estimate` → `exists_uniform_static_product_family_estimate` → 基底紧致性产生实际 Ric/Rm/covRic 系数 → 一维产品真实张量界 → `static_product_family_estimate_of_tensorBounds` → 已证明 `curve_family_uniform_estimate`。最后一个桥内部也真实证明了每个产品的 Ricci 流身份，而非额外假设之。

曲线输入 `IsCurveShorteningFlowOn` 仅含联合光滑、周期一闭合、非零速度浸入以及实际曲线缩短方程；未含速度/曲率/长度演化或最终估计。初始长度和总曲率界必须对所有尺度与曲线统一给出，结论不会构造这些初值界。全区间版本从积分的非负性和实际某条曲线的初始上界推得 `L₀ ≥ 0`、`Θ₀ ≥ 0`，再用 `B,C ≥ 0` 和 `t ≤ b` 将指数时间项替换成 `b-a`。空指标类型的情形只使最终全称命题空真，不造成错误地从空族推导全局正性。

因此所得有限上界确实同时适用于所有 `t ∈ Icc a b`、曲线指标和任意正尺度，无需正的统一尺度下界。这里“尺度趋零仍统一”仅指这组正尺度估计，不是对退化极限度量、极限曲线或极限流的存在/收敛声明。

## 明确范围与验收建议

文件只接收一个已有的真实光滑一维流形及度量。若调用者确实提供圆，则可用于该圆的通常 λ² 度量缩放；本文件没有构造圆的图册，也没有证明流形为圆、曲线为 ramp、闭浸入存在或曲线缩短流存在。源码文档对这些限制已有准确声明。建议以“真实缩放静态一维因子的统一估计应用”验收，不将其重命名为“具体圆/ramp 的完整构造”。

本审核未修改源码、配置或看板。

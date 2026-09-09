# 产品几何链独立语义审核

> 本文保留产品基础链完成时的审核截面。后续全部产品接入缺口的关闭和最终验收见 [最终统一估计审核](final-uniformity-semantic-review.md)。

2026-09-09。仅只读代码、上游定义及父代理编译/公理证据，未更改 Lean 和看板。

结论：本批八个文件按其真实声明范围语义通过。它们证明了实际乘积度量、合法 L² 模型重表述、有效图册上的联络和曲率拆分以及真实一维曲率为零；尚不能单独验收 uniformity。intrinsic product curvature/Ricci/covRic、product Ricci flow 及环境界根须继续接入。

## 冻结版本与验证证据

|文件|SHA-256|公开声明审计|
|---|---|---|
|ProductMetric|`606f102ed53c58ec5a2fb672a761b8e3242add8fa70d3004b711d79d574f76a5`|10/10|
|ProductModel|`d6b38166051d3dd77b9a5a0ae05a33d1aedf0e4ccca39ba9649bc53059d05328`|7/7|
|ProductModelCoordinates|`1ea1eabd4600933a52b0f09d1d158186871d5351444cea838844dc139a1ee5ed`|7/7|
|ProductConnection|`eaad17e8a0d5e17906bea6d15db2a19598ddb217afe7315cc1c545015d50a9da`|9/9|
|ProductChartCurvature|`e420fc076bcb6f38f3daa137c030e3c0c3c3d3d77bd4836e8246c3672ef88e7d`|7/7|
|ProductL2Connection|`9be9087732efdf3460adfe8397d542a8941e2fe64504b649550de9f293c8559b`|8/8|
|OneDimensionalCurvature|`43c48163eb8e6d2d198b9188372af587edb6c59f5260263d3b463b3bd64ed5d8`|10/10|
|RicciTraceProduct|`a16511a14e2a96d2114fb4b1e455f8412eb62c0be709d65192f0350e60d62264`|2/2|

上述所有 hash 与对应 verification JSON 一致，compile exit 0，extra_axioms=[]。ProductModel 的另两个 instance（productL2_boundaryless、productL2_isManifold）已查 `work/lean-start/product-model-instances.log`，均仅三项标准公理，故没有因扫描漏掉 instance 而漏审。本文是独立语义审核，不把编译本身当作数学目标范围证明。

## 实际度量与模型转换

ProductMetric 复用 upstream DCProductMetric，已查 DoCarmoCh1 实际定义：它是两个真实流形投影 pullback 双线性形式之和，正定性和光滑性由上游证明，不是定义一个仅具有预期字段的假想产品。该文件只要求有限维 NormedSpace，因此 E×F 的默认 max norm 在此合法；Riemannian metric 是另一个真实纤维双线性形式，并未要求该 max norm 由它诱导。

实际 productMetric_inner 给 g(u₁,v₁)+h(u₂,v₂)，长度平方拆分和投影缩短用实际 g、h 正定性。没有把模型 norm 当作实际 metric norm。

ProductModel 在同一点集 M×N 和同一 product atlas 上，以连续线性等价 e:E×F≃L WithLp 2(E×F) 改变模型。L² 模型具有真正的标准 Hilbert norm；代码未向 max-norm product 添加 InnerProductSpace。e 只是连续线性等价，不被错误宣称为模型范数的 isometry。

productModelDiffeomorph 在点上是恒等，逆映射真实 smooth immersion 由 diffeomorphism 导数可逆性得到。productL2Metric 是 DCProductMetric 沿此逆映射的真实 pullback，因此保留相同几何目标，仅更换合法建模。后续 actual metric 不是 L² 模型的固定欧氏内积，仍须使用 g、h。

## 图册有效域和求导

ProductModelCoordinates 证明 extChartAt 与 inverse 的精确线性共轭，且 productModelInverse_mfderiv=e⁻¹。该导数使用 chart target 邻域上的 EventuallyEq，未从一点恒等错误推出导数。Boundaryless 用于 chart target 开性与 full derivative，符合目标闭流形。

tangentCoordChange 的 product split 和 L² conjugation 都保留源图/目标图 source 条件。实际 chartMetricInner 使用真实 inverse tangent trivialization，并证明其坐标目标上恒等。没有假设全部流形落在某个全局 chart。

ProductConnection 的关键点是：先对真实 Gram 形式拆分在坐标直线 y+r x 上求导。连续直线在 r=0 邻域留在开放 chart target，所以得到的 EventuallyEq 可以通过导数唯一性传递。因子和产品的实际 Christoffel 都满足度量相容性；再用对称、非退化 Gram 的点态 Koszul 唯一性识别实际 Christoffel。connectionCoefficient_unique 虽是抽象代数引理，所有具体假设在产品应用中均已证明，未把 splitting 当输入。

ProductChartCurvature 先在任意有限维 normed model 中证明真实 Γ bilinear packaging 与 contraction 相同、Γ 可微，再以相同开邻域直线方法得到真实 fderiv Γ 拆分。代入 upstream christoffelCurvature 得真实 chartCurvature_product，混合项确实随因子结构消失。

ProductL2Connection 对实际 transported Gram 重复度量相容性与唯一性，证明 Γnew=e Γold(e⁻¹·,e⁻¹·)。因为 e 是固定线性映射，坐标变换无二阶项；fderiv 共轭亦保留方向输入 e⁻¹x。随后曲率三个向量槽和输出均正确共轭。没有漏维数因子、迹归一化或额外时间依赖。本批是静态几何，未宣称已证明时间 Ricci flow。

## 曲率符号和一维结论

ProductChartCurvature 和 ProductL2Connection 两边均采用同一 upstream chartCurvature，即此前核对的 R⁺ 坐标算子；产品拆分自身不引入反号。将它连接到 do Carmo intrinsic curvatureOperatorAt/curvatureFormAt 时仍要使用 R⁻=−R⁺ 的实际桥。双边同号翻译会保持 splitting，但不能跳过真实向量/四张量桥。

OneDimensionalCurvature 没有 flatness 假设。其代数证明使用 finrank=1，使任意 x 是非零 y 的倍数，再由曲率第一对交替性归零；y=0 单独处理。实际 LC 曲率的代数性质由真实 metric connection 定理供给，随后得到真实 Ricci trace 为零。局部 letI RiemannianBundle 用 g 的实际纤维内积，维数是相同切空间的线性维数，不受范数实例变化影响。

covRicci 为零先证明实际 Ricci 标量场恒零，再对零场求导并消去协变修正，不是由单点 Ricci=0 错误推得其导数为零。canonical curvatureOperator 为零由与任意 w 的真实内积全零及 metric 非退化推出，强于只证明 trace 零。适用于任意一维真实 Riemannian metric，不要求系数常数、选定坐标、圆半径或曲率界。

RicciTraceProduct hash 与前次审核相同，重读确认：真正 LinearIsometryEquiv 到 L² 正交直和及实际 curvature split 是显式代数输入；按两因子正交基求和，无遗漏因子或 max norm 冒充 IP。产品应用必须构造实际 g⊕h 纤维 isometry，不能直接拿 productL2Equiv 的模型连续线性等价充当它。

## 剩余验收边界

本批可作为通过的产品基础链记录，但不增加完整 uniformity 节点。接下来必须实际证明：canonical intrinsic Rm/Ric/∇Ric split；真实纤维等距识别；静态一维 h 与 g(t) 的 product Ricci flow（joint within 时间正则及 gₜ方程）；实际投影范数控制传递 B,K,D；最后调用已验收曲线根。若采用任意 h_λ，要求对每个 λ 静态，允许 λ 改变度量，不能默许 h 随时间变化而仍称产品 Ricci 流。

此实现足以面向任意合法圆表示，不须预先指定 AddCircle 图册，但尚未构造具体圆对象/度量或从紧致性抽取环境常数。曲线存在仍是输入，不因产品工具而新增存在/延拓承诺。

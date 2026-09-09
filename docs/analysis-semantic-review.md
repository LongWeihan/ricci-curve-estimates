# 首批分析 Lean 初稿独立语义审核

日期：2026-09-09。审核方式：只读逐条数学陈述与证明体静态审查。**未运行 Lean；无编译、依赖可达公理检查或模块验收结论。** 本文不修改代码或进度数据。

## 结论

三个文件的陈述在当前抽象分析层级上数学含义正确；未发现错误指数、符号方向错误、把最终结论直接作为假设或人为矛盾假设。当前内容足以作为值得编译验证的分析组件初稿。它们尚未证明实际 Ricci 流下曲线的长度/曲率结论；几何方程、正则化 PDE、密度演化和积分极限桥均须由下游真实几何输入证明。

最重要的连接约束：`CoupledComparison` 对 Q 要求每个时刻真正的右导数，因此应首先令 Q=Θε；不能把仅有 Dini 界或 a.e. 导数的 Θ 直接传入。`WeightedIntegral` 当前要求双侧邻域上的经典导数，时间端点必须有光滑延拓证据或另提供 within/right 版本。

## 审核版本

相对于 `outputs/poincare-curve-control/`：

| 文件 | SHA-256 |
|---|---|
| CurveControl/Analysis/RegularizedNorm.lean | 57b2f51f9ef10e2f21529cc94e8064437d24b894ad549200471b1f113b2def62 |
| CurveControl/Analysis/CoupledComparison.lean | b7746c6be0e327afafe4652c611d9ef529fab8b0687d360bd662fd1db9d7930b |
| CurveControl/Analysis/WeightedIntegral.lean | c24006ea307fd3790a7ef535b0b9955ef2b7427635884268f60cc7188814ec4b |

后续编辑需重新核对相应结论；行号以此初稿为准。

## 1. RegularizedNorm.lean

### 已覆盖的真实数学内容

- 行 14–45：hε=√(q+ε²) 的非负、正性、平方恒等式，以及 0≤hε−√q≤ε；上界正确要求 q≥0、ε≥0。
- 行 47–66：q²/hε≤(√q)³、q/hε≤hε、√q/hε≤1，分母正性均由 q≥0、ε>0 提供。
- 行 68–73：q 在 t 处经典可微且 q(t)≥0 时，固定 ε>0 的链式导数 q′/(2hε)。点处正性足够：q 的可微性蕴含连续性，复合平方根无需额外假设整个邻域 q≥0。
- 行 75–81：关于 ε 的连续性与 ε→0 极限。对任意实数 q 也成立，因为 Lean 的 `Real.sqrt` 是全域连续的截断平方根；实际几何仍需实例化 q=|H|²≥0。

### 未覆盖但必须补齐

此文件没有向量/张量内容，因此没有证明 q=|H|²、Dₛq=2⟨P,H⟩、|Dₛhε|²≤|P|²、二阶链式法则或 ∂ₜhε≤Dₛ²hε+k³+C₁(hε+1)。这些不是当前文件的隐藏假设，而是尚未实现的几何及正则化 PDE 层。

`hasDerivAt_regularizedNorm` 是双侧经典导数接口。初始时间若只给右光滑数据，需将其适配为 `HasDerivWithinAt`，或从规定的光滑延拓获得经典导数。

点态误差/极限尚未升级为 0≤Θε−Θ≤εL 或积分后统一极限；最终比较闭合需要这些桥梁，不能用点态 `Tendsto` 直接替代积分极限。

## 2. CoupledComparison.lean

### 已覆盖的真实数学内容

- 行 23–34：从闭区间连续性、每个 t∈[a,b) 的右导数和 f′≤Kf，得到 f(t)≤C exp(K(t−a))。这是合法的标量比较原理。
- 行 39–59：由 L′≤c₂L、Q′≤(c₁+c₂)Q+c₁L，相加得到 (Q+L)′≤(c₁+c₂)(Q+L)。对应指数没有额外错误的 c₁；无需 L,Q 或 c₁,c₂ 非负，代码注释对此说明正确。
- 行 62–74：经典导数转为右导数，条件比上一接口强但正确。
- 行 79–98：索引族共享系数与初始界，由 exp>0 放大比较。索引类型不需要紧性/拓扑结构是正确设计。

### 参数与端点审计

没有显式 a≤b 并非漏洞：a>b 时结论的 `t ∈ Icc a b` 无实例；a=b 时结论退化为初值比较。实际调用需取合法 s≤t。t=b 无导数假设、但闭区间连续性保留，足以通过比较达到右端点。t=a 要求右导数；这与半开存在区间截取闭子区间的实现方式兼容。

`HasDerivWithinAt ... (Ici t) t` 是实际右导数，不是上右 Dini 导数，也不是几乎处处条件。数学上的一般 Θ=∫|H|ds 在 H=0 处不应未经证明便声明这种处处右可微性。可靠根调用是 Q=Θε 后过 ε→0。若选择直接应用 Θ，必须另给真正的右导数证明，或者建立只需 Dini/integrated inequality 的不同定理。

### 假设边界

两个微分不等式作为**分析比较引理**输入完全合理，没有直接假设指数结论。它们若被原样提升为最终 `RicciCurveFlow` 根定理的外部输入，则会违反任务范围。最终代码依赖图必须能追到实际 metric、curve、联络演化证明，而不能停在 `hLbound`、`hQbound` 字段。

族引理仅证明已有共同系数下的逻辑统一化，尚未证明产品圆 λ 改变时环境常数相同。可用索引 ι=A×{λ:ℝ // 0<λ}；若取 0<λ<1 也可以，但共同初始界与环境产品估计必须另证。

## 3. WeightedIntegral.lean

### 已覆盖的真实数学内容

- 行 19–44：固定 x∈(0,1] 的 Lebesgue 积分下，乘积 f(t,x)v(t,x) 的时间微分等于 ∫(fₜv+fvₜ)。局部同一时间邻域的可积导数支配和 a.e. 量词顺序正确：存在同一个满测空间集合，使其上所有 u∈s 的导数/支配成立。
- 行 48–60：把已经给出的 vₜ=−(q+r)v 代入加权 first variation，得到 ∫(fₜ−f(q+r))v。符号及乘法结合正确。
- 行 67–76：从 g 真正可微、g′ 区间可积、g(1)=g(0)，由微积分基本定理得 ∫g′=0；消项是结论而非假设。
- 行 80–93：Dₛf=f′/v，Dₛ²f·v=(Dₛf)′，正速度允许约分，flux 端点相同给出二阶项积分为零。使用固定参数区间而不误当成弧长参数是正确的。

### 几何调用仍需证明的条件

1. 将 v 定义为实际 |cₓ|，建立 v>0、真实 vₜ，并把 q=|H|²、r=Ric(S,S) 接到 `hevol`。目前 `hevol` 是合法的代入引理输入，不能当作已证明的几何结果。
2. f=1 或 hε 的真实时间导数、空间周期 lift 和足够的二阶正则性。
3. 从紧参数圆×紧时间子区间上的连续导数，构造共同时间邻域与可积空间 bound；仅逐点存在导数不足以使用当前定理。
4. 时间左端点当前不是 within/right API：`s ∈ 𝓝 t` 与 `HasDerivAt` 都要求双侧。指定光滑至端点的数据可以通过延拓匹配，但不得把只定义在 [a,b] 的函数任意补零后宣称导数仍成立。
5. `arcDeriv` 使用 Lean 的 totalized `deriv`。行 80 的定理不要求原 f 本身可微，数学上仍成立，因为它只是对名为 `arcDeriv v f` 的函数应用 FTC。几何意义上若 f 不可微，`deriv f` 可退化为默认值；因此必须另证实际 f 可微并把该定义与真实 Dₛf 对齐。这不是现有定理错误，而是最终模型防止空洞实例化的必要条件。
6. `hperiod` 只要求实际一阶 arc derivative 的端点相等，这比全周期性更弱且足够。需要从 S¹ 上真实函数及 v 的周期性证明它，而不能把“二阶积分为零”另作为假设。

### 注释准确性

行 47 的 “does not assert or assume any unproved geometric law” 可被误解：函数明确接受 `hevol` 作为前提。其合理含义应是“这是给定密度恒等式的条件代入，不是几何证明”。建议以后澄清措辞；无需因此否定数学陈述。

## 4. 无空洞性与验收边界

静态观察到各主要假设均可满足，例如 q 为非负常数、f,v 为常数且 v>0、L,Q 常数并取 c₁=c₂=0；没有为得到结论而加入明显矛盾条件。a>b 的空区间情况是普通一般性，不影响合法时间区间应用。当前未见 `sorry` 或自定义公理的显式源码，但这不等于已完成可达公理检查。

`WeightedIntegral` 底部的四条 `#print axioms` 是待运行命令，不能拿其存在当作输出证据。三个文件全部编译后，应保存各导出根声明的真实 axioms 输出；后续根集成仍需重新检查完整依赖树。

## 5. 下一步最小闭合顺序

先保留这些抽象分析层，不把它们包装成实际几何成功。建议按如下顺序连接：

1. 实际速度/联络→vₜ 与平方曲率完整演化。
2. 真正 Kato 界+此文件的标量除法→hε PDE。
3. 光滑性、周期性、支配证据→加权积分定理→L′、Θε′ 不等式。
4. `coupled_exp_comparison_right` 应用于 Θε；积分误差≤εL→ε 极限→Θ 的结论。
5. 产品圆几何环境常数稳定+初始共同界→索引族定理实例。

完成上述连接、编译与公理检查之前，这三份文件只能记作“分析组件初稿经静态语义审核，编译待验证”，不能记作完整 8 模块口径中的几何交付已验收。

## 更新审核：最新 14 条正则化定理与积分便利接口

复核日期仍为 2026-09-09。本节更新先前文件快照的语义结论；仍未由本审核者执行编译。最新 SHA-256：

| 文件 | SHA-256 |
|---|---|
| RegularizedNorm.lean | c5460d42e519d0cfee01fa8083df89d2ba61a7bd7bf915ccf13862167f9a9b2c |
| WeightedIntegral.lean | 2c481dc1d03f9600cf9a1018205172b44986c0116f9e732a7134d15970348adc |
| CoupledComparison.lean | 0d4ed7fe141644e6edc57db156bbae828b572d08e540688ac9da865e96b4ff4c |

RegularizedNorm 现有 14 条定理。原链式法则只调整证明 elaboration，不改陈述。新增 `abs_regularizedNorm_sub_sqrt_le` 正确地把非负误差转为绝对值界；`tendsto_regularizedNorm_error_zero` 正确由点态极限相减得到零极限。它们没有额外几何假设，数学语义审核通过。

WeightedIntegral 新增 `continuousOn_weightedIntegral` 与 `hasDerivAt_weightedIntegral_interior`，语义均正确。前者用共同可积支配与逐空间点时间连续性得到闭时间区间连续性，端点不需要导数；后者在 Ioo a b 内使用这一开区间作为时间邻域。新增条件中的 bound 对整个开区间统一是充分条件，可能比点处所需更强，但可由更小紧时间矩形的光滑性提供。

**实际读取版本不是直接的 HasDerivWithinAt 接口**：它提供闭区间连续性+内点经典导数。这个设计能避免初始时间延拓，但连接当前 `coupled_exp_comparison_right` 还差一个小桥：其导数输入覆盖 Ico，包含初值 a。可对每个 a<δ<t 先在 [δ,t] 应用比较，再以连续性令 δ↓a；或另补只需内点导数的比较定理。不能把新 interior 接口直接当成 a 处右导数证据。

CoupledComparison 最新改动是增加四条 `#print axioms` 指令，没有改变原数学陈述；仍须取得实际执行输出才可认定公理检查完成。

## 更新审核：InteriorComparison 与 CurvatureError

2026-09-09 冻结快照：

| 文件 | SHA-256 |
|---|---|
| InteriorComparison.lean | 8b01b5eb8f3f7cb70fd52bc094d511d273f1cab9c7b518aecf2dc4c551bd1333 |
| CurvatureError.lean | 36d8b78ffd91afa555882fee497da3d439cde37a8d610e9baac356294bceb7cd |

### InteriorComparison

语义审核通过。其 scalar/coupled/on 三接口均只需 closed-interval continuity 和 `Ioo a b` 内的实际右导数 `HasDerivWithinAt ... (Ioi t) t`，不要求 a 或 b 的导数。一般双侧导数可限制得到此右导数；它依旧不是 a.e. 或 Dini 导数接口，所以几何上先应用 Θε。

已读取所复用的 EnergyIntegral：`weighted_energy_integral_le` 用真实右导数的积分不等式 FTC，energy 仅需可积，L′ 不需额外可积假设。令 E=0 得 e^(−KΔ)f(b)≤f(a)，再乘正指数，符号正确。K 和 f 无非负要求。a=b 时恒等式成立；on 版本从 t∈Icc a b 取得合法子区间并限制条件，无空洞问题。

该接口**解决此前新 WeightedIntegral interior 接口与旧 Ico 比较之间的初值导数缺口**：闭区间连续性+内点加权积分导数可直接接入，不必再造初始时间延拓或右导数。

### CurvatureError

语义审核通过。正确吸收纯空间版本的五个标量项

    4k²RicSS−2RicHH+2Rm(H,S,H,S)−4∇S Ric(S,H)+2∇H Ric(S,S)

为 (6B+2K)k²+6Dk，并给出 absolute-value 版本以及 Ĉ(k²+k)，其中 Ĉ=max(6B+2K,6D)。非负性引理只需 D≥0 即保证 Ĉ≥0，这是充分且正确的较弱条件。

输入为真实 tensor contraction 的绝对值上界；作为常数吸收引理合法，最终需由 |S|=1、|H|=k、环境算子范数界得这些上界。它不证明这些项出现在 q 演化中，也不能替代实际 connection variation/root evolution。

注释称“six correction terms”，但 displayed formula 有五项（四倍项可理解由合并产生）；这是措辞计数问题，不影响数学结论，无需阻断验收。

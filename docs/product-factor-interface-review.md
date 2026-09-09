# λ 统一估计的静态一维因子接口审核

日期：2026-09-09。结论：**可行；对本模块所需的长度、总曲率与能量一致估计，任意静态一维真实 Riemannian 因子定理足以作为圆尺度 λ 路线的强形式。** 无需首先制作新的 AddCircle chart 实现；但必须保持实际 metric/product/tensor 的证明链，不能把 flatness 或 uniform curvature 作为未经证明的因子数据字段。

## 建议的精确接口

给定真实 Ricci flow (M,g(t))，真实一维光滑无边界流形 C 与 Riemannian metric h，令 G(t)=g(t)⊕h 是 M×C 上**实际构造的正交乘积度量**。h 不随 flow time t 改变。取任意已存在的 smooth immersed closed curve-shortening flow into (M×C,G(t))。

从 base 的真实 tensor bounds B,K,D，推出 G 的相同 bounds，并应用已证明的根估计。最终指数仅依赖 B,K,D 与初始 L、Θ；不依赖 C 的具体 metric h、长度、直径、injectivity radius 或某一坐标表示。

然后给定任意索引 λ（可以是 {λ:ℝ // 0<λ} 或 0<λ<1），允许每个 λ 提供不同的 Cλ,hλ，以及每个 family index a 的实际 curve flow。共同初始 L₀,Θ₀ 推出对所有 a,λ 的同一指数界。不要求 λ↦hλ 或 λ↦c_{a,λ} 光滑/连续。

## 必须实际证明的条目

1. **一维真实曲率为零。** 由切空间维数为一，任意两个方向线性相关；真实 connection curvature 对前两方向交替，故 R(X,Y)Z=0。再 contraction 得 Ric=0，张量导数得 ∇Ric=0。不能仅给因子加 `Flat` 假设而称已证明“一维自动平坦”。
2. **实际 product tangent identification。** T(M×C) 与 TM×TC 的 vector-bundle 同构、chart compatibility、projection/pairing；不能把类型等同当作未经检查的几何同构。
3. **实际 G 构造。** G((v₁,w₁),(v₂,w₂))=g(v₁,v₂)+h(w₁,w₂)，并证明正定性、smoothness 与所需时间联合 smoothness。
4. **Levi–Civita split。** 从正交 product metric 的 Koszul/无挠且 metric-compatible uniqueness 得实际连接分裂，两个因子之间 mixed connection terms 为零。若采用坐标法，仍需 bridge 到真实 canonical LC。
5. **Rm、Ric、∇Ric split。** R^G 仅有 base R^g 分量，factor 与所有 mixed 分量为零；Ric^G 是 base Ric 的 pullback；∇^G Ric^G 是 base ∇Ric 的 pullback。最后一项不能只凭前两项口头略过，它决定修正线性曲率误差的常数 D。
6. **真实 Ricci flow 时间方程。** ∂ₜG=(∂ₜg)⊕0=−2Ric^G，且时间域内的 within derivative 语义保留。任意 h 可以依赖 λ，但本项要求对 t 静态；若允许任意 h(t)，便不能自动得到 Ricci flow。
7. **算子范数界继承。** 正交 product 中 |π_MV|_g≤|V|_G；因此把实际投影向量代入 base 的 multilinear bounds，得到同一 B,K,D。不要用坐标 coefficient norm 控制替代这个结论，否则常数可能隐含依赖 h 或 chart。
8. **family 应用与初始界。** 为每个实际 factor/flow 实例化同一个根估计，显式输出 ∀a,λ 的 bound；共同 L₀,Θ₀ 是允许的上游初始数据，不能由任意紧 C⁰ family 自动推断。

## 紧性与常数范围

若单曲线根定理用显式 B,K,D，而不要求整个 ambient 紧，则上述接口可允许非紧 C；环境 bounds 仍从紧 base 得到。若当前根定理把 ambient compactness 固定在 typeclass 中，可以要求 `CompactSpace C`：所有尺度圆满足此条件，并不会缩减原目标。不要为了声称“任意一维因子”却给根实例制造无法满足的 compactness 缺口。

一维 h 的 curvature 为零不代表其 chart Christoffel 系数在任意 chart 为零；只有适当弧长坐标有该性质。product split 与 tensor norm 继承应该在实际几何层证明，不能把非全局的弧长坐标假设塞入因子接口。

## 是否必须先造 AddCircle 的细节

本根估计只需要目标 factor 的一维 smooth Riemannian 结构，不使用圆周长的数值、degree-one map 或 unit circle vector field。因此把 theorem 写成对所有真实 C,h 的量化，确实是原 circle 模块的强推广，不是只证明一个 Euclidean surrogate。

为了向团队明确交付“所有 λ 的辅助圆”，最终还应给出一个 λ-indexed corollary，接受/复用所选圆表示的真实 chart、维数一与 metric 实例。若现有库已有这些实例，直接实例化；若团队将其作为显式 geometric input，则说明这一输入接口，不要宣称已构造一个尚不存在的 AddCircle metric instance。至少不能以抽象任意 connection coefficients 或抽象 flat tensors 代替真实 factor。

本模块不证明 ramp initial lift、degree、ramp preservation 或存在/延拓；它只对用户允许作为输入的实际 smooth flows 提供一致估计。这些上游构造无需为采用本 factor 接口而额外加入当前范围。

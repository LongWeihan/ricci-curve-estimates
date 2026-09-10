# 纯空间时变联络路线：独立等价性核对

日期：2026-09-09。结论：主代理提出的公式正确，可作为显式路线适配，不缩减目标模块范围。以下是数学审核及推导，非 Lean 编译或公理验收证据。

来源核对：联络一般变分公式见 [Danny Calegari, Ricci Flow, §3.2，PDF 第19–20页](https://math.uchicago.edu/~dannyc/courses/ricci_2019/ricci_flow.pdf)。完整时空公式对照 [第 19.2 节更正 Lemma 0.2](https://arxiv.org/html/1512.00699)；估计目标对照 [Perelman §2.1](https://arxiv.org/pdf/math/0307245)。这里对纯空间路线作独立推导，并显式计算它与时空表达的转换。

## 1. 定义与不可混用的约定

所有空间内积/联络均使用 g(t)，cₜ=H，X=cₓ，v=|X|，S=X/v，H=DₛS，q=|H|²，k=√q，a=q+Ric(S,S)。

在 c*TM 上定义：

    DₓW = ∂ₓW + Γ(g(t))(X,W),
    DₛW = v⁻¹DₓW,
    DₜW = ∂ₜW + Γ(g(t))(H,W).

这里坐标分量是在空间时间点附近**固定的有效空间 chart**内计算；Γ 的时间偏导保持空间坐标不变。`Dₜ` 没有 −Ric♯(W) 项，因而不是 ĝ 的度量相容时空导数。其内积乘积律为

    ∂ₜ⟨V,W⟩ = −2Ric(V,W)+⟨DₜV,W⟩+⟨V,DₜW⟩.

定义联络变分张量 A=∂ₜ∇^g；以固定的空间向量场进行变分。它的坐标分量是 ∂ₜΓ，而不是沿 c 的 Γ 总导数。规范固定为

    R(U,V,W,Z)=⟨(D_U D_V−D_V D_U−D_[U,V])Z,W⟩.

若上游 Lean 采用不同四张量 slot order，需要单独翻译。不能只因都写 `Rm` 就直接复用。

## 2. 从速度到完整 q 演化

由实际 Ricci 流与 cₜ=H，速度律为 vₜ/v=−a。无挠性给 DₜX=DₓH，于是

    DₜS = DₛH + aS.

对任意 pullback 向量场 W，直接交换固定 x,t 坐标导数可得

    (DₜDₓ−DₓDₜ)W = R(H,X)W + A(X,W),
    (DₜDₛ−DₛDₜ)W = aDₛW + R(H,S)W + A(S,W).

第二式的 aDₛW 来自 v⁻¹ 的时间导数；A 是连接本身的时间变化。将 W=S 代入得到

    DₜH = Dₛ²H + 2aH + (Dₛa)S + R(H,S)S + A(S,S).

Ricci 流的联络变分公式为

    ⟨A(U,V),W⟩
      = −(∇_U Ric)(V,W)−(∇_V Ric)(U,W)+(∇_W Ric)(U,V).

特别

    2⟨A(S,S),H⟩ = −4(∇_S Ric)(S,H)+2(∇_H Ric)(S,S).

空间单位切向量给 ⟨H,S⟩=0、⟨DₛH,S⟩=−q。明确新定义

    Psp = DₛH−⟨DₛH,S⟩S = DₛH+qS.

则 |DₛH|²=|Psp|²+q²。对 q 使用前述时变内积律而非固定 metric 律，得到

    qₜ = Dₛ²q−2|Psp|²+2q²
         +4q Ric(S,S)−2Ric(H,H)+2R(H,S,H,S)
         −4(∇_S Ric)(S,H)+2(∇_H Ric)(S,S).

该式每个系数、正负号均与主代理所提一致。尤其 −2Ric(H,H) 不能从 DₜH 中“自动包含”而忘记 metric variation。

## 3. 与更正文献中的时空公式的显式转换

设 ĝ=g(t)+dt²，T=∂ₜ，∇̂ 为其 Levi–Civita 联络；这里只作纸面等价性审计，纯空间实现不需要先构造 ĝ。写 α=Ric(S,S)、β=Ric(S,H)、δ=Ric(H,H)。

由 ∇̂_S H=DₛH+βT，时空投影与空间投影的关系是

    P̂=Psp+βT,
    |P̂|²=|Psp|²+β².

二者不能直接等同。利用 ∇̂_U V=∇^g_U V+Ric(U,V)T 和 ∇̂_U T=−Ric♯U，得到所需的两个 curvature component identities：

    R̂(H,S,H,S)=R(H,S,H,S)−αδ+β²,
    R̂(T,S,H,S)=−(∇_S Ric)(S,H)+(∇_H Ric)(S,S).

第二式也可由其水平曲率算子写作 A(S,S)+(∇_S Ric)♯S，再与 H 取内积验证。

把 Ĥ=H+T 与这些公式代入更正文献中的完整公式：

- 投影平方中的 −2β² 与纯水平曲率中的 +2β² 抵消。
- 纯水平曲率中的 −2αδ 与显式 +2Ric(S,S)Ric(H,H) 抵消。
- 单时间曲率中的 −2(∇_S Ric)(S,H)+2(∇_H Ric)(S,S)，与原显式 −2(∇_S Ric)(S,H) 合并。

结果恰为第 2 节的纯空间公式。因而这条路线保留了修正项的全部数学内容；它没有把错误的旧版曲率公式重新引入。

## 4. 环境常数与后续分析链

假设 B,K,D≥0 是真实 Ric、Rm、∇Ric 的 tensor operator norm bounds。因为 |S|=1，|H|=k：

    |4q RicSS−2RicHH+2R(H,S,H,S)| ≤ (6B+2K)q,
    |−4(∇_S Ric)(S,H)+2(∇_H Ric)(S,S)| ≤ 6Dk.

因此 A₀=6B+2K、A₁=6D，Ĉ=max(A₀,A₁)，C₁=Ĉ/2 合法。它们没有额外 B² 项，是时空拆分中二次 Ric 项抵消后的直接估计。

正则化也用空间投影：Dₛq=2⟨Psp,H⟩，故 hε 的 Kato 界 |Dₛhε|²≤|Psp|² 仍成立。之后 hε PDE、移动弧长积分、Θε 比较、ε 极限以及 λ-统一产品圈估计完全保留原目标。

平坦 circle product 中 Ric、Rm、∇Ric 的所有 circle direction contributions 为零，所以这三种环境界从 base flow 直接传递，独立于 λ 和圆的 injectivity radius。

## 5. 作为 Lean 路线适配的验收要求

可采用，但须在进度/来源说明中明确“适配：时空投影版本改写为纯空间联络变分版本”，并记录上面的等价转换，不要称直接复用更正文献的公式。

必须实际证明 A 的变分式、pullback 的 Dₜ/Dₓ 交换式以及时变内积律，不能把它们包装成 curve data 的未经证明字段。这替代的是 ĝ 构造和其混合曲率桥，仍有实质几何证明负担。

Basic 的 moving-foot 定义可保留，但时间微分计算应先在固定 chart 内表达，并用合法 chart/trivialization bridge 识别结果。不得对“随基点变化的选定 chart”裸求时间导数，也不需要为全曲线假设一个全局坐标域。

内点推导已足够，端点用连续性/积分比较延伸；光滑解存在仍为输入，不增加存在或延拓结论。根定理假设与原规格相同，输出的长度、总曲率、能量和参数族范围不变。

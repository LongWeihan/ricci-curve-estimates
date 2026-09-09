# Ricci 流下曲线的一致估计

**GPT-6 Astra · Juii-hang Leung（龙维汉）**

本项目形式化 Perelman–Morgan–Tian 有限消失路线中的曲线长度与总曲率估计。输入是已经存在的光滑浸入闭曲线收缩流及真实 Ricci 流背景；内部证明修正曲率演化、曲率零点正则化、移动弧长积分，以及静态一维辅助因子下的一致常数。

[English](README.md) · [英文技术报告 PDF](paper/curve-estimates.pdf) · [中文蓝图](website/zh/index.html) · [English](website/index.html) · [文档索引](docs/index.md)

## 可接入的结论

记 `L` 为长度、`Θ` 为总曲率。给定紧致基底上的 Ricci 流，最终产品定理在**所有辅助因子度量、曲线族和初值界之前**选取非负 `B,C`。若共同初值满足 `L(a)≤L₀`、`Θ(a)≤Θ₀`，则对所有曲线、辅助度量和 `a≤t≤b`，

\[
L(t)\le L_0 e^{B(t-a)},\qquad
\Theta(t)\le(\Theta_0+L_0)e^{C(t-a)}.
\]

初始长度项保留了 Morgan–Tian 修正的必要依赖。辅助因子须为真实一维光滑 Riemannian 流形，度量在 Ricci 时间上静态；正尺度无需统一正下界。新增应用模块从供给的 `h₀` 实际构造 `hλ=λ²h₀`，并给出整个闭时间区间上的统一界。

| 用途 | 入口 |
|---|---|
| 任意静态因子度量族、正尺度统一 | [UniformProductEstimates](CurveControl/Geometry/UniformProductEstimates.lean) |
| 实际缩放度量与应用 | [StaticFactorApplication](CurveControl/Examples/StaticFactorApplication.lean) |
| 给定真实环境界的几何根 | [CurveEstimates](CurveControl/Geometry/CurveEstimates.lean) |
| 长度演化与曲率能量积分 | [LengthEstimates](CurveControl/Geometry/LengthEstimates.lean) |
| 完整输入及声明名称 | [接入指南](docs/integration-guide.md) |

内部的曲率 PDE、Kato、张量分裂、积分求导及比较均已证明。流存在、真实因子流形与初始度量、统一初值界仍是调用者输入。具体 `AddCircle` 图册、ramp 构造、解延拓及有限消失本身不在本模块内。实现先比较正则化总曲率再取极限，没有另行逐字实现未正则化 `Θ` 的绝对连续及几乎处处微分接口。

## 审阅与复现

[技术报告](paper/curve-estimates.pdf) 解释数学内容与形式化选择，是代码的技术审阅文件，不主张新的数学结论。[蓝图](website/index.html) 将证明步骤关联至实际 Lean 声明；[贡献地图](docs/contribution-map.md) 区分上游复用与新增证明、适配和集成。

依赖固定的 Lean 4.32.1 与源版本。使用已有匹配源树的复现入口为：

```sh
python3 scripts/prepare_dependencies.py --mathlib /path/to/mathlib4 --geometry /path/to/Poincare-Conjecture
python3 scripts/verify.py
```

完整操作见 [复现说明](docs/reproduction.md)。当前机械证据以 [release-check.json](verification/release-check.json) 的真实运行结果和源码哈希为准；历史审核保留各自的时间截面，不应把旧统计当成本版覆盖证据。[验收记录](docs/release-acceptance.md) 链接独立语义复核。复核由 Astra AI 代理完成，并非外部人类同行评审；见 [作者与工具说明](AUTHORS.md)。

项目复用 mathlib 和 frenzymath 的 DoCarmoLib/MorganTianLib，遵循 [Perelman](https://arxiv.org/abs/math/0307245) 与 [Morgan–Tian 2015 修正](https://arxiv.org/abs/1512.00699) 的既有数学路线，不主张首次或新发现。许可证及来源见 [LICENSE](LICENSE)、[NOTICE](NOTICE)；引用草案见 [CITATION.bib](CITATION.bib)，版本变化见 [CHANGELOG](CHANGELOG.md)。署名如上；未声明 DOI 或正式发表。

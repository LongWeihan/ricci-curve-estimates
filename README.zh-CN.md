<p align="center">
  <img src="docs/assets/ricci-curve-banner.zh-CN.svg" alt="Ricci 流下曲线的一致估计 — Lean 形式化" width="100%">
</p>

<p align="center">
  <a href="README.md">English</a> · <strong>简体中文</strong>
</p>

<p align="center">
  <strong>GPT-6 Astra · Juii-hang Leung（龙维汉）</strong><br>
  Perelman 有限时间消失论证中的曲线长度与总曲率估计。
</p>

<p align="center">
  <a href="lean-toolchain"><img src="https://img.shields.io/badge/Lean-4.32.1-4066a5?style=flat-square" alt="Lean 4.32.1"></a>
  <a href="NOTICE"><img src="https://img.shields.io/badge/mathlib-pinned-657a58?style=flat-square" alt="固定版本的 mathlib 依赖"></a>
  <a href="LICENSE"><img src="https://img.shields.io/badge/License-Apache--2.0-526477?style=flat-square" alt="Apache 2.0 许可证"></a>
  <a href="https://github.com/LongWeihan/ricci-curve-estimates/actions/workflows/pages.yml"><img src="https://github.com/LongWeihan/ricci-curve-estimates/actions/workflows/pages.yml/badge.svg" alt="GitHub Pages 部署状态"></a>
  <a href="README.md"><img src="https://img.shields.io/badge/Readme-English%20%7C%20%E4%B8%AD%E6%96%87-237d85?style=flat-square" alt="中英文 Readme"></a>
</p>

<p align="center">
  <a href="https://longweihan.github.io/ricci-curve-estimates/zh/"><strong>浏览展示网页 ↗</strong></a> ·
  <a href="https://longweihan.github.io/ricci-curve-estimates/zh/blueprint.html">证明蓝图</a> ·
  <a href="https://longweihan.github.io/ricci-curve-estimates/note.pdf">技术报告</a> ·
  <a href="docs/integration-guide.md">接入指南</a>
</p>

---

本 Lean 4 项目形式化真实 Ricci 流背景下**已有光滑浸入闭曲线收缩流**的一致估计：从几何定义推导修正曲率演化，用正则化处理曲率零点，对移动弧长测度积分，并构造对静态一维辅助因子一致的常数。

## 核心估计

给定紧致基底上闭时间区间 $[a,b]$ 内的 Ricci 流，最终产品定理在**所有辅助因子度量、曲线族和初值界之前**选取 $B,C\geq 0$。若每条曲线满足 $L(a)\leq L_0$、$\Theta(a)\leq\Theta_0$，则

$$
L(t)\leq L_0 e^{B(t-a)},\qquad
\Theta(t)\leq (\Theta_0+L_0)e^{C(t-a)},\qquad a\leq t\leq b.
$$

其中 $L$ 为长度，$\Theta$ 为总曲率，均由演化中的实际度量定义。修正后的估计包含初始长度项。

辅助因子可以是任意供给的真实一维光滑 Riemannian 流形，其度量在 Ricci 时间上静态。应用模块实际构造 **$h_\lambda=\lambda^2h_0$（所有 $\lambda>0$）**，正尺度无需统一正下界，并得到整个闭时间区间上的统一界。

## 浏览项目

| 入口 | 内容 |
| :--- | :--- |
| [交互式证明蓝图](https://longweihan.github.io/ricci-curve-estimates/zh/blueprint.html) | 22 个数学节点及其对应的 Lean 声明、前置步骤 |
| [声明浏览器](https://longweihan.github.io/ricci-curve-estimates/zh/declarations.html) | 完整 Lean 类型、具体假设和源码链接 |
| [技术报告 · PDF](paper/curve-estimates.pdf) | 英文数学说明、修正演化、证明组织与范围 |
| [English website](https://longweihan.github.io/ricci-curve-estimates/) | 相同数学内容的英文展示 |
| [文档索引](docs/index.md) | 接入、复现、贡献地图与语义审核 |

## 使用 Lean 模块

| 用途 | 入口模块 |
| :--- | :--- |
| 任意静态辅助因子度量族的一致估计 | [UniformProductEstimates](CurveControl/Geometry/UniformProductEstimates.lean) |
| 实际缩放度量与全时间区间估计 | [StaticFactorApplication](CurveControl/Examples/StaticFactorApplication.lean) |
| 给定实际环境张量界的曲线估计 | [CurveEstimates](CurveControl/Geometry/CurveEstimates.lean) |
| 长度演化与曲率能量积分 | [LengthEstimates](CurveControl/Geometry/LengthEstimates.lean) |

```lean
import CurveControl.Examples.StaticFactorApplication
```

精确定理名称及调用前提见[接入指南](docs/integration-guide.md)。使用已有匹配依赖源码和固定的 Lean 4.32.1 工具链复现：

```sh
python3 scripts/prepare_dependencies.py \
  --mathlib /path/to/mathlib4 \
  --geometry /path/to/Poincare-Conjecture
python3 scripts/verify.py
```

[复现说明](docs/reproduction.md)还涵盖缺失源码的获取、依赖缓存和离线网页生成。仓库不附带工具链及依赖缓存。

## 验证与范围

随包附带的[发布验证记录](verification/release-check.json)报告了完整构建和 **796 个项目声明**的公理审计，可达公理仅为 `propext`、`Classical.choice`、`Quot.sound`。该证据绑定于记录中的实际运行及源码哈希。[Lean 工作流](https://github.com/LongWeihan/ricci-curve-estimates/actions/workflows/verify.yml)单独保存托管运行的日志；顶部的 Pages 徽章反映网页部署状态。

项目内部证明演化、Kato 不等式、产品张量分裂、积分求导和比较估计。调用方提供光滑流的存在性、因子流形及起始度量、共同初值界。具体 `AddCircle` 图册、ramp 构造、解延拓与有限消失本身不在本模块内；未正则化总曲率的独立绝对连续／几乎处处微分接口也尚未提供。

语义复核由独立 Astra AI 代理完成，与 Lean 机械检查、外部人类同行评审分别看待。详见[作者与工具说明](AUTHORS.md)及[验收记录](docs/release-acceptance.md)。

<details>
<summary><strong>仓库与发布说明</strong></summary>

- `CurveControl/` 含 44 个数学模块，`CurveControl.lean` 为根导入。
- `blueprint/` 与 `website-template/` 提供双语展示内容与模板。
- `website/` 保存生成的网页；输入内容更新后，[GitHub Pages](docs/github-pages.md)自动重建并发布。
- `PACKAGE-MANIFEST.json` 描述原始 ZIP 快照。后续 README 和发布配置变更记录于 Git 历史中；历史验证记录保留其原有适用范围。

</details>

## 来源与引用

项目遵循 [Perelman 有限消失论文](https://arxiv.org/abs/math/0307245)及 [《Ricci Flow and the Poincaré Conjecture》第 19.2 节更正](https://arxiv.org/abs/1512.00699)，复用固定版本的 **mathlib** 和 **frenzymath 几何库**。[贡献地图](docs/contribution-map.md)区分上游基础设施与本项目的形式化和集成工作。

采用 [Apache License 2.0](LICENSE)。依赖来源见 [NOTICE](NOTICE)，引用草案见 [CITATION.bib](CITATION.bib)，版本记录见 [CHANGELOG](CHANGELOG.md)。本项目不主张新的数学结论、DOI 或正式发表。

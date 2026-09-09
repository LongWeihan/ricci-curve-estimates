# 验证与复现记录

署名：**GPT-6 Astra（AI 模型）与 Juii-hang Leung（龙维汉）**。日期：2026-09-09。

本模块证明 Perelman–Morgan–Tian 有限消失路线中的 Ricci 流曲线族一致长度与总曲率估计，并提供实际缩放度量应用。报告、数学蓝图和声明浏览器与同一组 Lean 源码对应。

## 最终检查

完整冻结验证完成于 **2026-09-09T12:25:29+00:00**。

| 项目 | 结果 |
|---|---|
| Lean | 4.32.1，源码提交 `f054605aea4b840552cca2e725580bffd1e1b704` |
| 库构建 | `lake build CurveControl`，exit 0 |
| 公理审计 | 796 个项目声明；仅 `propext`、`Classical.choice`、`Quot.sound` |
| 源码与配置 | 四个外部库指纹匹配；73 个发布输入文件在检查前后哈希相同 |
| 数学源码保持 | 44 个数学模块及根模块与已独立重建的源码逐文件相同 |
| 报告 | 8 页；署名与中文姓名正确；所有页面渲染检查通过，数学正文保持不变 |
| 双语网站 | 98 页；22 个数学节点、62 个真实完整 Lean 类型；17,790 个本地链接与锚点通过 |
| 语言对应 | 公式、Lean 声明、前置依赖与源代码锚点在两种语言中一致；中文说明经独立审核 |

声明数包含定义、实例、私有和生成声明，不是定理数量。网站切换语言时保留搜索词和源码行锚点；类型和源码以 Lean 原文显示。两种语言的网站均可离线阅读。

## 复现与审核证据

- [机器可读验证记录及哈希](../verification/release-check.json)，[完整构建日志](../verification/full-build.log)，[公理明细](../verification/reachable-axioms.json)。
- [已有隔离重建](isolated-reproduction.md)：从没有项目编译缓存的新目录重建全部 45 个 Lean 源文件，复用同机固定外部依赖缓存，验证通过。[本次源码保持检查](../verification/presentation-math-preservation.json)确认这些数学源码没有变化；本次完整验证覆盖新的报告与网站工具输入。
- [报告排版检查](../verification/note-check.json)与[数学正文对比](../verification/paper-content-preservation.json)。
- [英文蓝图独立审核](blueprint-independent-review.md)、[中文蓝图独立审核](chinese-blueprint-review.md)、[双语工具审核](bilingual-tooling-review.md)及[浏览器呈现检查](../verification/bilingual-presentation-check.json)。
- [实际缩放应用审核](scaled-factor-semantic-review.md)、[最终统一估计审核](final-uniformity-semantic-review.md)、[曲率根审核](curvature-root-semantic-review.md)。

历史记录保留各自的源码哈希和时间。新的署名和双语呈现不改变历史检查的结论或范围。AI 语义复核与 Lean 机械检查分别记录；没有声称外部人类同行评审或已运行托管 GitHub CI。

## 接入范围

调用方提供真实光滑流的存在、因子流形与起始度量、共同初始界。内部曲率演化、Kato、产品张量分裂、积分求导与比较均由模块证明。具体 AddCircle 图册、ramp 存在/延拓、未正则化总曲率的独立 AC/a.e. 接口和完整有限消失/Poincaré 定理不在本模块范围内。参见[接入指南](integration-guide.md)和[贡献地图](contribution-map.md)。

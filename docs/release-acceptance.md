# 验证与复现记录

日期：2026-09-09。完整冻结验证完成于 **2026-09-09T13:45:48+00:00**。

本模块证明 Ricci 流下已有光滑浸入闭曲线族的一致长度与总曲率估计，并提供静态因子度量缩放的应用。报告、数学蓝图和声明浏览器与同一组 Lean 源码对应。

## 检查结果

| 项目 | 结果 |
|---|---|
| Lean | 4.32.1，源码提交 `f054605aea4b840552cca2e725580bffd1e1b704` |
| 库构建 | `lake build CurveControl`，exit 0 |
| 公理审计 | 796 个项目声明；仅 `propext`、`Classical.choice`、`Quot.sound` |
| 验证输入 | 四个外部库指纹匹配；73 个输入文件在检查前后哈希相同 |
| 数学源码 | 44 个数学模块及根模块与已独立重建的源码逐文件相同 |
| 报告 | 8 页英文报告；逐页渲染检查通过，数学正文逐字保持 |
| 双语网站 | 98 页；22 个数学节点、62 个完整 Lean 类型；17,692 个本地链接与锚点通过 |
| 语言对应 | 数学公式、声明、依赖与源码锚点一致；中英文说明经独立复核 |
| 页面交互 | 首页单次署名；地球图标配“语言 / Language”提示，切换时保留章节、源码行和搜索内容 |

声明数包括定义、实例、私有声明和生成声明。数学命题及其具体假设可在网站的完整 Lean 类型中查看。

## 证据

- [机器验证与输入哈希](../verification/release-check.json)、[完整构建日志](../verification/full-build.log)、[公理明细](../verification/reachable-axioms.json)。
- [隔离重建](isolated-reproduction.md)：同机新目录、无项目编译缓存，复用固定外部依赖缓存。[源码保持检查](../verification/presentation-math-preservation.json)将该次重建绑定到当前数学源码。
- [报告排版检查](../verification/note-check.json)、[数学正文对比](../verification/paper-content-preservation.json)。
- [蓝图措辞与双语语义复核](minimal-exposition-review.md)、[网站工具复核](bilingual-tooling-review.md)、[浏览器检查](../verification/bilingual-presentation-check.json)。
- [缩放应用审核](scaled-factor-semantic-review.md)、[统一估计审核](final-uniformity-semantic-review.md)、[曲率演化审核](curvature-root-semantic-review.md)。

各项历史审核保留时间与源码哈希。语义审核方法记录在 [AUTHORS](../AUTHORS.md)；当前 Lean 检查与上述呈现检查分别记录。

## 接入范围

调用方提供已有光滑流、因子流形与起始度量、共同初始界。模块证明内部曲率演化、Kato 不等式、乘积张量分裂、积分求导和比较估计。接入完整有限消失证明还需圆图册、ramp 构造与延拓及其余几何拓扑步骤；独立的未正则化总曲率 AC/a.e. 接口另需建立。参见[接入指南](integration-guide.md)和[贡献地图](contribution-map.md)。

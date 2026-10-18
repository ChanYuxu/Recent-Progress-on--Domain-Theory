# 逐项形式化状态

形式化对应论文正文第 2–5 节；论文 TeX 源码不随代码包提供。
附录与说明性 remarks 不在形式化范围内。章节 1 是说明性 introduction。

“已证明”在下表中表示已构造 Lean 证明项。该证明可能传递依赖登记的文献公理；
可运行 `lake env lean PointCentralFubini/AxiomAudit.lean` 查看主要结论的传递公理依赖。
没有把未完成的本稿命题变成公理。

| 原文 | 标签 | 当前状态 |
|---|---|---|
| 2.1 | `thm:heckmann-approximation` | 外引公理，包含有界连续及有界点连续逼近两部分 |
| 2.2 | `prop:normalization` | 已证明，包含两个 centrality 约定及三种全局条件的等价 |
| 2.3 | `prop:heckmann` | 已证明：point topology 的连续性与有限见证判据等价 |
| 2.4 | `thm:point-central-subprob` | 外引公理，仅 JLMZ 的开集、次概率版本 |
| 2.5 | `cor:point-central` | 已证明：任意质量的点连续估值 central |
| 2.6 | `def:fubini-object` | 定义，量化所有连续估值及任意伴随 dcpo |
| 2.7 | `lem:membership` | 已证明：有序积的 incidence 开性及 neighbourhoodMap 连续性 |
| 2.8 | `prop:incidence` | 已证明：canonical incidence 判据 |
| 2.9 | `cor:incidence-subprobability` | 已证明：有限或次概率 incidence 测试均足够 |
| 3.1 | `lem:kappa-countable` | 已证明；内部辅助结论允许任意递增集合序列 |
| 3.2 | `thm:countable-point` | 已证明；无分离性要求，保留可数 saturation 的一般形式 |
| 3.3 | `cor:countable-dcpo` | 已证明一般共初条件及可数 dcpo 的类等式/Fubini 结论 |
| 4.1 | `lem:scott-fatou` | 已证明；尾部下确界与 h 取最小后的连续性已检查 |
| 4.2 | `prop:measure-source-incidence` | 已证明；有限分割近似、Λ 测度、Radon–Nikodym 与支撑集比较 |
| 4.3 | `lem:full-outer-trace` | 已证明；A 不要求 Borel，包括 τ-smoothness |
| 4.4 | `lem:full-vietoris-lift` | 已证明；使用原文引用的 AJK 测度扩张文献公理 |
| 4.5 | `lem:extremal-observables` | 已证明；具体 extrema、连续性、生成完整 Vietoris 拓扑、第一可数性 |
| 4.6 | `lem:inner-skeleton` | 已证明；正测度纤维、较粗可数拓扑及同测度内逼近 |
| 4.7 | `thm:sorgenfrey-fubini` | 已证明；无未完成的本稿命题参数，保留显式文献公理边界 |
| 5.1 | `thm:descent` | 已证明，未添加可数性或 core-compactness 假设 |
| 5.2 | `cor:cocon-descent` | 已证明；另有 weak topology 与 point topology 相等的证明 |
| 5.3 | `thm:dBK` | 外引公理，对应已核验的 Proposition 7.2 |
| 5.4 | `cor:second-countable` | 已证明；假设为 Scott 拓扑第二可数，而非载体可数 |

## 第四节的完整证明链

1. **4.2 测度关联恒等式**：构造有限 Borel 测度 Λ，使用 mathlib 的 Radon–Nikodym 定理；在支撑点归一化限制测度，应用 Scott–Fatou，得到几乎处处的密度比较。另一方向选取分割各原子上接近下确界的代表点，精确保持有限个 skeleton 测试，并将单边积分误差趋零。结论保留原文完整假设，未增加 Radon 或分离性要求。
2. **4.4 full Vietoris 提升**：从 clopen 基构造 Sorgenfrey 线的 Stone–Čech 嵌入；证明紧集空间的闭序、两种 Vietoris 嵌入及像的上闭性。使用原文引用的 AJK Theorem 27 存在性条款，证明像外 Borel 集测度为零、Radon 测度的 τ 光滑性，再传输已证明的 full-outer 迹测度。
3. **4.7 主定理**：`sorgenfrey_fubini` 调用上述实际证明以及 4.5、4.6，经 finite incidence 判据和归一化得到完整的 Fubini object 结论。

`SourceStatements.lean` 保留各命题类型；兼容的条件组装接口不替代实际定理的证明。

两处证明方法作了等价调整：4.2 使用近下确界代表点的单边误差，
替代原文的 dyadic oscillation 分割；4.4 通过把邻域中的紧集加入候选紧集，直接证明
full Vietoris 的开上集拓扑等于 upper Vietoris，避免再导入环境空间的 Scott 拓扑识别定理。

4.5 的证明通过紧集左侧空隙构造有理 clopen 细化，覆盖完整的连续性与拓扑生成结论。
4.6 的证明处理所有有限 τ 光滑 Borel 测度，未增加 Radon 或可分性假设。
两项新引理只依赖 Lean 标准公理 `propext`、`Classical.choice`、`Quot.sound`。
另已证明一般 Hausdorff 空间的非空紧集按反包含序形成 dcpo；
`xuYang_sorgenfrey_dcpo` 保留原声明名，已由外引公理改为内部定理。
当前文献公理数量为 10；正文没有 statement-only 证明债，但外引定理尚未内部重证。
独立数学复核及人工批准均待进行。

## 语义与验证边界

- 连续估值真正作用于拓扑开集，具有 strictness、modularity、Scott continuity。
- point-continuity 定义为 point topology 到 `[0,∞]` Scott topology 的实际连续性；有限见证判据有证明。
- 积分使用 layer-cake Lebesgue 积分。只在已证明 LSC 的函数上使用 Choquet 积分定理；任意函数的 total extension 采用 superlevel 的 interior。
- centrality 的测试函数取有序积上的 Scott-continuous maps，未替换成普通拓扑积。
- partner universe 显式多态。incidence 的 iff 使用同宇宙；充分性及两个主结论可实例化到任意伴随宇宙。
- `SorgenfreySmyth` 是 Sorgenfrey 拓扑下的非空紧子集，使用反包含序；full Vietoris 和 Scott 空间通过不同载体/拓扑接口区分。
- 文献公理的准确 statement、来源和是否内部重证分别记录在 `external-sources.json`。

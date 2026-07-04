<!-- markdownlint-disable MD013 MD052 -->

# 缝合方法程序使用说明

## 文档目标与读者

本文面向需要实际调用和维护程序的学生。读者应已经熟悉基本 spinor-helicity 记号、massive external leg 的 polarization 标记，以及局域振幅基底的线性约化思想。本文不假设读者了解本项目的历史代码结构。

程序的核心目标是计算含有一对等自旋重粒子外腿 \(1,2\) 的局域振幅基底。程序先按 \(12\) 通道角动量 \(J_{12}\) 把 heavy-pair 部分分离为左侧三点 current，再构造右侧 residual block，最后缝合并用 CF block 做独立完备性检查。普通使用者只需要调用一个主函数：

```wl
ConstructProjectedSewingRelativeChiralBasis
```

其余函数主要用于检查中间结构、定位错误或扩展程序。

## 获取与部署

代码仓库为

```text
https://github.com/zizhengzhou/MassiveAmplitude.git
```

当前用于本文方法的分支为

```text
chiral-HBP
```

在一台已经安装 Mathematica 或 Wolfram Engine 的机器上，可用以下命令取得代码：

```powershell
git clone https://github.com/zizhengzhou/MassiveAmplitude.git
cd MassiveAmplitude
git checkout chiral-HBP
```

若代码已经随论文工作区存在，当前本地位置通常为

```text
chiral-QCD-paper/sewing-method-code
```

进入仓库根目录后，在 Mathematica notebook 或 WolframScript 中加载 package：

```wl
Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];
```

在 PowerShell 中运行回归测试：

```powershell
wolframscript -file tests\run_all.wls
```

该测试会加载 package 并运行维护中的核心回归，包括 symbol/amp form 分离、左右缝合、相对 chiral order、identical projection、SU(3) direct product 和若干文章例子。

## 主接口

普通计算应使用以下两种调用形式之一。

```wl
ConstructProjectedSewingRelativeChiralBasis[
  leftSpin,
  rightSpins,
  ampDim,
  identicalParam,
  opts
]
```

或显式给出右侧 massive label：

```wl
ConstructProjectedSewingRelativeChiralBasis[
  leftSpin,
  rightSpins,
  rightMass,
  ampDim,
  identicalParam,
  opts
]
```

输入参数含义如下。

| 参数 | 含义 |
| --- | --- |
| `leftSpin` | 外腿 \(1,2\) 的共同自旋，例如 `1/2` 或 `3/2` |
| `rightSpins` | 外腿 \(3,\ldots,n\) 的自旋列表 |
| `rightMass` | 可选参数，只列出右侧有质量物理腿，例如 `{3}` 或 `{3,4}` |
| `ampDim` | 文章约定中的振幅维数 \(d_{\rm amp}\) |
| `identicalParam` | 右侧全同粒子分组，例如 `{}` 或 `{{3,4}}` |
| `opts` | 选项，包括 SU(3)、极化过滤、Q 展示、调试数据等 |

`rightMass` 的语义需要特别注意。主函数中，腿 \(1,2\) 总是在内部视为 massive；位置参数 `rightMass` 只描述右侧物理腿。调用

```wl
ConstructProjectedSewingRelativeChiralBasis[leftSpin, rightSpins, {3}, ampDim, identicalParam]
```

表示腿 \(3\) massive；位置参数 `{3,4}` 表示腿 \(3,4\) massive。若必须使用选项写法，应使用公开选项名 `RightMass -> {3}`，不要使用小写的伪选项名。若省略该参数，主函数中的 `Automatic` 表示所有右侧物理腿 \(3,\ldots,n\) massive。

## 常用选项

`su3ShapeList` 给出所有外腿的 SU(3) shape label。若取空列表 `{}`，程序只计算 Lorentz 结构。常见 label 包括 `""`、`"q"`、`"aq"` 和 `"g"`。开启 SU(3) 后，输出项不再只是 Lorentz amplitude，而是包含 `LorentzSymbolForm`、`SU3Basis`、`SU3IndexDictionary` 和 `DirectProduct` 的 association。

`RightPolarizationFilter` 用于限制右侧粒子的允许极化。默认值为 `All`。例如

```wl
RightPolarizationFilter -> <|3 -> 1, 5 -> {0, 2}|>
```

表示只保留腿 \(3\) 极化为 \(1\)，且腿 \(5\) 极化为 \(0\) 或 \(2\) 的 sector。key 必须是右侧物理腿标签 \(3,4,\ldots\)，value 可以是整数、整数列表或 `All`。若存在全同粒子，程序先做标准 identical representative selection，再应用该过滤。

`QReplacement` 控制 formal `Q` 在内部 amp form 中如何替换。默认值为

```wl
QReplacement -> {1, -2}
```

即 \(Q=p_1-p_2\)。如果只想在调试时把 \(Q\) 替成单个标签，也可以使用 `QReplacement -> 2`，但论文展示通常应保留 formal \(Q\) 的物理含义。

`ReplaceQInFinalSymbolForm` 控制最终 symbolic 输出中是否保留 `Q`。默认值为 `True`，即按 `QReplacement` 替换。若希望最终结果中看到 formal `Q`，使用

```wl
ReplaceQInFinalSymbolForm -> False
```

`ReturnProjectionData` 默认值为 `False`。若设为 `True`，返回值会包含详细数据：每个 sector 的 sewing records、CF/sewing rank、identical Young operator、SU(3) 字典、\(J\)-block 诊断和性能记录。

`SewingContractionMode` 默认值为 `"Split"`。这表示全对称缝合的各项先作为独立 record 进入 reduction。若设为 `"Sum"`，同一组全对称收缩会先求和再进入 reduction。两者不改变 span 完备性，但 `"Split"` 保留更细的来源信息。

`SewingDebug -> True` 会打印额外诊断信息。普通计算中应保持默认关闭。

## 输出结构

默认输出是按 relative chiral order 分组的 association：

```wl
<|
  2 -> {amp1, amp2, ...},
  3 -> {amp3, ...}
|>
```

key 是程序定义的相对 chiral-order 标签

$$
d_{\rm rel}=d_{\rm amp}-J_{12}-n_x ,
$$

其中 \(n_x\) 是 `Xhard` 幂次。这个标签用于同一 sector 内排序，不包含具体 operator convention 的整体平移。

若 `ReturnProjectionData -> True`，常用字段如下。

| 字段 | 内容 |
| --- | --- |
| `"BasisByRelativeChiralOrder"` | 与默认输出相同的最终分组基底 |
| `"SectorResults"` | 每个右侧极化 sector 的投影、rank 和 \(J\)-block 诊断 |
| `"Spins"` | 全部外腿自旋 |
| `"Mass"` | 内部使用的完整 mass option |
| `"IdenticalTypeList"` | identical representative 与 Young projection 数据 |
| `"CandidateBlocks"` | 枚举得到的 CF sector 候选 |
| `"PhysicalBlocks"` | 经过 identical 和极化过滤后的物理 sector |
| `"RightPolarizationFilter"` | 实际使用的右侧极化过滤规则 |
| `"SU3ShapeList"` | 输入的 SU(3) shape 信息 |
| `"SU3IndexDictionaries"` | SU(3) 结构生成返回的 index dictionary |

调试时首先看 `"BasisByRelativeChiralOrder"`，随后看 `"SectorResults"` 中每个 sector 的 `CompleteQ`、rank 和 `TotalJBlockDiagnostics`。

## 最小例子：\(\bar B B u f_+\)

考虑四点 sector

$$
(\bar B,B,u,f_+)=(1,2,3,4).
$$

腿 \(3\) 是 massive spin-one \(u_\mu\)，腿 \(4\) 是 positive-helicity massless vector \(f_+\)。计算 \(d_{\rm amp}=4\) 的 Lorentz basis：

```wl
Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

res = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3},
  4,
  {},
  su3ShapeList -> {},
  RightPolarizationFilter -> <|3 -> 1|>,
  ReplaceQInFinalSymbolForm -> False
];
```

输出形式为

```wl
<|
  order1 -> {basis...},
  order2 -> {basis...}
|>
```

这里 `RightPolarizationFilter -> <|3 -> 1|>` 固定 \(u_\mu\) 的 longitudinal polarization。若不加该过滤，主函数会枚举 \(u_\mu\) 的所有 massive polarization sector，输出不会等于文章中的单 sector 表格。

在文章的 \(\bar B B u f_+\) 例子中，\(d_{\rm amp}=3\) 产生两个 \(J_{12}=1\) leading rows；\(d_{\rm amp}=4\) 在该 longitudinal sector 中产生两个 \(J_{12}=1\) residual blocks 和一个 raised \(J_{12}=2\) block。重要结论是：\(d_{\rm amp}=4\) 的正确结构不是旧的 \(J_{12}=0\) 的 `Xhard/Xsoft` 闭合行。

若需要看到内部 sector 数据，可使用

```wl
resData = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3},
  4,
  {},
  su3ShapeList -> {},
  RightPolarizationFilter -> <|3 -> 1|>,
  ReturnProjectionData -> True,
  ReplaceQInFinalSymbolForm -> False
];

resData["BasisByRelativeChiralOrder"]
```

若只想复现固定右侧极化 \(\{1,0\}\) 的 CF/sewing 秩比较，可运行维护脚本：

```powershell
wolframscript -file tests\section_5_2_bbuf_reproduce.wls
```

该脚本检查 \(d_{\rm amp}=3,4,5,6\)，并验证

$$
\operatorname{rank}M_{\rm CF}
{}=
\operatorname{rank}M_{\rm sew}
{}=
\operatorname{rank}M_{\rm joined}.
$$

## identical 例子

若右侧腿 \(3,4\) 是全同 massive spin-one 粒子，可以写

```wl
resIdentical = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3, 4},
  4,
  {{3, 4}},
  su3ShapeList -> {},
  ReturnProjectionData -> True,
  ReplaceQInFinalSymbolForm -> False
];
```

若只保留两条右侧腿都处于 longitudinal polarization 的 sector，可加入

```wl
RightPolarizationFilter -> <|3 -> 1, 4 -> 1|>
```

全同粒子必须具有兼容的自旋、质量、极化 scheduling 和 SU(3) shape。程序会先把混合极化的等价 sector 折叠为代表元；只有真正相同极化的 sector 才计算 Young projection matrix。

## SU(3) 例子

若需要附加 SU(3) 结构，给出每条外腿的 shape label。例如

```wl
resColor = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3},
  4,
  {},
  su3ShapeList -> {"", "", "q", "aq"},
  ReturnProjectionData -> True
];
```

开启颜色后，Lorentz 与 SU(3) 的关系是 direct product。程序不会把颜色结构当成普通 Lorentz 多项式因子相乘，而是用

$$
P_{\rm total}=P_{\rm Lorentz}\otimes P_{\rm color}
$$

计算投影和独立性。

## 模块组织

核心文件位于

```text
src/Package/Codes/Sewing.m
```

该文件实现左三点 current、右 residual records、全对称缝合、symbol/amp form 映射、CF comparison、relative chiral sorting、identical projection、SU(3) direct product 和主函数。

最重要的依赖文件如下。

| 文件 | 作用 |
| --- | --- |
| `src/Package/Codes/Amplitude.m` | 提供 `ConstructAmp`、`MassOption`、`ReduceSt` 等基础构造与约化 |
| `src/Package/Codes/CFblocks.m` | 提供 `ConstructIndepCFBlock`，作为 CF 完备性比较基准 |
| `src/Package/Codes/Operator.m` | 提供 `Amp2MetaInfo`，用于检查 spin 与 polarization sector |

文档位于 `docs/` 与 `notes/`。`docs/api.md` 给出 API 概览，`docs/physics-conventions.md` 给出约定，`docs/testing.md` 给出测试说明。当前方法的主要数学说明是 `notes/left_right_sewing_construction_note.md`。

测试位于 `tests/`。维护中的总入口是

```text
tests/run_all.wls
```

开发探针或一次性检查脚本不应随意加入 `run_all.wls`，除非它们已经成为稳定回归测试。

## 修改程序的建议顺序

修改程序时应先写或更新一个具体测试，再修改 `Sewing.m`，最后更新 usage message 和文档。对于与物理约定相关的修改，应同时检查 `docs/physics-conventions.md` 和主方法 note。

常见修改位置如下。

| 修改目标 | 主要位置 |
| --- | --- |
| 左三点 current 结构 | `ConstructLeft3PointOpenBasis` |
| 右侧 auxiliary residual | `ConstructRightProjectedJResidualRecords` |
| 全对称缝合方式 | `SewingContractionTerms` 与 `SymmetricSewContract` |
| symbol/amp form 分离 | `SewingSymbolToAmpForm` 与 `SewingReplaceQInSymbolForm` |
| relative chiral order | `SewingStaticXPower` 与 `SewingRelativeChiralOrder` |
| 主函数 sector 调度 | `ConstructProjectedSewingRelativeChiralBasis` |
| identical projection | `ProjectSewingAmplitudeRecords` |

低层 reduction、coefficient matrix、permutation matrix 和 tableaux 处理函数不是稳定公开接口。若必须修改，应先用 `ReturnProjectionData -> True` 保存能复现问题的最小输入，再比较修改前后的 CF rank、sewing rank 和 joined rank。

## 维护检查

修改后至少运行：

```powershell
wolframscript -file tests\section_5_2_bbuf_reproduce.wls
wolframscript -file tests\section_5_2_chiral_order_reproduce.wls
wolframscript -file tests\run_all.wls
```

文档修改后还应运行 Markdown 检查：

```powershell
markdownlint.cmd docs\program-user-guide.zh.md notes\left_right_sewing_construction_note.md
```

如果 `markdownlint.cmd` 不存在，应至少检查是否存在行首裸等号、行首 hyphen-space bullet、未闭合代码块、未定义的关键符号和陈旧物理叙述。

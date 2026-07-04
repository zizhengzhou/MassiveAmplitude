<!-- markdownlint-disable MD013 MD052 -->

# 重重粒子振幅的左右缝合构造

## 目标与适用范围

本文说明当前程序采用的左右缝合构造。目标是在含有一对等自旋重粒子的局域 on-shell 振幅中，按重粒子对的角动量通道组织 Lorentz 结构，并在约化后得到与既有 CF block 构造等价的独立完备基底。本文中的重粒子位于外腿 \(1,2\)，右侧物理粒子位于外腿 \(3,\ldots,n\)。所有粒子均取全入射约定。

本文的逻辑分为三层。第一层给出数学对象：重粒子对的 \(J_{12}\) 角动量分解、左侧三点 current、右侧 residual block 和全对称缝合。第二层说明程序如何在有限维 spinor 多项式空间中实现这些对象，并如何与 CF block 做秩比较。第三层给出公开接口和 \(\bar B B u f_+\) 例子的可重复计算。

本文只讨论当前程序已经实现的等自旋重粒子对。程序入口 `ConstructProjectedSewingRelativeChiralBasis` 令外腿 \(1,2\) 的自旋相同。若要推广到不等自旋重粒子对，需要重新定义左三点 open-current 结构和未匹配 heavy spin slot 的闭合因子。

## 标签、质量与极化约定

本文使用的外腿标签具有固定含义。腿 \(1,2\) 始终是等自旋重粒子对，腿 \(3,\ldots,n\) 是右侧物理粒子。程序主函数的位置参数 `rightMass` 只描述右侧哪些物理腿是 massive；腿 \(1,2\) 在内部总是手动加入 massive 集合。因此

```wl
ConstructProjectedSewingRelativeChiralBasis[
  leftSpin,
  rightSpins,
  {3},
  ampDim,
  identicalParam
]
```

表示腿 \(3\) 是右侧 massive 粒子，而不是说完整 massive 集合只有 \(\{3\}\)。实际传入底层构造的完整集合为 \(\{1,2,3\}\)。若省略位置参数 `rightMass`，主函数的默认含义是右侧物理腿 \(3,\ldots,n\) 全部 massive。这个约定与较低层 fixed-polarization 辅助函数的历史默认值不同，因此在主函数的讨论中必须始终以主函数语义为准。

massive square-spinor 的特殊标签只用于记录 massive 极化。对于 \(n\) 点振幅，massive 腿 \(i\) 的 square slot 在内部可能被替换为 \(2n+1-i\) 类型的 reflected label，例如四点时腿 \(1,2\) 的 massive square 标签为 \(8,7\)。这种标签只表示 massive little-group polarization slot，不能用于动量标签。特别地，formal `Q` 永远表示 \(Q=P_1-P_2\)，不可能变成 \(8,7,6,\ldots\) 这样的 massive square label。

polarization 约定也需要分开理解。massive spin-\(s\) 腿的极化标签为 \(0,1,\ldots,2s\)，它表示该 massive leg 中 square-type slot 的个数；例如 massive spin-one 的 polarization \(0,1,2\) 分别对应不同的 longitudinal/transverse representative。massless 粒子的 helicity 由输入的 spin 符号和粒子类型决定，程序中 massless leg 的 polarization slot 取唯一值 \(0\)。因此，右侧极化 sector \(\rho_R\) 只对 massive 右侧腿有真正的多值枚举，对 massless 右侧腿只是占位的 \(0\)。

CF block 的历史接口使用 code dimension。当前主函数的输入是文章中的振幅维数 \(d_{\rm amp}\)，并在枚举 CF sector 时把固定极化 block 写成

$$
\{d_{\rm amp}+n,\rho\},
$$

其中 \(\rho\) 是完整外腿极化列表。这一步不需要重新计算物理维数，也不应调用旧的维数推断函数。给定 `spins`、`ampDim` 和完整 massive 集合后，程序直接枚举所有允许的 \(\rho\)，再由 identical 规则和 `RightPolarizationFilter` 选择真正需要计算的 sector。

## 振幅空间与约化对象

固定外部数据

$$
\mathcal D=(s;\,s_3,\ldots,s_n;\,\mathcal M_R;\,\rho_R;\,d_{\rm amp}),
$$

其中 \(s\) 是腿 \(1,2\) 的共同自旋，\(\{s_3,\ldots,s_n\}\) 是右侧物理腿的自旋，\(\mathcal M_R\subset\{3,\ldots,n\}\) 是右侧 massive leg 集合，\(\rho_R\) 是右侧极化 sector，\(d_{\rm amp}\) 是文章使用的振幅维数。腿 \(1,2\) 总是 massive。程序内部把完整 massive 集合写成

$$
\mathcal M=\{1,2\}\cup\mathcal M_R .
$$

令 \(\mathscr P(\mathcal D)\) 为满足上述自旋、质量和极化条件的局域 spinor 多项式空间。它仍包含 Schouten identity、momentum conservation、EoM relation 和 massive-to-massless representative choice 产生的等价关系。约化后的振幅空间定义为

$$
\mathscr A(\mathcal D)
{}=
\mathscr P(\mathcal D)/\mathscr I_{\rm os},
$$

其中 \(\mathscr I_{\rm os}\) 是这些 on-shell 等价关系生成的子空间。程序通过 `ReduceSt` 和相关 massless representative 规则实现对 \(\mathscr I_{\rm os}\) 的商空间坐标化。给定一组候选振幅 \(\{A_i\}\)，约化后得到坐标向量

$$
\operatorname{red}(A_i)\in \mathbb C^{N_{\rm mon}},
$$

其中 \(N_{\rm mon}\) 是该 sector 中 reduction 后 monomial basis 的长度。把这些向量按行排列得到 coefficient matrix。独立性和完备性判断都只作用在这些约化坐标上。

既有 CF block 构造提供同一商空间中的参考基底。若 CF 候选给出矩阵 \(M_{\rm CF}\)，缝合候选给出矩阵 \(M_{\rm sew}\)，则同一 reduced space 的 span 等价性由

$$
\operatorname{rank}M_{\rm CF}
{}=
\operatorname{rank}M_{\rm sew}
{}=
\operatorname{rank}
\begin{pmatrix}
M_{\rm CF}\\
M_{\rm sew}
\end{pmatrix}
$$

判断。这个检查不是定义缝合方法本身，而是当前程序用来确认每个 sector 中 sewing construction 与 CF construction 等价的可执行标准。

固定右侧极化 \(\rho_R\) 与完整 CF 极化 \(\rho\) 的关系如下。缝合构造本身不需要预先固定腿 \(1,2\) 的 massive polarization，因为左侧三点 current 已经枚举了所有与重粒子对有关的 little-group slot 分配。相反，CF block 是完整 \(n\) 点振幅的 fixed-polarization 构造，它要求给出

$$
\rho=(\rho_1,\rho_2,\rho_3,\ldots,\rho_n).
$$

因此，对一个固定右侧 sector \(\rho_R=(\rho_3,\ldots,\rho_n)\)，程序比较 sewing span 与 CF span 时会取

$$
\rho_1,\rho_2=0,1,\ldots,2s,
\qquad
\rho_{3\ldots n}=\rho_R,
$$

并把这些完整 CF blocks 合并为同一个参考 reduced space。这个合并不是物理投影，而是为了把“左侧 current 已经包含的所有重腿极化分量”与“CF 构造必须逐个完整极化输入”的接口差异统一起来。

主函数 `ConstructProjectedSewingRelativeChiralBasis` 还要在固定右侧 sector 之外处理全同粒子和可选颜色结构。它先通过 `GenerateNeedCFBlocks` 枚举所有完整极化 sector，再通过 `FilterCFBlocksByIdentical` 折叠全同粒子的等价混合极化 sector，最后把剩余 blocks 按右侧极化 \(\rho_R\) 分组。每个分组共享同一组 sewing records；该分组内可能含有多个完整 \(\rho\)，它们共同定义后续 Lorentz projection 所需的 CF 参考空间。

## 动量分解与角动量通道

重粒子对的总动量与相对动量分别定义为

$$
p_+^\mu=P_1^\mu+P_2^\mu,\qquad
Q^\mu=p_-^\mu=P_1^\mu-P_2^\mu .
$$

在 heavy-baryon 展开中，\(p_+\) 是流入右侧轻自由度的软动量，而 \(Q\) 是重粒子对内部的硬相对动量。程序中的 formal `Q` 永远表示这个动量标签；它不是 massive square-spinor 的极化标签，也不会被替换成 \(2n,2n-1,\ldots,n+1\) 这样的 reflected massive label。

局域接触振幅被写成 \(12\) 通道角动量和 current spinor weight 的和，

$$
\mathcal A_{12\,3\cdots n}^{(d_{\rm amp})}
{}=
\sum_{J_{12},\omega}
\mathcal A_L^{(J_{12},\omega)}\odot_{J_{12},\omega}
\mathcal A_R^{(J_{12},\omega)}.
$$

这里 \(\mathcal A_L^{(J_{12},\omega)}\) 是重粒子对与辅助 current 的三点结构，\(\mathcal A_R^{(J_{12},\omega)}\) 是带 formal \(J\)-slot 的右侧 residual 结构，\(\odot_{J_{12},\omega}\) 表示把左右两边所有 formal \(J\)-slot 作 singlet contraction。辅助 current 只用于对角化 \(12\) 通道角动量；它不是物理传播粒子。权重 \(\omega\) 记录 current 的 anti-holomorphic minus holomorphic spinor weight。在程序中它不是单独输入，而是由 formal \(J\)-slot 计数实现：

$$
\omega=N_J^{\square}-N_J^{\angle}.
$$

因此，按 \(N_J^{\angle}\) 与 \(N_J^{\square}\) 分别过滤右侧 residual block 等价于同时固定 \((J_{12},\omega)\)。

重粒子对的 hard scaling 由左侧 current 决定。当前程序使用相对 chiral-order 标签

$$
d_{\rm rel}=d_{\rm amp}-J_{12}-n_x ,
$$

其中 \(d_{\rm amp}\) 是程序输入的振幅维数，\(n_x\) 是左侧显式 `Xhard` 因子的幂次。这个标签用于同一计算内部排序。完整物理 chiral dimension 还可能包含外场归一化和具体 operator convention 的整体平移。

## 左侧三点 current 结构

设两条重腿的共同自旋为 \(s\)，并记

$$
N=2s .
$$

左侧三点结构由腿 \(1,2\) 和 formal current \(J\) 构成。程序把 current 的 spinor label 也记作 \(J\)。对于给定 \(J_{12}=J\)，定义

$$
m=\min(J,N),\qquad r=N-m .
$$

当前等自旋构造采用如下基底：

$$
\mathcal V_{J;a,b,k}
{}=
\langle 1J\rangle^a[1J]^{m-a}
\langle 2J\rangle^b[2J]^{m-b}
X_{\rm hard}^{\,r-k}X_{\rm soft}^{\,k}
\bigl(\langle QJ\rangle[QJ]\bigr)^{\max(J-N,0)},
$$

其中

$$
a,b=0,\ldots,m,\qquad k=0,\ldots,r .
$$

这不是三角形截取，而是对腿 \(1\) 和腿 \(2\) 的 angle/square 分配分别取笛卡尔积。其含义如下。每条重腿有 \(N\) 个 little-group spinor slot。current 最多从每条重腿吸收 \(m\) 个 slot；剩余 \(r\) 个 heavy-pair slot 由两种闭合因子 `Xhard` 与 `Xsoft` 生成。若 \(J>N\)，额外角动量由唯一的 current-raising 因子 \(\langle QJ\rangle[QJ]\) 承担。因而 formal `Q` 只来自左侧三点 current，右侧 residual block 本身不应含有 formal `Q`。

这个公式也给出每个 \(J\) 通道的左侧候选数：

$$
N_L(s,J)=(m+1)^2(r+1).
$$

该数目不是最终物理基底数。它只统计左侧三点 current 的 independent tensor structures；右侧 residual block、缝合、on-shell reduction 和全同投影仍会改变候选记录数和最终 representative 数。

程序中左侧 current 同时保存 symbolic form 和 amp form。symbolic form 使用 `L1`、`L2`、`Q`、`Xhard`、`Xsoft` 保留物理来源；amp form 则把这些符号转成可约化的 spinor 表达式。对 \(n\) 点振幅，`L1` 与 `L2` 在 amp form 中分别对应腿 \(1,2\) 的 massive square 标签 \(2n\) 与 \(2n-1\)。闭合因子的内部替换为

$$
X_{\rm hard}\mapsto [L_1L_2]-\langle12\rangle,
\qquad
X_{\rm soft}\mapsto [L_1L_2]+\langle12\rangle .
$$

这里的替换只用于商空间约化和秩计算。最终输出可以重新显示为 `Xhard` 与 `Xsoft`，从而保留 hard/soft 左侧闭合因子的物理分类。formal `Q` 的替换也只在 amp form 中进行，默认

$$
Q\mapsto p_1-p_2 .
$$

由于 `Q` 总是动量标签，程序对 \(\langle QJ\rangle[QJ]\) 的替换按成对 angle-square 因子逐项进行。例如 `QReplacement -> {1,-2}` 将一个 formal pair 转成两项之差，而不是把 `Q` 当作某个 massive square-spinor label。

对于 spin-\(\frac12\) 重粒子对，\(N=1\)。闭合通道为

$$
J_{12}=0:\qquad
\mathcal A_L=\{X_{\rm hard},X_{\rm soft}\}.
$$

开 current 通道 \(J_{12}=1\) 为

$$
\mathcal A_L^{J_{12}=1}
{}=
\left\{
\langle 2J\rangle[1J],
\langle 1J\rangle[2J],
[2J][1J],
\langle 1J\rangle\langle 2J\rangle
\right\}.
$$

当 \(J_{12}=2\) 时，在上面四个结构后乘以 \(\langle QJ\rangle[QJ]\)；更高 \(J_{12}\) 重复乘以该 raising factor。

对于 spin-\(\frac32\) 重粒子对，\(N=3\)。\(J_{12}=0\) 有 \(X_{\rm hard},X_{\rm soft}\) 的三次齐次多项式；\(J_{12}=1\) 有二次齐次多项式并从每条重腿取一个 current slot；\(J_{12}=2\) 有一次 \(X_{\rm hard}\) 或 `Xsoft` 因子并从每条重腿取两个 current slot；\(J_{12}\ge3\) 不再有额外 \(X_{\rm hard},X_{\rm soft}\) 因子，所有 heavy spin slot 都接到 current 上，若 \(J_{12}>3\) 再乘以 \((\langle QJ\rangle[QJ])^{J_{12}-3}\)。

可以把 spin-\(\frac32\) 的低 \(J\) 结构写成下表。表中 \(a,b\) 的范围是每条重腿可接入 current 的 angle-slot 数。

| \(J_{12}\) | \(m\) | \(r\) | \(X_{\rm hard},X_{\rm soft}\) 次数 | current spinor 因子 |
| --- | ---: | ---: | --- | --- |
| \(0\) | \(0\) | \(3\) | \(X_{\rm hard}^{3-k}X_{\rm soft}^{k}\), \(k=0,1,2,3\) | 无 |
| \(1\) | \(1\) | \(2\) | \(X_{\rm hard}^{2-k}X_{\rm soft}^{k}\), \(k=0,1,2\) | \(\langle1J\rangle^a[1J]^{1-a}\langle2J\rangle^b[2J]^{1-b}\) |
| \(2\) | \(2\) | \(1\) | \(X_{\rm hard}^{1-k}X_{\rm soft}^{k}\), \(k=0,1\) | \(\langle1J\rangle^a[1J]^{2-a}\langle2J\rangle^b[2J]^{2-b}\) |
| \(J\ge3\) | \(3\) | \(0\) | 无 | \(\langle1J\rangle^a[1J]^{3-a}\langle2J\rangle^b[2J]^{3-b}(\langle QJ\rangle[QJ])^{J-3}\) |

这张表也是检查左侧构造是否正确的最直接方法。若 \(J=1\) 或 \(J=2\) 被错误地按三角形条件过滤，而不是对 \(a,b\) 取笛卡尔积，则会漏掉合法三点 current structure。

## 右侧 residual block

右侧 residual block 保存原始局域振幅中除重粒子对三点 current 以外的 Lorentz 数据。数学上，它可看作带 formal \(J\)-slot 的 SSYT 构造。其 bracket 内容必须与左侧 current 的 \(J\)-slot 数匹配。若左侧结构含有

$$
N_J^{\angle} \quad\hbox{个 angle }J\hbox{ slot},\qquad
N_J^{\square} \quad\hbox{个 square }J\hbox{ slot},
$$

则右侧 residual 只保留满足同一组 \(J\)-slot 计数的结构。

程序实现采用两个临时无质量辅助粒子来生成右侧 residual。辅助粒子不是物理外腿。其作用只是让已有 on-shell SSYT/CF 构造可以枚举包含 formal \(J\)-slot 的右侧结构。构造结束后，辅助标签被投影回 formal \(J\)，随后执行三类过滤：

1. 去除 auxiliary self-contraction 和投影后为零的项。
2. 检查投影后 angle \(J\)-slot 与 square \(J\)-slot 是否分别等于左侧目标。
3. 检查右侧物理粒子自旋、质量与极化 sector 是否与输入一致。

更明确地说，一条左侧 record 传给右侧构造的数据可以写成

$$
\left(J;\,N_J^{\angle},N_J^{\square};\,d_L;\,d_{\rm amp}\right).
$$

右侧生成器先在包含两个辅助无质量腿与 \(n-2\) 个右侧物理腿的普通 on-shell 振幅空间中枚举候选项。辅助腿的自旋不是外部物理输入，而是由 bracket 维数、目标 \(J\)-slot 数和等辅助自旋约束共同限制。随后把两个辅助腿的 spinor labels 投影为同一个 formal \(J\)-slot。只有投影后正好留下 \(N_J^{\angle}\) 个 angle \(J\)-slot 与 \(N_J^{\square}\) 个 square \(J\)-slot 的项才保留。这个过程实现的是“先在普通 on-shell 构造中枚举，再投影到 formal residual space”的计算策略。

从数学上看，右侧 residual 不是一个独立的物理散射振幅。它保留右侧局域 Lorentz 结构及其与 formal current 的耦合方式，但 formal current 并非传播粒子。因此右侧 residual 允许有 \(J\)-slot，却不允许有 heavy-pair closed factor，也不允许生成 \(Q=P_1-P_2\)。若在某个右侧 record 中看到 formal `Q`、`Xhard` 或 `Xsoft`，则说明来源混淆，必须回到左侧三点 current、右侧投影或缝合映射中检查错误。

右侧 residual 的振幅维数由 bracket 维数守恒决定。若完整 sewn amplitude 的维数为 \(d_{\rm amp}\)，左侧结构的总 bracket degree 为 \(d_L\)，其中 \(J\)-slot 的总数为 \(N_J=N_J^{\angle}+N_J^{\square}\)，则右侧 residual 使用

$$
d_R=d_{\rm amp}-d_L+N_J .
$$

这个公式反映了缝合时每一对 \(J\)-slot 被收缩成一个普通 spinor bracket：左右两侧各贡献一个 formal slot，但 sewn amplitude 中只留下一个物理 bracket 因子。

计算上可以把一条左侧 record 之后的右侧选择理解为下表。

| 输入对象 | 右侧使用方式 |
| --- | --- |
| \(N_J^{\angle}\) | 右 residual 投影后必须含有的 angle \(J\)-slot 数 |
| \(N_J^{\square}\) | 右 residual 投影后必须含有的 square \(J\)-slot 数 |
| \(d_L\) | 与 \(d_{\rm amp}\) 和 \(N_J\) 一起决定 \(d_R\) |
| \(\rho_R\) | 过滤右侧物理腿的 massive polarization sector |
| \(\mathcal M_R\) | 传给右侧 on-shell 生成器的右侧 massive 集合 |

不同左侧 record 可能给出相同的 \((d_R,N_J^{\angle},N_J^{\square},\rho_R)\)。程序会在同一次主函数调用中复用这类右侧 projected records；这只是计算优化，不改变数学定义。

辅助粒子的自旋不是额外物理输入，而是由右侧 on-shell 生成器的 bracket 维数和 formal \(J\)-slot 目标共同决定。程序实际枚举一组候选辅助自旋，默认要求两个辅助粒子等自旋，然后只保留投影后满足目标 \((N_J^{\angle},N_J^{\square})\) 的项。这个做法的数学意义是用普通 on-shell SSYT 构造实现 formal \(J\)-slot residual space。若一个 auxiliary record 在投影回 formal \(J\) 后含有不正确的 \(J\)-slot 数、仍含辅助标签、出现 self-contraction，或右侧物理极化不匹配，则它不属于目标 residual block。

右侧 residual 与左侧 current 的来源严格分离。左侧 current 可以含 `Q`、`Xhard`、`Xsoft`；右侧 residual 不产生这些 formal heavy-pair 因子。特别地，在 \(\bar B B u f_+\) 例子的 \(d_{\rm amp}=4\) 中，\(J_{12}=2\) 行的 `Q` 因子来自左侧 raising factor \(\langle QJ\rangle[QJ]\)，而不是来自右侧 \(A_R\)。

## 全对称缝合与表示分离

给定一个左侧 monomial 和一个右侧 monomial，缝合把左侧所有 \(J\)-slot 与右侧所有 \(J\)-slot 作全对称 singlet contraction。若有多种等价收缩方式，程序提供两种解释：

* `SewingContractionMode -> "Split"`：把全对称和中的每一项作为一个单独 record。当前默认值为 `"Split"`。
* `SewingContractionMode -> "Sum"`：把同一组全对称收缩直接求和，作为一个 record。

两种设置不会改变 span 完备性。`"Split"` 的优势是每一项在排序和独立性选择前保留更细的来源信息；后续 reduced coefficient matrix 会自动去除线性冗余。

若左侧 monomial 含有 \(N_J\) 个 formal \(J\)-slot，右侧 monomial 也含有 \(N_J\) 个 formal \(J\)-slot，则全对称缝合可写成

$$
\mu_J(L,R)
{}=
\sum_{\pi\in S_{N_J}}
\prod_{\alpha=1}^{N_J}
C\!\left(J_\alpha,J'_{\pi(\alpha)}\right)
\;L_{\rm rest}R_{\rm rest},
$$

其中 \(C\) 表示 angle 与 square slot 的 singlet contraction，\(L_{\rm rest}\) 与 \(R_{\rm rest}\) 是去掉 formal \(J\)-slot 后的其余因子。`"Sum"` 模式直接使用 \(\mu_J(L,R)\)。`"Split"` 模式则把每个 permutation term 分别记录为 \(\mu_{J,\pi}(L,R)\)。因为所有 split terms 都属于 \(\mu_J(L,R)\) 展开的线性空间，且后续 reduction 按矩阵秩选择 independent rows，所以 split/sum 的差别只影响代表元来源和排序，不改变最终 span。

一个简单例子可以说明 `"Split"` 的含义。设

$$
A_L=X_{\rm hard}[1J][2J],
\qquad
A_R=[3J][4J].
$$

全对称缝合的求和形式为

$$
A_{\rm sew}
{}=X_{\rm hard}\bigl([13][24]+[14][23]\bigr).
$$

在 `"Sum"` 模式中，这个和式作为一个 record 进入后续约化；在 `"Split"` 模式中，程序记录两条 symbolic records，

$$
X_{\rm hard}[13][24],
\qquad
X_{\rm hard}[14][23].
$$

这里被拆开的是全对称收缩产生的多项式项，而不是左侧 closed factor 本身。`Xhard`、`Xsoft` 和 formal `Q` 在 symbolic form 中始终作为整体来源标签保留；只有进入 amp form 约化时才按一一映射规则替换成真实 spinor 表达式。

程序同时维护两种表示。`SewingSymForm` 是展示用的 symbolic form，其中保留 `Q`、`Xhard`、`Xsoft`。`SewingAmpForm` 是内部约化用的 amp form，其中 `Q` 按 `QReplacement` 展开为真实动量标签，`Xhard` 与 `Xsoft` 也被替换为能参与 spinor-polynomial reduction 的表达式。独立性判断总是在 amp form 上进行。选出独立 record 后，最终输出再映射回 symbolic form。这个映射必须是一一对应的；否则会出现约化用结构和展示结构不一致的问题。

更具体地说，程序为每个 record 同时保存

| 字段 | 含义 |
| --- | --- |
| `SewingSymForm` | 最终展示用结构，保留 formal `Q`、`Xhard`、`Xsoft` |
| `SewingAmpForm` | 内部约化用结构，已把 formal 因子替换为可约化 spinor 表达式 |
| `ReducedAmp` | 对 `SewingAmpForm` 约化后的 monomial 坐标对象 |
| `SortData` | 包含 \(J\)、`Xhard` power、`Xsoft` power 的排序元数据 |

最终基底选择的逻辑是：先按 `SortData` 和 chiral-order key 对 record 排序，再对 `ReducedAmp` 构成的矩阵做 rank selection，最后把被选中的 record 映射回 `SewingSymForm`。因此，读者在输出中看到的 `Q`、`Xhard`、`Xsoft` 不是参与线性代数的抽象占位符，而是与内部 amp form 一一对应的展示标签。

默认设置

```wl
QReplacement -> {1, -2}
```

表示 \(Q=p_1-p_2\)。若希望最终结果中仍显示 formal `Q`，应使用

```wl
ReplaceQInFinalSymbolForm -> False
```

## 完备性、全同投影与颜色结构

对于固定右侧极化 sector，程序将 sewn records 做 massless-limit reduction，并与 `ConstructIndepCFBlock` 得到的 CF block 在同一个 reduced monomial basis 中比较。设三组矩阵分别为 \(M_{\rm sew}\)、\(M_{\rm CF}\) 和纵向拼接矩阵 \(M_{\rm joined}\)。完备性检查要求

$$
\operatorname{rank}M_{\rm sew}
{}=
\operatorname{rank}M_{\rm CF}
{}=
\operatorname{rank}M_{\rm joined}.
$$

这个等式说明 sewing construction 在该 sector 中生成的 span 与既有 CF block 完全相同。随后程序按固定优先级选择独立 record，并按 \(d_{\rm rel}\) 分组。

固定 sector 的计算次序可以概括为以下数学步骤。

1. 枚举左侧 \(\mathcal V_{J;a,b,k}\)，得到每条左侧 record 的 \(J\)-slot target。
2. 根据 \(d_R=d_{\rm amp}-d_L+N_J\) 枚举右侧 auxiliary on-shell records。
3. 把 auxiliary labels 投影回 formal \(J\)，并按 \((N_J^{\angle},N_J^{\square})\) 过滤。
4. 对每一对匹配的左、右 record 做全对称缝合。
5. 把 symbolic record 转换成 amp form 并做 on-shell reduction。
6. 与 CF block 在同一 reduced monomial basis 中比较 rank。
7. 在 verified span 中按优先级选取 independent representatives。

其中第六步采取保守失败准则：若 rank 等式不成立，主函数不会把该 sector 当作成功结果返回。这一点区分了“生成一些候选结构”和“得到经 CF 比较验证的独立完备基底”。

投影主函数还在固定 sector 计算外面包了一层物理调度。给定 `leftSpin`、`rightSpins`、`rightMass`、`ampDim` 和 `identicalParam` 后，它先形成

$$
\texttt{spins}=\{s,s,s_3,\ldots,s_n\},
\qquad
\mathcal M=\{1,2\}\cup\mathcal M_R .
$$

随后 `GenerateNeedCFBlocks` 枚举所有允许的完整 CF descriptors \(\{d_{\rm amp}+n,\rho\}\)。这些 descriptors 经过 `FilterCFBlocksByIdentical` 后分为两类。若某组全同粒子具有不同极化，则只保留一个代表 sector；若某组全同粒子具有完全相同极化，则该 sector 需要真正计算 Young projection。`RightPolarizationFilter` 在这个代表元列表上继续删去不允许的右侧极化。

经过这些选择后，程序按 \(\rho_R=\rho_{3\ldots n}\) 分组，而不是按完整 \(\rho\) 分组。这样做的原因是 sewing 生成只依赖右侧物理极化；腿 \(1,2\) 的极化已经在左侧 current 中枚举。对每个右侧分组，程序做三件事：

1. 对分组内所有完整 \(\rho\) 分别调用 `ConstructIndepCFBlock`。
2. 用 `SewingMergeCFBlocks` 把这些 CF blocks 合并成一个 reduced target span。
3. 对同一个 \(\rho_R\) 构造 sewing records，并投影到这个合并后的 CF span。

这也是为什么主函数能处理“右侧极化相同但腿 \(1,2\) 极化不同”的 CF 参考空间。若按完整 \(\rho\) 分组，会把同一个 sewing residual 重复计算，并可能在输出中产生重复 representative。

全同粒子只允许出现在右侧物理粒子中。程序沿用旧的 identical-sector 处理：不同极化的全同粒子先选代表元，真正相同极化的 sector 再计算右侧置换作用在 Lorentz basis 上的矩阵，并由 Young operator 投影。由于 sewing construction 的 \(J_{12}\) 分类来自左侧 current，而全同置换只作用在右侧物理腿上，预期 Lorentz permutation matrix 对 \(J_{12}\) 分块对角。相关测试检查了这一性质。

Lorentz 投影矩阵的构造使用 amp form，而不是 symbolic form。设经过 fixed-sector rank 检查和优先级排序后得到的独立 Lorentz records 为

$$
B_i=\sum_a c_{ia} e_a,
$$

其中 \(e_a\) 是共同 reduced monomial basis。对一个右侧置换 \(\sigma\)，程序先把 \(\sigma\) 作用在 selected records 的 amp form 上并再次约化，

$$
\sigma(B_i)=\sum_a c^{(\sigma)}_{ia}e_a .
$$

由两组坐标矩阵 \(c\) 与 \(c^{(\sigma)}\) 可解出置换在独立 Lorentz basis 上的表示矩阵 \(P_{\rm Lorentz}(\sigma)\)。Young operator 是这些置换矩阵的多项式。这个过程不依赖 symbolic `Q/Xhard/Xsoft` 展示形式，因此不会把展示标签误当作新的 Lorentz 多项式自由度。

若开启 `su3ShapeList`，程序调用旧的 SU(3) 结构生成函数得到 color basis 和 color permutation matrix。Lorentz 与 color 的关系是 direct product。投影使用

$$
P_{\rm total}=P_{\rm Lorentz}\otimes P_{\rm color},
$$

随后仍通过 coefficient matrix 的秩选择独立 representative，而不是把 Lorentz 多项式与 color 多项式普通相乘后再化简。

## 公开程序接口

普通使用者只需要调用

```wl
ConstructProjectedSewingRelativeChiralBasis[
  leftSpin,
  rightSpins,
  ampDim,
  identicalParam,
  opts
]
```

或显式指定右侧 massive label：

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

其中 `leftSpin` 是腿 \(1,2\) 的共同自旋，`rightSpins` 是腿 \(3,\ldots,n\) 的自旋列表，`rightMass` 只表示右侧哪些物理腿有质量，`ampDim` 是文章中的振幅维数，`identicalParam` 是右侧全同粒子分组。若省略 `rightMass`，主函数中 `Automatic` 表示右侧所有物理腿 \(3,\ldots,n\) 都有质量；腿 \(1,2\) 总是在内部视为有质量。

默认返回值是 association：

```wl
<|
  relativeOrder1 -> {basis1, basis2, ...},
  relativeOrder2 -> {...}
|>
```

其中 key 是 \(d_{\rm rel}\)。若设置 `ReturnProjectionData -> True`，返回 association 会包含 sector-level records、CF/sewing rank、identical Young operator、SU(3) 字典和 \(J\)-block 诊断数据。

最常用的选项如下表。

| 选项 | 默认值 | 含义 |
| --- | --- | --- |
| `RightMass` | `Automatic` | 右侧 massive label；主函数中 `Automatic` 表示右侧 \(3,\ldots,n\) 全部 massive |
| `su3ShapeList` | `{}` | SU(3) shape labels；空列表表示只计算 Lorentz 结构 |
| `RightPolarizationFilter` | `All` | 过滤右侧物理腿极化；key 必须是 \(3,\ldots,n\) 的粒子标签 |
| `QReplacement` | `{1,-2}` | 内部 amp form 中 \(Q\) 的替换，即 \(Q=p_1-p_2\) |
| `ReplaceQInFinalSymbolForm` | `True` | 是否在最终 symbolic 输出中也替换 formal `Q` |
| `ReturnProjectionData` | `False` | 是否返回 sector records、rank、投影矩阵和诊断数据 |
| `SewingContractionMode` | `"Split"` | 全对称缝合项是拆成多条 records 还是先求和 |
| `SewingDebug` | `False` | 是否打印默认关闭的调试日志 |

`RightPolarizationFilter` 的 association 形式为

```wl
RightPolarizationFilter -> <|3 -> 1, 5 -> {0, 2}|>
```

其中 key 是右侧物理腿标签，value 可以是一个整数、整数列表或 `All`。该过滤不作用于腿 \(1,2\)，因为主函数不会用腿 \(1,2\) 的极化决定 sewing 调度。若使用全同粒子，过滤作用在 identical representative selection 之后的物理 sector 列表上。

若需要检查中间步骤，`ReturnProjectionData -> True` 是推荐入口。典型字段包括 `"CandidateBlocks"`、`"PhysicalBlocks"`、`"RightPolarizationGroups"`、`"SectorResults"`、`"BasisByRelativeChiralOrder"` 和 `"PerformanceSummary"`。其中 `"SectorResults"` 内部保存每个右侧极化分组的 `CFRank`、`SewingRank`、`JoinedRank`、`RecordsBeforeIdentical`、`Records`、`LorentzYoungOperator` 和 \(J\)-block diagnostics。

## \(\bar B B u f_+\) 可重复例子

考虑四点 sector

$$
(\bar B,B,u,f_+)=(1,2,3,4).
$$

输入为

```wl
ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3},
  ampDim,
  {},
  su3ShapeList -> {},
  RightPolarizationFilter -> <|3 -> 1|>,
  ReturnProjectionData -> True,
  ReplaceQInFinalSymbolForm -> False
]
```

这里腿 \(3\) 是有质量 spin-one \(u_\mu\)，腿 \(4\) 是无质量正 helicity \(f_+\)。`RightPolarizationFilter -> <|3 -> 1|>` 把右侧 sector 固定到 \(u\) 的 longitudinal polarization；腿 \(4\) 的正 helicity 已由 massless spin-one 输入固定。若不加这个过滤，主函数会枚举所有右侧物理极化 sector，得到的 association 不是本文表格所展示的单一 sector。

固定 `ampDim` 的主函数返回的是该维数内部的 relative-order 分组。对本文 sector，当前程序给出的结构计数为

| `ampDim` | relative-order 计数 | 物理来源 |
| ---: | --- | --- |
| \(3\) | order \(2\) 有 \(2\) 个结构 | 两个 \(J_{12}=1\) open-current rows |
| \(4\) | order \(2\) 有 \(1\) 个结构，order \(3\) 有 \(2\) 个结构 | 一个 raised \(J_{12}=2\) row 与两个 \(J_{12}=1\) rows |

文章中的 leading/NLO 表格不是把每个固定 `ampDim` 完全独立地读出后直接并列，而是把 \(d_{\rm amp}=3,4,\ldots\) 的候选项放入同一个优先级排序中，再按 relative chiral order 选择独立方向。因此，\(d_{\rm amp}=3\) 的两个 \(J_{12}=1\) rows 与 \(d_{\rm amp}=4\) 的 raised \(J_{12}=2\) row 同属 leading relative order；\(d_{\rm amp}=4\) 的两个 \(J_{12}=1\) residual rows 属于下一阶。

若要从程序返回值中机械抽取表格里的 \(A_L,A_R,A_{\rm sew}\)，可使用 `ReturnProjectionData -> True` 后的 `"Records"` 字段。例如对 \(d_{\rm amp}=4\)，运行

```wl
res4 = ConstructProjectedSewingRelativeChiralBasis[
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

records4 = res4["SectorResults"][[1, "Records"]];

({#["J"], #["AmpLSymbolForm"], #["AmpR"], #["SewingSymForm"],
   SewingRelativeChiralOrder[#]} &) /@ records4
```

输出的五列依次为 \(J_{12}\)、\(A_L\)、\(A_R\)、\(A_{\rm sew}\) 和 \(d_{\rm rel}\)。同样的代码把 `4` 改成 `3` 即可抽取 \(d_{\rm amp}=3\) 的两行。为了阅读方便，表格中把 `L1,L2` 写回腿 \(1,2\) 的 massive square slot，把 `ab`、`sb` 分别写成角括号与方括号。

若只需要验证固定右侧极化 \(\{1,0\}\) 的 sewn span 与 CF block 等价，可使用较低层 fixed-polarization 比较函数：

```wl
CompareGeneralSewingToCFBlocks[
  1/2, {1, 1}, {3}, ampDim, {1, 0},
  JMax -> 3,
  QReplacement -> 2
]
```

这个函数只用于 rank/span verification。它的内部独立 representative 选择可以与本文表格中的 manuscript-facing representative 不同，但三者张成同一个 reduced amplitude space。本文下面的 \(A_L,A_R,A_{\rm sew}\) 表格采用与 `ConstructProjectedSewingRelativeChiralBasis` 加右侧极化过滤后相容的展示基底。特别地，\(d_{\rm amp}=4\) 的 projected 主函数计数为 order \(2\) 有一个结构、order \(3\) 有两个结构；低层 fixed-sector verification 的代表元不应直接替代表格代表元。

在 \(d_{\rm amp}=3\) 时，只有 \(J_{12}=1\) 的两个 open-current 结构进入：

| index | \(J_{12}\) | \(A_L\) | \(A_R\) | \(A_{\rm sew}\) |
| --- | --- | --- | --- | --- |
| \(L^{(3)}_1\) | \(1\) | \(\langle2J\rangle[1J]\) | \(\langle3J\rangle[34][4J]\) | \(\langle23\rangle[34][14]\) |
| \(L^{(3)}_2\) | \(1\) | \(\langle1J\rangle[2J]\) | \(\langle3J\rangle[34][4J]\) | \(\langle13\rangle[34][24]\) |

在 \(d_{\rm amp}=4\) 时，当前正确结果不是旧的 \(J_{12}=0\) 的 `Xhard/Xsoft` 行，而是两个 \(J_{12}=1\) residual block 与一个 raised \(J_{12}=2\) block：

| index | \(J_{12}\) | \(A_L\) | \(A_R\) | \(A_{\rm sew}\) |
| --- | --- | --- | --- | --- |
| \(L^{(4)}_1\) | \(1\) | \([2J][1J]\) | \(\langle34\rangle[34][4J][4J]\) | \(\langle34\rangle[14][24][34]\) |
| \(L^{(4)}_2\) | \(1\) | \(\langle1J\rangle\langle2J\rangle\) | \(\langle3J\rangle\langle3J\rangle[34]^2\) | \(\langle13\rangle\langle23\rangle[34]^2\) |
| \(L^{(4)}_3\) | \(2\) | \([2J][1J]\langle QJ\rangle[QJ]\) | \(\langle3J\rangle[4J][4J][3J]\) | \(\langle3Q\rangle[14][24][3Q]\) |

这些结构的 relative order 为

$$
d_{\rm rel}=d_{\rm amp}-J_{12}-n_x .
$$

对于显示的 \(d_{\rm amp}=4\) 三行，\(n_x=0\)。因此 \(L^{(3)}_1\)、\(L^{(3)}_2\) 与 \(L^{(4)}_3\) 同属 leading relative order；\(L^{(4)}_1\) 和 \(L^{(4)}_2\) 属于下一阶。文章中的 operator correspondence 采用 \(Q=P_1-P_2\) 对应 \(\bar B\) 与 \(B\) 之间的左右导数，并把 Lorentz 指标与 \(u_\mu\) 和 \(F_{\nu\rho}\) 作相应收缩。

固定维数的 CF comparison 给出

$$
\operatorname{rank}M_{\rm CF}
{}=
\operatorname{rank}M_{\rm sew}
{}=
\operatorname{rank}M_{\rm joined},
$$

并且在 \(d_{\rm amp}=3,4,5,6\) 的 rank 分别为 \(2,3,4,5\)。\(d_{\rm amp}=5,6\) 的计算只作为一致性检查；它们不改变上述 leading 与 next-to-leading 的分类。

## 结论与局限

当前方法已经建立了等自旋重粒子对局域振幅的可执行 factorized construction。左侧三点 current 负责全部 heavy-pair hard scaling，右侧 residual block 保存原 full contact amplitude 的局域数据；对当前返回的 sector，全对称缝合后的 span 经由 CF block 的 reduced-rank comparison 验证为等价。程序最终输出以 symbolic form 展示，使 `Q`、`Xhard` 和 `Xsoft` 的物理含义可读，而内部约化始终使用真实 amp form。

尚未在本文中证明的部分是更一般的数学定理：即辅助无质量粒子实现的右侧 residual 构造在所有可能 sector 中都与直接 formal \(J\)-slot SSYT 后端完全等价。当前程序以 CF rank comparison 作为每个 sector 的可执行验证。若将来推广到不等自旋重粒子对、非当前 SU(3) 形状约定或更复杂的 gauge structure，需要同步更新左侧三点结构、右侧 residual 过滤条件和投影矩阵验证。

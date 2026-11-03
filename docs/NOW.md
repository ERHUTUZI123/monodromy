# 现在

**两座山峰的阶段性总定理已经完成严格 Lean 核验：任意有限图灵机的原生延拓模拟，以及本项目有限覆盖演算的精确计算结构刻画。** 四根模型的定义、证明、执行器与论文继续冻结。固定解释器、存储程序机器和其他新功能保持封存。

## 最终结构定理

[Structure.lean](../src/Monodromy/Structure.lean) 的主定理为：

```lean
continuation_characterization (function : ℕ → Part ℕ) :
  Realizable function ↔ Partrec function
```

`Realizable` 以有限三维程序、固定三次观察和完整原生 `evalReal` 的结果图定义。输入、输出在程序选择之前固定，并已证明原始递归；待计算函数只决定有限程序。完整结果、停机和发散同时保真。

`analytic_continuation_realization` 给出全局实解析后继及任意有限运行的真实覆盖输运。计算域是精确整数格点，运行采用内部停止信号控制的离散返回语义。

完整的数学解释、定理范围与证据链见 [延拓计算的结构刻画](structure.md)。

## 为什么能够产生通用计算

对数覆盖保存无界分支；三次覆盖读出当前数字；正则根核将读位变成内部操作选择；下降显露更深记忆；仿射写入与有限控制将这些操作组织成两栈执行。所有选择与停止信号来自当前状态及程序自身的规则。

路径先由内部解析后继确定端点，再投影到基空间。实际提升定理核验它的连续延拓实现。一个固定三次观察覆盖与三个对数记忆分支已经足够；这是充分构造。

## 已证明的结构边界

- `closed_observation_barrier`：任何系统若具有有限、演化闭合的停止观察，且初始观察可计算，其停机域可计算。完整状态空间可以无限。
- `descent_strictly_extends`：删除下降后的整个 `Forward` 子语言严格弱于完整语言。其停止控制封闭于语法给出的有限余数商；整数载荷仍可无界。
- [Resolution](../src/Monodromy/Resolution.lean)：整数 B>0、m≥2 时，下降 r 层后输入模 N 保持输出模 m，恰当且仅当 B^r·m 整除 N。B≥2 时，没有非零固定模数能保持全部深度的这些观察。该精确结论针对整个整数域。
- `descent_can_be_inactive`：某个程序含有下降表达式，也可以只有恒等执行。原语的可用性与某段程序的能力分别判断。
- [Tower.loop_transport_commute](../src/Monodromy/Tower.lean)：幂覆盖在基点 1 的固定闭路输运彼此交换。内部反馈仍能产生不交换的返回操作；当前通用构造使用的数学结构已足够简单。

## 证明链与数学位置

| 环节 | 正式证据 |
| --- | --- |
| 每个有限源图灵机的完整模拟 | [Universality](../src/Monodromy/Universality.lean)：初态、逐轮执行、整张纸带、停机、发散、真实输运 |
| 有限原语的递归有效性及整个执行上界 | [IntegerPrimrec](../src/Monodromy/IntegerPrimrec.lean)、[Effectiveness](../src/Monodromy/Effectiveness.lean) |
| 部分递归程序到有限图灵表的下界 | [FormalCompilation](../src/Monodromy/FormalCompilation.lean)、[FiniteSupport](../src/Monodromy/FiniteSupport.lean) |
| 固定三次覆盖上的原生实现 | [CoverCompiler](../src/Monodromy/CoverCompiler.lean)、[NativeLowerBound](../src/Monodromy/NativeLowerBound.lean) |
| 固定有效输入与完整数值读出 | [CanonicalIO](../src/Monodromy/CanonicalIO.lean)、[BlockCoding](../src/Monodromy/BlockCoding.lean)、[NativeIO](../src/Monodromy/NativeIO.lean) |
| 总等价、严格分离与一般观察障碍 | [Structure](../src/Monodromy/Structure.lean)、[ForwardBoundary](../src/Monodromy/ForwardBoundary.lean) |

进制记忆、周期解析选择与解析图灵机模拟已有先例，见 [Koiran–Moore 作者稿](https://perso.ens-lyon.fr/pascal.koiran/Publis/DIMACS.96-25.ps)；使用的计算理论形式化见 [Carneiro（2019）](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.12)。当前完成的是固定有效接口下有限覆盖演算的精确刻画、下降删除的严格能力分离，以及与真实提升相连的 Lean 证明链。

该定理刻画本项目的可接受有限语法及规范格点表示。最小维数、统一有效编译器、连续自治调度、数值稳定性和资源优势各需独立结论；学习与 PGP 仍保留为历史研究中的开放问题。

## 核验

```sh
lake build
lake env lean -DautoImplicit=false -DwarningAsError=true src/Audit.lean
```

全项目构建通过；1979 个 Monodromy 声明及其传递公理依赖审计通过，仅使用标准 Lean 公理。独立子代理复核了主等价、完整数值读出、停机／发散、有效性、实际提升及结构边界。

[四根论文](monodromy.pdf) · [源稿](monodromy.tex) · [研究来路](history.md)

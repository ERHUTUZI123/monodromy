# 延拓计算的结构刻画

基础问题是：怎样使分支的延拓成为一个能够自行读写、选择并继续运行的计算模型？本项目现在给出一个明确的有限演算，并证明它的计算能力恰为部分递归函数。证明同时解释了无界记忆从何而来、条件如何内生，以及有限观察在什么条件下成为计算边界。

## 分支、观察与下降

指数覆盖的一个纤维包含所有整数分支。以整数 x 表示角度 2πx，三个保留分支组成计算状态。三次覆盖提供有限观察：

\[
 r(x)=e^{2\pi i x/3},\qquad r(x)^3=e^{2\pi i x}.
\]

整数状态上的 r(x) 只区分三个余数。要把观察变成内部选择，令 ζ_d=e^{2πid/3}，并在可去奇点处连续延拓

\[
 K_d(z)=\frac{z^3-1}{3\zeta_d^2(z-\zeta_d)},\qquad
 W_d(x)=\operatorname{Re}K_d(r(x)),\quad d=0,1,2.
\]

正则根核满足 K_d(ζ_j)=δ_dj。因此 W_d(k) 在每个整数 k 上精确指示其余数，而整个公式仍为实解析函数。有限操作表通过加权和选择当前操作。读出一个数字后，定义

\[
 D(x)=\frac{x-\sum_{d=0}^{2}d\,W_d(x)}{3}.
\]

它在整数格点上恰为欧几里得商 k÷3，包括负整数。于是同一个覆盖既能观察当前数字，也能通过下降暴露下一层数字。这些结论分别由 [Choice](../src/Monodromy/Choice.lean)、[Radix](../src/Monodromy/Radix.lean) 和 [CoverExpressions](../src/Monodromy/CoverExpressions.lean) 验证。

非零数字编码有限词：E([])=0，E(b::w)=b+1+3E(w)，其中 b∈{0,1}。零余数识别空词；其余两位识别字母。压栈是仿射写入，弹栈是下降。任意有限字母表再用固定长度的二元块表示。两个词分支保存纸带，一个坐标保存有限控制与当前符号，便得到三维原生返回系统。

## 有限语言与固定接口

程序由有限表达式和停止守卫构成。表达式使用整数常数、坐标、加法、整数倍、三次根观察和下降；守卫由同一有限观察组成。选择、写入、下一状态与停止信号全部由这些规则根据当前状态产生。程序文本在运行中保持固定。

[NativeIO](../src/Monodromy/NativeIO.lean) 在选择程序之前固定输入和输出格式。输入把自然数的规范二进制纸带编码为初始控制、空左栈和右词分支；输出解码右词分支并读取数值位。两个映射均已证明原始递归，且完全独立于待计算函数和控制表大小。

持久执行域是精确整数格点。每个有限程序还定义整个实状态空间上的联合实解析后继；`evalReal_init` 将格点上的原生部分执行与整数解释精确对应。

## 主定理

记 Realizable(f) 表示：存在一个三维有限程序，全部有限观察与下降均使用三次覆盖；对于每个自然数输入，其完整原生执行经上述固定读出，恰好给出部分函数 f 的结果。

**结构刻画定理。** 对任意部分函数 f:ℕ→Part ℕ，

\[
 \operatorname{Realizable}(f)\quad\Longleftrightarrow\quad\operatorname{Partrec}(f).
\]

正式入口是 [Structure.continuation_characterization](../src/Monodromy/Structure.lean)。`Computes` 直接以完整原生 `evalReal` 的结果图定义，`computes_iff` 将它等价为完整的部分函数相等。停机、数值结果和发散因此同时保真。

上界从原语出发。[IntegerPrimrec](../src/Monodromy/IntegerPrimrec.lean) 证明整数算术和正进制商余运算的原始递归性；[Effectiveness](../src/Monodromy/Effectiveness.lean) 按有限语法归纳，再证明整个反馈迭代为部分递归。有限函数分支的每一支都在证明中处理。

下界复用 Mathlib 的经典计算理论，将部分递归程序依次译为栈机、纸带机和有限控制的 Post–Turing 表。[FormalCompilation](../src/Monodromy/FormalCompilation.lean) 保留完整终态与定义域；[NativeLowerBound](../src/Monodromy/NativeLowerBound.lean) 接入三次覆盖程序；固定读出恢复最终数值。源程序只决定有限控制表，输入格式始终相同。计算理论形式化的基础见 [Carneiro（2019）](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.12)。

`analytic_continuation_realization` 进一步给出全局实解析后继与每段有限运行的真实覆盖输运。当前路径先由内部解析规则确定后继，再连接端点并投影到基空间；实际提升定理证明这套返回计算的几何实现。

## 决定能力的结构边界

**有限闭合观察构成一般障碍。** 设 q:S→F，F 有限，且 q(Ts)=T̄(q(s))，停止信号也只依赖 q(s)。若初始观察可计算，整个系统的停机域可计算。`closed_observation_barrier` 对任意这样的状态空间成立；完整状态本身可以无限。

在本语言中，删除下降得到 `Forward` 子语言。每个程序的语法算出一个正模数 M，使观察模 M 在整个执行中闭合。n 个坐标的停止搜索只需前 M^n 次状态访问。其停机谓词已证明原始递归；`descent_strictly_extends` 用不可判定停机域证明整个子语言严格弱于完整语言。

**下降改变观察所需的层级。** 对整数 B>0、m≥2，下降 r 层后，输入模 N 保持输出模 m，当且仅当 B^r·m 整除 N。当 B≥2，没有非零固定模数能保持全部深度的这些观察。[Resolution](../src/Monodromy/Resolution.lean) 给出精确证明；它针对整个整数域。一般表达式和有限运行的充分观察需求由 `demand` 与 `runDemand` 向后复合。

这解释了计算组织的关键：保留无界分支，以有限观察选择操作，再使未来观察接触更深记忆。完整语言具备通用能力；单个程序的行为仍由自己的控制规则决定，`descent_can_be_inactive` 给出明确反例边界。

**非交换单值群并非本构造所需。** [Tower.loop_transport_commute](../src/Monodromy/Tower.lean) 证明幂覆盖的固定闭路输运彼此交换。内部反馈则可以产生不交换的返回操作。分支保存、可扩展观察和状态依赖控制承担了这里的通用计算组织作用。覆盖对称与单值作用的经典背景见 [Hatcher，§1.3](https://pi.math.cornell.edu/~hatcher/AT/ATch1.pdf)。

这些结构还具有可转移的形式。[SelfEmbedding](../src/Monodromy/SelfEmbedding.lean) 从群自嵌入与分离陪集导出代数词记忆及扭曲拼接律；[Choice](../src/Monodromy/Choice.lean) 的根核沿复合映射分层，其差商背景见 [Floater–Lyche（2007），式 (6)](https://www.researchgate.net/publication/220577596_Two_chain_rules_for_divided_differences_and_Faa_di_Bruno%27s_formula)。[Feedback](../src/Monodromy/Feedback.lean) 证明相容的覆盖同构和路径同伦保持完整执行。代数递归的标准背景见 [Nekrashevych，§3.5–3.8](https://people.tamu.edu/~nekrash/teaching/06F/lectures689/ssimilar.pdf)。有效读出与实际覆盖条件在各个具体实现中分别验证。

## 数学位置与核验

进制纸带、周期解析读位和解析图灵机模拟已有经典先例，参见 [Koiran–Moore，DIMACS 96-25 作者稿](https://perso.ens-lyon.fr/pascal.koiran/Publis/DIMACS.96-25.ps)。这里完成的是固定有效接口下有限覆盖演算的精确计算刻画、下降删除的严格能力分离，以及连接真实提升的完整 Lean 证明链。

定理的范围是有限整数系数语法、固定规范数值接口、合法整数格点与离散返回语义。三个坐标和三次观察给出充分构造；全局解析性描述其连续扩展。维数最小性、统一有效编译器、数值稳定性及物理资源界各自需要额外定理。

Lean 4.35.0 与锁定的 Mathlib 版本共同检查上述定义和证明。复核命令：

```sh
lake build
lake env lean -DautoImplicit=false -DwarningAsError=true src/Audit.lean
```

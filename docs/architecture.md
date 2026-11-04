# Monodromy — 原生延拓

**保留根是状态，基路径是程序，实际提升产生下一状态。**

当前核心 [Continuation.lean](../src/Monodromy/Continuation.lean) 使用三个持久复坐标：两个下层记忆根与一个上层控制根。所有操作共享同一覆盖关系。

## 同一个几何对象

令 \(Y=\mathbb C\setminus\{0,1\}\)，\(D=\exp^{-1}(Y)\)。两层匹配的覆盖为
\[
(D\times D)\times\mathbb C
\xrightarrow{p}(D\times D)\times\mathbb C^*
\xrightarrow{q}(Y\times Y)\times\mathbb C^*,
\]
其中
\[
p(w_1,w_2,z)=\left(w_1,w_2,\frac{e^z}{w_1w_2}\right),\qquad
q(w_1,w_2,v)=(e^{w_1},e^{w_2},v).
\]

上层是指数覆盖的连续拉回，下层是两个限制指数覆盖与恒等覆盖的乘积。`CoupledPullback.upperCovering`、`lowerCovering` 分别验证它们。拉回关系中的 \(v\) 由三个根唯一决定；同胚 `chart` 将它消去。

复合投影为
\[
F(w_1,w_2,z)=\left(e^{w_1},e^{w_2},\frac{e^z}{w_1w_2}\right).
\]
状态是基点 \((e,e,1)\) 上的整个纤维。每个状态恰有唯一表示
\[
w_j=1+2\pi i k_j,\qquad z=\log w_1+\log w_2+2\pi i m,
\quad(k_1,k_2,m)\in\mathbb Z^3.
\]
`prepare_surjective` 与 `prepare_injective` 证明这一完整性。整数标签用于初始化与描述结果；执行直接接收保留的三个复根。

## 路径怎样执行

`Driver` 给出基回路 \((u_1,u_2,v)\)。运行先实际提升 \(u_1,u_2\)，得到 \(w_1(t),w_2(t)\)，再生成上层输入
\[
\eta(t)=v(t)w_1(t)w_2(t).
\]
第二次实际指数提升产生 \(z(t)\)，`execute` 保留三个实际终根。

`intermediateCurve_actual_lift` 与 `restrictedTrajectory_actual_lift` 将完整运行曲线分别识别为匹配下层、上层覆盖的 Mathlib `liftPath`。起点、每个时刻的投影关系与实际终点均有定理。显式轨迹只用于提升唯一性的证明。

程序在运行中仅持有有限路径词表与停止位表。源机器只用于静态生成这张表；
每次返回的判断、路径选择和执行都由保留根与实际提升完成。计数器源语义和
普通解析比较位于后续证明模块，执行核心直接依赖覆盖、对数和有限根数学。

## 五个固定回路

在一个下层坐标使用
\[
A(t)=\exp(1+2\pi it),\qquad B(t)=\exp(e^{2\pi it}),
\]
其他基坐标保持不动，得到 \(A_1,A_2,B_1,B_2\)。第三个基坐标绕单位圆一次，得到 \(C\)。实际执行满足
\[
\begin{aligned}
A_1 &: (k_1,k_2,m)\mapsto(k_1+1,k_2,m),\\
A_2 &: (k_1,k_2,m)\mapsto(k_1,k_2+1,m),\\
B_j &: (k_1,k_2,m)\mapsto(k_1,k_2,m+\mathbf1_{k_j=0}),\\
C &: (k_1,k_2,m)\mapsto(k_1,k_2,m+1).
\end{aligned}
\]

条件写入来自下层实际提升的绕行：\(B\) 提升为以 \(2\pi i k_j\) 为中心的单位圆，仅零分支绕过上层对数的删去点 0。对应定理为 `execute_A_left/right`、`execute_B_left/right`、`execute_control_prepare`。

一个手算实例为
\[
(-1,1,0)\xrightarrow{A_1}(0,1,0)\xrightarrow{B_1}(0,1,1)
\xrightarrow{B_2}(0,1,1)\xrightarrow{A_2^{-1}}(0,0,1)
\xrightarrow{B_2}(0,0,2).
\]
`example_run` 与 `example_reverse` 验证整个路径词及其逆。一般串接与双向恢复由 `execute_driver_trans`、`execute_driver_reverse`、`execute_after_driver_reverse` 从提升唯一性导出。

`execute_homotopic` 证明完整状态只依赖允许基空间内的端点固定同伦类。两层实际提升将这一不变性传递到全部保留根。

## 根怎样选择下一条路径

固定正整数 \(N\)，读取
\[
\rho_N(w_1,w_2,z)=\exp\!\left(\frac{z-\log w_1-\log w_2}{N}\right).
\]
整个返回纤维上都有 \(\rho_N^N=1\)。有限幂覆盖的归一化核在这些根上恰为零或一，因此固定有限路径表产生整条基路径
\[
\gamma_s(t)=\sum_{j<N}K_j(\rho_N(s))\,\gamma_j(t),
\]
逐坐标取和。`routeDriver_eq` 证明它全程等于其中一条合法路径；`executeRouted` 随后调用同一个实际提升执行器。`executeRouted_prepare` 给出控制标签 \(Nq+j\) 的精确路由。

这里 \(m\) 仍是无界整数，有限的是控制观察。下层返回根的实部均为一，`analyticAt_control_observation` 证明读出在每个返回态附近具有复解析延伸。执行采用精确根与离散返回语义；纤维外混合路径的安全性、数值误差和单一自治流属于后续问题。

## 可逆反馈

原生条件写入、内部有限根路由与固定路径组合已经闭合。表项保持控制根时，`routedEquiv` 给出整表的双向逆；随后组合任意固定条件门，`feedbackEquiv` 仍为整个几何纤维上的双射。其逆先反向执行条件门，再由恢复的控制根选择反向表项。

两项表 \(A_1,A_2\) 接条件门 \(B_1\)，产生
\[
(-1,0,0)\longmapsto(0,0,1)\longmapsto(0,1,2).
\]
第一次写入改变控制根，第二次因此选择另一侧记忆操作。`shiftFeedback_two_steps` 验证这段完整内部反馈，全部信息保留于原有三个根。一般路径表的可逆性仍取决于相应控制条件。

## 可逆路由的一般判据

上层平移 z↦z+2πin 是同一纤维上的 deck 作用，并恰由已有控制路径词 C^n
执行。实际提升唯一性给出
\[
T_\gamma D_n=D_nT_\gamma.
\]
`execute_controlDeck` 证明该等式，`controlDeck_eq_control_word` 连接实际执行。

设一个路径表使每个控制根单元 j 始终进入指定单元 σ(j)，且这一根观察闭合。
deck 对易性把单向包含加强为单元的精确对应。`routed_bijective_iff` 证明：
路由后的整体执行为双射，当且仅当 σ 为有限置换。逆表使用 σ⁻¹ 重编号，并
反向执行原路径。旧的保根路由现在是这个结论的恒等置换特例。

条件绕行还能执行任意给定的有限控制置换 π。例如程序表在根 j 处放入
\[
W_j=B_1^{\,\pi(j)-j}.
\]
左记忆为零时，它将 m=Nq+j 变为 Nq+π(j)；否则保持原状态。逆表由 π⁻¹
静态生成，运行仍由实际返回根选择。`ReversibleControl.inverse`、`compose`
证明完整纤维上的双侧逆与组合。`guardWord` 同时处理无条件、左右记忆零／非零
五类条件；非零条件用 C^d B_j^(-d)，零时两段恰好抵消。`guardWord_length`
给出已有原语的实际次数。`ReversibleMemory` 则按不变的控制根选择双记忆平移，
其逆将静态位移取负。

## 可逆计数器与阶段组合

有限阶段按 m↦km+t 编码在同一上层根中。阶段词将 B、C 的次数乘以 k，
保留 A 的次数，再执行固定的阶段时钟词。`StagedProgram.advance_embed`
证明它恰执行当前阶段并推进时钟；`executionEquiv` 给出实际反向词表。
相位边界由真实根观察 ρ_k=1 定义，`cycle_firstReturn` 排除中间返回。

`Counter.Reversible` 的源边表使用整数移位和零／非零测试。同一来源或目标
的不同边只能是同一记忆上的互补测试。将有限地址分为源顶点与边端口，每类
条件产生顶点—端口匹配置换。五次出路由、一次端口记忆更新、五次逆序入路由，
组成同一原生程序的十一阶段周期。没有新增持久坐标或基本操作。

`ReversibleCompilation.cycle_step` 证明该周期的单步交换等式；正反路径表
在整个纤维上互逆。若每个有出边的源地址总有启用边（`Complete`），有限
停机位准确识别源停机，`eval_iota` 保留完整部分执行与发散。
`step_firstReturn` 和 `result_actual_lifts` 分别给出精确周期及真实路径证书。
`eval_iota_on` 将相同结论限制到一个保持的合法不变量；入口条件与非负性
属于对应证明，执行表保持相同。
当前还需构造任意图灵机的可逆源编码，并证明其自然数域与历史编码的不变量。

`Counter.Reversible.Multiply` 给出一个已接通的算术实例：固定 p>0，有限图
用一段循环把第一项转成第二项的 p 倍，再用另一段循环移回。
`native_eval` 证明同一几何程序对任意自然数 n 将 (n,0) 变成 (pn,0)。
合法不变量保证减法安全及测试入口条件；十二条源边仍只编译为原来的路径词。
反转源图交换边端点并取负位移，`reverse_native_eval` 在倍数输入上还原原数。
下一步将余数保留在有限控制中，建立适用于所有自然输入的商余操作。

## 有限程序与计算能力

`Word` 是五回路的有限有符号词，`Program` 是有限词表与有限停止根表。运行通过当前控制根选择整条基路径，并在标记的根上停止。整数位移 \(d\) 展开为 \(|d|\) 次控制绕行；`Word.inverse` 给出等长逆程序。

[Counter.lean](../src/Monodromy/Counter.lean) 中的 `CounterContinuation.compile` 将任意有限双计数器程序编译为这些路径词。源地址 \(q\) 与两个中间阶段使用同一控制分支中的 \(3q,3q+1,3q+2\)。每个活动源步骤恰经过两次原生返回，各返回包含预先固定的有限词；中间阶段继续执行。

`encode_injective`、`step_bind_step_encode` 与 `eval_encode` 分别证明完整配置的单射表示、单步交换等式，以及
\[
\operatorname{eval}_{P}(\iota c)=\iota_*\operatorname{eval}_{M}(c).
\]
这是完整部分结果的等式，因而同时保留结果、停机与发散。自然数计数器的零分支与正分支由实际条件门区分。

[Continuation.lean](../src/Monodromy/Continuation.lean) 从实际输运导出固定词的整数坐标公式；
[Effectiveness.lean](../src/Monodromy/Effectiveness.lean) 证明其原始递归性。
`Program.partrec_with_io` 得到固定原始递归输入输出映射下的部分递归上界。
坐标公式用于对应证明；路径生成使用保留根与实际提升。

[ForwardBoundary.lean](../src/Monodromy/ForwardBoundary.lean) 证明删除两个条件门及其逆后，控制余数形成自主演化的有限商；少于控制度数次的返回观察即可决定停机。另一方面，仅含固定词 \([B_1]\) 的 `zeroTest` 在输入 \(\operatorname{prepare}(n,0,0)\) 上恰于 \(n=0\) 时停机。同一输入表示下，删门子语言无法实现该停机域。这给出固定接口下的严格表达能力分离。

## 原生图灵模拟

[FormalCompilation.lean](../src/Monodromy/FormalCompilation.lean) 中的
`NativeTuring` 接通完整证明链：有限纸带机先译为三个源计数器，再用素数幂压缩
为两个计数器，最后译为上述五回路的有限路径词。源计数器只是证明中的中间
表示；原生状态始终只有三个保留根。

`iota_injective` 证明完整配置的单射编码；`eval_iota` 给出完整部分结果等式，
因此同时保留终态、停机与发散。静态有限根标记识别源步骤的返回边界。
`macroStep_iota` 证明从当前根执行到下一标记返回，恰好对应一个源步骤；
`finiteMacro_iota` 将它推广到任意有限非空字母表与控制类型。

`Program.runDriver` 仅用程序、初始根和有限前缀长度递归生成路径。
`result_actual_lifts` 将其完整曲线识别为匹配的两层覆盖提升，终根对应源终态。
`native_universality` 汇集编码、首次返回、完整执行与路径实现。

## 有效性与源码

[NativeIO.lean](../src/Monodromy/NativeIO.lean) 固定与程序无关的原始递归输入输出。
[Structure.lean](../src/Monodromy/Structure.lean) 在同一接口下连接原生计算与部分递归函数。
删去两个条件回路后的可判定停止商由
[ForwardBoundary.lean](../src/Monodromy/ForwardBoundary.lean) 单独刻画。

当前目录及每个模块的责任见 [structure.md](structure.md)。旧的后继先行实现和
四根模型完整保存在 [history.zip](history.zip)，当前源码包为
[Monodromy.zip](../Monodromy.zip)。数学短文见
[monodromy-note.tex](../notes/monodromy-note.tex)。

## 普通解析比较

[Effectiveness.lean](../src/Monodromy/Effectiveness.lean) 中的
`AnalyticComparison` 给同一有限路径词表一个直接解析比较器：整数平移对应
实平移，条件门对应 m↦m+sinc(πx)，有限控制由解析基数权重选择。权重读取
整个词开始时的控制值；到下一次返回才重新路由。

固定词及其逆在整个三维实空间上解析且互逆。整个程序的解析后继与停止信号
在精确整数格点上与原生执行完全一致，见 `eval_embed`、`result_iff`、
`halting_iff`、`divergence_iff`。`Structure.analytic_computes_iff` 保留同一输入
输出图。这是能力与执行方式的精确比较：普通解析公式实现相同格点计算，
原生构造则通过同一覆盖输运实际生成操作。格点外性质、数值成本及物理容差
分别研究。

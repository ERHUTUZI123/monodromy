# 现在

**原生几何图灵通用性证明链已经接通。**

当前状态是同一纤维中的三个复根。两条下层实际提升生成第三条提升的输入；
五个固定基回路完成记忆位移、零条件写入与控制运动。有限根观察选择下一整条
路径词。配置后继由提升产生。

## 已建立的结果

- **真实几何执行。** `CoupledPullback.upperCovering/lowerCovering` 与
  `CoupledContinuation.restrictedTrajectory_actual_lift` 识别两层覆盖及其实际运行。
  `execute_B_left/right` 从绕行几何导出零条件写入。
- **原生通用性。** `NativeTuring.native_universality` 将任意有限 Post–Turing
  机器编译到同一五回路执行器，保留完整配置、停机与发散。
- **源单步与内生边界。** `macroStep_iota` 与 `finiteMacro_iota` 证明原生首次返回
  恰好等于编码后的源单步；有限根标记决定返回边界。
- **完整路径证书。** `finite_run_path`、`result_actual_lifts` 证明每段有限执行
  均由先前实际返回根递归生成，并由两层实际提升实现。
- **有效性与固定接口。** `Effectiveness.lean`、`NativeIO.lean`、`Structure.lean`
  连接原生执行、固定有效数值编码与部分递归函数。
- **删门边界。** `ForwardBoundary.lean` 证明删除两个零条件回路及其逆后，
  控制余数形成闭合有限商，完整停机谓词可判定。

以上简称均位于 `Monodromy`。文件、精确入口及依赖顺序见
[structure.md](structure.md)；数学构造见 [architecture.md](architecture.md)。

## 主线的执行边界

通用性由无界分支记忆、条件绕行和内部路径选择共同实现。运行数据始终只有
有限 `Word` 表与有限停止位表。源图灵机及计数器机只出现在静态编译和正确性
证明中；原生返回调用实际路径提升，路径生成接收程序、初始根与前缀长度。
后续构造继续沿这条执行链发展。普通解析比较器位于后续证明层，用于检验
能力主张；它与计数器解释器均不在几何执行核心的依赖闭包内。

## 当前稿件

[monodromy-note.tex](../notes/monodromy-note.tex) 从几何观察出发，推导五个操作，
展示具体根的执行，再证明原生图灵通用性。固定接口刻画与删门分离保留在 Lean
中，当前短文以几何通用性为唯一主定理。原论文保持冻结。

## 数学范围

执行使用精确返回纤维、有限路径词表和离散返回语义。每个原语及其逆均来自实际
路径输运；一般状态依赖程序的可逆性需要相应控制条件。读出在每个返回态附近
有解析延伸。单一自治流、定量误差容限、物理实现与资源复杂度仍是开放问题。

## 可逆控制与解析比较

**可逆根路由。** 每个固定驱动与上层 deck 平移对易：
`CoupledContinuation.execute_controlDeck` 从实际提升唯一性证明这一点。
当有限根观察在路由下闭合时，`routed_bijective_iff` 给出精确判据：
整个返回映射为双射，当且仅当其有限根映射为置换。逆执行反向提升由逆置换
重新编号的路径；原 `routedEquiv` 是恒等置换特例。

**条件路由与阶段组合。** `ReversibleControl` 将无条件、任一记忆的零／非零
条件下的有限置换编译为已有回路的词；`ReversibleMemory` 编译控制根不变的
双记忆平移。二者均有原生逆表。`StagedProgram` 把有限阶段编码为同一控制
分支的 km+t，完整周期组合这些实际返回；其反向表仍使用相同五个回路。

**可逆计数器编译。** `Counter.Reversible` 定义局部前驱唯一的整数计数器边表。
`ReversibleCompilation` 用五次出端口路由、一次记忆更新、五次逆序入端口路由，
将每条启用边编译为同一程序的十一条原生词返回。端口和阶段都是已有控制根
中的有限地址。`reverse_after_forward`、`forward_after_reverse` 恢复整个纤维；
`step_firstReturn` 证明十一返回之间没有更早的相位零返回。

若每个非停机地址都有启用边（`Complete`），`eval_iota` 保留整个源配置及其
部分执行，`halting_iff`、`divergence_iff` 保留停机与发散，`result_actual_lifts`
给出两层实际提升。更一般地，`eval_iota_on` 只要求该条件在一个保持的不变量
上成立（`CompleteOn`、`Stable`），并复用同一执行表。源测试是零／非零，
移位作用在整数上；通用源机的自然数不变量与历史编码仍须构造。

**原生可逆倍乘。** `Counter.Reversible.Multiply.native_eval` 已构造固定正整数 p
的有限两计数器图，并证明同一个几何程序对所有自然数 n 将 (n,0) 变为 (pn,0)。
十一顶点、十二条测试／移位边组成两个可逆循环；合法不变量保持自然数域和
单测试端口的入口条件。工作空间回到零，完整原生推进保留显式逆表。
`reverse_native_eval` 反转同一有限图，在合法倍数输入 (pn,0) 上恢复 (n,0)。
`reverse_cycle_step` 则逐源步骤识别原生逆词表的十一返回。

**同一程序的普通解析实现。** `AnalyticComparison` 用 sinc(πx) 作整数零
指示函数，以有限解析权重选择整个词的输出，直接定义三个实坐标上的解析
后继与解析停止信号。`eval_embed`、`result_iff`、`halting_iff`、
`divergence_iff` 与原生路径程序的完整格点执行一致；
`Structure.analytic_computes_iff` 保留同一固定数值接口。
`analytic_realization` 因此给出每个部分递归函数的普通解析实现。

比较的范围是精确格点、离散返回与相同程序文本。格点外共轭、误差容限和
成本等价各需额外结论。这项证据说明：本构造的可计算函数集合也能由普通
解析公式实现；几何执行的具体内容在于从实际提升导出条件操作、组合、反演
与允许路径变形下的不变性。解析模拟的既有背景见
[Koiran–Moore](https://sites.santafe.edu/~moore/pubs/elem.html) 与
[Graça–Campagnolo–Buescu](https://sqigmath.tecnico.ulisboa.pt/pub/GracaDS/05-GCB-stable.pdf)。

## 当前集中问题

**把任意图灵机编译为具有可恢复历史的可逆双计数器源机，再接入已证明的
几何编译器。** 当前缺口在源侧：历史编码、可逆算术及合法自然数域。
`ReversibleReturn.source_defined_injective` 已证明，同一忠实编码下的可逆首次
返回保留源前驱唯一性；这决定新编码必须把源计算丢弃的信息保存在现有记忆中。

下一构造是可逆商余与整除选择，用于素数编码中的读取和递减。倍乘已经给出
第一个经过实际几何编译的算术部件；接下来须把这些部件组合为保留历史的
通用源机。入口条件与自然数域继续由保持的不变量证明。

文献提供明确源模型：[Morita（1996），Definitions 2.1–2.3、Theorems 4.1–4.2](https://doi.org/10.1016/S0304-3975(96)00081-3)。
其源模型采用自然数计数器与独立测试／跳转；完整源侧通用性构造尚待 Lean
证明。指令集条件必须保留：[Dudenhefner（2022）](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2022.16)
说明受限跳转语言中的可逆停机行为可以不同。文献提供构造依据，当前已验证
的几何编译定理并未假定此整数源语言已经通用。

待证结构线索：固定五门词的标签作用可能恰有标准形
\((x,y,m)\mapsto(x+a,y+b,m+c+f(x)+g(y))\)，其中 f、g 是有限支撑整数函数。
这可能组织固定路径词的代数结构，并与有限反馈后的计算能力对照。该标准形
及其文献位置尚待核验，当前优先完成可逆通用模拟。

## 保存与核验

当前活动源码已收敛为一套实现。退役的后继先行演算、四根执行器与全部清理前
源码集中于 [history.zip](history.zip)。历史判断见 [history.md](history.md)。
[Monodromy.zip](../Monodromy.zip) 是当前源码包，两者用途分别明确。

```sh
lake build
lake env lean -DautoImplicit=false -DwarningAsError=true src/Audit.lean
```

本轮统一构建通过 3071 项 Lake 任务，1945 个 Monodromy 声明的传递公理审计
通过，仅使用 `propext`、`Classical.choice`、`Quot.sound`。原生定义体的依赖
审计也通过：执行与正反编译表保留实际提升，未调用源机解释器、整数后继
解释或普通解析比较器。独立复核检查了可逆编译、不变量语义与倍乘构造。

短文审阅包独立锁定于其已核验的 1531 声明快照；主线继续推进，二者版本
分别记录于本页与 [notes/README.md](../notes/README.md)。

执行核心仍只依赖 Covering、Choice、Logarithm、Radix、Continuation；解析比较
与递归性证明位于后续证明层。活动模块数仍为 16，原生几何、三个保留根与五个
回路保持一致。

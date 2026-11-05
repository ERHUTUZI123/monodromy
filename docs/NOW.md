# 现在

原生几何通用性与保留完整历史的可逆通用模拟已经建立。
执行核心保持三个保留根、五个固定回路：实际逐层提升产生操作，返回根选择下一条有限路径词。

## 已建立的基础

- **实际几何执行：** `CoupledPullback.upperCovering/lowerCovering`、
  `CoupledContinuation.restrictedTrajectory_actual_lift` 给出覆盖及实际提升；
  `execute_B_left/right` 从条件绕行导出零条件写入。
- **原生通用性：** `NativeTuring.native_universality`、`macroStep_iota`、
  `result_actual_lifts` 保留完整图灵配置、首次返回、停机、发散及有限执行路径。
- **能力刻画：** `Structure.lean` 在固定有效数值接口下连接部分递归函数；
  `ForwardBoundary.lean` 证明删去条件回路后，停止观察形成有限商并可判定。
- **可逆几何编译：** `ReversibleCompilation` 将局部可逆双计数器表编译为同一
  五回路的十一阶段返回。正反词表在整个纤维上互逆；完整部分执行的对应条件
  见 `eval_iota_on`，实际提升见 `result_actual_lifts`。

精确入口与依赖顺序见 [structure.md](structure.md)，构造见 [architecture.md](architecture.md)。

## 已完成的可逆源模拟

`Counter.Reversible.Recording` 将有限自然数计数器程序编译成实际有限边图。
每步以非零数字保存旧地址与分支，反向 radix 图将其压入历史；返回边界时工作
寄存器为零。`deterministic` 与 `targetCompatible` 保证定义步的前驱唯一。

`ReversibleTuring.step_firstReturn`、`macroStep_encode`、`result_iff`、
`halting_iff`、`divergence_iff` 与 `step_retraces` 将任意有限图灵机接到这张
记录图，保留完整配置、终态及可恢复历史。宏只执行固定图并观察有限控制标记；
源转移用于正确性证明。同一首次返回见证具有严格增长的历史。

`ReversibleReturn.source_defined_injective` 证明忠实的可逆首次返回保持源前驱
唯一性。这说明源计算丢弃的信息需要保存在编码中，供逆向恢复。

这一阶段使用四计数器的**中间源表示**。历史保留在终态中，逆图逐步恢复前态；
算术工作空间在返回时归零。四到二计数器压缩已接通同一三个根的原生执行器。

## 可逆原生总定理

`ReversibleNativeTuring.native_universality` 已通过主工程完整构建和严格审计。
若图灵机单步 c↦c′，则同一个实际生成的 H′>H 满足：正向宏在下一标记返回
得到完整配置 (c′,H′)，逆向宏在前一标记返回恢复 (c,H)。两宏只接收当前根，
按固定词表及有限根标记执行。`step_return_pair` 与 `macroStep_iota` 给出精确
交换关系；`FirstReturn.iterates/inverse_iterates` 排除正逆途中的提前标记返回。
结果、停机、发散、全纤维上的双侧 `advance` 逆及每段有限执行的两层实际提升
均在总定理中连接。边界按指定路径词完成后的离散返回时刻采样。

支撑构造包括：

- `PrimeCode.Basis` 统一有限维素数幂编码；旧三寄存器定理复用同一证明。
  `Recording.unitShift` 与 `encode_reaches_nonnegative` 保证实际图只作 ±1 位移，
  且从编码初态出发的全部中间状态均非负。
- `Counter.Reversible.Radix` 用同一图分解商余、逆向打包。余数留在有限控制中，
  工作空间在两端归零；`native_eval`、`native_reverse_pack` 已接到几何执行。
- `RadixObservation.native_eval` 实现
  \( (n,0,j)\mapsto(n,0,\pi_{n\bmod p}(j)) \)。
  条件是 n 为自然数、p>0、初始工作空间为零，且各 π_r 为有限置换。
  选择由实际到达的余数端口及其静态粘合产生，两个记忆值完整恢复。

`PortNetwork.Wiring` 已证明识别出口与入口可保持原边及局部正反可逆性。
压缩共享测试与恢复端口；`step_firstReturn` 排除内部提前返回，普通运行复用
同一证明。正式整合已替换旧拼接实现并合并重复证明；源侧与原生侧的普通
运行结论均由同一首次返回证明导出。独立核验稿与其锁定基线保存在
[history.zip](history.zip)。

## 数学位置与开放问题

历史记录沿用经典可逆模拟思想，见
[Bennett（1973）](https://www.cs.princeton.edu/courses/archive/fall04/cos576/papers/bennett73.html)。
[Morita（1996）](https://doi.org/10.1016/S0304-3975(96)00081-3) 已建立不可逆 k
计数器到可逆 k+2、再到可逆双计数器的模拟。本研究沿这条源侧路线，将实际
有限图接入几何执行并核验每次编译的条件。
[Dudenhefner（2022）](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2022.16)
说明跳转限制会改变可逆停机行为，指令集条件须逐项保留。

`Structure.partrec_of_realizable` 给出部分递归上界，
`continuation_characterization` 在固定有效输入输出下给出精确等价。
新增可逆程序属于同一有限 `Program` 类型，故也受该上界约束。
该精确等价针对整个 `Program` 类。一个更强的后续问题，是单独刻画新可逆
编译子类在统一固定接口下的下界。

原生性已作独立源码复核：程序仅含五门的有限词表及停止位；下层实际提升逐点
生成上层输入，上层提升只接收初态。有限解析选路与经典编译的作用明确保留，
执行不接收任意状态后继回调，也不调用源解释器。复核证据随上述证明阶段归档。

`AnalyticComparison` 与 `Structure.analytic_computes_iff` 证明：同一程序的完整
整数格点计算也有普通三维解析实现。因此可计算函数集合本身不能建立几何必要性。
本构造的具体几何内容是实际提升产生的条件操作、组合、反演及相应同伦不变性。
单一自治流、格点外行为、误差容限、物理实现与资源成本仍是开放问题。相关解析
计算背景见 [Koiran–Moore](https://sites.santafe.edu/~moore/pubs/elem.html) 与
[Graça–Campagnolo–Buescu](https://sqigmath.tecnico.ulisboa.pt/pub/GracaDS/05-GCB-stable.pdf)。

第二座山峰暂存一条待证线索：固定五门词的标签作用是否恰有
(x,y,m)↦(x+a,y+b,m+c+f(x)+g(y)) 的标准形，其中 f、g 有限支撑。
这条问题与已完成的可逆模拟分开研究。

## 核验、稿件与历史

```sh
lake build
lake env lean -DautoImplicit=false -DwarningAsError=true src/Audit.lean
```

本轮完整构建通过 3071 项 Lake 任务；2661 个 Monodromy 声明的传递公理审计
通过，仅使用 `propext`、`Classical.choice`、`Quot.sound`。定义依赖审计同时
通过：原生执行保留实际提升，执行与静态编译避开源解释器和整数后继后端。
历史图、首次返回、非负不变量、素数编码、正逆宏与只读观测经过独立子代理复核。
活动模块仍为 16，执行核心的五个几何模块保持原有依赖顺序。

[短文及审阅包](../notes/README.md) 已冻结，独立锁定在 1531 声明快照；其范围
是原生几何图灵通用性，主线可逆研究独立推进。早期论文保持冻结。
[Monodromy.zip](../Monodromy.zip) 是当前源码发行包；[history.zip](history.zip)
保存退役实现、原四根模型、证明草稿及锁定源码与核验记录。历史证据见
[history.md](history.md)。

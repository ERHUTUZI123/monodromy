# 源码与证明链

活动源码只有一套原生执行构造。旧实现及清理前的完整工作树见
[history.zip](history.zip)；历史记录见 [history.md](history.md)。

## 目录

```text
monodromy/
├── src/
│   ├── Monodromy.lean       公共入口
│   ├── Audit.lean           传递公理审计
│   └── Monodromy/           当前数学与证明
├── docs/                    架构、证明导航与历史
├── notes/
│   ├── monodromy-note.tex   当前几何构造论文
│   ├── monodromy-note.pdf
│   └── monodromy-review.zip 独立锁定的完整审阅工程
├── paper/                  冻结的早期论文
├── Monodromy.zip            当前源码发行包
├── lakefile.lean
├── lake-manifest.json
└── lean-toolchain
```

## 数学模块

| 文件 | 作用 |
| --- | --- |
| [Covering](../src/Monodromy/Covering.lean) | 实际路径输运、唯一性、同伦、逆路径、积与拉回覆盖 |
| [Choice](../src/Monodromy/Choice.lean) | 正则纤维上的解析选择核 |
| [Logarithm](../src/Monodromy/Logarithm.lean) | 指数覆盖及两次提升产生条件绕行的基础构造 |
| [Radix](../src/Monodromy/Radix.lean) | 有限幂覆盖、单位根与精确有限观察 |
| [Continuation](../src/Monodromy/Continuation.lean) | 三根几何、五回路、可逆条件控制、阶段组合与首次返回 |
| [Tape](../src/Monodromy/Tape.lean) | 空白补齐半纸带的规范单射编码 |
| [Counter](../src/Monodromy/Counter.lean) | 纸带／计数器编译、统一素数编码、可逆商余与历史图、原生可逆编译 |
| [FiniteSupport](../src/Monodromy/FiniteSupport.lean) | 有限控制支持及保留空白的有限重编号 |
| [FormalCompilation](../src/Monodromy/FormalCompilation.lean) | 原生通用性、真实提升证书与保留历史的可逆源模拟 |
| [IntegerPrimrec](../src/Monodromy/IntegerPrimrec.lean) | 整数算术的原始递归性 |
| [Effectiveness](../src/Monodromy/Effectiveness.lean) | 整数解释的原始递归性、部分递归上界与普通解析比较 |
| [CanonicalIO](../src/Monodromy/CanonicalIO.lean) | Mathlib 源机器的固定数值纸带协议 |
| [NativeIO](../src/Monodromy/NativeIO.lean) | 与程序无关的原生输入输出及部分递归下界 |
| [Observation](../src/Monodromy/Observation.lean) | 有限闭合停止观察的一般界限 |
| [ForwardBoundary](../src/Monodromy/ForwardBoundary.lean) | 删除条件回路后的有限商与停机判定 |
| [Structure](../src/Monodromy/Structure.lean) | 固定接口刻画、子语言分离及普通解析实现 |

## 原生通用性的证据顺序

1. `CoupledPullback.upperCovering`、`lowerCovering` 给出真实的两层覆盖。
2. `CoupledContinuation.intermediateCurve_actual_lift`、`restrictedTrajectory_actual_lift`
   将执行曲线识别为这两个覆盖的实际提升。
3. `execute_A_left/right`、`execute_B_left/right`、`execute_control_prepare`
   从这些提升导出五个固定回路的操作。
4. `routeDriver_eq` 与 `Program.runDriver_actual_lifts` 证明返回根选择整条路径，
   并生成下一段真实提升。
5. `CounterContinuation.eval_encode`、`Counter.TuringCompiler.eval_encode`、
   `Counter.Compression.eval_encode` 接通有限纸带机与同一原生执行器。
6. `NativeTuring.macroStep_iota` 给出精确源单步的首次返回等式；
   `eval_iota` 保留完整部分结果，`result_actual_lifts` 保留实际路径。
7. `NativeTuring.native_universality` 汇集上述性质；`finiteMacro_iota`、
   `finite_eval_iota` 覆盖任意有限非空字母与控制类型。

所有名称均位于 `Monodromy` 命名空间。主定理的完整陈述与解释见
[当前论文](../notes/monodromy-note.tex)。执行核心的依赖先于计数器编码和递归性证明；
整数解释由实际输运导出；递归性与解析比较处于后续证明模块。

## 可逆模拟的证据顺序

1. `ReversibleControl.executionEquiv`、`ReversibleMemory.executionEquiv`
   分别给出条件控制置换与记忆平移的原生逆表。
2. `StagedProgram.executionEquiv` 将有限阶段及其逆编译为同一控制根中的循环。
   `cycle_firstReturn` 以实际有限根观察识别完整周期。
3. `Counter.Reversible` 给出源侧局部可逆条件；`ReversiblePorts` 与
   `ReversibleRouting` 共用一个有限端口匹配构造。
4. `ReversibleCompilation.cycle_step` 将源单步实现为十一条原生词返回；
   `executionEquiv` 给出整个纤维上的显式正反执行。
5. 在明确的 `Complete` 条件下，`eval_iota`、`step_firstReturn`、
   `result_actual_lifts` 保留部分结果、首次返回及两层实际提升。
   `eval_iota_on` 允许在保持的合法不变量上满足完整性条件，执行表相同。
6. `Counter.Reversible.Radix.native_eval` 在有限余数出口计算 (n,0)↦(n/p,0)；
   `native_reverse_pack` 反转同一图，将出口 r 的 (q,0) 恢复为 (pq+r,0)。
7. `Counter.Reversible.Recording.deterministic/targetCompatible` 给出保存历史的
   实际有限图；`step_firstReturn`、`eval_embed`、`step_reaches_reverse` 保留
   完整配置、部分执行与可恢复历史。普通执行由同一首次返回证明导出。
8. `FormalCompilation.lean` 中的 `ReversibleTuring.step_firstReturn`、
   `macroStep_encode`、`result_iff`、`halting_iff`、`divergence_iff` 与
   `step_retraces` 将任意有限图灵机接到四计数器的部分可逆源图。
9. `PrimeCode.Basis` 统一有限维素数编码；`Recording.unitShift` 与
   `encode_reaches_nonnegative` 给出压缩所需的实际移位与自然数域条件。
   `RadixObservation.native_eval` 以余数端口的静态粘合执行有限控制置换，
   正反 radix 执行完整恢复两个记忆值。

10. `PortNetwork.Wiring` 直接识别实际出口与入口；`PrimeCompression.table`
    用素数幂将四计数器中间表示压缩到两个计数器，同时保持两个局部可逆条件。
    `marked_firstReturn` 保留实际历史及所有内部边界条件。
11. `ReversibleCompilation.marked_firstReturn` 将有限源标记提升到同一原生词表。
    `ReversibleNativeTuring.step_return_pair` 证明正逆宏恢复同一完整配置与历史；
    `macroStep_iota` 给出源可选单步结果的精确对应。
12. `ReversibleNativeTuring.native_universality` 汇集完整注入、全纤维双侧逆、
    首次返回、正逆宏、结果、停机、发散与每段有限执行的两层实际提升。

这里的首次返回指指定路径词完成后的离散返回时刻。源计数器图仅用于静态
编译及对应证明；原生宏的运行定义只使用实际提升、有限根观察与内部迭代。

短文的完整冻结工程与复核说明见 [notes/README.md](../notes/README.md)。
旧编号副本已归档；主线构建使用独立推进的 `src/Monodromy/`。

## 包与历史

- [monodromy-review.zip](../notes/monodromy-review.zip)：单层 `Monodromy/` 工程，
  包含 PDF、一个 README、完整源码和三份构建配置。README 合并证明索引、
  复核命令与精确源码指纹。最终 ZIP 已在独立目录重新构建并审计。


- [Monodromy.zip](../Monodromy.zip)：当前可构建源码包，包含版本锁定与 SHA-256 清单。
- [history.zip](history.zip)：清理前的源码、原四根命令行演示、冻结论文及研究证据。
  包内 `PROVENANCE.txt` 说明来源，`SHA256.json` 校验各文件。
- `paper/monodromy.tex`、`references.bib` 及对应 PDF、arXiv 包保持冻结；
  新稿使用 `notes/monodromy-note.tex`。

核验命令见 [README](../README.md)。

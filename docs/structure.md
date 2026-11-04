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
│   ├── monodromy-review.zip 独立锁定的完整审阅工程
│   └── *.lean              该审阅快照的编号证明副本
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
| [Counter](../src/Monodromy/Counter.lean) | 纸带／计数器编译；可逆边表到同一原生执行器的完整模拟 |
| [FiniteSupport](../src/Monodromy/FiniteSupport.lean) | 有限控制支持及保留空白的有限重编号 |
| [FormalCompilation](../src/Monodromy/FormalCompilation.lean) | 原生图灵通用性总定理、首次返回与真实提升证书 |
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
6. `Counter.Reversible.Multiply.native_eval` 将有限可逆倍乘图接到同一几何
   执行器，对固定 p>0 和任意自然数 n 计算 (n,0)↦(pn,0)。
   `reverse_native_eval` 由反转的有限图在倍数输入上恢复原数；
   `ReversibleCompilation.reverse_cycle_step` 识别原生逆表对源单步的回退。

这条可逆编译链的源是整数双计数器边表。任意图灵机到该可逆源语言的构造
是当前主线问题，尚未由上述定理替代。

编号证明副本及其与正式源码的对应见 [notes/README.md](../notes/README.md)。
这些副本与审阅 ZIP 的冻结版本一致；主线构建使用独立推进的 `src/Monodromy/`。

## 包与历史

- [monodromy-review.zip](../notes/monodromy-review.zip)：面向数学审阅的完整包。
  顶层为论文、LaTeX 与简明 README；`formalization/` 保留正常模块名、完整工程、
  锁定依赖、数学定理索引和 SHA-256 清单。工程已在独立目录重新构建并审计。
  Git 基准提交与当前快照分开记录，以准确标识未提交的源码版本。


- [Monodromy.zip](../Monodromy.zip)：当前可构建源码包，包含版本锁定与 SHA-256 清单。
- [history.zip](history.zip)：清理前的源码、原四根命令行演示、冻结论文及研究证据。
  包内 `PROVENANCE.txt` 说明来源，`SHA256.json` 校验各文件。
- `paper/monodromy.tex`、`references.bib` 及对应 PDF、arXiv 包保持冻结；
  新稿使用 `notes/monodromy-note.tex`。

核验命令见 [README](../README.md)。

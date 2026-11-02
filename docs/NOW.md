# Monodromy

我要美。Lean 是唯一原生研究环境。

## 当前核心

\[
(z^2-u)^2=\theta,\qquad |u|=2,\quad |\theta|=1.
\]

状态是根，执行是沿路径携带这个根。控制与参数的行走使用同一条提升规则。

- [Quartic.lean](../src/Monodromy/Quartic.lean)：完整方程空间、连续根式、覆盖与统一延拓律；环面只是经过证明的坐标。
- [Paths.lean](../src/Monodromy/Paths.lean)：根的记忆、行走与自治反馈流。
- [Covering.lean](../src/Monodromy/Covering.lean)：实际路径提升、复合、同伦，以及连续矩形导出的保护。
- [Algebra.lean](../src/Monodromy/Algebra.lean)：作用、共同识别、保护边界与有限程序。

入口是 [Monodromy.lean](../src/Monodromy.lean)。

## 已经成立

Lean 已检查：方程空间确为覆盖，基点纤维恰有四个根。控制回路使 `z ↦ −z`；参数回路改变根，同时保留旧控制操作及其全部有限组合。在这个受限覆盖内，任何 `θ=1` 的路径都无法实现后一种运算。

同一个方程给出同一条延拓律：

\[
\dot z=\frac{2(z^2-u)\dot u+\dot\theta}{4z(z^2-u)}.
\]

实际覆盖内分母始终非零。`lift_hasDerivAt` 从实时间轨迹的连续性和控制的可微性推出根可微并服从此律；`equation_of_velocity` 证明正则可微解从合法初值出发保持方程；`velocity_transport` 将其在 `[0,1]` 的终点识别为已有覆盖输运的终点。这些定理识别给定正则轨迹；一般 ODE 存在性与数值求解保证仍需另证。

现在由根恢复内部分支 `b=z²−u`，选择反馈律

\[
\dot u=i\,u\,\operatorname{Re}b,\qquad \dot\theta=0.
\]

`flow : Flow ℝ Space` 是它的全实时间连续流，控制速度始终由当前状态给出，根继续服从同一延拓律。`inner_flow` 证明 b 守恒；在基点记忆纤维上，`flow_two_pi` 证明时间 `2π` 后基底闭合、根变为 `−z`。参数写入反演后续基底路径，`parameter_changes_path` 还给出了正时间路径确实不同的见证；原终端控制操作仍保持。

这里的 `Re b` 是我们选择的反馈律，闭合结论限于基点纤维。这个构造使用守恒记忆，尚未自行更新它；也未获得新操作类。路径学习、反馈驱动的几何适应和实际结构增长尚未实现，Productive Geometric Plasticity 仍未验证。

## 下一问

让反馈也参与内分支的变化：能否在同一延拓律下构造会改变 b 的运动，同时给出回归条件、留下的状态和旧操作保持条件？构造与证明继续直接在 Lean 中生长。

## 复核与来路

`lake build` 与 `lake env lean src/Audit.lean` 均通过。公理检查只允许 Lean 标准公理，无占位证明。工具链与依赖固定于 [lean-toolchain](../lean-toolchain) 和 [lake-manifest.json](../lake-manifest.json)。

[研究来路](history.md) 保存档案证据、失败与对照。历史实验没有建立 Monodromy 的独立优势；当前构造也没有作此声称。旧架构与解析草稿留在 [docs/](.)。本轮只进行了 Lean 构造与证明检查，未启动训练或新实验。

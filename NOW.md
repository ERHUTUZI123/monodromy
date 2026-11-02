# Monodromy

我只要美。Lean 是唯一原生研究环境。

## 当前核心

\[
(z^2-u)^2=\theta,\qquad |u|=2,\quad |\theta|=1.
\]

状态是根，执行是沿路径携带这个根。控制与参数的行走使用同一条提升规则。

- [Quartic.lean](Monodromy/Quartic.lean)：完整方程空间、连续根式、覆盖与统一延拓律；环面只是经过证明的坐标。
- [Paths.lean](Monodromy/Paths.lean)：根的记忆与行走，以及微分轨迹和覆盖输运的一致性。
- [Covering.lean](Monodromy/Covering.lean)：实际路径提升、复合、同伦，以及连续矩形导出的保护。
- [Algebra.lean](Monodromy/Algebra.lean)：作用、共同识别、保护边界与有限程序。

入口是 [Monodromy.lean](Monodromy.lean)。

## 已经成立

Lean 已检查：方程空间确为覆盖，基点纤维恰有四个根。控制回路使 `z ↦ −z`；参数回路改变根，同时保留旧控制操作及其全部有限组合。在这个受限覆盖内，任何 `θ=1` 的路径都无法实现后一种运算。

同一个方程给出同一条延拓律：

\[
\dot z=\frac{2(z^2-u)\dot u+\dot\theta}{4z(z^2-u)}.
\]

实际覆盖内分母始终非零。`lift_hasDerivAt` 从实时间轨迹的连续性和控制的可微性推出根可微并服从此律；`equation_of_velocity` 证明正则可微解从合法初值出发保持方程；`velocity_transport` 将其在 `[0,1]` 的终点识别为已有覆盖输运的终点。这些是精确轨迹的定理，未提供 ODE 存在性或数值求解保证。

这是精确连续几何中的构造。路径学习、反馈驱动的几何适应和实际结构增长尚未实现；已有增长定理只证明显式合同的后果。Productive Geometric Plasticity 仍未验证。

## 下一问

让当前根参与产生下一段路径。先构造一个由根决定基底方向、仍服从同一延拓律的反馈流，研究何时形成闭路径、留下什么状态。构造与证明继续直接在 Lean 中生长。

## 复核与来路

`lake build` 与 `lake env lean Audit.lean` 均通过。161 项声明的传递公理依赖只含 Lean 标准公理，无占位证明。工具链与依赖固定于 [lean-toolchain](lean-toolchain) 和 [lake-manifest.json](lake-manifest.json)。

[研究来路](thoughts/history.md) 保存档案证据、失败与对照。历史实验没有建立 Monodromy 的独立优势；当前构造也没有作此声称。旧架构与解析草稿留在 [thoughts/](thoughts/)。本轮只进行了 Lean 构造与证明检查，未启动训练或新实验。

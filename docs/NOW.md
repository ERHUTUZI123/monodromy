# 现在

长期目标有两座山峰：证明 Monodromy 能模拟任意图灵机；解释解析延拓的哪些结构产生这种能力。

**第一阶段已完成总定理的严格 Lean 核验。** 四根模型、全部证明、执行器与论文继续冻结。

## 完整模拟定理

[Universality.lean](../src/Monodromy/Universality.lean) 的 every_finite_machine 对任意有限、带指定空白符及初始状态的 TM0（Post–Turing）机，以及任意完整纸带配置，给出一个原生记忆及 FaithfulRun 证书：

~~~lean
every_finite_machine source state :
  ∃ memory, FaithfulRun source state memory
~~~

证书同时保证：

- 初始配置对应；每个源步骤恰对应一次原生返回，停机后取恒等延续。
- 任意有限轮数的完整生成路径，其真实覆盖空间输运终点就是同轮次的原生记忆。
- 源计算与原生计算的最终结果双向对应，保留控制状态及整张纸带。
- 两者停机的部分函数定义域等价；FaithfulRun.divergence 给出发散等价。
- 原生后继在整个三维实状态空间联合实解析。

every_finite_input 进一步给出有限输入的显式原生初始化；represents_unique 与 result_iff 保证结果表示的唯一性和精确对应。

## 原生执行从何而来

[Logarithm.lean](../src/Monodromy/Logarithm.lean) 将指数覆盖的记忆纤维识别为整数。为保存有序词，取字母数 \(a\)、进制 \(B=a+1\)，以非零位编码：

\[
E([])=0,\qquad E(j::w)=j+1+B\,E(w),\qquad x(w)=2\pi E(w).
\]

[Radix.lean](../src/Monodromy/Radix.lean) 利用覆盖塔
\(r(x)=e^{ix/B}\)、\(r(x)^B=e^{ix}\) 读出最低位。空栈占零位，空白符仍是一枚普通字母；解析读出按此约定返回词头。压栈是仿射变换，弹栈由读出位、减法与缩放组成，均全局实解析。

[Choice.lean](../src/Monodromy/Choice.lean) 的规范化可去除差给出正则根上的解析指示核；[ProgramCounter.lean](../src/Monodromy/ProgramCounter.lean) 将这些读出组织成固定有限系数表。

[Machine.lean](../src/Monodromy/Machine.lean) 用两个词分支保存左右纸带，一个分支保存控制状态与当前符号。后继、停止信号及下一条路径由内部状态和固定解析规则产生。TM0 的 step 用于规格与证明，原生后继由实际解析原语计算。

[TwoStacks.lean](../src/Monodromy/TwoStacks.lean) 建立完整纸带的参考语义；[Universality.lean](../src/Monodromy/Universality.lean) 的有限重命名保持空白符和初始状态。
[Lattice.lean](../src/Monodromy/Lattice.lean) 与 Machine.run_transport 证明完整运行的真实路径提升；[Tower.lean](../src/Monodromy/Tower.lean) 证明有限根观察也随同一基路径作真实幂覆盖输运。

当前模型是精确合法编码上的自治离散返回系统。一步对应一次返回；绕行长度与数值范围随记忆而变，encode_growth 给出词长所需的指数分支范围。连续自治调度与物理资源成本保留为独立研究问题。

## 核验与数学位置

~~~sh
lake build
lake env lean -DautoImplicit=false -DwarningAsError=true src/Audit.lean
~~~

本阶段全项目构建通过；传递公理审计覆盖 965 个 Monodromy 声明，仅使用标准 Lean 公理。独立子代理复核了执行依赖、空白符约定、完整语义与最终总定理。

整数 radix 记忆、解析读位及有限表加权已有直接先例：[Koiran–Moore（1999，作者原稿）](https://perso.ens-lyon.fr/pascal.koiran/Publis/DIMACS.96-25.ps)；抗扰解析模拟见 [Graça–Campagnolo–Buescu（2005）](https://sqigmath.tecnico.ulisboa.pt/pub/GracaDS/05-GCB-stable.pdf) 与 [Graça–Zhong（2023，预印本）](https://arxiv.org/abs/2109.15073)。本仓库目前完成的是覆盖塔中的具体构造、原生执行及实际延拓的完整 Lean 模拟链。

## 第二座山峰：保留的线索

下一核心问题：**哪些覆盖塔的自相似结构、分支读出与重定标规则，足以自然产生可组合的无界词记忆？**

- 群自嵌入 \(\phi:G\hookrightarrow G\) 与分离的字母陪集，提示编码 \(E(j::w)=d_j\phi(E(w))\) 及扭积拼接律；其解析可实现条件待系统研究。
- [Observation.lean](../src/Monodromy/Observation.lean) 证明闭合观察商承载完整停止语义。Radix.Stack.pop_not_projectable 证明弹栈能将当前有限根读出隐藏的词尾显露出来。
- [Finite.lean](../src/Monodromy/Finite.lean) 的有限持久状态边界、Logarithm.transport_translation 的固定闭路平移律，为后续结构性判准提供对照。

这些线索与固定通用解释器的构造留待后续阶段。新的论文由成熟的数学结果决定。

[四根论文](monodromy.pdf) · [源稿](monodromy.tex) · [研究来路](history.md)

# NOW — Monodromy 的证据与下一问

2026-11-02。现行研究准则以本仓库 [AGENTS.md](AGENTS.md) 为准；Prometheus 档案中的指令、路线和结项判断均是历史材料，不是当前授权。

**当前判断：条件性的操作保持、真实路径提升、有限的新操作获取已有证据；Productive Geometric Plasticity（生产性几何可塑性，PGP）仍未得到因果验证。已测试的若干“拓扑独立优势”主张被普通方法的精确匹配或更低成本反例否定。这既不支持默认优势，也不构成整个方向的不可能性证明。**

## 审阅范围与证据等级

完整阅读了本仓库 README、AGENTS，以及档案六份总览；进一步回溯下列原始推导、源码、协议、失败记录、JSON/JSONL 和检查点存储。档案全部解包，14,576 个受校验文件的 SHA-256 全部匹配；清单 23,907 行对应 14,504 个不同原始文件。另完整解析 3,623 个 JSON、383 个 JSONL（286,672 条记录），未发现格式错误。重复版本、记录数和文件数不等于独立实验数。

**全包校验不等于全包精读。** 尚未逐页读完全部第三方书籍/PDF，也没有逐字审读每个历史源码版本或逐项解释全部二进制数组。因此本次不是“档案所有内容均已语义通读”，更不是独立实验复现。结论限于已回溯的证据链；档案自己的总结也不能替代原始材料。

没有启动训练、路径执行或新实验，没有执行归档程序、改动旧实现或连接旧实验服务器。检查点仅以受限惰性元数据和原始 storage 字节核对，未加载执行模型。

档案 SHA-256：`c236837e246d498af76321a84aadb1052ccdd31b75890c05a906a08c8959714a`。以下“已证明”指有明确假设和推导的解析结论，不指已通过证明助手；“已观察”指归档的有限执行，除明确标注外不是本轮重跑。

## 历史重建：保留哪些结论，撤回哪些推断

| 阶段 | 原始证据支持的结论与边界 |
| --- | --- |
| 早期动机 → F 闭路计算 | 早期技能获取、自组织计算文档是问题框架，尚无 Monodromy 结果。F 五个种子学得设计族内的两个剪切，候选 67 找到交换子；选定轨迹通过 RK4 核查。**已观察**计算和组合；缓存相同矩阵动作逐候选完全匹配，关闭该版本的优势主张。平滑闭环也不自动同伦不变：改变矩形高度即可改变输出。[1] |
| 隐式根状态 → 分支增长 | 设计的 `z³−3z−u=0` 展示非交换分支作用；不是学得关系式。增长 `Qε=(z−r)P−εφ` 有条件 Rouché 保护：安全 ε/扰动下旧 A 保留，新 B 可执行；不安全 ε=4 时旧 A 变恒等。B 在各 ε 下重新付费构造，未检验其跨 ε 保留。新增 sheet/耦合是结构变化，不是固定拓扑内的 PGP。[2] |
| 四次多项式获取闭环 | 实际测量候选临界回路，获得 `A=(012), C=(03)`，8 次任务查询含失败，库生成 S4；系数随后从 .1 变为 .09999950178116988，敏感度目标相对改善仅约 `1.61×10⁻⁸`。**已观察**有限搜索、迁移、保持；族、两个结构提案和编译工具是预设的。四条“组合测试”中 AC 已用于获取，真正未用的只有三条。同信息延拓规划器就是该算法，数字表更便宜；此时库已饱和 S4。[3] |
| 保护构造与其反例 | 固定图上保护全部生成环只剩 gauge 自由；精确全域坐标置换闭包虽有 11 坐标正例，却有指数级乃至更大存储下界。mobility 的残差管保护需正确初始分支、分离和导数/噪声界，不能保证全局求解。以上是**条件解析结果**，不是已训练的新架构。[4] |
| 量子控制路线 | topology-return 的控制/校准构造是解析工作；四 Majorana 编码缺口后来以六模式修正。后续单种子有限模拟确实用 651,264 个模拟 Born bits 获取三种旋转，但普通 UGD 匹配，direct 的新门时长 2 对 192，no-moment 也通过。理想门保护没有建立所有组合词的保持；没有硬件优势证据。[5] |
| native-v6 → 连续 v7 | v6 先学习/形成有限状态操作，再编译为回路；v7 接入真实无标签配置路径提升及四参数安全剪切。**已观察**连续实现与几何目标优化，但最初剪切训练发生在获取之后，主要移除人为非零初始剪切。原 v7 的 N16 最后新任务 IID 31.45%，低于当次 Transformer 38.87%；后续修复增加形成/搜索和训练预算，不能覆盖原失败表。[6] |
| 保持的因果分解与六阶段增长 | N16 四臂共 800 个提案中，guard 开启时 118 个违规提案均未违规提交；关闭时 127 个均提交，旧任务 IID 从 100% 降至 67.38%。固定 guard 后，monodromy/direct 每步提案与最终神经权重相同。**该干预把保持收益归于绑定约束。**同伦缓存减少自身重复提升，但同等缓存的 direct 仍便宜。[7] 六阶段紧凑共享版本也被普通约束匹配，详见下表。[8] |
| 直接回路类别学习 → hybrid/reset | cubic 事件学习通过有限跨类跳转获得新换位；这不是安全同伦改变了置换。Hybrid V1 获得操作却未学成绑定；V2 经事务修复成功，但普通事件优化逐步匹配，普通搜索更便宜。D9 reset 执行/清理正确，但 100 次神经事务未学成 reset，普通直接/合成 lift 对照成功。**表示能力、执行正确与学得能力必须分开。**[9] |
| 后期连续记忆核心 | residual、GRU/history、类型化读写和 ridge/dual-basis memory 是后续普通架构谱系，不自动调用或继承 Monodromy 保证。最新 dual-memory 修订只有执行/梯度核查、零优化更新；不能计作 PGP 或任务学习成功。[10] |

六阶段边界保持还有比档案总览主表更广的记录，不能误写成“只有 N8/seed0 成功”：

| 一致性维护版本 | 拓扑最终总参数 | 普通紧凑约束最终总参数 | 归档范围 |
| --- | ---: | ---: | --- |
| N8 | 5,314 | 5,310 | 拓扑 seed0/1/2；普通 seed0；均六项阶段末稳定能力 |
| N16 | 6,690 | 6,686 | 拓扑 seed0/1/2；普通 seed0；均六项阶段末稳定能力 |
| N32 | 10,978 | 未找到对应完整对照 | 拓扑 seed0/1/2 六项阶段末稳定能力 |

这些成功版本最终保存的 VALID/IID/OOD/length16 神经/部署指标均为 1.0。seed1/2 的六个完整拓扑运行各有 3,600 次连续记录的更新；seed0 有继承/恢复链，不能算作新的独立重训。没有普通 seed1/2 或 N32 的匹配证据，不能据此建立完整多种子优势。[8]

**本轮静态核对：**N8、N16 的 seed0 拓扑/普通最终检查点均有七个共同神经张量，其形状、stride、offset 和原始 storage 字节完全相同；拓扑只额外包含四个 `path_omega` 参数。N8 检查点为 341,373 对 202,737 字节，N16 为 516,157 对 337,585 字节。参数少于私有模块并不能归因于拓扑，参数数也不等于系统存储。[8]

原始 soft 退化、stage0 后 AttributeError、冻结读出容量失败、V1 绑定失败、reset 失败及修复额外成本全部保留。阶段末恢复到 100% 不证明训练中逐步保持；一次 backend 替换也没有移除所有臂共同保留的几何目标，不能泛化成“所有拓扑机制都无效”。

## 当前科学位置

**已证明，条件限定：**`F_z` 可逆只给局部 sheets。有限覆盖还需要全局条件，例如投影是 proper、满射局部微分同胚且有有限非空纤维；固定次数 monic 复多项式在判别集补集上提供明确实例。比较参数族时，须固定 D、基点和接口，指定整个参数/路径族避奇点，并用共同纤维输运 `τs` 识别 sheets。以映射复合记号，先 a 后 b 为 `σb∘σa`；此时 `ρs(γs)=τs ρ0(γ0) τs⁻¹`。独立重编号只给共轭等价。结构增长须另立合同。[2,3,6]

**已证明/已观察的边界：**固定覆盖类型的安全变形不会因此扩大可实现的 monodromy 作用群。它可能改变候选路径的可达概率、净空、条件数或数值工作量，但这些是另外的命题。保护旧操作还需保护编码、调用、读出；完美 I/X 门配上改变的 router 仍可遗忘旧任务。[4,6,7]

**未知：**过去任务驱动的安全几何变化是否真正帮助未来未知操作获取；效果能否超过普通约束、候选分布适应和数值预条件；能否在多次获取、较大规模和完整成本下持续成立。学得覆盖/构造规则、一般非可逆能力以及更广架构优势也未建立，优先级仍低于前一问。

最强的普通解释已经很具体：共享与坐标压缩节省参数，终端观测表/自动机识别形成操作，绑定 guard 保持旧行为，事件估计/离散搜索跨操作类，缓存减少重复执行。**PGP 必须在这些解释之外提供可测的增量。**

## 唯一建议的下一项调查：过去学得的几何是否改善未来获取？

**待检验假说：**仅依据过去任务学得的安全几何，在不损害旧操作及其任务绑定的前提下，降低独立留出新能力的获取成本；收益不能由普通搜索重参数化或预条件完整解释。先做机制与等价性分析，再决定是否值得执行下述配对试验。本轮不实现、不运行。

1. **先排除代数饱和与精确等价。**固定一个已知有限覆盖及经过认证的同类型参数族，旧库生成真子群 `H`。评估器私下抽取 `ρ(π₁)\H` 中的目标，学习者只获约定的终端反馈，不获目标置换、正确路径或未来标签。D3 的两个换位已经生成 S3，不能再测“群外新操作”。现成 D4 只能从非零 ε、尚未准入 C 的状态开始；其窄安全区间和四候选编译器可能已让问题退化，应先证明存在可区分的因果通路，不盲目放大。
2. **隔离几何的迁移效应。**从同一旧库/控制器出发，仅用过去任务反馈和执行统计学习几何；未来任务揭示前冻结几何。各臂复制相同的记忆、控制器、优化器和纤维标识，再做未来获取。未来任务各自从这一共同旧状态分叉，避免先前未来任务使 H 饱和。若候选随微分同胚协变搬运，类序列可能完全相同；若固定外部坐标提案，才可能改变类的概率质量，必须明确选择并解释。
3. **对照同时允许成功。**比较学得安全几何、冻结初始几何、幅度匹配的安全随机/假适应、固定覆盖上的普通可学习 proposal/预条件，以及同信息的临界回路/程序搜索与 direct/FSM。普通方法获得同一变形的逆映射、几何信息、证书和缓存权限；不能靠禁止合法对手制造收益。数字输出与实际操控连续系统分开比较，操作表的获得不免费。
4. **前瞻冻结预算。**建议 20 对种子（0–19），每种子四个独立留出任务；每任务最多 300 个候选、1,200 次终端反馈、100,000 次 continuation RHS/Jacobian 求值，任一上限先到即停止。过去适应也设同样上限并计费；允许每家族至多四个仅用独立开发集选择的配置，开发成本入账。正式任务分布、采样规则、数值容差和超时规则在执行前锁定，不按测试表现调整。
5. **把发现、执行与总账分开判决。**同一连续执行赛道的首要终点为达到共同成功/保持标准所需的预算截断平均数值工作量；失败按预设截断值处理，另报实际消耗。数字赛道用共同设备的实际时间及各方法操作账比较，不把 FSM 的零 continuation 当成零计算。各赛道均报告成功率、反馈、有效/无效/拒绝候选、首次发现、冷/热执行、旧操作及完整绑定保持、参数和存储。过去适应及证明/维护计入四任务总账，另列不摊销成本；数值工作代理不能单独证明完整成本优势。评价端独立验证整个有限纤维和未用于学习的组合，评价费用单列。以种子为配对统计单位，预设实际意义门槛（例如至少 20% 成本下降），报告区间与失败；改善幅度区间的上界低于 20% 才排除这一预设效应量，跨越门槛记“不确定”。

只优于冻结几何，最多支持此设置中的几何适应效应；普通 proposal/预条件匹配时，不支持拓扑独立收益。只减少已知操作的求解步数，属于执行改进。只有未知操作获取、保持及含适应开销的总账共同改善，才支持这个限定版本的 PGP；仍不建立范式级结论。若静态分析证明首要成本终点也等价，应停止该设置，先找具体新机制；若仅类别序列等价，只关闭发现/样本效率主张，数值成本仍须另行判断。

## 原始证据定位

以下路径均在 [Prometheus-Monodromy-Archive.zip](Prometheus-Monodromy-Archive.zip) 内，根目录为 `Prometheus-Monodromy-Archive/`。缩写仅用于减少重复：`F=.deep-work/2026-10-31T215613-0400-campaign`；`V=.deep-work/2026-10-31T234403-0400-v2`；`T=V/probes/topology-architecture`。`D/C/M/E/R/Q` 分别代表 `originals/documents`、`originals/code`、`originals/mathematics`、`originals/experiments`、`originals/raw-results`、`originals/reviews`；下列 `V/T/F` 须展开。花括号表示并列文件。

1. `D/F/branches/F/{certificate.md,repair-and-attack.md}`；`C/F/probes/F/probe.py`；`E/F/probes/F/{summary.json,cost-accounting.json}`；BF 分析在 `D/F/branches/BF/postfreeze-physical-metric.md`。前驱文档位置见档案 `RESEARCH_HISTORY.md` 的 recovered-Git 附录及对应原件。
2. `M/V/candidates/constraint-computation/{v0.md,root-growth-v1.md,post-execution-certificate.md}`；`C/V/probes/constraint-growth/check_v1.py`；`E/V/probes/constraint-growth/summary.json`。
3. `D/V/final/topology-priority/result.md`；`C/V/probes/topology-acquisition/{pilot_v1.py,certificate.py}`；`E/V/probes/topology-acquisition/{contract-v1.md,summary.json,analysis.json}`；`R/V/probes/topology-acquisition/raw.jsonl`；`M/V/candidates/constraint-computation/root-compositional-acquisition.md`。
4. `M/V/candidates/after012-a/root-retention-boundary.md`；`M/V/candidates/after018-root/root-pullback-closure-bound.md`；`M/V/candidates/topology-return/mobility-root.md`；`M/V/candidates/topology-continual/root-architecture-bridge.md`。
5. `M/V/candidates/topology-return/{quantum-shared-control.md,calibration-observation.md}`；`M/V/candidates/topology-continual/{root-uniform-chart.md,root-uniform-finite-bound.md}`；`D/V/final/topology-continual/result.md`；`E/V/probes/topology-continual/pilot-v1.summary.json`；`R/V/probes/topology-continual/pilot-v1.raw.jsonl`。
6. `E/T/versions/native-v6-method-before-continuous-integration.md`；`C/T/continuous_monodromy.py`（`ConfigurationLoop`、`lift_sequence`）；`D/water/method.md` §§2、5–7、9.2–9.3；`D/V/final/topology-architecture/result.md`；修复来源见 `Q/V/supervision/reviews/review-033-acquisition-repair.md`。
7. `C/T/monodromy_contribution_study.py`；`E/T/runs/n16-monodromy-contribution-v1/learn/summary.json`；对应 `R/T/runs/.../learn/records.jsonl` 的 `raw_proposal_parameter_hash`；`E/T/runs/n16-homotopy-growth-cost-v1a/learn/summary.json`。
8. `C/T/parameter_native_models.py`；`E/T/runs/parameter-n{8,16}-seed0-topology-resumed-consistent/learn/summary.json`；普通分别为 `parameter-n8-seed0-constraint_compact-resumed-consistent`、`parameter-n16-seed0-constraint_compact-full-consistent`；同目录最终 `{topology,constraint_compact}-stage5-step600.pt`。额外种子：`parameter-n{8,16,32}-seed{1,2}-topology-full-consistent/learn/summary.json`；N32/seed0 为 `parameter-n32-seed0-topology-resumed-consistent`。逐步原始日志均在相同 `R/T/runs/<run>/learn/records.jsonl`。检查点核对对象为 `model` 张量的 descriptor/storage；本轮 N16 文件 SHA 分别为 `8b763cbb4fff271c6538981936931a5d4312c32e091263e116ae1e6240e26925`、`6baec458b2961e189b5816483380d473e0919265ae58ddec5b7a607bad489fec`。原失败与旧版 `full`/`resumed` 不与 `consistent` 混同。
9. `C/T/loop_boundary_learning.py`；`M/V/candidates/topology-architecture/loop-acquisition-boundary-rule.md`；`E/T/runs/{parameter-loop-boundary-learning-v1,parameter-hybrid-loop-learning-v1,parameter-hybrid-loop-learning-v2,parameter-hybrid-conventional-controls-v1,parameter-factorized-reset-v1}/learn/result.json`。Hybrid V2：32 事务/716 终端访问/11,526 提升步；普通 chamber/head：15/196/610；program：10/80/610。具体比较范围见 `Q/V/supervision/reviews/review-041-controls-and-reset-acquisition.md`。
10. `D/water/method.md` §§1、3.1–3.13、4；`C/T/continuous_primitive_block_typed_dual_memory_fp64_solve_ex.py`；`E/T/runs/parameter-typed-dual-memory-gpu-execution-v2a/admit/result.json` 中 `optimizer_instantiated=false`、`optimizer_updates=0`。

档案清单、历史版本与缺失材料边界见 `MANIFEST.csv`、`SOURCE_PROVENANCE.md`、`provenance/GIT_VERSION_MAP.jsonl`。本轮结论未依赖重新验证外部文献的新颖性，也未把缺失对话、丢失轨迹或未测 FLOPs/能耗当作已知证据。

# 二阶 SSP 上界的有限矩阵证明

目标是保持 `SSPRK.second_order_rk_ssp_bound` 的原始表述，证明任意实数稠密
$s$ 阶段 RK 系数在二阶条件及四个完整绝对单调性条件下满足 $r\leq 2s$。
这里不假设下三角结构、无环性或系数可对角化。

这条证明保留 V1.6 第 2.4 节的变换、第 2.6 节的矩恒等式和第 3 节的层级能量比较，
把连续时间鞅与停时的部分改写为有限矩阵恒等式。其后的 PH 模块进一步构造实际概率测度，
证明任意正整数阶积分矩，并把该矩阵不等式解释为 PH 方差下界。完整表示等号分类也已完成；
分布层面的最终等价定理仍待汇总。

## 1. 变换与 Green 矩阵

定义

$$
N=I+rA,\qquad M=N^{-1},\qquad P=I-M=rAM,\qquad \omega=rb^TM.
$$

原始假设给出 $P_{ij}\geq0$、$\sum_jP_{ij}\leq1$、$\omega_i\geq0$ 和
$\sum_i\omega_i\leq1$。$I-P=M$ 可逆。

对任意非负整数 $n$，$P^n$ 仍非负且行和至多为 1，因此其所有元素在 $[0,1]$ 中。
有限几何和满足

$$
\sum_{k=0}^{n-1}P^k=(I-P)^{-1}(I-P^n).
$$

右边每个元素的绝对值受 $(I-P)^{-1}$ 对应行的绝对值和的两倍控制。
左边每个元素是非负数的递增部分和，所以逐元素可求和。有限维的乘法连续性和几何和恒等式给出

$$
N=(I-P)^{-1}=\sum_{k=0}^{\infty}P^k\geq0.
$$

对应 `Substochastic.lean` 和 `RKSubstochastic.lean`。这个步骤也覆盖行和恰好为 1 的情况。

## 2. 只依赖状态数的势函数

对于任意非负向量 $m\in\mathbb R^s$，构造 $f\in\mathbb R^s$，使得

$$
0\leq f_i,\qquad m_i^2\leq s f_i,\qquad f_i\leq m_i^2,\qquad
f_i-f_j\leq(m_i-m_j)^2.
$$

直观上，将 0 和所有坐标值排序，$f_i$ 是从 0 到 $m_i$ 的相邻间隔长度平方之和。
Lean 中使用等价的归纳构造，避免依赖排序接口：取最小坐标 $a$，删去该坐标，
将其余坐标减去 $a$ 后应用归纳假设，最后将各个新势函数值加上 $a^2$。

下界所需的 Cauchy 不等式由如下多项式恒等式证明。当 $u^2\leq nv$ 且 $n>0$ 时，

$$
n\bigl((n+1)(a^2+v)-(a+u)^2\bigr)
=(n+1)(nv-u^2)+(u-na)^2\geq0.
$$

空状态集和单状态情形在归纳中单独处理。对应 `VariancePotential.lean`。

## 3. 能量比较

取 $m=N\mathbf1$，于是 $(I-P)m=\mathbf1$。把向量逐坐标平方记作 $m^{\circ2}$，定义

$$
q_i=\sum_jP_{ij}(m_i-m_j)^2+
\left(1-\sum_jP_{ij}\right)m_i^2.
$$

展开平方并使用 $(I-P)m=\mathbf1$，得到

$$
q=2m-(I-P)m^{\circ2},\qquad Nq=2Nm-m^{\circ2}.
$$

势函数的差值界处理每个状态间的跳跃，上界 $f_i\leq m_i^2$ 处理吸收项。
所有系数非负，因此

$$
(I-P)f\leq q.
$$

左乘非负矩阵 $N$ 并使用 $m_i^2\leq sf_i$，得到逐坐标不等式

$$
(s+1)m_i^2\leq2s(Nm)_i.
$$

最后，对非负且总质量不超过 1 的 $\omega$，加权 Cauchy 不等式给出

$$
(\omega m)^2\leq\left(\sum_i\omega_i\right)
\sum_i\omega_i m_i^2\leq\sum_i\omega_i m_i^2.
$$

从而

$$
(s+1)(\omega N\mathbf1)^2\leq2s\,\omega N^2\mathbf1.
$$

这就是二阶上界所需的最小方差不等式的矩阵形式。对应 `PhaseVariance.lean`
和 `PhaseMomentBound.lean`。缺失的初始质量直接由总质量不超过 1 的条件处理，无需除以 $\sigma$。

## 4. 代入 RK 二阶条件

$b^T\mathbf1=1$ 和 $b^TA\mathbf1=1/2$ 给出

$$
\omega N\mathbf1=r,\qquad \omega N^2\mathbf1=r+\frac{r^2}{2}.
$$

因此

$$
(s+1)r^2\leq2s\left(r+\frac{r^2}{2}\right),
\qquad r^2\leq2sr.
$$

由 $r>0$ 得到 $r\leq2s$。对应 `SecondOrder.lean`。
`Radius.lean` 进一步对全部可行参数取上确界，得到完整 SSP 半径的相同上界；
半径定义在扩展非负实数中，允许一般系数的可行参数集无界。

## 5. 达到上界与完整最优值

重复隐式中点法的 $s$ 阶段系数已经证明满足两个阶条件。在 $r=2s$ 时，
记 $L_{ij}=\mathbf1_{j\leq i}$，$S_{ij}=\mathbf1_{i=j+1}$，则

$$
I+2sA=2L,\qquad (I+2sA)^{-1}=\frac12(I-S).
$$

`ChainMatrices.lean` 证明这些有限矩阵的乘法恒等式，`MidpointAttainment.lean`
由显式逆逐项验证完整 SSP 条件，得到该方法的半径恰好为 $2s$。
`SecondOrderOptimality.lean` 对所有二阶表取上确界，完成最优值为 $2s$ 的结论。

`Endpoint.lean` 证明有限正半径的端点可行；`DownwardClosure.lean`
证明可行性传递到所有较小的正参数。等号证明进一步得到 $\sigma=1$，
剩余寿命的全部状态构成等间距层级，且每个正概率跳转只能保持当前状态或下降一层。
由 Green 占据关系逐层证明所有状态可达，得到完整等速链；混合初始质量只能位于最高层。
`PhaseMixtureChain.lean` 实现该表示刚性，`SecondOrderUniqueness.lean`
由逆 RK 变换恢复唯一的中点法系数（允许同时置换阶段）。

## 6. PH 概率测度与积分矩

对一般有限 PH 数据，以速率 $\nu>0$ 统一化，定义

$$
T=\nu(P-I),\qquad G=(I-P)^{-1},\qquad
w_n=\alpha P^n(I-P)\mathbf1.
$$

权重非负且总和为 $\alpha\mathbf1$。`PhaseType.lean` 构造

$$
\mu=(1-\alpha\mathbf1)\delta_0+
\sum_{n\geq0}w_n\operatorname{Gamma}(n+1,\nu),
$$

并证明它是非负半轴上的概率测度。一般非奇异有限子生成元可由
`PhaseTypeUniformization.lean` 转化为这样的表示。

由已证明的阶乘计数矩和 Gamma 密度积分，`PhaseTypeAllMoments.lean`
证明所有自然数次幂可积。对 $k\geq1$，`PhaseTypeGeneratorMoments.lean` 给出

$$
\int x^k\,d\mu(x)=\frac{k!}{\nu^k}\alpha G^k\mathbf1
=k!\alpha(-T)^{-k}\mathbf1.
$$

零阶矩单独为 $1$，包括零点原子。`PhaseTypeVariance.lean` 由第 3 节的不等式推出

$$
\operatorname{Var}_{\mu}(x)\geq\frac{(\int x\,d\mu)^2}{s}.
$$

RK 的情形取 $\alpha=\omega$、$P=I-M$、$\nu=1$。
`RKPhaseType.lean` 证明所构造分布满足

$$
\mathbb E[X]=r,\qquad \mathbb E[X^2]=r^2+2r,\qquad
\operatorname{Var}(X)=2r,
$$

并由实际概率测度的方差下界重新推出 $r\leq2s$。

## 验证边界

证明完成的判据是主定理及其全部依赖没有 `sorry`，默认 `lake build` 成功，
并且主定理仅依赖 Lean 的三个标准公理 `propext`、`Classical.choice`、`Quot.sound`。
具体检查结果记录在 `formalization-status.md`。

已完成二阶上界、达到性、最优值和完整最优系数唯一性，尚未完成三阶最优半径证明。
PH 的生成元 resolvent Laplace 积分公式已经证明。PH 测度与 CTMC 路径吸收时间的等价性、
矩阵指数形式的生存函数/密度公式，
仍是后续工作。不同统一化速率和状态置换定义出同一概率测度的结论已经证明。

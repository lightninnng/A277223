# A277223 最终证明可靠性与形式化审计报告

审计日期：2026-08-17

## 1. 当前可以严格声称什么

数学层面，本项目现在证明的核心结果不再只有 `<12` 分类，而是：

1. **Carry Obstruction 定理**：Good multiplier
   \[
   1,2,3,4,5,6,8,10
   \]
   均不可能是 maximal Good multiplier；
2. **非平凡无限 7 族**：存在显式、两两不同且非尾零缩放得到的无穷多个整数满足 `MaxGood(n,7)`；
3. **非平凡无限 11 族**：同样存在显式无穷多个整数满足 `MaxGood(n,11)`；
4. 作为应用，
   \[
   \boxed{\{a(n):a(n)<12\}=\{0,7,9,11\}.}
   \]

经过当前所有独立算术、局部完备性和参数族审计，**没有发现数学证明中的逻辑冲突或算术反例**。目前判断数学主定理和两个无限族定理均为正确，可靠性高。

必须单独说明：当前执行容器没有 Lean/Lake，因此这仍不是“Lean kernel 已经认证”的状态。数学正确性判断和机器认证状态是两个不同层次。

---

## 2. 为什么 Carry Obstruction 不是对整数的暴力搜索

令

\[
\operatorname{Good}(n,k)\iff s(kn)=k,
\]

并令

\[
m=kn,
\qquad s(m)=k.
\]

若存在整数 witness `(c,j,z)` 满足

\[
ck=j10^z,
\qquad j>k,
\qquad s(cm)=j,
\]

则尾零不改变数位和，故 `j` 也 Good，因而 `k` 不可能 maximal。

有限性的来源是 carry-defect identity，而不是给 `n` 设搜索上界。若

\[
m=\sum_i d_i10^{e_i},
\]

逐列乘以 `c`，记 carry 为 `C_t`，则

\[
\boxed{
\sum_i s(cd_i)-s(cm)=9\sum_t C_{t+1}.
}
\]

因此 witness 失败必由第一次 carry 引起。若所有 `cd_i` 的宽度至多 `w`，第一次 carry 只可能由宽度 `w` 的局部数字窗口产生。这是 first-carry locality。

所以 `8`、`10` 的有限 case 是**全部局部重叠类型**，而不是某个整数区间中的样本。

独立审计从头生成 digit mass 8 和 10 的全部无序数字分拆，得到：

- mass 8：22 个总分拆；含 `>=5` 数字的非平凡型恰好 7 个；
- mass 10：41 个总分拆；“恰好一个高数字”的非平凡型恰好 17 个，其中 15 个 profile-safe，剩且仅剩 `5+4+1` 与 `5+3+2`。

Primary motifs 独立重建为：

```text
k=8 : 16 ; 53 ; 52/12 ; 115
k=10: 54/145 ; 53
```

Secondary exceptional shifts 独立重建为：

```text
8:52  -> offset 2 only
8:12  -> offset 2 only
8:115 -> offsets -1,3 only
10:54 -> none
10:53 -> offset 2 only
```

与论文 obstruction tree 完全一致。

---

## 3. Periodic Crossing 的无限问题为什么只需一次 crossing

定义整数缺陷

\[
\Delta_N(k)=s(kN)-k.
\]

若 `p` Good，则由数位和次可加性

\[
\boxed{\Delta_N(k+p)\le\Delta_N(k).}
\]

因此固定剩余类 `r mod p`，

\[
q\mapsto\Delta_N(pq+r)
\]

单调不增。

只要找到相邻的

\[
\Delta_N(pq_0+r)>0,
\qquad
\Delta_N(p(q_0+1)+r)<0,
\]

整个无限 residue class 中就不可能出现 defect 0。

这一步是无限性证明的关键，因此 7/11 的最终证明都不需要 multiplier 的全局上界。

---

## 4. 通用 aligned periodic-block update

两个无限族共享同一个局部机制。

设

\[
\operatorname{Rep}_{W,d}(M)
\]

表示 `M` 个宽度 `d` 的重复块 `W`。若

\[
0\le i<M,
\quad W<10^d,
\quad W+x<10^d,
\]

则在第 `i` 个对齐块上增加 `x` 只改变该块：

\[
\boxed{
 s\!\left(\operatorname{Rep}_{W,d}(M)+x10^{di}\right)
 =(M-1)s(W)+s(W+x).
}
\]

有短尾块时同样成立。这一 lemma 在论文和 Lean 中都作为 7/11 两个族的共同底层，而不是分别发明两个专用技巧。

---

## 5. 非平凡无限 7 族的审计

定义

\[
M^{(7)}_0=25,
\qquad
M^{(7)}_{t+1}=10^6M^{(7)}_t+925925,
\]

\[
u_t=6t+2,
\qquad
q_t=10^{u_t},
\]

\[
N^{(7)}_t
=\frac{5\cdot10^{6M^{(7)}_t+2}+11}{7}.
\]

递推与 balance

\[
\boxed{27M^{(7)}_t+25=7q_t}
\]

等价。

对六个非零模 7 剩余类，aligned update 后统一得到

\[
\boxed{
\Delta(7(q_t-1)+r)=54t+9>0,
\qquad
\Delta(7q_t+r)=-9<0.
}
\]

并且

\[
\Delta(14)=-9.
\]

所以每个 `t` 都有

\[
\boxed{\operatorname{MaxGood}(N^{(7)}_t,7).}
\]

`t=0` 给出原 152 位例子。

`infinite_family_audit.py` 独立验证递推、balance、局部 residue 数据、endpoint 公式，并直接对第一项做任意精度大整数核对。

---

## 6. 非平凡无限 11 族的审计

最终采用最简 pure-power crossing 族，而不是发现阶段更复杂的重复 `22` crossing。

定义

\[
M^{(11)}_0=12219,
\qquad
M^{(11)}_{t+1}=100M^{(11)}_t+319,
\]

\[
q_t=100^{t+2},
\]

\[
N^{(11)}_t
=\frac{9\cdot10^{2M^{(11)}_t+2}+2}{11}.
\]

balance 为

\[
\boxed{9M^{(11)}_t+29=11q_t.}
\]

对 `1<=r<=10`，周期 residue blocks 为

```text
81,63,45,27,09,90,72,54,36,18
```

全部数位和 9。`2q_t` 只把一个对齐两位块 `W_r` 改成 `W_r+2`；左端 `q_t-1` 额外只把尾块 `T_r` 改成 `T_r-2`。所有 `W_r+2<100`、`T_r>=10`，所以没有隐藏的跨块 carry/borrow。

十个 residue 只分两类：

### A 类：`r notin {5,10}`

\[
\boxed{
\Delta(11(q_t-1)+r)=18t+27>0,
\qquad
\Delta(11q_t+r)=-9<0.
}
\]

### B 类：`r in {5,10}`

\[
\boxed{
\Delta(11(q_t-1)+r)=18t+18>0,
\qquad
\Delta(11q_t+r)=-27<0.
}
\]

所以**十个非零 residue 全部在同一个相邻 quotient**

\[
q_t-1\to q_t
\]

跨越。

零 residue：

\[
22N^{(11)}_t
=18\cdot10^{2M^{(11)}_t+2}+4,
\]

故

\[
\Delta(22)=13-22=-9.
\]

最终：

\[
\boxed{\operatorname{MaxGood}(N^{(11)}_t,11)\quad\forall t\ge0.}
\]

独立 Python 审计对 `t=0,1` 做了直接超大整数乘法/数位和核对，并对大量 `t` 逐项检查 symbolic recurrence、balance 和十个 residue 的 local constants。

### 与 52 位 compact witness 的关系

旧的小例子

\[
N_{11}^{\rm small}=\frac{9\cdot10^{52}+2}{11}
\]

**不是**上述纯幂 crossing 无限族的第一项。它被保留为单独 compact witness。论文现在给出了完整的 10-residue crossing 表，自包含地证明 `a(N11small)=11`；Lean `Eleven.lean` 也有对应固定例子定理。

---

## 7. Exact spectrum below 12

Carry Obstruction 排除

\[
1,2,3,4,5,6,8,10.
\]

剩余四个值内部实现为：

- `0`: `n=62`；
- `7`: compact 152 位 witness，且实际上存在上述非平凡无限族；
- `9`: `n=1`；
- `11`: compact 52 位 witness，且实际上也存在上述非平凡无限族。

所以

\[
\boxed{\{a(n):a(n)<12\}=\{0,7,9,11\}.}
\]

---

## 8. 本轮实际执行的独立审计

当前在容器中实际运行并通过：

```text
scripts/generate_carry_certificates.py
scripts/arithmetic_audit.py            -> AUDIT_OK
scripts/infinite_family_audit.py       -> INFINITE_FAMILY_AUDIT_OK
scripts/static_lean_audit.py           -> STATIC_LEAN_AUDIT_OK
LaTeX build                            -> success
PDF preflight/render                   -> final gate performed at packaging
```

当前 static Lean audit 检查：

- 16 个 Lean modules；
- 本地 imports 无缺失、无环；
- 无 `sorry/admit/axiom`；
- 无 `native_decide/unsafe/run_tac/implemented_by/addDeclWithoutChecking/ofReduceBool`；
- toolchain 固定 Lean 4.32.2；
- Mathlib 固定 v4.32.2。

困难有限证书通过显式 `decide +kernel` 作为 intended verification path；生成器不属于信任边界。

---

## 9. Lean 机器认证状态

这一点必须保持严格：**当前容器没有 `lean`、`lake`、`elan`。**

因此当前已经完成的是：

- 数学证明闭合；
- Lean theorem dependency 完整；
- 无 placeholder；
- 数学/证书/导入/信任边界静态审计通过。

当前尚未完成的是：

- 真正的 Lean elaboration；
- `lake build`；
- `leanchecker`；
- `nanoda`。

所以现在不能写：

> formally verified / kernel-certified in Lean 4.

只能写：

> accompanied by a Lean 4 formalization whose final kernel-certification gate is configured and pending a green pinned CI build.

`compile_audit.sh` 在完成所有不依赖 Lean 的 audit 后，真实停在

```text
ERROR: lean not found; elaboration/kernel check not started
exit code 127
```

这不是 theorem 编译错误，也不是编译成功，而是本环境没有启动 elaborator。

---

## 10. 可靠性结论

### 数学层

**高可信，当前未发现漏洞。**

尤其此前最危险的三个方面已经独立闭合：

1. Carry Obstruction 的 case 完备性；
2. 7/11 residue crossing 的无限性推理；
3. 两个 parameterized family 的 recurrence/balance/local-block 公式。

### Lean 源码层

**结构和 trust boundary 审计通过，但没有真实编译。**

新 family modules 还必须由真实 Lean 4.32.2 + Mathlib v4.32.2 elaborator 接受后，才能升级认证等级。

### 投稿放行标准

只有以下全部满足后，论文才能声称 machine-checked：

1. certificate regeneration clean；
2. `AUDIT_OK`；
3. `INFINITE_FAMILY_AUDIT_OK`；
4. `lake build` green；
5. `leanchecker` green；
6. `nanoda` green, `nanoda-allow-sorry=false`；
7. 论文 theorem map 与该 green commit 逐项一致。

在此之前，最严谨的表述是：**数学证明已完成并经多层独立审计；Lean 形式化源码已完整嵌入，但机器内核认证仍待真实 CI。**

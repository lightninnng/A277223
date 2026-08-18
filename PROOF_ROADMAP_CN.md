# A277223 完整证明路线（中文审计版）

本文档只保留最终证明依赖，不记录发现阶段的全局搜索、旧反例或试探性自动机。

目标是证明：若 `MaxGood n k` 且 `k < 12`，则

\[
k\in\{0,7,9,11\},
\]

并证明四个值都确实可以取到。论文中的 `a(n)` 因而满足

\[
\{a(n):a(n)<12\}=\{0,7,9,11\}.
\]

---

## 0. 基础定义

记十进制数位和为

\[
s(x).
\]

定义

\[
\operatorname{Good}(n,k)\iff s(kn)=k,
\]

以及

\[
\operatorname{MaxGood}(n,k)
\iff
\operatorname{Good}(n,k)\land
\forall j\, (\operatorname{Good}(n,j)\Rightarrow j\le k).
\]

Lean：`A277223/Basic.lean`。

这样不需要预先定义“最大值函数”并证明最大值一定存在。

基础引理：

1. `digitSum10_pow_mul`：
   \[
   s(10^t x)=s(x).
   \]
2. `digitSum10_append`：若 \(x<10^w\)，
   \[
   s(x+10^w y)=s(x)+s(y).
   \]
3. `digitSum10_add_le`：
   \[
   s(x+y)\le s(x)+s(y).
   \]
4. `maxGood_pow_mul_iff`：
   \[
   \operatorname{MaxGood}(10^t n,k)
   \iff
   \operatorname{MaxGood}(n,k).
   \]

---

# 模块 I：Carry Obstruction

## 1. Decimal Rescaling

假设 \(k\) Good，令

\[
m=kn,
\qquad s(m)=k.
\]

若存在正整数 \(c,j\) 和 \(z\ge0\)，满足

\[
j>k,
\qquad
ck=j10^z,
\qquad
s(cm)=j,
\]

则

\[
cm=ckn=j10^zn,
\]

故

\[
s(jn)=s(j10^zn)=s(cm)=j.
\]

因此 \(j\) 也是 Good，并且 \(j>k\)。所以 \(k\) 不可能是 MaxGood。

Lean：

- `RescalingWitness`
- `larger_good_of_witness`
- `not_maxGood_of_carryObstruction`

文件：`A277223/CarryObstruction/Theory.lean`。

---

## 2. Carry-defect identity

把

\[
m=\sum_i d_i10^{e_i},\qquad 1\le d_i\le9
\]

看成若干十进制“数字原子”。固定整数 \(c\)。写

\[
cd=\sum_{u\ge0}P_c(d,u)10^u.
\]

在真正传播 carry 之前，第 \(t\) 列的原始负载为

\[
L_t=\sum_iP_c(d_i,t-e_i).
\]

令传入第 \(t\) 列的 carry 为 \(C_t\)，输出数字为 \(E_t\)：

\[
L_t+C_t=E_t+10C_{t+1},\qquad C_0=0.
\]

对所有列求和：

\[
\boxed{
\sum_i s(cd_i)-s(cm)=9\sum_{t\ge0}C_{t+1}.
}
\]

因此：

- carry 只能降低数位和；
- 每单位 carry 恰好造成 9 的 digit-sum loss；
- 完全无 carry 当且仅当
  \[
  s(cm)=\sum_i s(cd_i).
  \]

这就是 Carry Obstruction 的机制核心。

论文：Theorem “Carry-defect identity”。

Lean 的底层证书通过真实 schoolbook carry 状态验证同一语义，见 `Certificate.lean` 中 `runLane_correct`。

---

## 3. First-carry locality

若每个 \(cd_i\) 最多占 \(w\) 位，则原子 \(d_i10^{e_i}\) 只能影响

\[
e_i,e_i+1,\dots,e_i+w-1.
\]

假设第一次 carry 出现在列 \(t\)。因为此前没有 carry，故 \(C_t=0\)，于是

\[
L_t\ge10.
\]

能够参与该列的输入数字只能满足

\[
t-w+1\le e_i\le t.
\]

所以任何 witness 的失败都由一个有限宽度的局部 motif 引起。

这解释了为什么最终出现的 `16`、`53`、`52`、`12`、`115`、`145`、`253` 等不是经验 case，而是 first-carry locality 的全部局部 obstruction。

---

## 4. Profile-safe criterion

对于 digit multiset \(\lambda=(d_1,\dots,d_r)\)，固定 \(c\)。定义一列中所有可能的最大原始负载

\[
M_c(\lambda).
\]

由于不同输入数字位于不同指数，其对同一输出列贡献的 profile offset 必须不同。

若

\[
M_c(\lambda)\le9
\]

且

\[
\sum_i s(cd_i)=j,
\]

则任何数字位置安排都不会产生第一次 carry，因而

\[
s(cm)=j.
\]

所以 `(c,j,z)` 是统一 rescaling witness。

---

# 5. 排除 1--6

## 5.1 k=1,2,3,4

若 \(s(m)=k\le4\)，则每个数字 \(d\le4\)。乘 2 时

\[
2d\le8,
\]

逐位完全无 carry：

\[
s(2m)=2s(m)=2k.
\]

因此 Good \(k\) 强迫 Good \(2k>k\)。

Lean：`carryObstruction_of_pos_le_four`。

## 5.2 k=5

若所有 digit \(\le4\)，仍由乘 2 得 Good 10。

否则出现 digit 5；总 digit mass 只有 5，因此

\[
m=5\cdot10^e.
\]

取

\[
(c,j,z)=(18,9,1),
\]

因为

\[
18\cdot5=9\cdot10.
\]

于是 Good 9。

Lean：`carryObstruction_five`。

## 5.3 k=6

若所有 digit \(\le4\)，乘 2 得 Good 12。

若出现 digit 6，则

\[
m=6\cdot10^e,
\]

取 `(15,9,1)`。

剩余唯一高数字 partition 为

\[
5+1,
\]

所以

\[
m=5\cdot10^e+10^f,\qquad e\ne f.
\]

取 `(25,15,1)`：基本块为 125 和 25。相邻两种重叠分别产生 375、2625；更远则分块，因此数位和始终为 15。

Lean：`carryObstruction_six` 和 `digitSum10_125_25_distinct`。

结论：

\[
a(n)\notin\{1,2,3,4,5,6\}.
\]

---

# 6. 排除 k=8

令 \(s(m)=8\)。

如果所有 digits \(\le4\)，乘 2 得 Good 16。

否则 digit partition 只有

\[
8,
7+1,
6+2,
6+1+1,
5+3,
5+2+1,
5+1+1+1.
\]

## 6.1 直接安全分支

- `8`：`(1125,9,3)`；
- `7+1`：`(15,12,1)`；
- `6+2`：`(15,12,1)`。

## 6.2 6+1+1

根 witness `(25,20,1)`：

\[
25\cdot6=150,
\qquad25\cdot1=25.
\]

唯一可能的首次 overload 为 \(5+5=10\)，对应输入 motif `16`。

若无 `16`，Good 20。

若出现 `16`，整体写成

\[
m=16\cdot10^a+10^b,
\qquad b\notin\{a,a+1\}.
\]

换 `(125,10,2)`：

\[
125\cdot16=2000,
\qquad125\cdot1=125,
\]

所有允许位置无 carry，数位和 10。

## 6.3 5+3

根 `(25,20,1)`，profiles `125,75`。
唯一首次 motif 为 `53`。

异常时 \(m=53\cdot10^a\)。取 `(2125,17,3)`：

\[
2125\cdot53=112625,
\qquad s(112625)=17.
\]

## 6.4 5+2+1

根 `(25,20,1)`，profiles `125,50,25`。
唯一首次 motifs：

\[
52,\qquad12.
\]

### 52 分支

使用 `(2125,17,3)`；其二块为

\[
110500,
\qquad2125.
\]

考虑合法相对位移后，唯一失败 offset 为 2，即输入 motif `152`。

最终：

\[
125\cdot152=19000,
\quad s=10.
\]

### 12 分支

使用 `(2250,18,3)`：

\[
2250\cdot12=27000,
\qquad2250\cdot5=11250.
\]

唯一失败 offset 为 2，即 `512`。

最终：

\[
125\cdot512=64000,
\quad s=10.
\]

## 6.5 5+1+1+1

根 `(45,36,1)`：

\[
45\cdot5=225,
\qquad45\cdot1=45.
\]

唯一可能 overload 为

\[
2+4+5=11,
\]

对应 motif `115`。

二级 `(375,30,2)`：

\[
375\cdot115=43125,
\qquad375\cdot1=375.
\]

排除已经被 `115` 占据的相对位置后，仅剩两个异常 offset：

\[
-1,\qquad3,
\]

对应

\[
1151,
\qquad1115.
\]

最终：

\[
1750\cdot1151=2014250,
\quad s=14,
\]

\[
2750\cdot1115=3066250,
\quad s=22.
\]

因此任何 Good 8 都强迫某个更大 Good multiplier。

\[
\boxed{a(n)\ne8.}
\]

Lean：`CarryObstruction/Eight.lean` 是由通用 schoolbook-carry soundness theorem 检查的 mass-8 proof-carrying certificate。该证书不是遍历整数 \(n\)，而是覆盖任意数位和为 8 的 decimal digit list。

---

# 7. 排除 k=10

Good 10 等价于

\[
s(10n)=s(n)=10.
\]

所以直接研究 \(n\) 的 digit partition。

若全部 digits \(\le4\)，乘 2 得 Good 20。

若至少两个 digits \(\ge5\)，总和为 10 强迫 partition `5+5`；乘 12 得两个 60 块，因此 Good 12。

只剩恰好一个 digit \(\ge5\)。全部 17 个 partitions 中，15 个由 profile-safe family 一次覆盖：

- `c=12`: `9+1`, exact max load 9;
- `c=13`: `8+2` (7), `8+1+1` (5);
- `c=15`: `7+3`, `7+2+1`, `6+4`, `6+2+2`，均为 9；
- `c=21`: `7+1^3` (9), `6+1^4` (8), `5+2+2+1` (9), `5+2+1^3` (9), `5+1^5` (7);
- `c=22`: `6+3+1` (9), `6+2+1+1` (7), `5+3+1+1` (9)。

仅剩两个 genuine carry partitions。

## 7.1 5+4+1

根 `c=21`，profiles

\[
105,84,21.
\]

首次 motifs 仅

\[
54,\qquad145.
\]

- `54`: 用 `c=24`，二块为 1296 和 24；所有合法位置安全，Good 24。
- `145`: \(12\cdot145=1740\)，Good 12。

## 7.2 5+3+2

根 `c=21`，profiles

\[
105,63,42.
\]

唯一首次 motif `53`。

二级 `c=24`：

\[
24\cdot53=1272,
\qquad24\cdot2=48.
\]

唯一异常 offset 2，即 `253`。

最终：

\[
12\cdot253=3036,
\quad s=12.
\]

所以

\[
\boxed{a(n)\ne10.}
\]

Lean：`CarryObstruction/Ten.lean` 为同一 generic carry semantics 的 mass-10 certificate。

---

# 8. Carry Obstruction 总结论

定义

\[
F=\{1,2,3,4,5,6,8,10\}.
\]

对任意 \(k\in F\)，

\[
\operatorname{Good}(n,k)
\Longrightarrow
\exists j>k,\operatorname{Good}(n,j).
\]

所以

\[
\boxed{
\operatorname{MaxGood}(n,k)\Longrightarrow k\notin F.
}
\]

Lean：`carryObstruction_of_forbiddenSmall`、`forbiddenSmall_not_maxGood`。

---

# 模块 II：Periodic Crossing

## 9. Defect monotonicity

定义整数缺陷

\[
\Delta_N(k)=s(kN)-k.
\]

若 \(p\) Good，则 \(s(pN)=p\)。由数位和次可加性：

\[
\begin{aligned}
\Delta_N(k+p)
&=s(kN+pN)-(k+p)\\
&\le s(kN)+s(pN)-k-p\\
&=\Delta_N(k).
\end{aligned}
\]

因此固定 residue \(r\)：

\[
q\mapsto\Delta_N(pq+r)
\]

单调不增。

Lean：

- `defect_add_period_le`
- `defect_residue_succ_le`
- `defect_residue_le_of_le`

文件：`PeriodicCrossing/Defect.lean`。

---

## 10. Crossing criterion

若：

1. \(p>0\) 且 \(p\) Good；
2. \(\Delta_N(2p)<0\)；
3. 每个 \(1\le r<p\) 存在 \(q_r\)，满足
   \[
   \Delta_N(pq_r+r)>0,
   \]
   \[
   \Delta_N(p(q_r+1)+r)<0,
   \]

则 \(p\) 是唯一正 Good multiplier。

理由：每个 residue class 的 defect 单调不增，而相邻两个点已经从严格正跳到严格负，故不可能取 0。

这一步彻底取消了旧证明中的全局 \(k\) 上界。

Lean：`unique_good_of_crossings`、`maxGood_of_crossings`。

---

## 11. Periodic-block normal form

定义

\[
\mathcal B_{W,d}^{(0)}(H)=H,
\]

\[
\mathcal B_{W,d}^{(M+1)}(H)
=W+10^d\mathcal B_{W,d}^{(M)}(H),
\]

以及

\[
\operatorname{Rep}_{W,d}(M)=\mathcal B_{W,d}^{(M)}(0).
\]

若 \(W<10^d\)，则

\[
s(\mathcal B_{W,d}^{(M)}(H))
=M s(W)+s(H).
\]

假设

\[
pQ+1=10^d,
\qquad
pC=A10^t+B.
\]

构造

\[
N=C+10^t\operatorname{Rep}_{AQ,d}(M).
\]

第一个 telescoping identity：

\[
p\operatorname{Rep}_{AQ,d}(M)+A
=A10^{dM}.
\]

于是

\[
\boxed{pN=A10^{dM+t}+B.}
\]

对于 residue \(r\)，写

\[
rA=ph_r+a_r,
\qquad
rC=h_r10^t+T_r.
\]

第二个 telescoping identity：

\[
r\operatorname{Rep}_{AQ,d}(M)+h_r
=h_r10^{dM}+\operatorname{Rep}_{a_rQ,d}(M).
\]

因此：

\[
(pq+r)N
=(Aq+h_r)10^{dM+t}
+10^t\operatorname{Rep}_{a_rQ,d}(M)
+(Bq+T_r).
\]

若 \(M=S+1\)，令

\[
W_r=a_rQ,
\quad
H_{q,r}=Aq+h_r,
\quad
L_{q,r}=W_r10^t+Bq+T_r,
\]

则

\[
(pq+r)N
=L_{q,r}+10^{d+t}\mathcal B_{W_r,d}^{(S)}(H_{q,r}).
\]

当

\[
W_r<10^d,
\qquad
L_{q,r}<10^{d+t},
\]

得到精确 digit-sum normal form：

\[
\boxed{
s((pq+r)N)
=s(L_{q,r})+S s(W_r)+s(H_{q,r}).
}
\]

Lean：`PeriodicCrossing/Blocks.lean`。

---

# 12. 构造 MaxGood = 7

取

\[
p=7,
Q=142857,
A=5,
B=11,
C=73,
d=6,
M=25,
t=2.
\]

满足

\[
7\cdot142857+1=10^6,
\]

\[
7\cdot73=5\cdot100+11.
\]

定义

\[
N_7
=73+100\operatorname{Rep}_{714285,6}(25)
=\frac{5\cdot10^{152}+11}{7}.
\]

于是

\[
7N_7=5\cdot10^{152}+11,
\]

故 Good 7。

对于 \(r=1,\ldots,6\)，对应 \(W_r\) 为

\[
714285,
428571,
142857,
857142,
571428,
285714,
\]

全部满足

\[
s(W_r)=27.
\]

24 个固定中间块贡献

\[
24\cdot27=648.
\]

代入 normal form 后，所有非零 residues 统一满足：

\[
\boxed{
\Delta_{N_7}(7\cdot99+r)=9,
}
\]

\[
\boxed{
\Delta_{N_7}(7\cdot100+r)=-9.
}
\]

零 residue：

\[
\Delta_{N_7}(7)=0,
\qquad
\Delta_{N_7}(14)=-9.
\]

由 Crossing criterion：

\[
\boxed{
\operatorname{Good}(N_7,k),\ k>0
\iff k=7.
}
\]

所以

\[
\boxed{\operatorname{MaxGood}(N_7,7).}
\]

Lean：`PeriodicCrossing/Seven.lean`。

---

# 13. 构造 MaxGood = 11

取

\[
p=11,
Q=9,
A=9,
B=2,
C=82,
d=2,
M=25,
t=2.
\]

满足

\[
11\cdot9+1=100,
\]

\[
11\cdot82=9\cdot100+2.
\]

定义

\[
N_{11}
=82+100\operatorname{Rep}_{81,2}(25)
=\frac{9\cdot10^{52}+2}{11}.
\]

于是

\[
11N_{11}=9\cdot10^{52}+2,
\]

故 Good 11。

非零 residue 中 \(W_r\) 为

\[
81,63,45,27,9,90,72,54,36,18,
\]

全部满足

\[
s(W_r)=9.
\]

固定中间块贡献

\[
24\cdot9=216.
\]

取 crossing quotient：

\[
q_1=q_2=22,
\qquad
q_r=21\quad(3\le r\le10).
\]

左端 defect：

- residues 3,8 为 18；
- 其余均为 9。

右端 defect：

- residues 2,8 为 -18；
- 其余均为 -9。

因此每个非零 residue 都有严格正到严格负的相邻 crossing。

零 residue：

\[
\Delta_{N_{11}}(11)=0,
\qquad
\Delta_{N_{11}}(22)=-9.
\]

所以

\[
\boxed{
\operatorname{Good}(N_{11},k),\ k>0
\iff k=11,
}
\]

即

\[
\boxed{\operatorname{MaxGood}(N_{11},11).}
\]

Lean：`PeriodicCrossing/Eleven.lean`。

---

# 14. 非平凡无限族：MaxGood = 7

旧的 152 位整数不再承担“孤立反例”的结构负担。定义

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

以及

\[
N^{(7)}_t
=73+10^2\operatorname{Rep}_{714285,6}(M^{(7)}_t).
\]

递推等价于精确平衡

\[
\boxed{27M^{(7)}_t+25=7q_t.}
\]

周期伸缩恒等式给出

\[
7N^{(7)}_t
=5\cdot10^{6M^{(7)}_t+2}+11,
\]

故 7 对每个族成员都 Good。

对任意非零剩余类 \(1\le r\le6\)，周期正规形的低位部分包含 \(M_t\) 个固定六位块

\[
W_r\in\{714285,428571,142857,857142,571428,285714\},
\]

且全部满足

\[
s(W_r)=27,
\qquad
s(W_r+11)=29.
\]

因为

\[
11q_t=10^2\bigl(11\cdot10^{6t}\bigr),
\]

它只把重复串中的第 \(t\) 个六位块从 \(W_r\) 改为 \(W_r+11\)。
`AlignedUpdate.lean` 把这一“只改单块、无跨块进位”抽象成通用定理。

结合有限 residue 恒等式，得到对所有 \(r=1,\dots,6\)：

\[
\boxed{
\Delta_{N^{(7)}_t}\bigl(7(q_t-1)+r\bigr)=54t+9>0,
}
\]

\[
\boxed{
\Delta_{N^{(7)}_t}(7q_t+r)=-9<0.
}
\]

零剩余类又有

\[
\Delta_{N^{(7)}_t}(14)=-9.
\]

由 Crossing Criterion：

\[
\boxed{\operatorname{MaxGood}(N^{(7)}_t,7)\quad(t\ge0).}
\]

其中 \(t=0\) 正是原来的 152 位例子。

Lean：

- `M7Family_balance`
- `N7Family_crossing_left`
- `N7Family_crossing_right`
- `N7Family_maxGood`
- `N7Family_injective`
- `infinitely_many_maxGood_seven`

文件：`PeriodicCrossing/SevenFamily.lean`。

---

# 15. 非平凡无限族：MaxGood = 11

为了避免 52 位 compact witness 看起来像 magic number，另构造一个具有统一纯十进制 crossing 的无限族。

定义

\[
M^{(11)}_0=12219,
\qquad
M^{(11)}_{t+1}=100M^{(11)}_t+319,
\]

\[
q_t=100^{t+2}=10^{2t+4},
\]

\[
N^{(11)}_t
=82+10^2\operatorname{Rep}_{81,2}(M^{(11)}_t).
\]

递推恰好保证

\[
\boxed{9M^{(11)}_t+29=11q_t.}
\]

并且

\[
11N^{(11)}_t
=9\cdot10^{2M^{(11)}_t+2}+2,
\]

故 11 Good。

对 \(1\le r\le10\)，写

\[
9r=11h_r+a_r,
\qquad
82r=100h_r+T_r,
\qquad
W_r=9a_r.
\]

十个重复块是

\[
81,63,45,27,09,90,72,54,36,18,
\]

全部数位和为 9。

因为

\[
2q_t=10^2\bigl(2\cdot10^{2(t+1)}\bigr),
\]

它恰好在重复的两位块串中把一个对齐块 \(W_r\) 改为 \(W_r+2\)。所有 \(W_r+2<100\)，因此没有跨块 carry。左端 \(q_t-1\) 只额外把尾块 \(T_r\) 改为 \(T_r-2\)，而全部 \(T_r\ge10\)，不会向周期区借位。

局部 residue 算术只产生两类：

- 若 \(r\notin\{5,10\}\)：
  \[
  \Delta(11(q_t-1)+r)=18t+27>0,
  \qquad
  \Delta(11q_t+r)=-9<0;
  \]
- 若 \(r\in\{5,10\}\)：
  \[
  \Delta(11(q_t-1)+r)=18t+18>0,
  \qquad
  \Delta(11q_t+r)=-27<0.
  \]

所以十个非零 residue **全部在同一相邻 quotient**

\[
q_t-1\longrightarrow q_t
\]

跨越零点。

零剩余类：

\[
22N^{(11)}_t
=18\cdot10^{2M^{(11)}_t+2}+4,
\]

故

\[
\Delta(22)=13-22=-9.
\]

于是

\[
\boxed{\operatorname{MaxGood}(N^{(11)}_t,11)\quad(t\ge0).}
\]

Lean：

- `M11Family_balance`
- `N11Family_local_data`
- `N11Family_crossing_left`
- `N11Family_crossing_right`
- `N11Family_maxGood`
- `N11Family_injective`
- `infinitely_many_maxGood_eleven`

文件：`PeriodicCrossing/ElevenFamily.lean`。

注意：原 52 位

\[
N_{11}^{\rm small}=\frac{9\cdot10^{52}+2}{11}
\]

仍保留为独立 compact witness，由 `Eleven.lean` 的固定 residue crossing 完整证明；它**不是**上述 pure-power 无限族的第一项。

---

# 16. 实现 9

取 \(n=1\)。

Good 条件为

\[
s(k)=k.
\]

所有一位正整数满足；若 \(k\ge10\)，写

\[
k=10q+r,
\quad q>0.
\]

则

\[
s(k)=s(q)+r\le q+r<10q+r=k.
\]

所以最大 Good 为 9：

\[
\boxed{\operatorname{MaxGood}(1,9).}
\]

Lean：`one_maxGood_nine`。

---

# 17. 实现 0

取 \(n=62\)。假设存在正 Good \(k\)：

\[
s(62k)=k.
\]

模 9：

\[
62k\equiv k\pmod9,
\]

故

\[
61k\equiv0\pmod9.
\]

由于 \(61\) 与 9 互素：

\[
9\mid k.
\]

令 \(L\) 为 \(62k\) 的十进制位数。则

\[
k=s(62k)\le9L.
\]

若 \(L\ge5\)：

\[
62k\le558L<10^{L-1},
\]

与 \(L\) 位正整数至少为 \(10^{L-1}\) 矛盾。

故 \(L\le4\)，于是 \(k\le36\)。结合 \(9\mid k\)，只剩

\[
9,18,27,36.
\]

直接：

\[
s(558)=18,
\quad
s(1116)=9,
\quad
s(1674)=18,
\quad
s(2232)=9.
\]

均不 Good。

所以没有正 Good multiplier：

\[
\boxed{\operatorname{MaxGood}(62,0).}
\]

Lean：`sixtyTwo_maxGood_zero`。

---

# 18. 最终分类

若

\[
\operatorname{MaxGood}(n,k),
\qquad k<12,
\]

则候选只有 \(0,1,\dots,11\)。

Carry Obstruction 排除

\[
1,2,3,4,5,6,8,10.
\]

所以

\[
k\in\{0,7,9,11\}.
\]

反向实现性由

\[
62,\quad N_7,\quad1,\quad N_{11}
\]

分别给出。

最终：

\[
\boxed{
(k<12\land\exists n\,\operatorname{MaxGood}(n,k))
\iff
k\in\{0,7,9,11\}.
}
\]

Lean：`small_value_spectrum_iff`。

---

# 19. 缩放无限族

因为

\[
s(10^tx)=s(x),
\]

整个 Good multiplier 集合在

\[
n\mapsto10^tn
\]

下不变。

因此对所有 \(t\ge0\)：

\[
\operatorname{MaxGood}(62\cdot10^t,0),
\]

\[
\operatorname{MaxGood}(N_7\cdot10^t,7),
\]

\[
\operatorname{MaxGood}(10^t,9),
\]

\[
\operatorname{MaxGood}(N_{11}\cdot10^t,11).
\]

Lean：`scaled_small_values_realized`。

---

# 20. Lean 信任边界

最终正式声称“形式化认证”需要同时满足：

1. `lake build` 成功；
2. generated carry certificates 重生成后 `git diff` 为空；
3. `arithmetic_audit.py` 输出 `AUDIT_OK`，且 `infinite_family_audit.py` 输出 `INFINITE_FAMILY_AUDIT_OK`；
4. 无 `sorry` / `admit` / 自定义 `axiom`；
5. `leanchecker` 成功；
6. `nanoda` 成功且 `nanoda-allow-sorry: false`。

当前生成环境没有 Lean/Lake，因此本快照虽然已经包含完整 intended proof source 和所有 concrete certificates，但在 CI 变绿前必须表述为：

> 数学证明闭合；Lean repo 已构建完整证明依赖并无占位符，但尚待 pinned toolchain 实际编译认证。

这也是 `FORMALIZATION_STATUS.md` 的正式状态说明。

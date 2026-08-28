# Carry Obstructions and Infinite Periodic Crossings for OEIS A277223

![CI](https://github.com/lightninnng/A277223/actions/workflows/lean.yml/badge.svg)
![Lean 4.32.2](https://img.shields.io/badge/Lean-4.32.2-blue)
![Mathlib v4.32.2](https://img.shields.io/badge/Mathlib-v4.32.2-orange)

Manuscript, Lean 4 formalization, and reproducibility checks for a decimal
digit-sum multiplier problem underlying [OEIS A277223](https://oeis.org/A277223).

**Manuscript** [`paper/main.pdf`](paper/main.pdf) · **LaTeX source** [`paper/main.tex`](paper/main.tex) · **Trust model** [`VERIFICATION.md`](VERIFICATION.md)

---

## The problem

For a positive integer $n$, let $s(x)$ denote the decimal digit sum, and define

$$
\operatorname{Good}(n,k) \;\iff\; s(kn) = k,
\qquad
\operatorname{MaxGood}(n,k) \;\iff\; \operatorname{Good}(n,k) \text{ and } \operatorname{Good}(n,j) \Rightarrow j \le k .
$$

Equivalently, if $a(n)$ is the largest positive Good multiplier of $n$
(or $0$ when none exists), then $\operatorname{MaxGood}(n,k) \iff a(n) = k$.

## Main theorem

The exact spectrum of maximal Good multipliers below $12$ is

$$
\bigl(k < 12 \ \wedge\ \exists n,\ \operatorname{MaxGood}(n,k)\bigr)
\ \iff\ k \in \{0,\; 7,\; 9,\; 11\},
\qquad\text{ i.e. }\qquad
\{\, a(n) : a(n) < 12 \,\} = \{0, 7, 9, 11\}.
$$

The values $7$ and $11$ are realized by **explicit infinite families**;
distinct members of a family are never related by multiplication by a
positive power of $10$.

| $k$ | $0$ | $7$ | $9$ | $11$ | $1$–$6,\,8,\,10$ |
|---|---|---|---|---|---|
| realized by | $n = 62$ | $N_7(t)$ for all $t$ | $n = 1$ | $N_{11}(t)$ for all $t$ | never (carry obstruction) |

---

## Mathematical structure

The proof has two independent structural components.

### 1 · Carry obstruction

If $m = kn$ and a decimal rescaling satisfies

$$
c \cdot k = j \cdot 10^{z},
\qquad j > k,
\qquad s(c \cdot m) = j,
$$

then $j$ is a larger Good multiplier for the same $n$. An exact
carry-defect identity and first-carry localization reduce the small cases
to finite local digit configurations, which excludes

$$
k \in \{1, 2, 3, 4, 5, 6, 8, 10\}
$$

as maximal Good multipliers. The manuscript gives a human-checkable
obstruction tree; for $k = 8$ and $k = 10$, Lean verifies the same
conclusion independently through exact schoolbook-multiplication
certificates over arbitrary decimal digit strings of total digit mass $8$
and $10$.

### 2 · Periodic crossing

For fixed $N$ define the defect $\Delta_N(k) = s(kN) - k$. If $p$ is Good,
digit-sum subadditivity implies

$$
\Delta_N(k + p) \;\le\; \Delta_N(k),
$$

so every residue-class sequence modulo $p$ is antitone. A strict adjacent
positive-to-negative crossing in each nonzero residue class, together with
a negative second point in the zero residue class, proves that $p$ is the
unique positive Good multiplier. This mechanism produces the two
parameterized families in `PeriodicCrossing/SevenFamily.lean` and
`PeriodicCrossing/ElevenFamily.lean`.

---

## Infinite families

**The seven family.** For $t \ge 0$ define

$$
M_7(0) = 25,
\qquad
M_7(t+1) = 10^{6} \, M_7(t) + 925\,925,
\qquad
N_7(t) = \frac{5 \cdot 10^{\,6 M_7(t) + 2} + 11}{7}.
$$

Then $\operatorname{MaxGood}\bigl(N_7(t),\, 7\bigr)$ for every $t$; the first
member is the $152$-digit witness

$$
N_7(0) = \frac{5 \cdot 10^{152} + 11}{7}.
$$

**The eleven family.** For $t \ge 0$ define

$$
M_{11}(0) = 12\,219,
\qquad
M_{11}(t+1) = 100 \, M_{11}(t) + 319,
\qquad
N_{11}(t) = \frac{9 \cdot 10^{\,2 M_{11}(t) + 2} + 2}{11}.
$$

Then $\operatorname{MaxGood}\bigl(N_{11}(t),\, 11\bigr)$ for every $t$. The
compact $52$-digit witness

$$
\frac{9 \cdot 10^{52} + 2}{11}
$$

is included as a separate explicit example (it is not a member of the
pure-power family above).

---

## Repository layout

```text
A277223/
  Basic.lean                    digit sums, Good / MaxGood definitions
  CarryObstruction/
    Theory.lean                 structural obstruction for k ≤ 6
    Certificate.lean            packed certificates + soundness theorem
    EightData.lean, Eight.lean  kernel-checked k = 8 machine (7608 states)
    TenData.lean,   Ten.lean    kernel-checked k = 10 machine (1543 states)
    Small.lean                  unified exclusion of the forbidden values
  PeriodicCrossing/
    Defect.lean, Blocks.lean    defect antitonicity, block normal form
    AlignedUpdate.lean          generic repeated-block update lemma
    Seven.lean,   SevenFamily.lean    the infinite seven family
    Eleven.lean, ElevenFamily.lean    the infinite eleven family
  Witnesses.lean                n = 62 and n = 1 spectrum endpoints
  Main.lean                     assembly: full spectrum + infinitude
paper/                          manuscript (LaTeX + PDF)
scripts/                        certificate generator + independent audits
.github/workflows/lean.yml      the CI verification gate
VERIFICATION.md                 exact verification and trust model
```

## Reproducibility

The project is pinned to Lean `4.32.2` and Mathlib `v4.32.2`. With Python 3,
Lean/Lake, and LaTeX available:

```bash
./scripts/verify.sh          # everything below in one script
```

or layer by layer:

```bash
python3 scripts/generate_carry_certificates.py   # regenerate certificate sources
python3 scripts/arithmetic_audit.py              # independent arithmetic checks
python3 scripts/infinite_family_audit.py         # family recurrences and crossings
python3 scripts/static_lean_audit.py             # source-level trust-boundary scan
lake exe cache get                              # fetch the pinned Mathlib cache
lake build                                       # all sixteen modules
```

The manuscript builds with `make paper`.

The GitHub Actions workflow regenerates the certificate sources and rejects
drift, runs the independent arithmetic and source checks, builds the
memory-intensive modules sequentially to bound peak runner memory, performs a
final whole-project `lake build`, and re-checks the entire environment with
`leanchecker` via `leanprover/lean-action`.

## Proof and trust boundary

The mathematical proof in `paper/main.tex` is self-contained. The Lean
development is a supplementary machine-checked verification of the main
theorem and the two infinite families.

The Python programs are **not** trusted proof oracles:
`generate_carry_certificates.py` emits finite tables, but the resulting
certificate obligations are rechecked inside Lean with kernel reduction and a
proved soundness theorem (`Certificate.lean`); the arithmetic scripts provide
independent regression checks only. See
[VERIFICATION.md](VERIFICATION.md) for the exact trust model.

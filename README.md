# Carry Obstructions and Infinite Periodic Crossings for OEIS A277223

![CI](https://github.com/lightninnng/A277223/actions/workflows/lean.yml/badge.svg)
![Lean 4.32.2](https://img.shields.io/badge/Lean-4.32.2-blue)
![Mathlib v4.32.2](https://img.shields.io/badge/Mathlib-v4.32.2-orange)

Manuscript, Lean 4 formalization, and reproducibility checks for a decimal
digit-sum multiplier problem underlying
[OEIS A277223](https://oeis.org/A277223).

| | |
|---|---|
| **Manuscript** | [`paper/main.pdf`](paper/main.pdf) · [`paper/main.tex`](paper/main.tex) |
| **Trust model** | [`VERIFICATION.md`](VERIFICATION.md) |
| **Verification gate** | [`.github/workflows/lean.yml`](.github/workflows/lean.yml) |

---

## The problem

For a positive integer $n$, let $s(x)$ denote the decimal digit sum, and define

$$
\mathrm{Good}(n,k) \iff s(kn) = k,
\qquad
\mathrm{MaxGood}(n,k) \iff \mathrm{Good}(n,k) \ \text{and} \ \mathrm{Good}(n,j) \Rightarrow j \le k .
$$

That is, a multiplier $k$ is *Good* when multiplying $n$ by $k$ preserves the
digit sum, and *maximal* when no larger Good multiplier exists. Writing
$a(n)$ for the largest positive Good multiplier of $n$ (or $0$ when none
exists), we have $\mathrm{MaxGood}(n,k) \iff a(n) = k$; this is the
characterization used by OEIS A277223.

## Main theorem

The exact spectrum of maximal Good multipliers below $12$ is

$$
(k < 12 \ \wedge\ \exists n,\ \mathrm{MaxGood}(n,k))
\ \iff\ k \in \{0, 7, 9, 11\},
\qquad
\{a(n) : a(n) < 12\} = \{0, 7, 9, 11\}.
$$

| $k$ | status | realized by |
|---|---|---|
| $0$ | realized | $n = 62$ (no positive Good multiplier exists) |
| $7$ | realized, **infinitely often** | $N_7(t)$ for every $t \ge 0$ |
| $9$ | realized | $n = 1$ |
| $11$ | realized, **infinitely often** | $N_{11}(t)$ for every $t \ge 0$ |
| $1$–$6$, $8$, $10$ | never | carry obstruction (finite certificates) |

Beyond the spectrum, the two infinite families give the structural result:
infinitely many integers have maximal Good multiplier $7$, infinitely many
have $11$, and distinct members of a family are never related by
multiplication by a positive power of $10$.

---

## Mathematical structure

The proof has two independent pillars.

### Pillar 1 · Carry obstruction

If $m = kn$ and a decimal rescaling satisfies

$$
ck = j \cdot 10^{z},
\qquad
j > k,
\qquad
s(cm) = j,
$$

then $j$ is a larger Good multiplier for the same $n$: the product $cm$
re-encodes the digit mass of $m$ at a coarser decimal scale. An exact
carry-defect identity and first-carry localization reduce the excluded
cases to finite local digit configurations, which rules out

$$
k \in \{1, 2, 3, 4, 5, 6, 8, 10\}
$$

as maximal Good multipliers. The manuscript exhibits the complete
human-checkable obstruction trees. For $k = 8$ and $k = 10$, Lean verifies
the same conclusion independently: an exact schoolbook-multiplication
automaton is enumerated over **all** decimal digit strings of total digit
mass $8$ (7608 reachable states) and $10$ (1543 states), and a proved
soundness theorem lifts the finite certificate to the obstruction property
for every $n$.

### Pillar 2 · Periodic crossing

For fixed $N$ define the defect $\Delta_N(k) = s(kN) - k$. If $p$ is Good,
digit-sum subadditivity implies

$$
\Delta_N(k + p) \le \Delta_N(k),
$$

so each residue-class sequence of $\Delta_N(k)$ modulo $p$ is
antitone. A strict adjacent positive-to-negative crossing in **every
nonzero** residue class, together with a negative second point in the zero
residue class, proves that $p$ is the unique positive Good multiplier of
$N$. The two families are engineered so that a periodic block structure
makes all $p - 1$ crossings (and the zero-class point) verifiable from a
single aligned block update.

---

## Infinite families

**The seven family.** For $t \ge 0$ define

$$
M_7(0) = 25,
\qquad
M_7(t+1) = 10^{6} M_7(t) + 925925,
\qquad
N_7(t) = \frac{5 \cdot 10^{6 M_7(t) + 2} + 11}{7}.
$$

Then $\mathrm{MaxGood}(N_7(t), 7)$ for every $t$. The block count obeys the
exact balance $27 M_7(t) + 25 = 7 \cdot 10^{6t+2}$, which places the
residue crossings exactly on the periodic block boundary. The first member
is the 152-digit witness

$$
N_7(0) = \frac{5 \cdot 10^{152} + 11}{7}.
$$

**The eleven family.** For $t \ge 0$ define

$$
M_{11}(0) = 12219,
\qquad
M_{11}(t+1) = 100 M_{11}(t) + 319,
\qquad
N_{11}(t) = \frac{9 \cdot 10^{2 M_{11}(t) + 2} + 2}{11}.
$$

Then $\mathrm{MaxGood}(N_{11}(t), 11)$ for every $t$, with all ten nonzero
residue crossings synchronized on the common modulus $10^{2t+4}$. The
compact 52-digit witness

$$
\frac{9 \cdot 10^{52} + 2}{11}
$$

is included as a separate explicit example (it is not a member of the
pure-power family above).

---

## Theorem map

Formal statement ↔ informal meaning (all names live under the `A277223`
namespace, abbreviated below).

| Declaration | Statement |
|---|---|
| `Main.maxGood_lt_twelve_classification` | a maximal Good multiplier $< 12$ is one of $0, 7, 9, 11$ |
| `Main.small_value_spectrum_iff` | the spectrum equivalence, $\iff$ form |
| `Main.small_values_realized` | $0, 7, 9, 11$ are all realized |
| `Main.infinitely_many_structural_values` | the set of structural values is infinite |
| `PeriodicCrossing.N7Family_maxGood` | $\mathrm{MaxGood}(N_7(t), 7)$ for every $t$ |
| `PeriodicCrossing.N11Family_maxGood` | $\mathrm{MaxGood}(N_{11}(t), 11)$ for every $t$ |
| `PeriodicCrossing.infinitely_many_maxGood_seven` | infinitely many $n$ with $a(n) = 7$ |
| `PeriodicCrossing.infinitely_many_maxGood_eleven` | infinitely many $n$ with $a(n) = 11$ |
| `PeriodicCrossing.M7Family_balance` / `M11Family_balance` | the block-count balances positioning the crossings |
| `PeriodicCrossing.N7Family_injective` / `N11Family_injective` | family members are pairwise distinct |
| `CarryObstruction.forbiddenSmall_not_maxGood` | no $n$ has maximal Good multiplier $1$–$6$, $8$, $10$ |
| `CarryObstruction.Certificate.carryObstruction_of_valid_certificate` | certificate soundness: valid ⇒ obstruction |
| `Witnesses.one_maxGood_nine` | $a(1) = 9$ |
| `Witnesses.sixtyTwo_maxGood_zero` | $a(62) = 0$ |

## Module guide

```text
A277223/
  Basic.lean                    digit sums, Good / MaxGood definitions
  CarryObstruction/
    Theory.lean                 abstract rescaling obstruction (k ≤ 6)
    Certificate.lean            packed certificate format + soundness theorem
    EightData.lean              k = 8 machine, packed tables (7608 states)
    Eight.lean                  k = 8 validity: kernel-checked ranges + assembly
    TenData.lean                k = 10 machine, packed tables (1543 states)
    Ten.lean                    k = 10 validity: kernel-checked ranges + assembly
    Forbidden.lean              unified exclusion of 1–6, 8, 10
  PeriodicCrossing/
    Defect.lean                 defect antitonicity along Good periods
    Blocks.lean                 periodic block normal form
    AlignedUpdate.lean          generic aligned repeated-block update lemma
    Seven.lean, SevenFamily.lean      finite seed + infinite seven family
    Eleven.lean, ElevenFamily.lean    finite seed + infinite eleven family
  Witnesses.lean                spectrum endpoints: n = 62 ↦ 0, n = 1 ↦ 9
  Main.lean                     assembly: full spectrum + infinitude
```

Certificate data modules hold the tables as packed natural numbers with
13-bit fields; lookups decode by kernel-native shifts, so each bounded-range
validity check is a small, fast kernel reduction, and `Certificate.lean`
proves that range checks reassemble into full validity.

## Verification pipeline

Every push to `main` runs the full gate:

| Layer | What it checks |
|---|---|
| certificate regeneration | `generate_carry_certificates.py` output matches the committed sources byte-for-byte |
| arithmetic audit | independent recomputation of all certificate arithmetic (`AUDIT_OK`) |
| family audit | family recurrences, balances, and residue crossings (`INFINITE_FAMILY_AUDIT_OK`) |
| static source check | import DAG, version pins, no `sorry` / `admit` / `axiom`, no trust-bypass constructs |
| sequential prebuild | the four memory-intensive modules build one process at a time |
| full `lake build` | all sixteen modules under the pinned toolchain |
| `leanchecker` | independent whole-environment re-typecheck |

## Reproducibility

Pins: Lean `4.32.2`, Mathlib `v4.32.2` (see `lean-toolchain` and
`lakefile.toml`). With Python 3, Lean/Lake, and LaTeX available:

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

## Proof and trust boundary

The mathematical proof in `paper/main.tex` is self-contained. The Lean
development is a supplementary machine-checked verification of the main
theorem and the two infinite families.

The Python programs are **not** trusted proof oracles:
`generate_carry_certificates.py` emits finite tables, but the resulting
certificate obligations are rechecked inside Lean with kernel reduction and
the proved soundness theorem in `Certificate.lean`; the arithmetic scripts
provide independent regression checks only. See
[VERIFICATION.md](VERIFICATION.md) for the exact trust model.

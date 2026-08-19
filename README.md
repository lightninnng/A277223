# Carry Obstructions and Infinite Periodic Crossings for OEIS A277223

This repository contains the manuscript, Lean 4 formalization, and reproducibility checks for a decimal digit-sum multiplier problem underlying OEIS A277223.

Manuscript: [`paper/main.pdf`](paper/main.pdf) · Source: [`paper/main.tex`](paper/main.tex)

For a positive integer `n`, let `s(x)` denote the decimal digit sum and define

```text
Good(n,k)    :<=> s(k*n) = k
MaxGood(n,k) :<=> Good(n,k) and every Good(n,j) has j <= k.
```

The principal result is the exact spectrum below 12:

```text
(k < 12 and exists n, MaxGood(n,k))
  <=> k = 0 or k = 7 or k = 9 or k = 11.
```

Equivalently, if `a(n)` is the largest positive Good multiplier (or `0` when none exists), then

```text
{ a(n) : a(n) < 12 } = {0,7,9,11}.
```

The values `7` and `11` are realized by explicit infinite families. Within each family, distinct members are not related by multiplication by a positive power of `10`.

## Mathematical structure

The proof has two independent structural components.

### Carry obstruction

If `m = k*n` and a decimal rescaling satisfies

```text
c*k = j*10^z,  j > k,  s(c*m) = j,
```

then `j` is a larger Good multiplier for the same `n`. An exact carry-defect identity and first-carry localization reduce the small cases to finite local digit configurations. This excludes

```text
1,2,3,4,5,6,8,10
```

as maximal Good multipliers. The manuscript gives a human-checkable obstruction tree. For `k=8` and `k=10`, Lean verifies the same conclusion independently through exact schoolbook-multiplication certificates over arbitrary decimal digit strings of total digit mass 8 and 10.

### Periodic crossing

For fixed `N`, define

```text
Delta_N(k) = s(k*N) - k.
```

If `p` is Good, digit-sum subadditivity implies

```text
Delta_N(k+p) <= Delta_N(k).
```

Thus each residue-class sequence modulo `p` is antitone. A strict adjacent positive-to-negative crossing in every nonzero residue class, together with a negative second point in the zero residue class, proves that `p` is the unique positive Good multiplier.

This mechanism produces the two parameterized families formalized in
`PeriodicCrossing/SevenFamily.lean` and `PeriodicCrossing/ElevenFamily.lean`.

## Infinite families

For `t >= 0`, define

```text
M7(0)     = 25
M7(t + 1) = 10^6*M7(t) + 925925
N7(t)     = (5*10^(6*M7(t)+2) + 11) / 7.
```

Then `MaxGood(N7(t),7)` for every `t`. In particular,

```text
N7(0) = (5*10^152 + 11) / 7.
```

Similarly, define

```text
M11(0)     = 12219
M11(t + 1) = 100*M11(t) + 319
N11(t)     = (9*10^(2*M11(t)+2) + 2) / 11.
```

Then `MaxGood(N11(t),11)` for every `t`. The explicit 52-digit witness

```text
(9*10^52 + 2) / 11
```

is included as a separate explicit example.

Distinct members within either parameterized family are not related by multiplication by a positive power of 10.

## Repository layout

```text
A277223/
  Basic.lean
  CarryObstruction/
    Theory.lean
    Certificate.lean
    EightData.lean
    Eight.lean
    TenData.lean
    Ten.lean
    Small.lean
  PeriodicCrossing/
    Defect.lean
    Blocks.lean
    AlignedUpdate.lean
    Seven.lean
    Eleven.lean
    SevenFamily.lean
    ElevenFamily.lean
  Witnesses.lean
  Main.lean
paper/
  main.tex
  main.pdf
scripts/
  generate_carry_certificates.py
  arithmetic_audit.py
  infinite_family_audit.py
  static_lean_audit.py
  verify.sh
.github/workflows/lean.yml
VERIFICATION.md
```

## Reproducibility

The project is pinned to Lean `4.32.2` and Mathlib `v4.32.2`. With Python 3, Lean/Lake, and LaTeX available, run

```bash
./scripts/verify.sh
```

or execute the layers separately:

```bash
python3 scripts/generate_carry_certificates.py
python3 scripts/arithmetic_audit.py
python3 scripts/infinite_family_audit.py
python3 scripts/static_lean_audit.py
lake exe cache get
lake build
```

To build the manuscript:

```bash
make paper
```

The GitHub Actions workflow regenerates the certificate sources and rejects drift, runs the independent arithmetic and source checks, builds memory-intensive modules sequentially to bound peak runner memory, performs a final whole-project `lake build`, and runs `leanchecker` through `leanprover/lean-action`.

See [VERIFICATION.md](VERIFICATION.md) for the exact verification and trust model.

## Proof and trust boundary

The mathematical proof in `paper/main.tex` is self-contained. The Lean development is a supplementary machine-checked verification of the main theorem and the two infinite families.

The Python programs are not trusted proof oracles. In particular, `generate_carry_certificates.py` emits finite tables, but the resulting certificate obligations are rechecked inside Lean with kernel reduction and a proved soundness theorem. The arithmetic scripts provide independent regression checks only.

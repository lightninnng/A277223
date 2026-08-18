# Carry Obstructions and Infinite Periodic Crossings for OEIS A277223

This repository contains the Lean 4 companion development, reproducibility scripts, and manuscript source for a decimal digit-sum multiplier problem underlying OEIS A277223.

For a natural number `n`, let `s(x)` be the decimal digit sum and define

```text
Good(n,k)    :<=> s(k*n) = k
MaxGood(n,k) :<=> Good(n,k) and every Good(n,j) has j <= k.
```

The project now has two levels of results.

## Main structural results

The proof is organized around exactly two reusable mechanisms.

### 1. Carry Obstruction

A Good multiplier `k` is nonterminal whenever a decimal rescaling

```text
c*k = j*10^z,   j > k
```

can be shown, via the carry-defect calculus, to satisfy `s(c*(k*n)) = j`.  The manuscript proves:

- an exact carry-defect identity;
- first-carry locality;
- a profile-safe criterion;
- a finite-state regularity/decidability statement for fixed multiplier constraints;
- complete exclusions of maximal multipliers

```text
1,2,3,4,5,6,8,10.
```

For `8` and `10`, the paper gives an explicit depth-at-most-two local obstruction tree.  Lean additionally checks exact proof-carrying digit-mass transition certificates as an independent low-level audit.  These certificates range over arbitrary digit strings of total digit mass 8 or 10, not over a bounded interval of integers.

### 2. Periodic Crossing

For fixed `N`, define the integer defect

```text
Delta_N(k) = s(k*N) - k.
```

If `p` is Good, digit-sum subadditivity gives

```text
Delta_N(k+p) <= Delta_N(k),
```

so each residue-class sequence `q |-> Delta_N(p*q+r)` is antitone.  A strict adjacent `+ -> -` crossing in every nonzero residue class, together with a negative second point in the zero residue class, makes `p` the unique positive Good multiplier.

A generic aligned-block update lemma allows one block in an arbitrarily long repeated decimal word to be changed without an unbounded carry analysis.

## Nontrivial infinite families

### Infinite family with maximal multiplier 7

Define

```text
M7(0)     = 25
M7(t + 1) = 10^6 * M7(t) + 925925
u7(t)     = 6*t + 2
q7(t)     = 10^u7(t)
N7(t)     = (5*10^(6*M7(t)+2) + 11) / 7.
```

The balance identity is

```text
27*M7(t) + 25 = 7*q7(t).
```

For every nonzero residue `r mod 7`,

```text
Delta(7*(q7(t)-1)+r) = 54*t + 9  > 0
Delta(7*q7(t)+r)     = -9         < 0,
```

and `Delta(14)=-9`.  Therefore

```text
MaxGood(N7(t), 7)
```

for every `t`.  The original 152-digit witness is exactly `N7(0)`.

### Infinite family with maximal multiplier 11

Define

```text
M11(0)     = 12219
M11(t + 1) = 100*M11(t) + 319
q11(t)     = 100^(t+2)
N11(t)     = (9*10^(2*M11(t)+2) + 2) / 11.
```

The balance identity is

```text
9*M11(t) + 29 = 11*q11(t).
```

All ten nonzero residue classes cross at the same adjacent quotients `q11(t)-1 -> q11(t)`:

```text
r not in {5,10}:  +(18*t+27) -> -9
r in     {5,10}:  +(18*t+18) -> -27.
```

Also `Delta(22)=-9`.  Therefore

```text
MaxGood(N11(t), 11)
```

for every `t`.

The repository separately retains the compact 52-digit witness

```text
N11small = (9*10^52 + 2) / 11,
```

whose maximality is proved both in the manuscript and in `PeriodicCrossing/Eleven.lean`.

The parameter maps in both infinite families are injective, and the Lean source includes intended theorems

```text
infinitely_many_maxGood_seven
infinitely_many_maxGood_eleven
```

stating that the corresponding `MaxGood` sets are infinite.

## Exact spectrum below 12

As an application of Carry Obstruction and the explicit witnesses,

```text
(k < 12 and exists n, MaxGood n k)
  <=> k = 0 or k = 7 or k = 9 or k = 11.
```

Equivalently,

```text
{ a(n) : a(n) < 12 } = {0,7,9,11}.
```

The values `0` and `9` are proved internally using `n=62` and `n=1`; no OEIS lookup is needed for those realizations.

## Repository map

```text
A277223/
  Basic.lean
  CarryObstruction/
    Theory.lean
    Certificate.lean
    Eight.lean
    Ten.lean
    Small.lean
  PeriodicCrossing/
    Defect.lean
    Blocks.lean
    AlignedUpdate.lean
    Seven.lean          # compact 152-digit witness
    Eleven.lean         # compact 52-digit witness
    SevenFamily.lean    # nontrivial infinite 7-family
    ElevenFamily.lean   # nontrivial infinite 11-family
  Witnesses.lean
  Main.lean
paper/
  main.tex
  main.pdf
scripts/
  discovery_search.py       # discovery only; not a proof dependency
  generate_carry_certificates.py
  arithmetic_audit.py
  infinite_family_audit.py
  static_lean_audit.py
  compile_audit.sh
audit/
.github/workflows/lean.yml
```

## Reproduce the audits

The project is pinned to Lean 4.32.2 and Mathlib v4.32.2.

```bash
python3 scripts/generate_carry_certificates.py
python3 scripts/arithmetic_audit.py
python3 scripts/infinite_family_audit.py
python3 scripts/static_lean_audit.py .
./scripts/compile_audit.sh
```

On a machine with Lean/Lake installed, the final gate continues with

```bash
lake update
lake exe cache get
lake build
```

GitHub CI additionally runs `leanchecker` and `nanoda` with `nanoda-allow-sorry: false`.

## Trust and certification status

The source contains no `sorry`, `admit`, user-declared `axiom`, `native_decide`, `unsafe`, `run_tac`, `implemented_by`, `addDeclWithoutChecking`, or `ofReduceBool`.  Concrete finite certificates are intended to be checked with explicit `decide +kernel`.

The manuscript is self-contained; Lean is a supplementary verification layer.  Local arithmetic, certificate-generation, dependency, trust-boundary, LaTeX, and PDF audits are regression checks, while the authoritative machine-verification status is the pinned `lake build + leanchecker + nanoda` CI result for the exact source commit.  Do not describe a release as Lean-kernel-certified unless that complete gate is green.

See:

- `PROOF_ROADMAP_CN.md` for the theorem-by-theorem mathematical route;
- `RELIABILITY_AUDIT_CN.md` for the reliability assessment;
- `FORMALIZATION_STATUS.md` for the exact formal certification boundary;
- `COMPILATION_AUDIT.md` for the local compilation attempt.

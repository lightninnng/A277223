# Verification and trust model

This document specifies the verification architecture, release procedure, and logical trust boundary of the repository.

## Pinned formal environment

The project pins:

- Lean: `leanprover/lean4:v4.32.2` in `lean-toolchain`;
- Mathlib: `v4.32.2` in `lakefile.toml` and `lake-manifest.json`.

A release claim should always refer to an exact Git commit and the successful CI run for that commit.

## Verification layers

The repository uses three complementary layers.

1. **Self-contained mathematical proof.** The manuscript proves the carry-obstruction theorem, the periodic-crossing criterion, both infinite families, and the exact spectrum below 12 without assuming any computation.
2. **Lean formalization.** Lean formalizes `Good`, `MaxGood`, the small-value exclusion, the periodic machinery, the explicit witnesses, both parameterized families, and the final spectrum theorem.
3. **Independent reproducibility checks.** Python scripts regenerate finite certificate data and recompute the bounded arithmetic used in the manuscript. These checks are diagnostic and are not part of the logical trust base.

## Carry certificates for 8 and 10

The difficult small values `8` and `10` are checked in Lean by an exact right-to-left schoolbook multiplication machine. A state records the input digit mass and the exact carry/output-digit-sum state for a finite list of rescaling witnesses.

`generate_carry_certificates.py` generates four source files:

```text
A277223/CarryObstruction/EightData.lean
A277223/CarryObstruction/Eight.lean
A277223/CarryObstruction/TenData.lean
A277223/CarryObstruction/Ten.lean
```

The generator is outside the formal trust boundary. CI regenerates all four files and rejects any source drift. Lean then checks the generated tables with `decide +kernel`, and `carryObstruction_of_valid_certificate` transfers the finite machine result to arbitrary decimal digit lists of the prescribed total digit mass.

The large finite checks are divided into bounded index ranges. This partitioning controls elaboration memory only: each range theorem is kernel checked, and `valid_of_rangeOK` proves that the collection covers the entire certificate state space.

## Continuous-integration verification

The public workflow in `.github/workflows/lean.yml` performs the following steps:

1. regenerate all generated certificate modules and require a clean diff;
2. run `arithmetic_audit.py` and `infinite_family_audit.py`;
3. run `static_lean_audit.py` and reject proof placeholders or trust-bypass constructs;
4. confirm the Lean and Mathlib version pins;
5. fetch the Mathlib cache;
6. prebuild the memory-intensive certificate/family modules sequentially;
7. perform a final full project build;
8. run `leanchecker` via `leanprover/lean-action`.

The sequential prebuild does not weaken the logical check. Lean modules are compiled and checked independently by design; the final whole-project build imports the resulting checked module environments. The scheduling choice only lowers peak memory on hosted runners.

## Source restrictions

The project source is checked to contain no project-level use of:

```text
sorry
admit
axiom
native_decide
run_tac
unsafe
implemented_by
addDeclWithoutChecking
ofReduceBool
```

Finite reflected obligations use explicit `decide +kernel`.

## Interpreting a green release

For an exact commit whose CI gate above is green, it is accurate to say that the accompanying Lean development successfully builds under the pinned Lean/Mathlib environment and passes an additional `leanchecker` recheck.

The manuscript remains logically independent of that machine verification: the Lean artifact strengthens reproducibility and error detection, but it is not a premise of the mathematical proofs.

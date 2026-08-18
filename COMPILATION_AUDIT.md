# Compilation audit

Audit date: 2026-08-17.

Target environment: Lean 4.32.2 / Mathlib v4.32.2.

## Actual compile-gate attempt

The repository gate is `scripts/compile_audit.sh`.  In the artifact container it executes all mathematical/source audits that do not require Lean before checking for the compiler:

```text
$ ./scripts/compile_audit.sh
lean-toolchain: leanprover/lean4:v4.32.2
mathlib pin: ... rev = "v4.32.2"
... carry certificate regeneration ...
... arithmetic audit ... AUDIT_OK
... infinite family audit ... INFINITE_FAMILY_AUDIT_OK
... static Lean audit ... STATIC_LEAN_AUDIT_OK
NOTE: no Git worktree metadata; generated-certificate drift check skipped
ERROR: lean not found; elaboration/kernel check not started
```

Exit status: **127**.

This is an environment failure before Lean elaboration starts.  It is neither a successful `lake build` nor evidence that any `.lean` theorem fails to compile.  The container contains no `lean`, `lake`, or `elan` executable.

Several acquisition routes for the official Lean 4.32.2 Linux toolchain were attempted.  The ordinary shell/Python environment has no usable outbound DNS/network path, and the available artifact download path could not follow the GitHub release-asset redirect into a usable local toolchain.  Consequently a genuine local `lake build` has **not** been executed and is not claimed.

## Checks completed successfully in this environment

- exact carry-certificate regeneration;
- `scripts/arithmetic_audit.py` -> `AUDIT_OK`;
- `scripts/infinite_family_audit.py` -> `INFINITE_FAMILY_AUDIT_OK`;
- complete digit-partition coverage checks for the small Carry-Obstruction theorem;
- primary first-carry motif completeness audit;
- secondary exceptional-offset audit;
- compact 152- and 52-digit witness arithmetic;
- 7-family recurrence/balance/crossing audit;
- 11-family recurrence/balance/all-ten-residue crossing audit;
- selected direct arbitrary-precision family instances;
- `scripts/static_lean_audit.py`, including local import DAG and trust-boundary checks;
- scan for `sorry`, `admit`, user-declared `axiom`, and selected trust-bypass constructs;
- cross-check of the Mathlib APIs used by the new infinitude theorems and digit infrastructure against current Mathlib documentation/source;
- LaTeX build and warning scan;
- PDF preflight/render gate at final packaging.

## New parameterized Lean surface

The final source now includes:

```text
PeriodicCrossing/AlignedUpdate.lean
PeriodicCrossing/SevenFamily.lean
PeriodicCrossing/ElevenFamily.lean
```

with intended declarations including:

```text
N7Family_maxGood
N11Family_maxGood
N7Family_injective
N11Family_injective
infinitely_many_maxGood_seven
infinitely_many_maxGood_eleven
```

These files pass the repository's static dependency/trust audit.  Acceptance by the Lean elaborator/kernel is determined only by the pinned CI build for the matching commit.

## Mandatory certification gate

On a machine with the pinned toolchain, run:

```bash
./scripts/compile_audit.sh
```

and require the final `lake build` to be green.  The included GitHub workflow additionally runs `leanchecker` and `nanoda` with `nanoda-allow-sorry: false`.

Do not label the formalization “kernel-certified”, “machine-checked”, or “formally verified” until all of those jobs are green on the exact release commit whose source matches the manuscript theorem map.

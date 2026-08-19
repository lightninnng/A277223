# Formalization status

Snapshot date: 2026-08-17.

## Mathematical theorem status

The manuscript is now organized around two reusable modules and proves three levels of results.

### Carry Obstruction

The paper proves:

1. decimal rescaling of a Good multiplier;
2. the exact carry-defect identity;
3. first-carry locality;
4. a profile-safe criterion and a fixed-multiplier regularity statement;
5. complete nonmaximality of Good multipliers `1,2,3,4,5,6,8,10`.

The difficult `8` and `10` branches are finite because first-carry locality reduces failure to bounded local overlaps.  The manuscript lists the complete obstruction trees; independent scripts regenerate the relevant digit partitions, first-overload motifs, and exceptional relative offsets.

### Periodic Crossing

The paper proves:

1. digit-sum subadditivity;
2. defect antitonicity `Delta_N(k+p) <= Delta_N(k)` whenever `p` is Good;
3. the residue-class crossing criterion;
4. the periodic-block normal form;
5. a generic aligned repeated-block update lemma.

It then proves two **nontrivial explicit infinite families**:

- `MaxGood (N7Family t) 7` for every `t`;
- `MaxGood (N11Family t) 11` for every `t`.

The parameter maps are intended to be proved injective in Lean, yielding:

- `infinitely_many_maxGood_seven`;
- `infinitely_many_maxGood_eleven`.

The compact witnesses

- `(5*10^152+11)/7`,
- `(9*10^52+2)/11`

remain as small concrete examples.  The 52-digit witness is proved self-containedly in the manuscript and separately in `PeriodicCrossing/Eleven.lean`; it is not the first member of the pure-power infinite eleven-family.

### Small spectrum

The values `0` and `9` are realized internally by `n=62` and `n=1`.  Combining all modules gives

```text
(k < 12 and exists n, MaxGood n k)
  <=> k = 0 or k = 7 or k = 9 or k = 11.
```

Thus the manuscript proves the exact spectrum below 12 while the infinite-family theorems provide the broader structural result.

## Independent arithmetic and structural audits

The following commands currently pass in the artifact environment:

```bash
python3 scripts/generate_carry_certificates.py
python3 scripts/arithmetic_audit.py
python3 scripts/infinite_family_audit.py
python3 scripts/static_lean_audit.py .
```

The current audits verify, independently of the prose:

- complete digit-partition coverage for masses 5, 6, 8, and 10;
- all primary and secondary Carry-Obstruction motifs;
- all fallback leaf arithmetic;
- the compact 152- and 52-digit witnesses;
- 846 exact periodic-normal-form comparisons;
- the seven-family recurrence, balance, residue crossings, and zero-residue defect;
- the eleven-family recurrence, balance, all ten synchronized residue crossings, and zero-residue defect;
- selected direct arbitrary-precision family instances;
- local Lean import graph and trust-boundary restrictions.

`arithmetic_audit.py` ends in `AUDIT_OK`; `infinite_family_audit.py` ends in `INFINITE_FAMILY_AUDIT_OK`.

## Lean source status

The source tree currently contains 16 Lean modules.  The static audit reports:

- no missing local imports;
- no import cycles;
- no `sorry`, `admit`, or project-declared `axiom`;
- no `native_decide`, `unsafe`, `run_tac`, `implemented_by`, `addDeclWithoutChecking`, or `ofReduceBool`;
- finite concrete certificate checks use explicit `decide +kernel`;
- toolchain pin `leanprover/lean4:v4.32.2`;
- Mathlib pin `v4.32.2`.

The new parameterized modules are:

```text
PeriodicCrossing/AlignedUpdate.lean
PeriodicCrossing/SevenFamily.lean
PeriodicCrossing/ElevenFamily.lean
```

and `Main.lean` combines the two infinite-set statements in `infinitely_many_structural_values`.

## Certification boundary

The manuscript is mathematically self-contained and treats Lean as a supplementary verification layer.  Local source, arithmetic, certificate, dependency, and trust-boundary audits are useful regression checks, but they are not substitutes for elaboration by the pinned Lean toolchain.  The authoritative machine-verification status is therefore the CI result for the exact source commit.

No release should be described as Lean-kernel-certified or fully machine-checked unless the complete pinned CI gate below is green.

## Final certification gate

A release may be called formally certified only after the pinned Lean 4.32.2 / Mathlib v4.32.2 environment produces all of the following:

1. certificate regeneration with no source drift;
2. `AUDIT_OK`;
3. `INFINITE_FAMILY_AUDIT_OK`;
4. `lake build` green;
5. `leanchecker` green;
6. final paper/source theorem-map review against the exact successful commit.

The included GitHub Actions workflow is configured as this gate.

`nanoda` is excluded from the gate: it cannot parse the Lean 4.28+ export
stream and fails immediately with `invalid digit found in string`, an open
upstream incompatibility (leanprover/lean-action#169, unresolved since
July 2026).  Independent re-verification of the whole environment is
already provided by `leanchecker`, which passes.  Re-add nanoda to the
gate once it supports the Lean 4.32 export format.

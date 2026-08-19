#!/usr/bin/env python3
"""Generate the small proof-carrying digit-mass certificates for Lean.

This is a generator, not a trusted proof component.  Lean re-checks the
resulting packed tables with `decide +kernel` and the generic soundness
theorem in CarryObstruction/Certificate.lean.
"""
from collections import deque
from pathlib import Path
import sys

# packed tables are emitted as ~450k-digit decimal literals
sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "A277223" / "CarryObstruction"


def ds(n: int) -> int:
    return sum(map(int, str(n)))


def step(c: int, lane: tuple[int, int], d: int) -> tuple[int, int]:
    carry, out = lane
    v = c * d + carry
    return v // 10, out + v % 10


def terminal(spec: tuple[int, int, int], lane: tuple[int, int]) -> bool:
    c, j, z = spec
    carry, out = lane
    return out + ds(carry) == j


def generate(k: int, specs: list[tuple[int, int, int]]):
    init = (0, tuple((0, 0) for _ in specs))
    states = [init]
    index = {init: 0}
    q = deque([init])
    transitions: list[list[int] | None] = []

    while q:
        state = q.popleft()
        mass, lanes = state
        row = [0] * 10
        for d in range(10):
            if mass + d > k:
                continue
            nxt = (mass + d, tuple(step(c, lane, d) for (c, _, _), lane in zip(specs, lanes)))
            if nxt not in index:
                index[nxt] = len(states)
                states.append(nxt)
                q.append(nxt)
            row[d] = index[nxt]
        transitions.append(row)

    assert len(transitions) == len(states)
    assert all(c * k == j * 10**z and j > k for c, j, z in specs)
    terminal_count = 0
    for mass, lanes in states:
        if mass == k:
            terminal_count += 1
            assert any(terminal(sp, lane) for sp, lane in zip(specs, lanes))

    flat = [x for row in transitions for x in row]
    return states, flat, terminal_count


def lean_specs(name: str, specs):
    rows = ", ".join(f"⟨{c}, {j}, {z}⟩" for c, j, z in specs)
    return f"def {name}Specs : List WitnessSpec := [{rows}]\n"


def chunks(seq, n):
    for i in range(0, len(seq), n):
        yield seq[i:i+n]


def write_cert(k: int, stem: str, specs):
    states, flat, terminal_count = generate(k, specs)
    cert_name = f"cert{k}"
    theorem_name = "eight" if k == 8 else "ten"
    n = len(states)
    lanes = len(specs)
    state_bits = 13 * (1 + 2 * lanes)

    # pack each state: mass followed by per-lane (carry, out), 13-bit fields
    def pack_state(state):
        mass, lane_list = state
        v = mass
        for j, (carry, out) in enumerate(lane_list):
            v |= carry << (13 * (1 + 2 * j))
            v |= out << (13 * (2 + 2 * j))
        return v

    states_packed = 0
    for i, s in enumerate(states):
        states_packed |= pack_state(s) << (state_bits * i)
    next_packed = 0
    for c, target in enumerate(flat):
        next_packed |= target << (13 * c)

    # --- data module: the two packed tables as single Nat literals ---
    dpath = OUT / f"{stem}Data.lean"
    with dpath.open("w", encoding="utf-8", newline="\n") as f:
        f.write("import A277223.CarryObstruction.Certificate\n\n")
        f.write("/-!\n")
        f.write(f"Generated exact digit-mass carry data for target `{k}`.\n")
        f.write(f"States: {n}; mass-`{k}` terminal states: {terminal_count}.\n")
        f.write("The generator is `scripts/generate_carry_certificates.py`; this file is\n")
        f.write("re-checked by Lean and is not trusted as an external oracle.\n")
        f.write("Both tables are packed into single natural numbers; see the packing\n")
        f.write("layout comment in `Certificate.lean` (13-bit fields, native shifts).\n")
        f.write("-/\n\n")
        f.write("namespace A277223\nnamespace CarryObstruction\nnamespace Certificate\n\n")
        f.write("set_option maxHeartbeats 0\n")
        f.write("set_option maxRecDepth 1000000\n")
        f.write(lean_specs(f"cert{k}", specs))
        f.write("\n")
        f.write(f"def {cert_name}States : ℕ := {states_packed}\n\n")
        f.write(f"def {cert_name}Next : ℕ := {next_packed}\n\n")
        f.write(f"def {cert_name} : CarryCertificate := {{\n")
        f.write(f"  specs := cert{k}Specs\n")
        f.write(f"  statesPacked := {cert_name}States\n")
        f.write(f"  nextPacked := {cert_name}Next\n")
        f.write(f"  total := {n}\n")
        f.write(f"  stateBits := {state_bits}\n")
        f.write(f"  laneCount := {lanes}\n")
        f.write("  initial := 0\n")
        f.write("}\n\n")
        f.write("end Certificate\nend CarryObstruction\nend A277223\n")

    # --- proof module: bounded-range kernel checks plus assembly; the
    # packed-arithmetic checker is cheap per state, so all ranges live in
    # one file (chunks exist for diagnostic granularity only) ---
    chunk_size = 1024
    ranges = [(lo, min(lo + chunk_size, n)) for lo in range(0, n, chunk_size)]
    path = OUT / f"{stem}.lean"
    with path.open("w", encoding="utf-8", newline="\n") as f:
        f.write(f"import A277223.CarryObstruction.{stem}Data\n\n")
        f.write("/-!\n")
        f.write(f"Validity proof for the generated carry certificate of target `{k}`.\n")
        f.write(f"The packed data lives in `{stem}Data.lean`; each bounded index range\n")
        f.write("is discharged by its own `decide +kernel`, and\n")
        f.write("`Certificate.valid_of_rangeOK` reassembles complete validity.\n")
        f.write("-/\n\n")
        f.write("namespace A277223\nnamespace CarryObstruction\nnamespace Certificate\n\n")
        f.write("set_option maxHeartbeats 0\n")
        f.write("set_option maxRecDepth 1000000\n\n")
        for idx, (lo, hi) in enumerate(ranges):
            f.write("set_option maxHeartbeats 0 in\n")
            f.write("set_option maxRecDepth 1000000 in\n")
            f.write(f"theorem {cert_name}_chunk_{idx} : rangeOK {k} {cert_name} {lo} {hi} = true := by\n")
            f.write("  decide +kernel\n\n")
        f.write(f"theorem {cert_name}_size : {cert_name}.total = {n} := by\n")
        f.write("  rfl\n\n")
        f.write("set_option maxHeartbeats 0 in\n")
        f.write("set_option maxRecDepth 1000000 in\n")
        f.write(f"theorem {cert_name}_header : {cert_name}.initial < {cert_name}.total ∧\n")
        f.write(f"    stateAt {cert_name} {cert_name}.initial = initialState {cert_name}.specs := by\n")
        f.write("  decide +kernel\n\n")
        f.write(f"theorem {cert_name}_valid : {cert_name}.Valid {k} := by\n")
        f.write(f"  refine valid_of_rangeOK {cert_name}_header.1 {cert_name}_header.2 ?_\n")
        f.write("  intro i hi\n")
        f.write(f"  rw [{cert_name}_size] at hi\n")
        for idx, (lo, hi_r) in enumerate(ranges[:-1]):
            f.write(f"  by_cases h{idx} : i < {hi_r}\n")
            f.write(f"  · exact ⟨{lo}, {hi_r}, by omega, by omega, {cert_name}_chunk_{idx}⟩\n")
        lo, hi_r = ranges[-1]
        f.write(f"  · exact ⟨{lo}, {hi_r}, by omega, by omega, {cert_name}_chunk_{len(ranges) - 1}⟩\n")
        f.write(f"theorem carryObstruction_{theorem_name} : CarryObstruction {k} :=\n")
        f.write(f"  carryObstruction_of_valid_certificate {cert_name}_valid\n\n")
        f.write("end Certificate\nend CarryObstruction\nend A277223\n")
    return path, len(states), terminal_count


def main():
    # Minimal witness pools that still cover every exact mass-k carry state.
    specs8 = [
        (2, 16, 0),
        (1125, 9, 3),
        (25, 20, 1),
        (2125, 17, 3),
        (45, 36, 1),
        (375, 30, 2),
        (2750, 22, 3),
    ]
    specs10 = [
        (2, 20, 0),
        (12, 12, 1),
        (15, 15, 1),
        (21, 21, 1),
        (22, 22, 1),
        (24, 24, 1),
    ]
    for k, stem, specs in [(8, "Eight", specs8), (10, "Ten", specs10)]:
        path, count, terminals = write_cert(k, stem, specs)
        print(f"{path.name}: {count} states, {terminals} terminal states")


if __name__ == "__main__":
    main()

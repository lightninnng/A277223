#!/usr/bin/env python3
"""Generate the small proof-carrying digit-mass certificates for Lean.

This is a generator, not a trusted proof component.  Lean re-checks the
resulting state/transition tables with `decide +kernel` and the generic
soundness theorem in CarryObstruction/Certificate.lean.
"""
from collections import deque
from pathlib import Path

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


def lean_state(state):
    mass, lanes = state
    ls = ", ".join(f"⟨{c}, {o}⟩" for c, o in lanes)
    return f"⟨{mass}, [{ls}]⟩"


def chunks(seq, n):
    for i in range(0, len(seq), n):
        yield seq[i:i+n]


def write_cert(k: int, stem: str, specs):
    states, flat, terminal_count = generate(k, specs)
    cert_name = f"cert{k}"
    theorem_name = "eight" if k == 8 else "ten"
    chunk_size = 512
    n = len(states)
    ranges = [(lo, min(lo + chunk_size, n)) for lo in range(0, n, chunk_size)]

    # --- data module: the state/transition literals, elaborated in their own
    # process so the memory footprint never overlaps with kernel checking of
    # the proof modules.  Both arrays are emitted as bounded-size parts
    # concatenated with ++: a single 76080-element literal overwhelms the
    # elaborator in the Mathlib environment (cascading 'Function expected'
    # errors near the end of the table) even though core Lean copes ---
    dpath = OUT / f"{stem}Data.lean"
    with dpath.open("w", encoding="utf-8", newline="\n") as f:
        f.write("import A277223.CarryObstruction.Certificate\n\n")
        f.write("/-!\n")
        f.write(f"Generated exact digit-mass carry data for target `{k}`.\n")
        f.write(f"States: {n}; mass-`{k}` terminal states: {terminal_count}.\n")
        f.write("The generator is `scripts/generate_carry_certificates.py`; this file is\n")
        f.write("re-checked by Lean and is not trusted as an external oracle.\n")
        f.write("Both tables are emitted as bounded parts concatenated with `++`;\n")
        f.write("a single table-sized literal overruns the elaborator.\n")
        f.write("-/\n\n")
        f.write("namespace A277223\nnamespace CarryObstruction\nnamespace Certificate\n\n")
        f.write("set_option maxHeartbeats 0\n")
        f.write("set_option maxRecDepth 1000000\n")
        f.write(lean_specs(f"cert{k}", specs))
        f.write("\n")

        def write_parts(prefix, ty, entries, per_part, per_line, render):
            parts = [entries[i:i + per_part] for i in range(0, len(entries), per_part)]
            for p, part in enumerate(parts):
                f.write(f"def {prefix}Part{p} : Array {ty} := #[\n")
                for chunk in chunks(part, per_line):
                    f.write("    " + " ".join(render(x) + "," for x in chunk) + "\n")
                f.write("  ]\n\n")
            f.write(f"def {prefix} : Array {ty} := " +
                    " ++ ".join(f"{prefix}Part{p}" for p in range(len(parts))) + "\n\n")

        write_parts(
            f"{cert_name}States", "MachineState", states, 2000, 4, lean_state)
        write_parts(
            f"{cert_name}Next", "ℕ", flat, 8000, 30, str)

        f.write(f"def {cert_name} : CarryCertificate := {{\n")
        f.write(f"  specs := cert{k}Specs\n")
        f.write(f"  states := {cert_name}States\n")
        f.write(f"  next := {cert_name}Next\n")
        f.write("  initial := 0\n")
        f.write("}\n\n")
        f.write("end Certificate\nend CarryObstruction\nend A277223\n")

    # --- proof modules: bounded-range kernel checks plus assembly.  Chunk
    # proofs are split at most five per module file: kernel-decide allocations
    # accumulate within one lean process, so each process checks a bounded
    # number of ranges and stays well inside a 16 GB build host ---
    chunks_per_file = 5
    parts = [ranges[i:i + chunks_per_file] for i in range(0, len(ranges), chunks_per_file)]
    part_names = []
    for p in range(len(parts)):
        # the final part lands in the module named `{stem}` itself, so the
        # existing importers (`Small.lean`) keep working unchanged
        part_names.append(stem if p == len(parts) - 1 else f"{stem}{chr(ord('A') + p)}")
    prev = f"{stem}Data"
    for p, (part, part_stem) in enumerate(zip(parts, part_names)):
        is_final = p == len(parts) - 1
        path = OUT / f"{part_stem}.lean"
        with path.open("w", encoding="utf-8", newline="\n") as f:
            f.write(f"import A277223.CarryObstruction.{prev}\n\n")
            f.write("/-!\n")
            if is_final:
                f.write(f"Validity proof for the generated carry certificate of target `{k}`.\n")
                f.write(f"The data lives in `{stem}Data.lean`; each bounded index range is\n")
                f.write("discharged by its own `decide +kernel` (a whole-table single decide\n")
                f.write("does not fit in the memory of a 16 GB build host), and\n")
                f.write("`Certificate.valid_of_rangeOK` reassembles complete validity.\n")
                f.write(f"Final range part; earlier parts live in {', '.join(n for n in part_names if n != stem)}.\n")
            else:
                f.write(f"Range checks {part[0][0]}..{part[-1][1]} of the generated carry\n")
                f.write(f"certificate for target `{k}`, split out to bound process memory.\n")
            f.write("-/\n\n")
            f.write("namespace A277223\nnamespace CarryObstruction\nnamespace Certificate\n\n")
            f.write("set_option maxHeartbeats 0\n")
            f.write("set_option maxRecDepth 1000000\n\n")
            base = p * chunks_per_file
            for idx, (lo, hi) in enumerate(part):
                f.write("set_option maxHeartbeats 0 in\n")
                f.write("set_option maxRecDepth 1000000 in\n")
                f.write(f"theorem {cert_name}_chunk_{base + idx} : rangeOK {k} {cert_name} {lo} {hi} = true := by\n")
                f.write("  decide +kernel\n\n")
            if is_final:
                f.write("set_option maxHeartbeats 0 in\n")
                f.write("set_option maxRecDepth 1000000 in\n")
                f.write(f"theorem {cert_name}_size : {cert_name}.states.size = {n} := by\n")
                f.write("  decide +kernel\n\n")
                f.write("set_option maxHeartbeats 0 in\n")
                f.write("set_option maxRecDepth 1000000 in\n")
                f.write(f"theorem {cert_name}_header : {cert_name}.next.size = 10 * {cert_name}.states.size ∧\n")
                f.write(f"    {cert_name}.initial < {cert_name}.states.size ∧\n")
                f.write(f"    stateAt {cert_name} {cert_name}.initial = initialState {cert_name}.specs := by\n")
                f.write("  decide +kernel\n\n")
                f.write(f"theorem {cert_name}_valid : {cert_name}.Valid {k} := by\n")
                f.write(f"  refine valid_of_rangeOK {cert_name}_header.1 {cert_name}_header.2.1 {cert_name}_header.2.2 ?_\n")
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
        prev = part_stem
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

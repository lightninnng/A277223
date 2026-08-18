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
    path = OUT / f"{stem}.lean"
    spec_name = f"{stem.lower()}"
    cert_name = f"cert{k}"
    theorem_name = "eight" if k == 8 else "ten"
    with path.open("w", encoding="utf-8") as f:
        f.write("import A277223.CarryObstruction.Certificate\n\n")
        f.write("/-!\n")
        f.write(f"Generated exact digit-mass carry certificate for target `{k}`.\n")
        f.write(f"States: {len(states)}; mass-`{k}` terminal states: {terminal_count}.\n")
        f.write("The generator is `scripts/generate_carry_certificates.py`; this file is\n")
        f.write("re-checked by Lean and is not trusted as an external oracle.\n")
        f.write("-/\n\n")
        f.write("namespace A277223\nnamespace CarryObstruction\nnamespace Certificate\n\n")
        f.write("set_option maxHeartbeats 0\n")
        f.write("set_option maxRecDepth 1000000\n")
        f.write(lean_specs(f"cert{k}", specs))
        f.write("\n")
        f.write(f"def {cert_name} : CarryCertificate := {{\n")
        f.write(f"  specs := cert{k}Specs\n")
        f.write("  states := #[\n")
        for chunk in chunks(states, 4):
            f.write("    " + ",\n    ".join(lean_state(s) for s in chunk) + ",\n")
        f.write("  ]\n")
        f.write("  next := #[\n")
        for chunk in chunks(flat, 30):
            f.write("    " + ", ".join(map(str, chunk)) + ",\n")
        f.write("  ]\n")
        f.write("  initial := 0\n")
        f.write("}\n\n")
        f.write("set_option maxHeartbeats 0 in\n")
        f.write("set_option maxRecDepth 1000000 in\n")
        f.write(f"theorem {cert_name}_valid : {cert_name}.Valid {k} := by\n")
        f.write("  decide +kernel\n\n")
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

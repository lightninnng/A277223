#!/usr/bin/env python3
"""Dry-run the hierarchical (Array-of-Arrays) certificate layout, core Lean.

Mirrors the proposed CarryCertificate redesign: stateParts/nextParts of a
fixed part size, so stateAt/nextId evaluate only one bounded part per access
instead of one table-sized array.  Emits D3.lean (data) and C3.lean (one
5-chunk proof file, the size of EightA) to measure kernel time and memory.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate_carry_certificates import generate

specs8 = [
    (2, 16, 0),
    (1125, 9, 3),
    (25, 20, 1),
    (2125, 17, 3),
    (45, 36, 1),
    (375, 30, 2),
    (2750, 22, 3),
]

CHUNK = 512
PART = 2000

states, flat, terminal_count = generate(8, specs8)
n = len(states)
npad = (-n) % PART
padded = states + [(0, [])] * npad
parts = [padded[i:i + PART] for i in range(0, len(padded), PART)]
next_parts = []
for p in range(len(parts)):
    cells = flat[10 * PART * p : 10 * PART * (p + 1)]
    if len(cells) < 10 * PART:
        cells = cells + [0] * (10 * PART - len(cells))
    next_parts.append(cells)

out = Path(__file__).resolve().parent.parent / "dryrun"

def lean_state(state):
    mass, lanes = state
    ls = ", ".join(f"⟨{c}, {o}⟩" for c, o in lanes)
    return f"⟨{mass}, [{ls}]⟩"

common = '''namespace DryRun

structure WitnessSpec where
  c : Nat
  j : Nat
  z : Nat
  deriving DecidableEq

structure LaneState where
  carry : Nat
  out : Nat
  deriving DecidableEq

structure MachineState where
  mass : Nat
  lanes : List LaneState
  deriving DecidableEq

def digitSum10 : Nat → Nat
  | 0 => 0
  | n + 1 =>
      if n + 1 < 10 then n + 1 else (n + 1) % 10 + digitSum10 ((n + 1) / 10)

def finalScore (s : LaneState) : Nat := s.out + digitSum10 s.carry

def stepLane (c : Nat) (s : LaneState) (d : Nat) : LaneState :=
  let v := c * d + s.carry
  ⟨v / 10, s.out + v % 10⟩

def terminalHit (k : Nat) : List WitnessSpec → List LaneState → Bool
  | sp :: specs, lane :: lanes =>
      decide (k < sp.j ∧ sp.c * k = sp.j * 10 ^ sp.z ∧ finalScore lane = sp.j) ||
        terminalHit k specs lanes
  | _, _ => false

structure CarryCertificate where
  specs : List WitnessSpec
  stateParts : Array (Array MachineState)
  nextParts : Array (Array Nat)
  statePartSize : Nat
  total : Nat
  initial : Nat

def initialState (specs : List WitnessSpec) : MachineState :=
  ⟨0, specs.map (fun _ => ⟨0, 0⟩)⟩

def stateAt (cert : CarryCertificate) (i : Nat) : MachineState :=
  match cert.stateParts[i / cert.statePartSize]? with
  | some part => (part[i % cert.statePartSize]?).getD ⟨0, []⟩
  | none => ⟨0, []⟩

def nextId (cert : CarryCertificate) (i d : Nat) : Nat :=
  let cell := 10 * i + d
  match cert.nextParts[cell / (10 * cert.statePartSize)]? with
  | some part => (part[cell % (10 * cert.statePartSize)]?).getD 0
  | none => 0

def stepState (specs : List WitnessSpec) (s : MachineState) (d : Nat) : MachineState :=
  ⟨s.mass + d, List.zipWith (fun sp lane => stepLane sp.c lane d) specs s.lanes⟩

def stateOKBool (k : Nat) (cert : CarryCertificate) (i : Nat) : Bool :=
  ((List.range 10).all fun d =>
      if (stateAt cert i).mass + d ≤ k then
        decide (nextId cert i d < cert.total) &&
          decide (stateAt cert (nextId cert i d) = stepState cert.specs (stateAt cert i) d)
      else true) &&
  (if (stateAt cert i).mass = k then terminalHit k cert.specs (stateAt cert i).lanes else true)

def rangeOK (k : Nat) (cert : CarryCertificate) (lo hi : Nat) : Bool :=
  (List.range hi).all fun i =>
    if lo ≤ i then stateOKBool k cert i else true

end DryRun
'''

d = [common, "", "namespace DryRun", "", "set_option maxHeartbeats 0", "set_option maxRecDepth 1000000", ""]
spec_rows = ", ".join(f"⟨{c}, {j}, {z}⟩" for c, j, z in specs8)
d.append(f"def cert8Specs : List WitnessSpec := [{spec_rows}]")
d.append("")
for p, part in enumerate(parts):
    d.append(f"def cert8StatesP{p} : Array MachineState := #[")
    for i in range(0, len(part), 4):
        d.append("    " + " ".join(lean_state(s) + "," for s in part[i:i+4]))
    d.append("  ]")
    d.append("")
for p, cells in enumerate(next_parts):
    d.append(f"def cert8NextP{p} : Array Nat := #[")
    for i in range(0, len(cells), 30):
        d.append("    " + " ".join(str(x) + "," for x in cells[i:i+30]))
    d.append("  ]")
    d.append("")
d.append("def cert8 : CarryCertificate := {")
d.append("  specs := cert8Specs")
d.append("  stateParts := #[" + ", ".join(f"cert8StatesP{p}" for p in range(len(parts))) + "]")
d.append("  nextParts := #[" + ", ".join(f"cert8NextP{p}" for p in range(len(parts))) + "]")
d.append(f"  statePartSize := {PART}")
d.append(f"  total := {n}")
d.append("  initial := 0")
d.append("}")
d.append("")
d.append("end DryRun")
(out / "D3.lean").write_text("\n".join(d) + "\n", encoding="utf-8", newline="\n")

c = ["import D3", "", "namespace DryRun", "", "set_option maxHeartbeats 0", "set_option maxRecDepth 1000000", ""]
for idx in range(5):
    lo = idx * CHUNK
    hi = min((idx + 1) * CHUNK, n)
    c.append("set_option maxHeartbeats 0 in")
    c.append("set_option maxRecDepth 1000000 in")
    c.append(f"theorem cert8_chunk_{idx} : rangeOK 8 cert8 {lo} {hi} = true := by")
    c.append("  decide +kernel")
    c.append("")
c.append("set_option maxHeartbeats 0 in")
c.append("set_option maxRecDepth 1000000 in")
c.append(f"theorem cert8_size : cert8.total = {n} := by")
c.append("  decide +kernel")
c.append("")
c.append("end DryRun")
(out / "C3.lean").write_text("\n".join(c) + "\n", encoding="utf-8", newline="\n")

print(f"wrote D3.lean ({len(parts)} parts of {PART}, total {n}) and C3.lean (5 chunks + size)")

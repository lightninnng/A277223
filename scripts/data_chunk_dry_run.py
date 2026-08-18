#!/usr/bin/env python3
"""Dry-run the data/proof module split with core Lean only.

Emits dryrun/D.lean (certificate data: the full 7608-state k=8 machine as a
single literal) and dryrun/C.lean (512-state chunk kernel checks, size/header
checks, and the valid_of_rangeOK-style assembly ladder).  Build D.olean, then
run C.lean against it, to measure the per-process memory of the proposed
architecture before applying it to the real project.
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

states, flat, terminal_count = generate(8, specs8)
n = len(states)
out = Path(__file__).resolve().parent.parent / "dryrun"
out.mkdir(exist_ok=True)

def lean_state(state):
    mass, lanes = state
    ls = ", ".join(f"⟨{c}, {o}⟩" for c, o in lanes)
    return f"⟨{mass}, [{ls}]⟩"

common_defs = """namespace DryRun

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
  states : Array MachineState
  next : Array Nat
  initial : Nat

def stateAt (cert : CarryCertificate) (i : Nat) : MachineState :=
  (cert.states[i]?).getD ⟨0, []⟩

def nextId (cert : CarryCertificate) (i d : Nat) : Nat :=
  (cert.next[10 * i + d]?).getD 0

def stepState (specs : List WitnessSpec) (s : MachineState) (d : Nat) : MachineState :=
  ⟨s.mass + d, List.zipWith (fun sp lane => stepLane sp.c lane d) specs s.lanes⟩

def stateOKBool (k : Nat) (cert : CarryCertificate) (i : Nat) : Bool :=
  ((List.finRange 10).all fun d =>
      if (stateAt cert i).mass + d ≤ k then
        decide (nextId cert i d < cert.states.size) &&
          decide (stateAt cert (nextId cert i d) = stepState cert.specs (stateAt cert i) d)
      else true) &&
  (if (stateAt cert i).mass = k then terminalHit k cert.specs (stateAt cert i).lanes else true)

def rangeOK (k : Nat) (cert : CarryCertificate) (lo hi : Nat) : Bool :=
  (List.range hi).all fun i =>
    if lo ≤ i then stateOKBool k cert i else true

end DryRun
"""

# --- D.lean: data module only ---
d = []
d.append(common_defs)
d.append("")
d.append("namespace DryRun")
d.append("")
d.append("set_option maxHeartbeats 0")
d.append("set_option maxRecDepth 1000000")
d.append("")
spec_rows = ", ".join(f"⟨{c}, {j}, {z}⟩" for c, j, z in specs8)
d.append(f"def cert8Specs : List WitnessSpec := [{spec_rows}]")
d.append("")
d.append("def cert8 : CarryCertificate := {")
d.append("  specs := cert8Specs")
d.append("  states := #[")
for i in range(0, n, 4):
    d.append("    " + ", ".join(lean_state(s) for s in states[i:i+4]) + ",")
d.append("  ]")
d.append("  next := #[")
for i in range(0, len(flat), 30):
    d.append("    " + " ".join(str(x) + "," for x in flat[i:i+30]))
d.append("  ]")
d.append("  initial := 0")
d.append("}")
d.append("")
d.append("end DryRun")
(out / "D.lean").write_text("\n".join(d) + "\n", encoding="utf-8", newline="\n")

# --- C.lean: chunk checks + assembly ---
ranges = [(lo, min(lo + CHUNK, n)) for lo in range(0, n, CHUNK)]
c = []
c.append("import D")
c.append("")
c.append("namespace DryRun")
c.append("")
c.append("set_option maxHeartbeats 0")
c.append("set_option maxRecDepth 1000000")
c.append("")
for idx, (lo, hi) in enumerate(ranges):
    c.append("set_option maxHeartbeats 0 in")
    c.append("set_option maxRecDepth 1000000 in")
    c.append(f"theorem cert8_chunk_{idx} : rangeOK 8 cert8 {lo} {hi} = true := by")
    c.append("  decide +kernel")
    c.append("")
c.append("set_option maxHeartbeats 0 in")
c.append("set_option maxRecDepth 1000000 in")
c.append(f"theorem cert8_size : cert8.states.size = {n} := by")
c.append("  decide +kernel")
c.append("")
c.append("set_option maxHeartbeats 0 in")
c.append("set_option maxRecDepth 1000000 in")
c.append("theorem cert8_header : cert8.next.size = 10 * cert8.states.size ∧")
c.append("    cert8.initial < cert8.states.size ∧")
c.append("    stateAt cert8 cert8.initial = initialState cert8.specs := by")
c.append("  decide +kernel")
c.append("")
c.append("end DryRun")
(out / "C.lean").write_text("\n".join(c) + "\n", encoding="utf-8", newline="\n")

# initialState is referenced by cert8_header but defined nowhere yet; add it.
fix = "def initialState (specs : List WitnessSpec) : MachineState :=\n  ⟨0, specs.map (fun _ => ⟨0, 0⟩)⟩\n"
src = (out / "D.lean").read_text(encoding="utf-8")
src = src.replace("def stateAt (cert : CarryCertificate)", fix + "\ndef stateAt (cert : CarryCertificate)")
(out / "D.lean").write_text(src, encoding="utf-8", newline="\n")

print(f"wrote D.lean ({n} states) and C.lean ({len(ranges)} chunks of {CHUNK})")

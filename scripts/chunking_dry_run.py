#!/usr/bin/env python3
"""Dry-run the chunked certificate check with core Lean only (no Mathlib).

Reuses the real machine generated for k=8 (7608 states, 7 witness lanes) and
emits a standalone .lean file that mirrors the proposed Certificate.lean
boolean checkers, so kernel-reduction cost and memory can be measured locally
before touching the real project.
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

if "--micro" in sys.argv:
    k_target, specs8, CHUNK = 2, [(5, 10, 0)], 8
else:
    k_target = 8

states, flat, terminal_count = generate(k_target, specs8)
n = len(states)
CHUNK = 1024
out = Path(__file__).resolve().parent.parent / "dryrun"
out.mkdir(exist_ok=True)

def lean_state(state):
    mass, lanes = state
    ls = ", ".join(f"⟨{c}, {o}⟩" for c, o in lanes)
    return f"⟨{mass}, [{ls}]⟩"

lines = []
lines.append("namespace DryRun")
lines.append("")
lines.append("set_option maxHeartbeats 0")
lines.append("set_option maxRecDepth 1000000")
lines.append("")
lines.append("structure WitnessSpec where")
lines.append("  c : Nat")
lines.append("  j : Nat")
lines.append("  z : Nat")
lines.append("  deriving DecidableEq")
lines.append("")
lines.append("structure LaneState where")
lines.append("  carry : Nat")
lines.append("  out : Nat")
lines.append("  deriving DecidableEq")
lines.append("")
lines.append("structure MachineState where")
lines.append("  mass : Nat")
lines.append("  lanes : List LaneState")
lines.append("  deriving DecidableEq")
lines.append("")
lines.append("def digitSum10 : Nat → Nat")
lines.append("  | 0 => 0")
lines.append("  | n + 1 =>")
lines.append("      if n + 1 < 10 then n + 1 else (n + 1) % 10 + digitSum10 ((n + 1) / 10)")
lines.append("")
lines.append("def finalScore (s : LaneState) : Nat := s.out + digitSum10 s.carry")
lines.append("")
lines.append("def stepLane (c : Nat) (s : LaneState) (d : Nat) : LaneState :=")
lines.append("  let v := c * d + s.carry")
lines.append("  ⟨v / 10, s.out + v % 10⟩")
lines.append("")
lines.append("def terminalHit (k : Nat) : List WitnessSpec → List LaneState → Bool")
lines.append("  | sp :: specs, lane :: lanes =>")
lines.append("      decide (k < sp.j ∧ sp.c * k = sp.j * 10 ^ sp.z ∧ finalScore lane = sp.j) ||")
lines.append("        terminalHit k specs lanes")
lines.append("  | _, _ => false")
lines.append("")
lines.append("structure CarryCertificate where")
lines.append("  specs : List WitnessSpec")
lines.append("  states : Array MachineState")
lines.append("  next : Array Nat")
lines.append("  initial : Nat")
lines.append("")
lines.append("def stateAt (cert : CarryCertificate) (i : Nat) : MachineState :=")
lines.append("  (cert.states[i]?).getD ⟨0, []⟩")
lines.append("")
lines.append("def nextId (cert : CarryCertificate) (i d : Nat) : Nat :=")
lines.append("  (cert.next[10 * i + d]?).getD 0")
lines.append("")
lines.append("def stepState (specs : List WitnessSpec) (s : MachineState) (d : Nat) : MachineState :=")
lines.append("  ⟨s.mass + d, List.zipWith (fun sp lane => stepLane sp.c lane d) specs s.lanes⟩")
lines.append("")
lines.append("def stateOKBool (k : Nat) (cert : CarryCertificate) (i : Nat) : Bool :=")
lines.append("  ((List.finRange 10).all fun d =>")
lines.append("      if (stateAt cert i).mass + d ≤ k then")
lines.append("        decide (nextId cert i d < cert.states.size) &&")
lines.append("          decide (stateAt cert (nextId cert i d) = stepState cert.specs (stateAt cert i) d)")
lines.append("      else true) &&")
lines.append("  (if (stateAt cert i).mass = k then terminalHit k cert.specs (stateAt cert i).lanes else true)")
lines.append("")
lines.append("def rangeOK (k : Nat) (cert : CarryCertificate) (lo hi : Nat) : Bool :=")
lines.append("  (List.range hi).all fun i =>")
lines.append("    if lo ≤ i then stateOKBool k cert i else true")
lines.append("")
spec_rows = ", ".join(f"⟨{c}, {j}, {z}⟩" for c, j, z in specs8)
lines.append(f"def cert8Specs : List WitnessSpec := [{spec_rows}]")
lines.append("")
lines.append("def cert8 : CarryCertificate := {")
lines.append("  specs := cert8Specs")
lines.append("  states := #[")
for i in range(0, n, 4):
    lines.append("    " + ", ".join(lean_state(s) for s in states[i:i+4]) + ",")
lines.append("  ]")
lines.append("  next := #[")
for i in range(0, len(flat), 30):
    lines.append("    " + " ".join(str(x) + "," for x in flat[i:i+30]))
lines.append("  ]")
lines.append("  initial := 0")
lines.append("}")
lines.append("")

# chunk theorems
nchunks = (n + CHUNK - 1) // CHUNK
for c in range(nchunks):
    lo = c * CHUNK
    hi = min((c + 1) * CHUNK, n)
    lines.append(f"set_option maxHeartbeats 0 in")
    lines.append(f"theorem cert8_chunk_{c} : rangeOK {k_target} cert8 {lo} {hi} = true := by")
    lines.append("  decide +kernel")
    lines.append("")

# also a full single-range check for comparison, behind a flag
if "--full" in sys.argv:
    lines.append("set_option maxHeartbeats 0 in")
    lines.append(f"theorem cert8_full : rangeOK {k_target} cert8 0 {n} = true := by")
    lines.append("  decide +kernel")
    lines.append("")

if "--header" in sys.argv:
    lines.append("set_option maxHeartbeats 0 in")
    lines.append("theorem cert8_header : cert8.next.size = 10 * cert8.states.size := by")
    lines.append("  decide +kernel")
    lines.append("")

lines.append("end DryRun")

target = out / ("TestFull.lean" if "--full" in sys.argv else "TestChunks.lean")
target.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
print(f"wrote {target} ({n} states, {len(flat)} transitions, terminal={terminal_count}, chunks={nchunks})")

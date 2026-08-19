import A277223.CarryObstruction.Theory

/-!
# Proof-carrying finite certificates for carry obstruction

This file does not enumerate candidate integers `n`.  It formalizes the usual
right-to-left decimal multiplication algorithm.  A certificate contains a
finite set of exact carry states for a *fixed total input digit mass* `k`, plus
a transition table.  Soundness is proved once, for arbitrary decimal digit
lists.  Concrete certificates for `k=8` and `k=10` are generated from the
structural Carry-Obstruction witnesses in the paper.

The accumulated output digit sum is exact (not capped).  Consequently the
certificate checker is a straightforward reflection of schoolbook decimal
multiplication.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

/-- Rescaling parameters without proofs; validity is checked at a terminal state. -/
structure WitnessSpec where
  c : ℕ
  j : ℕ
  z : ℕ
  deriving DecidableEq, Repr

/-- State of one schoolbook-multiplication lane. -/
structure LaneState where
  carry : ℕ
  out : ℕ
  deriving DecidableEq, Repr

@[simp] def zeroLane : LaneState := ⟨0, 0⟩

/-- One exact digit transition for multiplication by `c`. -/
def stepLane (c : ℕ) (s : LaneState) (d : ℕ) : LaneState :=
  let v := c * d + s.carry
  ⟨v / 10, s.out + v % 10⟩

/-- Process a little-endian list of decimal digits. -/
def runLane (c : ℕ) : LaneState → List ℕ → LaneState
  | s, [] => s
  | s, d :: ds => runLane c (stepLane c s d) ds

/-- Digit sum represented by a completed lane. -/
def finalScore (s : LaneState) : ℕ := s.out + digitSum10 s.carry

/-- `e + 10*r` has the expected digit-sum decomposition when `e` is a digit. -/
theorem digitSum10_lowDigit {e r : ℕ} (he : e < 10) :
    digitSum10 (e + 10 * r) = e + digitSum10 r := by
  by_cases hz : e = 0 ∧ r = 0
  · rcases hz with ⟨rfl, rfl⟩
    simp
  · unfold digitSum10
    rw [Nat.digits_add 10 (by norm_num : 1 < 10) e r he (by tauto)]
    simp

/-- Exact semantic invariant of the lane machine. -/
theorem runLane_correct (c : ℕ) (s : LaneState) (L : List ℕ) :
    finalScore (runLane c s L) =
      s.out + digitSum10 (c * Nat.ofDigits 10 L + s.carry) := by
  induction L generalizing s with
  | nil => simp [runLane, finalScore, Nat.ofDigits]
  | cons d L ih =>
      let v := c * d + s.carry
      have hv : v % 10 + 10 * (v / 10) = v := Nat.mod_add_div v 10
      have htotal :
          c * Nat.ofDigits 10 (d :: L) + s.carry =
            v % 10 + 10 * (c * Nat.ofDigits 10 L + v / 10) := by
        calc
          c * Nat.ofDigits 10 (d :: L) + s.carry
              = (c * d + s.carry) + 10 * (c * Nat.ofDigits 10 L) := by
                  simp only [Nat.ofDigits_cons]
                  ring
          _ = (v % 10 + 10 * (v / 10)) + 10 * (c * Nat.ofDigits 10 L) := by
                  rw [hv]
          _ = v % 10 + 10 * (c * Nat.ofDigits 10 L + v / 10) := by ring
      have hsplit :
          digitSum10 (c * Nat.ofDigits 10 (d :: L) + s.carry) =
            v % 10 + digitSum10 (c * Nat.ofDigits 10 L + v / 10) := by
        rw [htotal, digitSum10_lowDigit (Nat.mod_lt _ (by norm_num : 0 < 10))]
      change finalScore (runLane c (stepLane c s d) L) = _
      rw [ih, hsplit]
      simp [stepLane, v]
      omega

/-- State shared by all rescaling lanes. `mass` is the sum of processed input digits. -/
structure MachineState where
  mass : ℕ
  lanes : List LaneState
  deriving DecidableEq, Repr

@[simp] def defaultState : MachineState := ⟨0, []⟩

/-- Initial state for a list of witness specifications. -/
def initialState (specs : List WitnessSpec) : MachineState :=
  ⟨0, specs.map (fun _ => zeroLane)⟩

/-- Advance every multiplication lane by the same input digit. -/
def stepState (specs : List WitnessSpec) (s : MachineState) (d : ℕ) : MachineState :=
  ⟨s.mass + d,
    List.zipWith (fun sp lane => stepLane sp.c lane d) specs s.lanes⟩

/-- Process a digit list from an arbitrary machine state. -/
def runMachineFrom (specs : List WitnessSpec) : MachineState → List ℕ → MachineState
  | s, [] => s
  | s, d :: ds => runMachineFrom specs (stepState specs s d) ds

/-- Process a digit list from the zero state. -/
def runMachine (specs : List WitnessSpec) (L : List ℕ) : MachineState :=
  runMachineFrom specs (initialState specs) L

/-- A `zipWith` against a mapped copy of the same specification list. -/
theorem zipWith_map_same (specs : List WitnessSpec) (f : WitnessSpec → LaneState) (d : ℕ) :
    List.zipWith (fun sp lane => stepLane sp.c lane d) specs (specs.map f) =
      specs.map (fun sp => stepLane sp.c (f sp) d) := by
  induction specs with
  | nil => simp
  | cons sp specs ih => simp [ih]

/-- Semantic form of all lanes after running a digit suffix. -/
theorem runMachineFrom_lanes (specs : List WitnessSpec) (L : List ℕ)
    (s : MachineState) (f : WitnessSpec → LaneState)
    (hs : s.lanes = specs.map f) :
    (runMachineFrom specs s L).lanes =
      specs.map (fun sp => runLane sp.c (f sp) L) := by
  induction L generalizing s f with
  | nil => simpa [runMachineFrom, runLane] using hs
  | cons d L ih =>
      have hstep :
          (stepState specs s d).lanes =
            specs.map (fun sp => stepLane sp.c (f sp) d) := by
        simp only [stepState, hs]
        exact zipWith_map_same specs f d
      simpa [runMachineFrom, runLane] using
        ih (stepState specs s d) (fun sp => stepLane sp.c (f sp) d) hstep

/-- In particular, each final lane is the exact lane run from zero. -/
theorem runMachine_lanes (specs : List WitnessSpec) (L : List ℕ) :
    (runMachine specs L).lanes =
      specs.map (fun sp => runLane sp.c zeroLane L) := by
  apply runMachineFrom_lanes specs L (initialState specs) (fun _ => zeroLane)
  rfl

/-- The mass component equals the sum of processed input digits. -/
theorem runMachineFrom_mass (specs : List WitnessSpec) (L : List ℕ) (s : MachineState) :
    (runMachineFrom specs s L).mass = s.mass + L.sum := by
  induction L generalizing s with
  | nil => simp [runMachineFrom]
  | cons d L ih =>
      rw [runMachineFrom, ih]
      simp [stepState]
      omega

@[simp] theorem runMachine_mass (specs : List WitnessSpec) (L : List ℕ) :
    (runMachine specs L).mass = L.sum := by
  simpa [runMachine, initialState] using
    runMachineFrom_mass specs L (initialState specs)

/-- Boolean terminal test: some lane is a valid larger decimal rescaling. -/
def terminalHit (k : ℕ) : List WitnessSpec → List LaneState → Bool
  | sp :: specs, lane :: lanes =>
      decide (k < sp.j ∧ sp.c * k = sp.j * 10 ^ sp.z ∧ finalScore lane = sp.j) ||
        terminalHit k specs lanes
  | _, _ => false

/-- A successful terminal test on semantic lanes yields a rescaling witness. -/
theorem terminalHit_semantic_sound (k : ℕ) (L : List ℕ) :
    ∀ specs : List WitnessSpec,
      terminalHit k specs (specs.map (fun sp => runLane sp.c zeroLane L)) = true →
        Nonempty (RescalingWitness k (Nat.ofDigits 10 L))
  | [], h => by simp [terminalHit] at h
  | sp :: specs, h => by
      simp only [List.map_cons, terminalHit, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with hhead | htail
      · refine ⟨{
          c := sp.c
          j := sp.j
          z := sp.z
          larger := hhead.1
          scale := hhead.2.1
          digitSum := ?_
        }⟩
        have hrun := runLane_correct sp.c zeroLane L
        simp [finalScore, zeroLane] at hrun
        rw [← hrun]
        exact hhead.2.2
      · exact terminalHit_semantic_sound k L specs htail

/-!
### Packed certificate data

Kernel `decide` re-evaluates an array literal at every access with no
sharing, so a table-shaped certificate costs one full table construction
per lookup and quickly exhausts both time and memory.  The certificate
therefore stores both tables as single natural numbers and decodes with
the kernel's native bitwise operations (`>>>`, `&&&`), which operate
directly on GMP integers in time linear in the number's size.

Packing layout (little-endian, 13 bits per field, all values below 8192):
a state occupies `stateBits = 13 * (1 + 2 * laneCount)` bits: the mass,
then per lane the carry followed by the out-sum.  A transition row occupies
130 bits: the ten target indices, 13 bits each.
-/

/-- Certificate data as packed natural numbers plus decoding parameters. -/
structure CarryCertificate where
  specs : List WitnessSpec
  statesPacked : ℕ
  nextPacked : ℕ
  /-- Number of encoded states; `stateAt` is only queried below it. -/
  total : ℕ
  /-- Bit width of one packed state: `13 * (1 + 2 * laneCount)`. -/
  stateBits : ℕ
  laneCount : ℕ
  initial : ℕ

/-- One multiplication lane decoded from 13-bit fields of a packed state. -/
def laneOf (s : ℕ) (j : ℕ) : LaneState :=
  ⟨(s >>> (13 * (1 + 2 * j))) &&& 8191, (s >>> (13 * (2 + 2 * j))) &&& 8191⟩

/-- A machine state decoded from its packed bit slice. -/
def decodeState (lanes : ℕ) (s : ℕ) : MachineState :=
  ⟨s &&& 8191, (List.range lanes).map (laneOf s)⟩

/-- Safe packed lookup used by the certificate logic. -/
def stateAt (cert : CarryCertificate) (i : ℕ) : MachineState :=
  decodeState cert.laneCount
    ((cert.statesPacked >>> (cert.stateBits * i)) &&& (2 ^ cert.stateBits - 1))

/-- Transition ID for digit `d`, decoded from the packed row table. -/
def nextId (cert : CarryCertificate) (i d : ℕ) : ℕ :=
  (cert.nextPacked >>> (130 * i + 13 * d)) &&& 8191

/--
A proof-carrying certificate is valid when the initial state is present,
every transition compatible with total digit mass `k` is represented exactly,
and every mass-`k` state has a terminal rescaling hit.
-/
def CarryCertificate.Valid (k : ℕ) (cert : CarryCertificate) : Prop :=
  cert.initial < cert.total ∧
  stateAt cert cert.initial = initialState cert.specs ∧
  (∀ i : Fin cert.total, ∀ d : Fin 10,
      (stateAt cert i.val).mass + d.val ≤ k →
        nextId cert i.val d.val < cert.total ∧
          stateAt cert (nextId cert i.val d.val) =
            stepState cert.specs (stateAt cert i.val) d.val) ∧
  (∀ i : Fin cert.total,
      (stateAt cert i.val).mass = k →
        terminalHit k cert.specs (stateAt cert i.val).lanes = true)

/-- The validity check is decidable: unfold the definition and appeal to the
computable instances on its components. -/
instance instDecidableValid (k : ℕ) (cert : CarryCertificate) : Decidable (cert.Valid k) := by
  unfold CarryCertificate.Valid
  exact inferInstance

/-!
### Range-restricted certificate checks

A single `decide +kernel` over the whole state table of a large certificate
(the `k = 8` machine has 7608 states) does not fit into the memory of a
standard 16 GB build host: the kernel reduction of the complete `Valid`
proposition allocates for every state simultaneously.  The per-state
obligations are therefore reflected into a boolean checker over a state-index
range; a certificate file discharges each bounded range with its own
`decide +kernel`, and `valid_of_rangeOK` reassembles complete validity from
the chunk results with an ordinary proof term.
-/

/-- Boolean reflection of the per-state obligations of `CarryCertificate.Valid`. -/
def stateOKBool (k : ℕ) (cert : CarryCertificate) (i : ℕ) : Bool :=
  ((List.range 10).all fun d =>
      if (stateAt cert i).mass + d ≤ k then
        decide (nextId cert i d < cert.total) &&
          decide (stateAt cert (nextId cert i d) = stepState cert.specs (stateAt cert i) d)
      else true) &&
  (if (stateAt cert i).mass = k then terminalHit k cert.specs (stateAt cert i).lanes else true)

theorem stateOK_of_bool {k : ℕ} {cert : CarryCertificate} {i : ℕ}
    (h : stateOKBool k cert i = true) :
    (∀ d : ℕ, d < 10 →
      (stateAt cert i).mass + d ≤ k →
        nextId cert i d < cert.total ∧
          stateAt cert (nextId cert i d) = stepState cert.specs (stateAt cert i) d) ∧
    ((stateAt cert i).mass = k → terminalHit k cert.specs (stateAt cert i).lanes = true) := by
  rw [stateOKBool, Bool.and_eq_true] at h
  obtain ⟨hall, hterm⟩ := h
  refine ⟨fun d hd hle => ?_, fun hmass => ?_⟩
  · have hmem : d ∈ List.range 10 := List.mem_range.mpr hd
    have hdall := List.all_eq_true.1 hall d hmem
    rw [if_pos hle] at hdall
    rw [Bool.and_eq_true] at hdall
    exact ⟨of_decide_eq_true hdall.1, of_decide_eq_true hdall.2⟩
  · rw [if_pos hmass] at hterm
    exact hterm

/-- Boolean chunk check: every state index in `[lo, hi)` passes `stateOKBool`.
Enumerates only the `hi - lo` in-range offsets; enumerating from zero would
make the cost of a chunk grow with its absolute position. -/
def rangeOK (k : ℕ) (cert : CarryCertificate) (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all fun off =>
    stateOKBool k cert (lo + off)

theorem stateOK_of_rangeOK {k : ℕ} {cert : CarryCertificate} {lo hi i : ℕ}
    (h : rangeOK k cert lo hi = true) (hlo : lo ≤ i) (hhi : i < hi) :
    (∀ d : ℕ, d < 10 →
      (stateAt cert i).mass + d ≤ k →
        nextId cert i d < cert.total ∧
          stateAt cert (nextId cert i d) = stepState cert.specs (stateAt cert i) d) ∧
    ((stateAt cert i).mass = k → terminalHit k cert.specs (stateAt cert i).lanes = true) := by
  have hmem : i - lo ∈ List.range (hi - lo) := List.mem_range.mpr (by omega)
  have hdall := List.all_eq_true.1 h (i - lo) hmem
  have hidx : lo + (i - lo) = i := by omega
  rw [hidx] at hdall
  exact stateOK_of_bool hdall

/-- Assemble `CarryCertificate.Valid` from bounded range checks. -/
theorem valid_of_rangeOK {k : ℕ} {cert : CarryCertificate}
    (hinit : cert.initial < cert.total)
    (hinitstate : stateAt cert cert.initial = initialState cert.specs)
    (hcover : ∀ i, i < cert.total →
      ∃ lo hi, lo ≤ i ∧ i < hi ∧ rangeOK k cert lo hi = true) :
    cert.Valid k := by
  unfold CarryCertificate.Valid
  refine ⟨hinit, hinitstate, ?_, ?_⟩
  · intro i d hcond
    obtain ⟨lo, hi, hlo, hhi, hok⟩ := hcover i.val i.isLt
    exact (stateOK_of_rangeOK hok hlo hhi).1 d.val d.isLt hcond
  · intro i hmass
    obtain ⟨lo, hi, hlo, hhi, hok⟩ := hcover i.val i.isLt
    exact (stateOK_of_rangeOK hok hlo hhi).2 hmass

/-- Follow certificate transition IDs. -/
def runIdFrom (cert : CarryCertificate) : ℕ → List ℕ → ℕ
  | i, [] => i
  | i, d :: ds => runIdFrom cert (nextId cert i d) ds

/--
Soundness of following the transition table.  The hypothesis `s.mass + L.sum ≤ k`
is precisely what makes every requested transition a certified one.
-/
theorem runIdFrom_sound {k : ℕ} {cert : CarryCertificate}
    (hvalid : cert.Valid k) :
    ∀ {i : ℕ} {s : MachineState} {L : List ℕ},
      i < cert.total →
      stateAt cert i = s →
      s.mass + L.sum ≤ k →
      (∀ d ∈ L, d < 10) →
      let j := runIdFrom cert i L
      j < cert.total ∧
        stateAt cert j = runMachineFrom cert.specs s L
  | i, s, [], hi, his, hmass, hdigits => by
      simp [runIdFrom, runMachineFrom, hi, his]
  | i, s, d :: ds, hi, his, hmass, hdigits => by
      rcases hvalid with ⟨hinitb, hinits, htrans, hterminal⟩
      have hd10 : d < 10 := hdigits d (by simp)
      have hstepmass : s.mass + d ≤ k := by
        simp only [List.sum_cons] at hmass
        omega
      have ht := htrans ⟨i, hi⟩ ⟨d, hd10⟩
      have htcond : (stateAt cert i).mass + d ≤ k := by simpa [his] using hstepmass
      obtain ⟨hnextb, hnexts⟩ := ht htcond
      have hremain : (stepState cert.specs s d).mass + ds.sum ≤ k := by
        simp only [stepState, List.sum_cons] at hmass ⊢
        omega
      have htaildigits : ∀ x ∈ ds, x < 10 := by
        intro x hx
        exact hdigits x (List.mem_cons_of_mem d hx)
      have hrec := runIdFrom_sound
        (k := k) (cert := cert) ⟨hinitb, hinits, htrans, hterminal⟩
        (i := nextId cert i d) (s := stepState cert.specs s d) (L := ds)
        hnextb (by simpa [his] using hnexts) hremain htaildigits
      simpa [runIdFrom, runMachineFrom] using hrec

/-- A valid carry certificate proves the abstract carry-obstruction property. -/
theorem carryObstruction_of_valid_certificate {k : ℕ} {cert : CarryCertificate}
    (hvalid : cert.Valid k) : CarryObstruction k := by
  intro m hm
  let L := Nat.digits 10 m
  have hsum : L.sum = k := by simpa [L, digitSum10] using hm
  have hdigits : ∀ d ∈ L, d < 10 := by
    intro d hd
    exact Nat.digits_lt_base (by norm_num : 1 < 10) (by simpa [L] using hd)
  rcases hvalid with ⟨hinitb, hinits, htrans, hterminal⟩
  have hwalk := runIdFrom_sound
    (k := k) (cert := cert) ⟨hinitb, hinits, htrans, hterminal⟩
    (i := cert.initial) (s := initialState cert.specs) (L := L)
    hinitb hinits (by simp [initialState, hsum]) hdigits
  let finalId := runIdFrom cert cert.initial L
  have hfinalb : finalId < cert.total := by simpa [finalId] using hwalk.1
  have hfinals : stateAt cert finalId = runMachine cert.specs L := by
    simpa [finalId, runMachine] using hwalk.2
  have hmass : (stateAt cert finalId).mass = k := by
    rw [hfinals, runMachine_mass, hsum]
  have hhit := hterminal ⟨finalId, hfinalb⟩ hmass
  rw [hfinals, runMachine_lanes] at hhit
  have hw := terminalHit_semantic_sound k L cert.specs hhit
  simpa [L, Nat.ofDigits_digits] using hw

end Certificate
end CarryObstruction
end A277223

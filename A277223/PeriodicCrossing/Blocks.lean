import A277223.PeriodicCrossing.Defect

/-!
# Periodic decimal blocks

`blockStack W d M H` is the base-`10^d` word consisting of `M` low copies of
`W` followed by a high block `H`.  When `W < 10^d`, its decimal digit sum is
exactly `M*s(W)+s(H)`.

The second part proves the algebraic periodic-quotient identities used for the
explicit `7` and `11` examples.
-/

namespace A277223
namespace PeriodicCrossing

/-- `M` copies of the width-`d` low block `W`, followed by high block `H`. -/
def blockStack (W d : ℕ) : ℕ → ℕ → ℕ
  | 0, H => H
  | M + 1, H => W + 10 ^ d * blockStack W d M H

/-- Repetition with no additional high block. -/
def repeatBlock (W d M : ℕ) : ℕ := blockStack W d M 0

@[simp] theorem blockStack_zero (W d H : ℕ) : blockStack W d 0 H = H := rfl

@[simp] theorem blockStack_succ (W d M H : ℕ) :
    blockStack W d (M + 1) H = W + 10 ^ d * blockStack W d M H := rfl

/-- Digit sum of a block stack. -/
theorem digitSum10_blockStack {W d M H : ℕ} (hW : W < 10 ^ d) :
    digitSum10 (blockStack W d M H) =
      M * digitSum10 W + digitSum10 H := by
  induction M with
  | zero => simp [blockStack]
  | succ M ih =>
      rw [blockStack_succ, digitSum10_append hW, ih]
      ring

@[simp] theorem digitSum10_repeatBlock {W d M : ℕ} (hW : W < 10 ^ d) :
    digitSum10 (repeatBlock W d M) = M * digitSum10 W := by
  simp [repeatBlock, digitSum10_blockStack hW]

/-- Split a block stack into the repeated low word and its high block. -/
theorem blockStack_eq_repeat_add_high (W d M H : ℕ) :
    blockStack W d M H = repeatBlock W d M + 10 ^ (d * M) * H := by
  induction M with
  | zero => simp [blockStack, repeatBlock]
  | succ M ih =>
      rw [blockStack_succ, ih]
      simp only [repeatBlock, blockStack_succ]
      have hpow : 10 ^ (d * (M + 1)) = 10 ^ d * 10 ^ (d * M) := by
        rw [show d * (M + 1) = d * M + d by ring]
        rw [Nat.pow_add]
        ring
      rw [hpow]
      ring

/--
If `p*Q+1 = 10^d`, multiplication of the repetend `A*Q` telescopes.
This subtraction-free form is particularly convenient in Lean.
-/
theorem repeatBlock_scale {p Q A d M : ℕ}
    (hpQ : p * Q + 1 = 10 ^ d) :
    p * repeatBlock (A * Q) d M + A = A * 10 ^ (d * M) := by
  induction M with
  | zero => simp [repeatBlock, blockStack]
  | succ M ih =>
      rw [repeatBlock, blockStack_succ]
      change p * (A * Q + 10 ^ d * repeatBlock (A * Q) d M) + A = _
      calc
        p * (A * Q + 10 ^ d * repeatBlock (A * Q) d M) + A
            = A * (p * Q + 1) + 10 ^ d * (p * repeatBlock (A * Q) d M) := by ring
        _ = 10 ^ d * (A + p * repeatBlock (A * Q) d M) := by rw [hpQ]; ring
        _ = 10 ^ d * (A * 10 ^ (d * M)) := by rw [add_comm A, ih]
        _ = A * 10 ^ (d * (M + 1)) := by
              rw [Nat.mul_add, Nat.pow_add]
              ring

/-- Residue-class companion of `repeatBlock_scale`. -/
theorem repeatBlock_residue_scale {p Q A d M r h a : ℕ}
    (hpQ : p * Q + 1 = 10 ^ d)
    (hrA : r * A = p * h + a) :
    r * repeatBlock (A * Q) d M + h =
      h * 10 ^ (d * M) + repeatBlock (a * Q) d M := by
  induction M with
  | zero => simp [repeatBlock, blockStack]
  | succ M ih =>
      rw [repeatBlock, blockStack_succ]
      change r * (A * Q + 10 ^ d * repeatBlock (A * Q) d M) + h = _
      have hcoeff : r * A * Q + h = h * 10 ^ d + a * Q := by
        calc
          r * A * Q + h = (p * h + a) * Q + h := by rw [hrA]
          _ = h * (p * Q + 1) + a * Q := by ring
          _ = h * 10 ^ d + a * Q := by rw [hpQ]
      calc
        r * (A * Q + 10 ^ d * repeatBlock (A * Q) d M) + h
            = (r * A * Q + h) + 10 ^ d * (r * repeatBlock (A * Q) d M) := by ring
        _ = a * Q + 10 ^ d * (h + r * repeatBlock (A * Q) d M) := by rw [hcoeff]; ring
        _ = a * Q + 10 ^ d *
              (h * 10 ^ (d * M) + repeatBlock (a * Q) d M) := by rw [add_comm h, ih]
        _ = h * 10 ^ (d * (M + 1)) + repeatBlock (a * Q) d (M + 1) := by
              simp only [repeatBlock, blockStack_succ]
              have hpow : 10 ^ (d * (M + 1)) = 10 ^ d * 10 ^ (d * M) := by
                rw [show d * (M + 1) = d * M + d by ring]
                rw [Nat.pow_add]
                ring
              rw [hpow]
              ring

/-- Periodic integer used by the construction. -/
def periodicN (A Q C d M t : ℕ) : ℕ :=
  C + 10 ^ t * repeatBlock (A * Q) d M

/-- The sparse product identity that makes `p` Good. -/
theorem periodicN_mul {p Q A B C d M t : ℕ}
    (hpQ : p * Q + 1 = 10 ^ d)
    (hpC : p * C = A * 10 ^ t + B) :
    p * periodicN A Q C d M t = A * 10 ^ (d * M + t) + B := by
  unfold periodicN
  have hrep := repeatBlock_scale (p := p) (Q := Q) (A := A) (d := d) (M := M) hpQ
  calc
    p * (C + 10 ^ t * repeatBlock (A * Q) d M)
        = p * C + 10 ^ t * (p * repeatBlock (A * Q) d M) := by ring
    _ = (A * 10 ^ t + B) + 10 ^ t * (p * repeatBlock (A * Q) d M) := by rw [hpC]
    _ = 10 ^ t * (A + p * repeatBlock (A * Q) d M) + B := by ring
    _ = 10 ^ t * (A * 10 ^ (d * M)) + B := by rw [add_comm A, hrep]
    _ = A * 10 ^ (d * M + t) + B := by rw [Nat.pow_add]; ring

/-- Exact residue-class product normal form. -/
theorem periodicN_mul_residue {p Q A B C d M t q r h a T : ℕ}
    (hpQ : p * Q + 1 = 10 ^ d)
    (hpC : p * C = A * 10 ^ t + B)
    (hrA : r * A = p * h + a)
    (hrC : r * C = h * 10 ^ t + T) :
    (p * q + r) * periodicN A Q C d M t =
      (A * q + h) * 10 ^ (d * M + t) +
        10 ^ t * repeatBlock (a * Q) d M + (B * q + T) := by
  have hpN := periodicN_mul
    (p := p) (Q := Q) (A := A) (B := B) (C := C)
    (d := d) (M := M) (t := t) hpQ hpC
  have hrRep := repeatBlock_residue_scale
    (p := p) (Q := Q) (A := A) (d := d) (M := M)
    (r := r) (h := h) (a := a) hpQ hrA
  unfold periodicN
  calc
    (p * q + r) * (C + 10 ^ t * repeatBlock (A * Q) d M)
        = q * (p * (C + 10 ^ t * repeatBlock (A * Q) d M)) +
            r * C + 10 ^ t * (r * repeatBlock (A * Q) d M) := by ring
    _ = q * (A * 10 ^ (d * M + t) + B) +
          (h * 10 ^ t + T) + 10 ^ t * (r * repeatBlock (A * Q) d M) := by
          have hpN' : p * (C + 10 ^ t * repeatBlock (A * Q) d M) =
              A * 10 ^ (d * M + t) + B := by
            simpa [periodicN] using hpN
          rw [hpN', hrC]
    _ = q * (A * 10 ^ (d * M + t) + B) + T +
          10 ^ t * (h + r * repeatBlock (A * Q) d M) := by ring
    _ = q * (A * 10 ^ (d * M + t) + B) + T +
          10 ^ t * (h * 10 ^ (d * M) + repeatBlock (a * Q) d M) := by
          rw [add_comm h, hrRep]
    _ = (A * q + h) * 10 ^ (d * M + t) +
          10 ^ t * repeatBlock (a * Q) d M + (B * q + T) := by
          rw [Nat.pow_add]
          ring

/-- Split the exact normal form at the lowest periodic block. -/
theorem periodicN_mul_blockForm {p Q A B C d S t q r h a T : ℕ}
    (hpQ : p * Q + 1 = 10 ^ d)
    (hpC : p * C = A * 10 ^ t + B)
    (hrA : r * A = p * h + a)
    (hrC : r * C = h * 10 ^ t + T) :
    (p * q + r) * periodicN A Q C d (S + 1) t =
      (a * Q * 10 ^ t + B * q + T) +
        10 ^ (d + t) * blockStack (a * Q) d S (A * q + h) := by
  rw [periodicN_mul_residue
    (p := p) (Q := Q) (A := A) (B := B) (C := C)
    (d := d) (M := S + 1) (t := t) (q := q) (r := r)
    (h := h) (a := a) (T := T) hpQ hpC hrA hrC]
  simp only [repeatBlock, blockStack_succ]
  have hhigh : blockStack (a * Q) d S (A * q + h) =
      blockStack (a * Q) d S 0 + 10 ^ (d * S) * (A * q + h) :=
    blockStack_eq_repeat_add_high (a * Q) d S (A * q + h)
  rw [hhigh]
  have hpow : 10 ^ (d * (S + 1) + t) = 10 ^ d * 10 ^ (d * S) * 10 ^ t := by
    rw [show d * (S + 1) = d * S + d by ring]
    rw [Nat.pow_add, Nat.pow_add]
    ring
  rw [hpow]
  rw [Nat.pow_add]
  ring

/-- Digit-sum formula associated with the periodic block normal form. -/
theorem periodicN_digitSum {p Q A B C d S t q r h a T : ℕ}
    (hpQ : p * Q + 1 = 10 ^ d)
    (hpC : p * C = A * 10 ^ t + B)
    (hrA : r * A = p * h + a)
    (hrC : r * C = h * 10 ^ t + T)
    (hW : a * Q < 10 ^ d)
    (hL : a * Q * 10 ^ t + B * q + T < 10 ^ (d + t)) :
    digitSum10 ((p * q + r) * periodicN A Q C d (S + 1) t) =
      digitSum10 (a * Q * 10 ^ t + B * q + T) +
        (S * digitSum10 (a * Q) + digitSum10 (A * q + h)) := by
  rw [periodicN_mul_blockForm
    (p := p) (Q := Q) (A := A) (B := B) (C := C)
    (d := d) (S := S) (t := t) (q := q) (r := r)
    (h := h) (a := a) (T := T) hpQ hpC hrA hrC]
  rw [digitSum10_append hL, digitSum10_blockStack hW]

end PeriodicCrossing
end A277223

import A277223.PeriodicCrossing.Blocks

/-!
# Aligned updates of periodic decimal blocks

The infinite families place the crossing correction exactly on a block boundary.
This file isolates the generic fact used by both constructions: changing one
block of a repeated word changes the digit sum locally, with no dependence on
the total number of untouched blocks.
-/

namespace A277223
namespace PeriodicCrossing

/-- Concatenation law for repeated fixed-width blocks. -/
theorem repeatBlock_add (W d m n : ℕ) :
    repeatBlock W d (m + n) =
      repeatBlock W d m + 10 ^ (d * m) * repeatBlock W d n := by
  induction m with
  | zero => simp [repeatBlock, blockStack]
  | succ m ih =>
      have ih' : blockStack W d (m + n) 0 =
          blockStack W d m 0 + 10 ^ (d * m) * blockStack W d n 0 := by
        simpa [repeatBlock] using ih
      rw [show Nat.succ m + n = (m + n) + 1 by omega]
      simp only [repeatBlock, blockStack_succ]
      rw [ih']
      have hpow : 10 ^ (d * (m + 1)) = 10 ^ d * 10 ^ (d * m) := by
        rw [show d * (m + 1) = d * m + d by ring]
        rw [Nat.pow_add]
        ring
      rw [hpow]
      ring

/-- A word of `M` legal width-`d` blocks is below `10^(d*M)`. -/
theorem repeatBlock_lt_pow {W d M : ℕ} (hW : W < 10 ^ d) :
    repeatBlock W d M < 10 ^ (d * M) := by
  induction M with
  | zero => simp [repeatBlock, blockStack]
  | succ M ih =>
      simp only [repeatBlock, blockStack_succ]
      have hsucc : blockStack W d M 0 + 1 ≤ 10 ^ (d * M) := by
        exact Nat.succ_le_iff.mpr (by simpa [repeatBlock] using ih)
      have hmul := Nat.mul_le_mul_left (10 ^ d) hsucc
      calc
        W + 10 ^ d * blockStack W d M 0
            < 10 ^ d + 10 ^ d * blockStack W d M 0 :=
              Nat.add_lt_add_right hW _
        _ = 10 ^ d * (blockStack W d M 0 + 1) := by ring
        _ ≤ 10 ^ d * 10 ^ (d * M) := hmul
        _ = 10 ^ (d * (Nat.succ M)) := by
              rw [show d * Nat.succ M = d + d * M by
                rw [Nat.succ_eq_add_one]
                ring, Nat.pow_add]

/-- Algebraic decomposition when one repeated block is increased by `x`. -/
theorem repeatBlock_update_decomp {W x d M i : ℕ} (hi : i < M) :
    ∃ j : ℕ, M = i + 1 + j ∧
      repeatBlock W d M + x * 10 ^ (d * i) =
        repeatBlock W d i + 10 ^ (d * i) *
          (W + x + 10 ^ d * repeatBlock W d j) := by
  obtain ⟨j, hM⟩ : ∃ j, M = i + 1 + j := by
    refine ⟨M - i - 1, by omega⟩
  refine ⟨j, hM, ?_⟩
  rw [hM, show i + 1 + j = i + (1 + j) by omega]
  rw [repeatBlock_add W d i (1 + j)]
  have hrep : repeatBlock W d (1 + j) = W + 10 ^ d * repeatBlock W d j := by
    rw [show 1 + j = j + 1 by omega]
    rfl
  rw [hrep]
  ring

/-- Exact digit sum after increasing one aligned block of a repeated word. -/
theorem digitSum10_repeatBlock_update {W x d M i : ℕ}
    (hW : W < 10 ^ d) (hWx : W + x < 10 ^ d) (hi : i < M) :
    digitSum10 (repeatBlock W d M + x * 10 ^ (d * i)) =
      (M - 1) * digitSum10 W + digitSum10 (W + x) := by
  obtain ⟨j, hM, hdecomp⟩ := repeatBlock_update_decomp (W := W) (x := x)
    (d := d) (M := M) (i := i) hi
  rw [hdecomp]
  rw [digitSum10_append (repeatBlock_lt_pow (W := W) (d := d) (M := i) hW)]
  rw [digitSum10_append hWx]
  rw [digitSum10_repeatBlock hW, digitSum10_repeatBlock hW]
  have hpred : M - 1 = i + j := by
    rw [hM]
    omega
  rw [hpred]
  ring

/-- The same aligned update remains within its original `M`-block width. -/
theorem repeatBlock_update_lt_pow {W x d M i : ℕ}
    (hW : W < 10 ^ d) (hWx : W + x < 10 ^ d) (hi : i < M) :
    repeatBlock W d M + x * 10 ^ (d * i) < 10 ^ (d * M) := by
  obtain ⟨j, hM, hdecomp⟩ := repeatBlock_update_decomp (W := W) (x := x)
    (d := d) (M := M) (i := i) hi
  rw [hdecomp]
  have hlo := repeatBlock_lt_pow (W := W) (d := d) (M := i) hW
  have hj := repeatBlock_lt_pow (W := W) (d := d) (M := j) hW
  have htail : W + x + 10 ^ d * repeatBlock W d j < 10 ^ (d * (j + 1)) := by
    have hsucc : repeatBlock W d j + 1 ≤ 10 ^ (d * j) := Nat.succ_le_iff.mpr hj
    have hmul := Nat.mul_le_mul_left (10 ^ d) hsucc
    calc
      W + x + 10 ^ d * repeatBlock W d j
          < 10 ^ d + 10 ^ d * repeatBlock W d j := Nat.add_lt_add_right hWx _
      _ = 10 ^ d * (repeatBlock W d j + 1) := by ring
      _ ≤ 10 ^ d * 10 ^ (d * j) := hmul
      _ = 10 ^ (d * (j + 1)) := by rw [Nat.mul_add, Nat.pow_add]; ring
  have htailsucc :
      (W + x + 10 ^ d * repeatBlock W d j) + 1 ≤ 10 ^ (d * (j + 1)) :=
    Nat.succ_le_iff.mpr htail
  have hmul := Nat.mul_le_mul_left (10 ^ (d * i)) htailsucc
  calc
    repeatBlock W d i + 10 ^ (d * i) *
          (W + x + 10 ^ d * repeatBlock W d j)
        < 10 ^ (d * i) + 10 ^ (d * i) *
          (W + x + 10 ^ d * repeatBlock W d j) := Nat.add_lt_add_right hlo _
    _ = 10 ^ (d * i) *
          ((W + x + 10 ^ d * repeatBlock W d j) + 1) := by ring
    _ ≤ 10 ^ (d * i) * 10 ^ (d * (j + 1)) := hmul
    _ = 10 ^ (d * M) := by
      rw [← Nat.pow_add]
      congr 1
      rw [hM]
      ring

/-- Add a short low tail in front of the aligned repeated-block update. -/
theorem digitSum10_tail_repeat_update {T shift W x d M i : ℕ}
    (hT : T < 10 ^ shift)
    (hW : W < 10 ^ d) (hWx : W + x < 10 ^ d) (hi : i < M) :
    digitSum10
      (T + 10 ^ shift * (repeatBlock W d M + x * 10 ^ (d * i))) =
      digitSum10 T + ((M - 1) * digitSum10 W + digitSum10 (W + x)) := by
  rw [digitSum10_append hT]
  rw [digitSum10_repeatBlock_update hW hWx hi]

/-- Width bound corresponding to `digitSum10_tail_repeat_update`. -/
theorem tail_repeat_update_lt_pow {T shift W x d M i : ℕ}
    (hT : T < 10 ^ shift)
    (hW : W < 10 ^ d) (hWx : W + x < 10 ^ d) (hi : i < M) :
    T + 10 ^ shift * (repeatBlock W d M + x * 10 ^ (d * i)) <
      10 ^ (d * M + shift) := by
  have hword := repeatBlock_update_lt_pow hW hWx hi
  have hsucc : (repeatBlock W d M + x * 10 ^ (d * i)) + 1 ≤ 10 ^ (d * M) :=
    Nat.succ_le_iff.mpr hword
  have hmul := Nat.mul_le_mul_left (10 ^ shift) hsucc
  calc
    T + 10 ^ shift * (repeatBlock W d M + x * 10 ^ (d * i))
        < 10 ^ shift + 10 ^ shift * (repeatBlock W d M + x * 10 ^ (d * i)) :=
          Nat.add_lt_add_right hT _
    _ = 10 ^ shift * ((repeatBlock W d M + x * 10 ^ (d * i)) + 1) := by ring
    _ ≤ 10 ^ shift * 10 ^ (d * M) := hmul
    _ = 10 ^ (d * M + shift) := by rw [Nat.pow_add]; ring

/-- Digit sum of a separated high digit and a low one-digit tail. -/
theorem digitSum10_digit_mul_pow_add {A h u : ℕ}
    (hA : A < 10) (hu : 0 < u) (hh : h < 10) :
    digitSum10 (A * 10 ^ u + h) = A + h := by
  cases u with
  | zero => omega
  | succ v =>
      rw [show A * 10 ^ (v + 1) + h = h + 10 ^ (v + 1) * A by ring]
      have hpow : 10 ≤ 10 ^ (v + 1) := by
        have hexp : 1 ≤ v + 1 := by omega
        simpa using Nat.pow_le_pow_right (by norm_num : 0 < 10) hexp
      rw [digitSum10_append (lt_of_lt_of_le hh hpow)]
      rw [digitSum10_of_lt_10 hh, digitSum10_of_lt_10 hA]
      omega

/-- Unfolding a decimal power of ten one step, in left-multiplied form. -/
theorem ten_pow_succ (m : ℕ) : 10 ^ Nat.succ m = 10 * 10 ^ m := by
  simp [Nat.pow_succ, Nat.mul_comm]

/-- Decimal complement formula used at the left side of a pure-power crossing. -/
theorem digitSum10_digit_mul_pred_pow_add {A h u : ℕ}
    (hA0 : 0 < A) (hA10 : A < 10) (hh : h < A) (hu : 0 < u) :
    digitSum10 (A * (10 ^ u - 1) + h) = 9 * u + h := by
  cases u with
  | zero => omega
  | succ m =>
    let low := 10 - A + h
    have hlow : low < 10 := by dsimp [low]; omega
    have hstack : blockStack 9 1 m (A - 1) + 1 = A * 10 ^ m := by
      clear hu
      induction m with
      | zero =>
          simp [blockStack]
          omega
      | succ m ih =>
          rw [blockStack_succ]
          rw [ten_pow_succ m]
          calc
            (9 + 10 * blockStack 9 1 m (A - 1)) + 1
                = 10 * (blockStack 9 1 m (A - 1) + 1) := by ring
            _ = 10 * (A * 10 ^ m) := by rw [ih]
            _ = A * (10 * 10 ^ m) := by ring
    have hrepr :
        A * (10 ^ (Nat.succ m) - 1) + h =
          low + 10 * blockStack 9 1 m (A - 1) := by
      dsimp [low]
      rw [ten_pow_succ m]
      have hkey : 10 * blockStack 9 1 m (A - 1) + 10 =
          A * (10 * 10 ^ m) := by
        calc
          10 * blockStack 9 1 m (A - 1) + 10
              = 10 * (blockStack 9 1 m (A - 1) + 1) := by ring
          _ = 10 * (A * 10 ^ m) := by rw [hstack]
          _ = A * (10 * 10 ^ m) := by ring
      have hlow : 10 - A + h + 10 * blockStack 9 1 m (A - 1) =
          10 * blockStack 9 1 m (A - 1) + 10 - A + h := by
        omega
      rw [hlow, hkey, Nat.mul_sub_left_distrib]
      simp
    rw [hrepr]
    rw [show low + 10 * blockStack 9 1 m (A - 1) =
        low + 10 ^ 1 * blockStack 9 1 m (A - 1) by rfl]
    rw [digitSum10_append hlow]
    rw [digitSum10_blockStack (by norm_num : 9 < 10)]
    have hAm1 : A - 1 < 10 := by omega
    have h9 : digitSum10 9 = 9 := by decide
    rw [digitSum10_of_lt_10 hlow, digitSum10_of_lt_10 hAm1, h9]
    dsimp [low]
    omega

end PeriodicCrossing
end A277223

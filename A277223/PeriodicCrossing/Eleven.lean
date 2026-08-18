import A277223.PeriodicCrossing.Blocks

/-!
# The value 11

The witness is the 52-digit periodic integer

`81 81 ... 81 82`

with 25 copies of `81`.  The structural identity is
`11*N11 = 9*10^52 + 2`.  Defect crossings occur at quotient 22 for residues
1,2 and at quotient 21 for residues 3,...,10.
-/

namespace A277223
namespace PeriodicCrossing

/-- Explicit periodic witness for the maximal value eleven. -/
def N11 : ℕ := periodicN 9 9 82 2 25 2

/-- Sparse product identity for `N11`. -/
theorem eleven_mul_N11 : 11 * N11 = 9 * 10 ^ 52 + 2 := by
  change 11 * periodicN 9 9 82 2 25 2 = _
  convert periodicN_mul
    (p := 11) (Q := 9) (A := 9) (B := 2) (C := 82)
    (d := 2) (M := 25) (t := 2)
    (by norm_num) (by norm_num) using 1 <;> norm_num

/-- Eleven is Good for `N11`. -/
theorem N11_good_eleven : Good N11 11 := by
  unfold Good
  rw [eleven_mul_N11]
  rw [show 9 * 10 ^ 52 + 2 = 2 + 10 ^ 52 * 9 by ring]
  have h2 : 2 < 10 ^ 52 := by
    have hpow : 10 ^ 1 ≤ 10 ^ 52 :=
      Nat.pow_le_pow_right (by norm_num : 0 < 10) (by norm_num)
    exact lt_of_lt_of_le (by norm_num : 2 < 10) hpow
  rw [digitSum10_append h2]
  decide

/-- Defect at the second point in the zero residue class. -/
theorem N11_defect_twenty_two : defect N11 22 = -9 := by
  unfold defect
  have h : 22 * N11 = 4 + 10 ^ 52 * 18 := by
    calc
      22 * N11 = 2 * (11 * N11) := by ring
      _ = 2 * (9 * 10 ^ 52 + 2) := by rw [eleven_mul_N11]
      _ = 4 + 10 ^ 52 * 18 := by ring
  have h4 : 4 < 10 ^ 52 := by
    have hpow : 10 ^ 1 ≤ 10 ^ 52 :=
      Nat.pow_le_pow_right (by norm_num : 0 < 10) (by norm_num)
    exact lt_of_lt_of_le (by norm_num : 4 < 10) hpow
  rw [h, digitSum10_append h4]
  decide

/-- Residue data `h` in `9r = 11h+a`. -/
def h11 : ℕ → ℕ
  | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4
  | 6 => 4 | 7 => 5 | 8 => 6 | 9 => 7 | 10 => 8 | _ => 0

/-- Residue data `a` in `9r = 11h+a`. -/
def a11 : ℕ → ℕ
  | 1 => 9 | 2 => 7 | 3 => 5 | 4 => 3 | 5 => 1
  | 6 => 10 | 7 => 8 | 8 => 6 | 9 => 4 | 10 => 2 | _ => 0

/-- Tail data `T` in `82r = 100h+T`. -/
def T11 : ℕ → ℕ
  | 1 => 82 | 2 => 64 | 3 => 46 | 4 => 28 | 5 => 10
  | 6 => 92 | 7 => 74 | 8 => 56 | 9 => 38 | 10 => 20 | _ => 0

/-- Crossing quotient for a nonzero residue. -/
def q11 : ℕ → ℕ
  | 1 => 22 | 2 => 22 | _ => 21

/-- Every periodic residue block has digit sum nine. -/
theorem N11_residue_block_sum {r : ℕ} (hr0 : 0 < r) (hr11 : r < 11) :
    digitSum10 (a11 r * 9) = 9 := by
  interval_cases r <;> decide +kernel

/-- Closed digit-sum formula in a nonzero residue class near the crossing. -/
theorem N11_residue_digitSum {r q : ℕ}
    (hr0 : 0 < r) (hr11 : r < 11) (hq : q ≤ 23) :
    digitSum10 ((11 * q + r) * N11) =
      digitSum10 (a11 r * 9 * 100 + 2 * q + T11 r) +
        216 + digitSum10 (9 * q + h11 r) := by
  have hrA : r * 9 = 11 * h11 r + a11 r := by
    interval_cases r <;> norm_num [h11, a11]
  have hrC : r * 82 = h11 r * 100 + T11 r := by
    interval_cases r <;> norm_num [h11, T11]
  have hW : a11 r * 9 < 10 ^ 2 := by
    interval_cases r <;> norm_num [a11]
  have hL : a11 r * 9 * 10 ^ 2 + 2 * q + T11 r < 10 ^ (2 + 2) := by
    interval_cases r <;> norm_num [a11, T11] at * <;> omega
  have hform := periodicN_digitSum
    (p := 11) (Q := 9) (A := 9) (B := 2) (C := 82)
    (d := 2) (S := 24) (t := 2) (q := q) (r := r)
    (h := h11 r) (a := a11 r) (T := T11 r)
    (by norm_num) (by norm_num) hrA hrC hW hL
  change digitSum10 ((11 * q + r) * periodicN 9 9 82 2 (24 + 1) 2) = _
  rw [hform, N11_residue_block_sum hr0 hr11]
  norm_num1
  ring

/-- Positive side of every nonzero residue-class crossing. -/
theorem N11_crossing_left {r : ℕ} (hr0 : 0 < r) (hr11 : r < 11) :
    0 < defect N11 (11 * q11 r + r) := by
  unfold defect
  have hq : q11 r ≤ 23 := by
    interval_cases r <;> norm_num [q11]
  rw [N11_residue_digitSum hr0 hr11 hq]
  interval_cases r <;> decide +kernel

/-- Negative side of every nonzero residue-class crossing. -/
theorem N11_crossing_right {r : ℕ} (hr0 : 0 < r) (hr11 : r < 11) :
    defect N11 (11 * (q11 r + 1) + r) < 0 := by
  unfold defect
  have hq : q11 r + 1 ≤ 23 := by
    interval_cases r <;> norm_num [q11]
  rw [N11_residue_digitSum hr0 hr11 hq]
  interval_cases r <;> decide +kernel

/-- Eleven is the unique positive Good multiplier for `N11`. -/
theorem N11_unique_good : ∀ k : ℕ, 0 < k → Good N11 k → k = 11 := by
  apply unique_good_of_crossings
    (N := N11) (p := 11) (by norm_num) N11_good_eleven
  · rw [show 2 * 11 = 22 by norm_num]
    rw [N11_defect_twenty_two]
    norm_num
  · intro r hr0 hr11
    exact ⟨q11 r, N11_crossing_left hr0 hr11, N11_crossing_right hr0 hr11⟩

/-- The explicit witness realizes the maximal value eleven. -/
theorem N11_maxGood : MaxGood N11 11 :=
  maxGood_of_unique_positive N11_good_eleven N11_unique_good

end PeriodicCrossing
end A277223

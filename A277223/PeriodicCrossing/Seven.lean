import A277223.PeriodicCrossing.Blocks

/-!
# The value 7

The witness is the 152-digit periodic integer

`714285 714285 ... 714285 73`

with 25 copies of `714285`.  The structural identity is
`7*N7 = 5*10^152 + 11`.  Every nonzero residue class modulo seven has the
same defect crossing: `+9` at quotient 99 and `-9` at quotient 100.
-/

namespace A277223
namespace PeriodicCrossing

/-- Explicit periodic witness for the maximal value seven. -/
def N7 : ℕ := periodicN 5 142857 73 6 25 2

/-- Sparse product identity for `N7`. -/
theorem seven_mul_N7 : 7 * N7 = 5 * 10 ^ 152 + 11 := by
  change 7 * periodicN 5 142857 73 6 25 2 = _
  convert periodicN_mul
    (p := 7) (Q := 142857) (A := 5) (B := 11) (C := 73)
    (d := 6) (M := 25) (t := 2)
    (by norm_num) (by norm_num) using 1 <;> norm_num

/-- Seven is Good for `N7`. -/
theorem N7_good_seven : Good N7 7 := by
  unfold Good
  rw [seven_mul_N7]
  rw [show 5 * 10 ^ 152 + 11 = 11 + 10 ^ 152 * 5 by ring]
  have h11 : 11 < 10 ^ 152 := by
    have hpow : 10 ^ 2 ≤ 10 ^ 152 :=
      Nat.pow_le_pow_right (by norm_num : 0 < 10) (by norm_num)
    exact lt_of_lt_of_le (by norm_num : 11 < 10 ^ 2) hpow
  rw [digitSum10_append h11]
  decide

/-- Defect at the second point of the zero residue class. -/
theorem N7_defect_fourteen : defect N7 14 = -9 := by
  unfold defect
  have h : 14 * N7 = 22 + 10 ^ 152 * 10 := by
    calc
      14 * N7 = 2 * (7 * N7) := by ring
      _ = 2 * (5 * 10 ^ 152 + 11) := by rw [seven_mul_N7]
      _ = 22 + 10 ^ 152 * 10 := by ring
  have h22 : 22 < 10 ^ 152 := by
    have hpow : 10 ^ 2 ≤ 10 ^ 152 :=
      Nat.pow_le_pow_right (by norm_num : 0 < 10) (by norm_num)
    exact lt_of_lt_of_le (by norm_num : 22 < 10 ^ 2) hpow
  rw [h, digitSum10_append h22]
  decide

/-- Residue data `h` in `5r = 7h+a`. -/
def h7 : ℕ → ℕ
  | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 2 | 5 => 3 | 6 => 4 | _ => 0

/-- Residue data `a` in `5r = 7h+a`. -/
def a7 : ℕ → ℕ
  | 1 => 5 | 2 => 3 | 3 => 1 | 4 => 6 | 5 => 4 | 6 => 2 | _ => 0

/-- Tail data `T` in `73r = 100h+T`. -/
def T7 : ℕ → ℕ
  | 1 => 73 | 2 => 46 | 3 => 19 | 4 => 92 | 5 => 65 | 6 => 38 | _ => 0

/-- The six periodic blocks all have digit sum 27. -/
theorem N7_residue_block_sum {r : ℕ} (hr0 : 0 < r) (hr7 : r < 7) :
    digitSum10 (a7 r * 142857) = 27 := by
  interval_cases r <;> decide +kernel

/-- Closed digit-sum formula in a nonzero residue class, for the crossing range. -/
theorem N7_residue_digitSum {r q : ℕ}
    (hr0 : 0 < r) (hr7 : r < 7) (hq : q ≤ 100) :
    digitSum10 ((7 * q + r) * N7) =
      digitSum10 (a7 r * 142857 * 100 + 11 * q + T7 r) +
        648 + digitSum10 (5 * q + h7 r) := by
  have hrA : r * 5 = 7 * h7 r + a7 r := by
    interval_cases r <;> norm_num [h7, a7]
  have hrC : r * 73 = h7 r * 100 + T7 r := by
    interval_cases r <;> norm_num [h7, T7]
  have hW : a7 r * 142857 < 10 ^ 6 := by
    interval_cases r <;> norm_num [a7]
  have hL : a7 r * 142857 * 10 ^ 2 + 11 * q + T7 r < 10 ^ (6 + 2) := by
    interval_cases r <;> norm_num [a7, T7] at * <;> omega
  have hform := periodicN_digitSum
    (p := 7) (Q := 142857) (A := 5) (B := 11) (C := 73)
    (d := 6) (S := 24) (t := 2) (q := q) (r := r)
    (h := h7 r) (a := a7 r) (T := T7 r)
    (by norm_num) (by norm_num) hrA hrC hW hL
  change digitSum10 ((7 * q + r) * periodicN 5 142857 73 6 (24 + 1) 2) = _
  rw [hform, N7_residue_block_sum hr0 hr7]
  norm_num1
  ring

/-- Uniform positive side of the six crossings. -/
theorem N7_crossing_left {r : ℕ} (hr0 : 0 < r) (hr7 : r < 7) :
    defect N7 (7 * 99 + r) = 9 := by
  unfold defect
  rw [N7_residue_digitSum hr0 hr7 (by norm_num : 99 ≤ 100)]
  interval_cases r <;> decide +kernel

/-- Uniform negative side of the six crossings. -/
theorem N7_crossing_right {r : ℕ} (hr0 : 0 < r) (hr7 : r < 7) :
    defect N7 (7 * 100 + r) = -9 := by
  unfold defect
  rw [N7_residue_digitSum hr0 hr7 (by norm_num : 100 ≤ 100)]
  interval_cases r <;> decide +kernel

/-- Seven is the unique positive Good multiplier for `N7`. -/
theorem N7_unique_good : ∀ k : ℕ, 0 < k → Good N7 k → k = 7 := by
  apply unique_good_of_crossings
    (N := N7) (p := 7) (by norm_num) N7_good_seven
  · rw [show 2 * 7 = 14 by norm_num]
    rw [N7_defect_fourteen]
    norm_num
  · intro r hr0 hr7
    refine ⟨99, ?_, ?_⟩
    · rw [N7_crossing_left hr0 hr7]
      norm_num
    · have h := N7_crossing_right hr0 hr7
      rw [h]
      norm_num

/-- The explicit witness realizes the maximal value seven. -/
theorem N7_maxGood : MaxGood N7 7 :=
  maxGood_of_unique_positive N7_good_seven N7_unique_good

end PeriodicCrossing
end A277223

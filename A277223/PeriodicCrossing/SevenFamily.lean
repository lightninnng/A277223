import A277223.PeriodicCrossing.Seven
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Monotone.Basic
import A277223.PeriodicCrossing.AlignedUpdate

/-!
# A nontrivial infinite family with maximal Good multiplier seven

The crossing is placed at the pure decimal boundary `q = 10^(6*t+2)`.
The block count is chosen by the exact balance `27*M + 25 = 7*q`.
-/

namespace A277223
namespace PeriodicCrossing

/-- Block count in the infinite seven-family. -/
def M7Family : ℕ → ℕ
  | 0 => 25
  | t + 1 => 1000000 * M7Family t + 925925

/-- Decimal exponent at the crossing. -/
def u7Family (t : ℕ) : ℕ := 6 * t + 2

/-- Crossing quotient. -/
def q7Family (t : ℕ) : ℕ := 10 ^ u7Family t

/-- The periodic family itself. -/
def N7Family (t : ℕ) : ℕ :=
  periodicN 5 142857 73 6 (M7Family t) 2

/-- The recurrence is precisely the balance that positions the crossing. -/
theorem M7Family_balance (t : ℕ) :
    27 * M7Family t + 25 = 7 * q7Family t := by
  induction t with
  | zero => norm_num [M7Family, q7Family, u7Family]
  | succ t ih =>
      calc
        27 * M7Family (t + 1) + 25
            = 1000000 * (27 * M7Family t + 25) := by
                simp [M7Family]
                ring
        _ = 1000000 * (7 * q7Family t) := by rw [ih]
        _ = 7 * q7Family (t + 1) := by
              unfold q7Family u7Family
              rw [show 6 * (t + 1) + 2 = 6 + (6 * t + 2) by omega, Nat.pow_add]
              norm_num
              ring

/-- There are always enough repeated blocks to contain the aligned update. -/
theorem M7Family_index_lt (t : ℕ) : t < M7Family t := by
  induction t with
  | zero => norm_num [M7Family]
  | succ t ih =>
      simp [M7Family]
      omega

/-- Sparse product identity for every member of the seven-family. -/
theorem seven_mul_N7Family (t : ℕ) :
    7 * N7Family t = 5 * 10 ^ (6 * M7Family t + 2) + 11 := by
  unfold N7Family
  convert periodicN_mul
    (p := 7) (Q := 142857) (A := 5) (B := 11) (C := 73)
    (d := 6) (M := M7Family t) (t := 2)
    (by norm_num) (by norm_num) using 1 <;> ring

/-- Seven is Good for every family member. -/
theorem N7Family_good (t : ℕ) : Good (N7Family t) 7 := by
  unfold Good
  rw [seven_mul_N7Family]
  rw [show 5 * 10 ^ (6 * M7Family t + 2) + 11 =
      11 + 10 ^ (6 * M7Family t + 2) * 5 by ring]
  have h11 : 11 < 10 ^ (6 * M7Family t + 2) := by
    have : 2 ≤ 6 * M7Family t + 2 := by omega
    have hpow : 10 ^ 2 ≤ 10 ^ (6 * M7Family t + 2) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 10) this
    exact lt_of_lt_of_le (by norm_num : 11 < 100) hpow
  rw [digitSum10_append h11]
  decide

/-- Finite residue identities used uniformly by the family. -/
theorem N7Family_residue_data {r : ℕ} (hr0 : 0 < r) (hr7 : r < 7) :
    digitSum10 (a7 r * 142857) = 27 ∧
    digitSum10 (a7 r * 142857 + 11) = 29 ∧
    11 ≤ T7 r ∧
    digitSum10 (T7 r - 11) + 2 = digitSum10 (T7 r) ∧
    h7 r + digitSum10 (T7 r) = r + 9 := by
  interval_cases r <;> decide +kernel

/-- Exact digit sum at the negative endpoint of every nonzero residue crossing. -/
theorem N7Family_digitSum_right {t r : ℕ} (hr0 : 0 < r) (hr7 : r < 7) :
    digitSum10 ((7 * q7Family t + r) * N7Family t) =
      digitSum10 (T7 r) + ((M7Family t - 1) * 27 + 29) + (5 + h7 r) := by
  rcases N7Family_residue_data hr0 hr7 with ⟨hWsum, hWxsum, hT11, hTsum, hres⟩
  have hrA : r * 5 = 7 * h7 r + a7 r := by
    interval_cases r <;> norm_num [h7, a7]
  have hrC : r * 73 = h7 r * 100 + T7 r := by
    interval_cases r <;> norm_num [h7, T7]
  have hW : a7 r * 142857 < 10 ^ 6 := by
    interval_cases r <;> norm_num [a7]
  have hWx : a7 r * 142857 + 11 < 10 ^ 6 := by
    interval_cases r <;> norm_num [a7]
  have hT : T7 r < 10 ^ 2 := by
    interval_cases r <;> norm_num [T7]
  have hi : t < M7Family t := M7Family_index_lt t
  have hlowSum := digitSum10_tail_repeat_update
    (T := T7 r) (shift := 2) (W := a7 r * 142857) (x := 11)
    (d := 6) (M := M7Family t) (i := t) hT hW hWx hi
  have hlowBound := tail_repeat_update_lt_pow
    (T := T7 r) (shift := 2) (W := a7 r * 142857) (x := 11)
    (d := 6) (M := M7Family t) (i := t) hT hW hWx hi
  have hprod := periodicN_mul_residue
    (p := 7) (Q := 142857) (A := 5) (B := 11) (C := 73)
    (d := 6) (M := M7Family t) (t := 2) (q := q7Family t) (r := r)
    (h := h7 r) (a := a7 r) (T := T7 r)
    (by norm_num) (by norm_num) hrA hrC
  have hq : q7Family t = 100 * 10 ^ (6 * t) := by
    unfold q7Family u7Family
    rw [show 6 * t + 2 = 2 + 6 * t by omega, Nat.pow_add]
  have hloweq :
      10 ^ 2 * repeatBlock (a7 r * 142857) 6 (M7Family t) +
          (11 * q7Family t + T7 r) =
        T7 r + 10 ^ 2 *
          (repeatBlock (a7 r * 142857) 6 (M7Family t) + 11 * 10 ^ (6 * t)) := by
    rw [hq]
    ring
  rw [show N7Family t = periodicN 5 142857 73 6 (M7Family t) 2 from rfl, hprod]
  first
  | rw [show ((5 * q7Family t + h7 r) * 10 ^ (6 * M7Family t + 2) +
        10 ^ 2 * repeatBlock (a7 r * 142857) 6 (M7Family t)) +
        (11 * q7Family t + T7 r) =
      (5 * q7Family t + h7 r) * 10 ^ (6 * M7Family t + 2) +
        (10 ^ 2 * repeatBlock (a7 r * 142857) 6 (M7Family t) +
        (11 * q7Family t + T7 r)) by ring]
  | skip
  rw [hloweq]
  rw [show (5 * q7Family t + h7 r) * 10 ^ (6 * M7Family t + 2) +
        (T7 r + 10 ^ 2 *
          (repeatBlock (a7 r * 142857) 6 (M7Family t) + 11 * 10 ^ (6 * t))) =
      (T7 r + 10 ^ 2 *
          (repeatBlock (a7 r * 142857) 6 (M7Family t) + 11 * 10 ^ (6 * t))) +
        10 ^ (6 * M7Family t + 2) * (5 * q7Family t + h7 r) by ring]
  rw [digitSum10_append hlowBound, hlowSum, hWsum, hWxsum]
  have hh : h7 r < 5 := by interval_cases r <;> norm_num [h7]
  have hhigh := digitSum10_digit_mul_pow_add
    (A := 5) (h := h7 r) (u := u7Family t)
    (by norm_num) (by dsimp [u7Family]; omega) (by omega)
  have hqpow : q7Family t = 10 ^ u7Family t := rfl
  rw [← hqpow] at hhigh
  rw [hhigh]

/-- Exact digit sum at the positive endpoint of every nonzero residue crossing. -/
theorem N7Family_digitSum_left {t r : ℕ} (hr0 : 0 < r) (hr7 : r < 7) :
    digitSum10 ((7 * (q7Family t - 1) + r) * N7Family t) =
      digitSum10 (T7 r - 11) + ((M7Family t - 1) * 27 + 29) +
        (9 * u7Family t + h7 r) := by
  rcases N7Family_residue_data hr0 hr7 with ⟨hWsum, hWxsum, hT11, hTsum, hres⟩
  have hrA : r * 5 = 7 * h7 r + a7 r := by
    interval_cases r <;> norm_num [h7, a7]
  have hrC : r * 73 = h7 r * 100 + T7 r := by
    interval_cases r <;> norm_num [h7, T7]
  have hW : a7 r * 142857 < 10 ^ 6 := by
    interval_cases r <;> norm_num [a7]
  have hWx : a7 r * 142857 + 11 < 10 ^ 6 := by
    interval_cases r <;> norm_num [a7]
  have hT : T7 r - 11 < 10 ^ 2 := by
    interval_cases r <;> norm_num [T7]
  have hi : t < M7Family t := M7Family_index_lt t
  have hlowSum := digitSum10_tail_repeat_update
    (T := T7 r - 11) (shift := 2) (W := a7 r * 142857) (x := 11)
    (d := 6) (M := M7Family t) (i := t) hT hW hWx hi
  have hlowBound := tail_repeat_update_lt_pow
    (T := T7 r - 11) (shift := 2) (W := a7 r * 142857) (x := 11)
    (d := 6) (M := M7Family t) (i := t) hT hW hWx hi
  have hprod := periodicN_mul_residue
    (p := 7) (Q := 142857) (A := 5) (B := 11) (C := 73)
    (d := 6) (M := M7Family t) (t := 2) (q := q7Family t - 1) (r := r)
    (h := h7 r) (a := a7 r) (T := T7 r)
    (by norm_num) (by norm_num) hrA hrC
  have hqpos : 0 < q7Family t := by unfold q7Family; positivity
  have hq : q7Family t = 100 * 10 ^ (6 * t) := by
    unfold q7Family u7Family
    rw [show 6 * t + 2 = 2 + 6 * t by omega, Nat.pow_add]
  have htail : 11 * (q7Family t - 1) + T7 r =
      11 * q7Family t + (T7 r - 11) := by omega
  have hloweq :
      10 ^ 2 * repeatBlock (a7 r * 142857) 6 (M7Family t) +
          (11 * (q7Family t - 1) + T7 r) =
        (T7 r - 11) + 10 ^ 2 *
          (repeatBlock (a7 r * 142857) 6 (M7Family t) + 11 * 10 ^ (6 * t)) := by
    rw [htail, hq]
    ring
  rw [show N7Family t = periodicN 5 142857 73 6 (M7Family t) 2 from rfl, hprod]
  first
  | rw [show ((5 * (q7Family t - 1) + h7 r) * 10 ^ (6 * M7Family t + 2) +
        10 ^ 2 * repeatBlock (a7 r * 142857) 6 (M7Family t)) +
        (11 * (q7Family t - 1) + T7 r) =
      (5 * (q7Family t - 1) + h7 r) * 10 ^ (6 * M7Family t + 2) +
        (10 ^ 2 * repeatBlock (a7 r * 142857) 6 (M7Family t) +
        (11 * (q7Family t - 1) + T7 r)) by ring]
  | skip
  rw [hloweq]
  rw [show (5 * (q7Family t - 1) + h7 r) * 10 ^ (6 * M7Family t + 2) +
        ((T7 r - 11) + 10 ^ 2 *
          (repeatBlock (a7 r * 142857) 6 (M7Family t) + 11 * 10 ^ (6 * t))) =
      ((T7 r - 11) + 10 ^ 2 *
          (repeatBlock (a7 r * 142857) 6 (M7Family t) + 11 * 10 ^ (6 * t))) +
        10 ^ (6 * M7Family t + 2) * (5 * (q7Family t - 1) + h7 r) by ring]
  rw [digitSum10_append hlowBound, hlowSum, hWsum, hWxsum]
  have hh : h7 r < 5 := by interval_cases r <;> norm_num [h7]
  have hhigh := digitSum10_digit_mul_pred_pow_add
    (A := 5) (h := h7 r) (u := u7Family t)
    (by norm_num) (by norm_num) hh (by dsimp [u7Family]; omega)
  have hqpow : q7Family t = 10 ^ u7Family t := rfl
  rw [← hqpow] at hhigh
  rw [hhigh]

/-- Positive side of every family crossing. -/
theorem N7Family_crossing_left {t r : ℕ} (hr0 : 0 < r) (hr7 : r < 7) :
    defect (N7Family t) (7 * (q7Family t - 1) + r) = 54 * t + 9 := by
  unfold defect
  rw [N7Family_digitSum_left hr0 hr7]
  rcases N7Family_residue_data hr0 hr7 with ⟨hWsum, hWxsum, hT11, hTsum, hres⟩
  have hbal := M7Family_balance t
  unfold u7Family at *
  push_cast
  omega

/-- Negative side of every family crossing. -/
theorem N7Family_crossing_right {t r : ℕ} (hr0 : 0 < r) (hr7 : r < 7) :
    defect (N7Family t) (7 * q7Family t + r) = -9 := by
  unfold defect
  rw [N7Family_digitSum_right hr0 hr7]
  rcases N7Family_residue_data hr0 hr7 with ⟨hWsum, hWxsum, hT11, hTsum, hres⟩
  have hbal := M7Family_balance t
  push_cast
  omega

/-- The second point of the zero residue class is already negative. -/
theorem N7Family_defect_fourteen (t : ℕ) : defect (N7Family t) 14 = -9 := by
  unfold defect
  have h : 14 * N7Family t = 22 + 10 ^ (6 * M7Family t + 2) * 10 := by
    calc
      14 * N7Family t = 2 * (7 * N7Family t) := by ring
      _ = 2 * (5 * 10 ^ (6 * M7Family t + 2) + 11) := by rw [seven_mul_N7Family]
      _ = 22 + 10 ^ (6 * M7Family t + 2) * 10 := by ring
  rw [h]
  have hb : 22 < 10 ^ (6 * M7Family t + 2) := by
    have : 2 ≤ 6 * M7Family t + 2 := by omega
    have hpow : 10 ^ 2 ≤ 10 ^ (6 * M7Family t + 2) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 10) this
    exact lt_of_lt_of_le (by norm_num : 22 < 100) hpow
  rw [digitSum10_append hb]
  decide

/-- Every member of the family has maximal Good multiplier seven. -/
theorem N7Family_maxGood (t : ℕ) : MaxGood (N7Family t) 7 := by
  apply maxGood_of_crossings (N := N7Family t) (p := 7) (by norm_num) (N7Family_good t)
  · rw [show 2 * 7 = 14 by norm_num]
    rw [N7Family_defect_fourteen t]
    norm_num
  · intro r hr0 hr7
    refine ⟨q7Family t - 1, ?_, ?_⟩
    · rw [N7Family_crossing_left hr0 hr7]
      omega
    · have hqpos : 0 < q7Family t := by unfold q7Family; positivity
      have harg : 7 * ((q7Family t - 1) + 1) + r = 7 * q7Family t + r := by omega
      have h := N7Family_crossing_right (t := t) hr0 hr7
      rw [harg]
      rw [h]
      norm_num


/-- The block counts in the seven-family increase strictly. -/
theorem M7Family_lt_succ (t : ℕ) : M7Family t < M7Family (t + 1) := by
  simp [M7Family]
  omega

/-- Strict monotonicity of the seven-family block count. -/
theorem M7Family_strictMono : StrictMono M7Family :=
  strictMono_nat_of_lt_succ M7Family_lt_succ

/-- Distinct parameters give distinct seven-family integers. -/
theorem N7Family_injective : Function.Injective N7Family := by
  intro a b hab
  have hmul := congrArg (fun x : ℕ => 7 * x) hab
  rw [seven_mul_N7Family a, seven_mul_N7Family b] at hmul
  have hpow : 10 ^ (6 * M7Family a + 2) = 10 ^ (6 * M7Family b + 2) := by
    omega
  have hexp : 6 * M7Family a + 2 = 6 * M7Family b + 2 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 10) hpow
  have hM : M7Family a = M7Family b := by omega
  exact M7Family_strictMono.injective hM

/-- Every seven-family member has units digit three. -/
theorem N7Family_mod_ten (t : ℕ) : N7Family t % 10 = 3 := by
  unfold N7Family periodicN
  simp [Nat.add_mod, Nat.mul_mod]

/-- The seven-family is not generated from itself by appending positive numbers of decimal zeroes. -/
theorem N7Family_not_decimal_scaled {a b z : ℕ} (hz : 0 < z) :
    N7Family a ≠ 10 ^ z * N7Family b := by
  intro h
  cases z with
  | zero => omega
  | succ z =>
      have hm := congrArg (fun x : ℕ => x % 10) h
      rw [N7Family_mod_ten] at hm
      simp [Nat.pow_succ, Nat.mul_mod] at hm

/-- There are infinitely many integers whose maximal Good multiplier is seven. -/
theorem infinitely_many_maxGood_seven :
    Set.Infinite {n : ℕ | MaxGood n 7} := by
  apply Set.infinite_of_injective_forall_mem (f := N7Family)
  · exact N7Family_injective
  · intro t
    exact N7Family_maxGood t

end PeriodicCrossing
end A277223

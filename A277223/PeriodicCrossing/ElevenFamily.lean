import A277223.PeriodicCrossing.Eleven
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Monotone.Basic
import A277223.PeriodicCrossing.AlignedUpdate

/-!
# A nontrivial infinite family with maximal Good multiplier eleven

For this family every nonzero residue class crosses at the same pure decimal
boundary `q = 10^(2*(t+2))`.  The aligned correction changes one width-two
periodic block by `+2`, so no unbounded carry analysis is required.
-/

namespace A277223
namespace PeriodicCrossing

/-- Block count in the pure-power eleven-family. -/
def M11Family : ℕ → ℕ
  | 0 => 12219
  | t + 1 => 100 * M11Family t + 319

/-- Common crossing quotient `100^(t+2)`. -/
def q11Family (t : ℕ) : ℕ := 10 ^ (2 * (t + 2))

/-- The periodic eleven-family. -/
def N11Family (t : ℕ) : ℕ :=
  periodicN 9 9 82 2 (M11Family t) 2

/-- Exact balance positioning the crossing. -/
theorem M11Family_balance (t : ℕ) :
    9 * M11Family t + 29 = 11 * q11Family t := by
  induction t with
  | zero => norm_num [M11Family, q11Family]
  | succ t ih =>
      calc
        9 * M11Family (t + 1) + 29
            = 100 * (9 * M11Family t + 29) := by
                simp [M11Family]
                ring
        _ = 100 * (11 * q11Family t) := by rw [ih]
        _ = 11 * q11Family (t + 1) := by
              unfold q11Family
              rw [show 2 * (t + 1 + 2) = 2 + 2 * (t + 2) by omega, Nat.pow_add]
              norm_num
              ring

/-- The aligned updated block lies inside the periodic word. -/
theorem M11Family_index_lt (t : ℕ) : t + 1 < M11Family t := by
  induction t with
  | zero => norm_num [M11Family]
  | succ t ih =>
      simp [M11Family]
      omega

/-- Sparse product identity for every member. -/
theorem eleven_mul_N11Family (t : ℕ) :
    11 * N11Family t = 9 * 10 ^ (2 * M11Family t + 2) + 2 := by
  unfold N11Family
  convert periodicN_mul
    (p := 11) (Q := 9) (A := 9) (B := 2) (C := 82)
    (d := 2) (M := M11Family t) (t := 2)
    (by norm_num) (by norm_num) using 1 <;> ring

/-- Eleven is Good throughout the family. -/
theorem N11Family_good (t : ℕ) : Good (N11Family t) 11 := by
  unfold Good
  rw [eleven_mul_N11Family]
  rw [show 9 * 10 ^ (2 * M11Family t + 2) + 2 =
      2 + 10 ^ (2 * M11Family t + 2) * 9 by ring]
  have h2 : 2 < 10 ^ (2 * M11Family t + 2) := by
    have hexp : 1 ≤ 2 * M11Family t + 2 := by omega
    have hpow : 10 ^ 1 ≤ 10 ^ (2 * M11Family t + 2) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 10) hexp
    exact lt_of_lt_of_le (by norm_num : 2 < 10) hpow
  rw [digitSum10_append h2]
  decide

/-- The two exceptional residue classes are exactly five and ten. -/
def special11 (r : ℕ) : Prop := r = 5 ∨ r = 10

theorem N11Family_local_data {r : ℕ} (hr0 : 0 < r) (hr11 : r < 11) :
    digitSum10 (a11 r * 9) = 9 ∧
    a11 r * 9 + 2 < 100 ∧
    2 ≤ T11 r ∧ T11 r < 100 ∧
    (((digitSum10 (T11 r) : ℤ) + digitSum10 (a11 r * 9 + 2) + h11 r - r - 29) =
      if special11 r then -27 else -9) ∧
    (((9 : ℤ) + digitSum10 (T11 r - 2) + digitSum10 (a11 r * 9 + 2) + h11 r - r) =
      if special11 r then 18 else 27) := by
  interval_cases r <;> decide +kernel

/-- Exact digit sum at the negative endpoint `q_t`. -/
theorem N11Family_digitSum_right {t r : ℕ} (hr0 : 0 < r) (hr11 : r < 11) :
    digitSum10 ((11 * q11Family t + r) * N11Family t) =
      digitSum10 (T11 r) + ((M11Family t - 1) * 9 +
        digitSum10 (a11 r * 9 + 2)) + (9 + h11 r) := by
  rcases N11Family_local_data hr0 hr11 with
    ⟨hWsum, hWx, hT2, hT100, hright, hleft⟩
  have hrA : r * 9 = 11 * h11 r + a11 r := by
    interval_cases r <;> norm_num [h11, a11]
  have hrC : r * 82 = h11 r * 100 + T11 r := by
    interval_cases r <;> norm_num [h11, T11]
  have hW : a11 r * 9 < 100 := by
    interval_cases r <;> norm_num [a11]
  have hi : t + 1 < M11Family t := M11Family_index_lt t
  have hlowSum := digitSum10_tail_repeat_update
    (T := T11 r) (shift := 2) (W := a11 r * 9) (x := 2)
    (d := 2) (M := M11Family t) (i := t + 1)
    (by simpa using hT100) hW (by simpa using hWx) hi
  have hlowBound := tail_repeat_update_lt_pow
    (T := T11 r) (shift := 2) (W := a11 r * 9) (x := 2)
    (d := 2) (M := M11Family t) (i := t + 1)
    (by simpa using hT100) hW (by simpa using hWx) hi
  have hprod := periodicN_mul_residue
    (p := 11) (Q := 9) (A := 9) (B := 2) (C := 82)
    (d := 2) (M := M11Family t) (t := 2) (q := q11Family t) (r := r)
    (h := h11 r) (a := a11 r) (T := T11 r)
    (by norm_num) (by norm_num) hrA hrC
  have hq : q11Family t = 100 * 10 ^ (2 * (t + 1)) := by
    unfold q11Family
    rw [show 2 * (t + 2) = 2 + 2 * (t + 1) by omega, Nat.pow_add]
  have hloweq :
      10 ^ 2 * repeatBlock (a11 r * 9) 2 (M11Family t) +
          (2 * q11Family t + T11 r) =
        T11 r + 10 ^ 2 *
          (repeatBlock (a11 r * 9) 2 (M11Family t) + 2 * 10 ^ (2 * (t + 1))) := by
    rw [hq]
    ring
  rw [show N11Family t = periodicN 9 9 82 2 (M11Family t) 2 from rfl, hprod]
  first
  · rw [show ((9 * q11Family t + h11 r) * 10 ^ (2 * M11Family t + 2) +
        10 ^ 2 * repeatBlock (a11 r * 9) 2 (M11Family t)) +
        (2 * q11Family t + T11 r) =
      (9 * q11Family t + h11 r) * 10 ^ (2 * M11Family t + 2) +
        (10 ^ 2 * repeatBlock (a11 r * 9) 2 (M11Family t) +
        (2 * q11Family t + T11 r)) by ring]
  · skip
  rw [hloweq]
  rw [show (9 * q11Family t + h11 r) * 10 ^ (2 * M11Family t + 2) +
        (T11 r + 10 ^ 2 *
          (repeatBlock (a11 r * 9) 2 (M11Family t) + 2 * 10 ^ (2 * (t + 1)))) =
      (T11 r + 10 ^ 2 *
          (repeatBlock (a11 r * 9) 2 (M11Family t) + 2 * 10 ^ (2 * (t + 1)))) +
        10 ^ (2 * M11Family t + 2) * (9 * q11Family t + h11 r) by ring]
  rw [digitSum10_append hlowBound, hlowSum, hWsum]
  have hh : h11 r < 9 := by interval_cases r <;> norm_num [h11]
  have hhigh := digitSum10_digit_mul_pow_add
    (A := 9) (h := h11 r) (u := 2 * (t + 2))
    (by norm_num) (by omega) (by omega)
  rw [← (show q11Family t = 10 ^ (2 * (t + 2)) by rfl)] at hhigh
  rw [hhigh]

/-- Exact digit sum at the positive endpoint `q_t-1`. -/
theorem N11Family_digitSum_left {t r : ℕ} (hr0 : 0 < r) (hr11 : r < 11) :
    digitSum10 ((11 * (q11Family t - 1) + r) * N11Family t) =
      digitSum10 (T11 r - 2) + (M11Family t - 1) * 9 +
        digitSum10 (a11 r * 9 + 2) + (18 * (t + 2) + h11 r) := by
  rcases N11Family_local_data hr0 hr11 with
    ⟨hWsum, hWx, hT2, hT100, hright, hleft⟩
  have hrA : r * 9 = 11 * h11 r + a11 r := by
    interval_cases r <;> norm_num [h11, a11]
  have hrC : r * 82 = h11 r * 100 + T11 r := by
    interval_cases r <;> norm_num [h11, T11]
  have hW : a11 r * 9 < 100 := by
    interval_cases r <;> norm_num [a11]
  have hTleft : T11 r - 2 < 100 := by omega
  have hi : t + 1 < M11Family t := M11Family_index_lt t
  have hlowSum := digitSum10_tail_repeat_update
    (T := T11 r - 2) (shift := 2) (W := a11 r * 9) (x := 2)
    (d := 2) (M := M11Family t) (i := t + 1)
    hTleft hW (by simpa using hWx) hi
  have hlowBound := tail_repeat_update_lt_pow
    (T := T11 r - 2) (shift := 2) (W := a11 r * 9) (x := 2)
    (d := 2) (M := M11Family t) (i := t + 1)
    hTleft hW (by simpa using hWx) hi
  have hprod := periodicN_mul_residue
    (p := 11) (Q := 9) (A := 9) (B := 2) (C := 82)
    (d := 2) (M := M11Family t) (t := 2) (q := q11Family t - 1) (r := r)
    (h := h11 r) (a := a11 r) (T := T11 r)
    (by norm_num) (by norm_num) hrA hrC
  have hqpos : 0 < q11Family t := by unfold q11Family; positivity
  have hq : q11Family t = 100 * 10 ^ (2 * (t + 1)) := by
    unfold q11Family
    rw [show 2 * (t + 2) = 2 + 2 * (t + 1) by omega, Nat.pow_add]
  have htail : 2 * (q11Family t - 1) + T11 r =
      2 * q11Family t + (T11 r - 2) := by omega
  have hloweq :
      10 ^ 2 * repeatBlock (a11 r * 9) 2 (M11Family t) +
          (2 * (q11Family t - 1) + T11 r) =
        (T11 r - 2) + 10 ^ 2 *
          (repeatBlock (a11 r * 9) 2 (M11Family t) + 2 * 10 ^ (2 * (t + 1))) := by
    rw [htail, hq]
    ring
  rw [show N11Family t = periodicN 9 9 82 2 (M11Family t) 2 from rfl, hprod]
  first
  · rw [show ((9 * (q11Family t - 1) + h11 r) * 10 ^ (2 * M11Family t + 2) +
        10 ^ 2 * repeatBlock (a11 r * 9) 2 (M11Family t)) +
        (2 * (q11Family t - 1) + T11 r) =
      (9 * (q11Family t - 1) + h11 r) * 10 ^ (2 * M11Family t + 2) +
        (10 ^ 2 * repeatBlock (a11 r * 9) 2 (M11Family t) +
        (2 * (q11Family t - 1) + T11 r)) by ring]
  · skip
  rw [hloweq]
  rw [show (9 * (q11Family t - 1) + h11 r) * 10 ^ (2 * M11Family t + 2) +
        ((T11 r - 2) + 10 ^ 2 *
          (repeatBlock (a11 r * 9) 2 (M11Family t) + 2 * 10 ^ (2 * (t + 1)))) =
      ((T11 r - 2) + 10 ^ 2 *
          (repeatBlock (a11 r * 9) 2 (M11Family t) + 2 * 10 ^ (2 * (t + 1)))) +
        10 ^ (2 * M11Family t + 2) * (9 * (q11Family t - 1) + h11 r) by ring]
  rw [digitSum10_append hlowBound, hlowSum, hWsum]
  have hh : h11 r < 9 := by interval_cases r <;> norm_num [h11]
  have hhigh := digitSum10_digit_mul_pred_pow_add
    (A := 9) (h := h11 r) (u := 2 * (t + 2))
    (by norm_num) (by norm_num) hh (by omega)
  rw [← (show q11Family t = 10 ^ (2 * (t + 2)) by rfl)] at hhigh
  rw [hhigh]
  ring

/-- Strict positive side of all ten residue crossings. -/
theorem N11Family_crossing_left {t r : ℕ} (hr0 : 0 < r) (hr11 : r < 11) :
    0 < defect (N11Family t) (11 * (q11Family t - 1) + r) := by
  unfold defect
  rw [N11Family_digitSum_left hr0 hr11]
  rcases N11Family_local_data hr0 hr11 with
    ⟨hWsum, hWx, hT2, hT100, hright, hleft⟩
  have hbal := M11Family_balance t
  by_cases hs : special11 r
  · rw [if_pos hs] at hleft
    push_cast at *
    omega
  · rw [if_neg hs] at hleft
    push_cast at *
    omega

/-- Strict negative side of all ten residue crossings. -/
theorem N11Family_crossing_right {t r : ℕ} (hr0 : 0 < r) (hr11 : r < 11) :
    defect (N11Family t) (11 * q11Family t + r) < 0 := by
  unfold defect
  rw [N11Family_digitSum_right hr0 hr11]
  rcases N11Family_local_data hr0 hr11 with
    ⟨hWsum, hWx, hT2, hT100, hright, hleft⟩
  have hbal := M11Family_balance t
  by_cases hs : special11 r
  · rw [if_pos hs] at hright
    push_cast at *
    omega
  · rw [if_neg hs] at hright
    push_cast at *
    omega

/-- The second zero-residue point is negative throughout the family. -/
theorem N11Family_defect_twenty_two (t : ℕ) : defect (N11Family t) 22 = -9 := by
  unfold defect
  have h : 22 * N11Family t = 4 + 10 ^ (2 * M11Family t + 2) * 18 := by
    calc
      22 * N11Family t = 2 * (11 * N11Family t) := by ring
      _ = 2 * (9 * 10 ^ (2 * M11Family t + 2) + 2) := by rw [eleven_mul_N11Family]
      _ = 4 + 10 ^ (2 * M11Family t + 2) * 18 := by ring
  rw [h]
  have hb : 4 < 10 ^ (2 * M11Family t + 2) := by
    have hexp : 1 ≤ 2 * M11Family t + 2 := by omega
    have hpow : 10 ^ 1 ≤ 10 ^ (2 * M11Family t + 2) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 10) hexp
    exact lt_of_lt_of_le (by norm_num : 4 < 10) hpow
  rw [digitSum10_append hb]
  decide

/-- Every member of the pure-power family has maximal Good multiplier eleven. -/
theorem N11Family_maxGood (t : ℕ) : MaxGood (N11Family t) 11 := by
  apply maxGood_of_crossings (N := N11Family t) (p := 11) (by norm_num) (N11Family_good t)
  · rw [show 2 * 11 = 22 by norm_num]
    rw [N11Family_defect_twenty_two t]
    norm_num
  · intro r hr0 hr11
    refine ⟨q11Family t - 1, N11Family_crossing_left hr0 hr11, ?_⟩
    have hqpos : 0 < q11Family t := by unfold q11Family; positivity
    have harg : 11 * ((q11Family t - 1) + 1) + r = 11 * q11Family t + r := by omega
    simpa [harg] using N11Family_crossing_right (t := t) hr0 hr11


/-- The block counts in the eleven-family increase strictly. -/
theorem M11Family_lt_succ (t : ℕ) : M11Family t < M11Family (t + 1) := by
  simp [M11Family]
  omega

/-- Strict monotonicity of the eleven-family block count. -/
theorem M11Family_strictMono : StrictMono M11Family :=
  strictMono_nat_of_lt_succ M11Family_lt_succ

/-- Distinct parameters give distinct eleven-family integers. -/
theorem N11Family_injective : Function.Injective N11Family := by
  intro a b hab
  have hmul := congrArg (fun x : ℕ => 11 * x) hab
  rw [eleven_mul_N11Family a, eleven_mul_N11Family b] at hmul
  have hpow : 10 ^ (2 * M11Family a + 2) = 10 ^ (2 * M11Family b + 2) := by
    omega
  have hexp : 2 * M11Family a + 2 = 2 * M11Family b + 2 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 10) hpow
  have hM : M11Family a = M11Family b := by omega
  exact M11Family_strictMono.injective hM

/-- Every eleven-family member has units digit two. -/
theorem N11Family_mod_ten (t : ℕ) : N11Family t % 10 = 2 := by
  unfold N11Family periodicN
  simp [Nat.add_mod, Nat.mul_mod]

/-- The eleven-family is not generated from itself by appending positive numbers of decimal zeroes. -/
theorem N11Family_not_decimal_scaled {a b z : ℕ} (hz : 0 < z) :
    N11Family a ≠ 10 ^ z * N11Family b := by
  intro h
  cases z with
  | zero => omega
  | succ z =>
      have hm := congrArg (fun x : ℕ => x % 10) h
      rw [N11Family_mod_ten] at hm
      simp [Nat.pow_succ, Nat.mul_mod] at hm

/-- There are infinitely many integers whose maximal Good multiplier is eleven. -/
theorem infinitely_many_maxGood_eleven :
    Set.Infinite {n : ℕ | MaxGood n 11} := by
  apply Set.infinite_of_injective_forall_mem (f := N11Family)
  · exact N11Family_injective
  · intro t
    exact N11Family_maxGood t

end PeriodicCrossing
end A277223

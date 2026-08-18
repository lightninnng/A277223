import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
# Basic decimal digit-sum infrastructure for A277223

The project deliberately keeps the OEIS definition out of the foundational layer.
`Good n k` is the equation `s(k*n)=k`; `MaxGood n k` says that `k` is a
largest solution of that equation. This formulation avoids any preliminary
existence theorem for the maximum.
-/

namespace A277223

open Nat

/-- Decimal digit sum. -/
def digitSum10 (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- `k` is a Good multiplier for `n` when the decimal digit sum of `k*n` is `k`. -/
def Good (n k : ℕ) : Prop := digitSum10 (k * n) = k

/-- `k` is a largest Good multiplier for `n`. -/
def MaxGood (n k : ℕ) : Prop := Good n k ∧ ∀ j, Good n j → j ≤ k

@[simp] theorem digitSum10_zero : digitSum10 0 = 0 := by
  simp [digitSum10]

@[simp] theorem good_zero (n : ℕ) : Good n 0 := by
  simp [Good]

/-- A one-digit natural has digit sum equal to itself. -/
theorem digitSum10_of_lt_10 {n : ℕ} (h : n < 10) : digitSum10 n = n := by
  interval_cases n <;> decide

/-- Recursive decimal digit-sum formula for nonzero naturals. -/
theorem digitSum10_rec {n : ℕ} (hn : n ≠ 0) :
    digitSum10 n = n % 10 + digitSum10 (n / 10) := by
  unfold digitSum10
  rw [Nat.digits_eq_cons_digits_div (by norm_num : 1 < 10) hn]
  simp

/-- Appending decimal zeroes does not alter digit sum. -/
theorem digitSum10_pow_mul (t n : ℕ) :
    digitSum10 (10 ^ t * n) = digitSum10 n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    unfold digitSum10
    rw [Nat.digits_base_pow_mul (by norm_num : 1 < 10) hnpos]
    simp

/-- Right-handed form of `digitSum10_pow_mul`. -/
theorem digitSum10_mul_pow (n t : ℕ) :
    digitSum10 (n * 10 ^ t) = digitSum10 n := by
  rw [Nat.mul_comm]
  exact digitSum10_pow_mul t n

/--
If `x` occupies fewer than `w+1` decimal places, then the two blocks in
`x + 10^w*y` are disjoint and their digit sums add.
-/
theorem digitSum10_append {x y w : ℕ} (hx : x < 10 ^ w) :
    digitSum10 (x + 10 ^ w * y) = digitSum10 x + digitSum10 y := by
  by_cases hy : y = 0
  · simp [hy]
  · have hypos : 0 < y := Nat.pos_of_ne_zero hy
    have hlen : (Nat.digits 10 x).length ≤ w :=
      (Nat.digits_length_le_iff (by norm_num : 1 < 10) x).2 hx
    let k := w - (Nat.digits 10 x).length
    have hk : (Nat.digits 10 x).length + k = w := by
      dsimp [k]
      exact Nat.add_sub_of_le hlen
    have hdigits := Nat.digits_append_zeroes_append_digits
      (b := 10) (k := k) (m := y) (n := x) (by norm_num : 1 < 10) hypos
    rw [hk] at hdigits
    have hsum := congrArg List.sum hdigits
    simpa [digitSum10, List.sum_append] using hsum.symm

/--
Decimal digit sum is subadditive. The proof is a strong induction on `x+y`
and makes the carry bit in the units column explicit.
-/
theorem digitSum10_add_le (x y : ℕ) :
    digitSum10 (x + y) ≤ digitSum10 x + digitSum10 y := by
  let P : ℕ → Prop := fun n =>
    ∀ a b : ℕ, a + b = n → digitSum10 (a + b) ≤ digitSum10 a + digitSum10 b
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp [P]
        intro a b hab
        by_cases ha : a = 0
        · subst a
          simp
        by_cases hb : b = 0
        · subst b
          simp
        let a0 := a % 10
        let a1 := a / 10
        let b0 := b % 10
        let b1 := b / 10
        let c := (a0 + b0) / 10
        let d := (a0 + b0) % 10
        let z := a1 + b1 + c
        have ha0 : a0 < 10 := by
          dsimp [a0]
          exact Nat.mod_lt _ (by norm_num)
        have hb0 : b0 < 10 := by
          dsimp [b0]
          exact Nat.mod_lt _ (by norm_num)
        have hd : d < 10 := by
          dsimp [d]
          exact Nat.mod_lt _ (by norm_num)
        have hc : c ≤ 1 := by
          dsimp [c]
          omega
        have ha1lt : a1 < a := by
          dsimp [a1]
          exact Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by norm_num)
        have hb1lt : b1 < b := by
          dsimp [b1]
          exact Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by norm_num)
        have hadecomp : a0 + 10 * a1 = a := by
          dsimp [a0, a1]
          exact Nat.mod_add_div a 10
        have hbdecomp : b0 + 10 * b1 = b := by
          dsimp [b0, b1]
          exact Nat.mod_add_div b 10
        have hab0decomp : d + 10 * c = a0 + b0 := by
          dsimp [c, d]
          exact Nat.mod_add_div (a0 + b0) 10
        have hsumdecomp : d + 10 * z = a + b := by
          dsimp [z]
          omega
        have hzlt : z < n := by
          dsimp [z]
          omega
        have hbclt : b1 + c < n := by
          omega
        have hzdef : a1 + (b1 + c) = z := by
          dsimp [z]
          omega
        have hIH1 := ih z hzlt a1 (b1 + c) hzdef
        have hIH1z : digitSum10 z ≤ digitSum10 a1 + digitSum10 (b1 + c) := by
          simpa [hzdef] using hIH1
        have hIH2 := ih (b1 + c) hbclt b1 c rfl
        have hcsum : digitSum10 c = c := digitSum10_of_lt_10 (by omega)
        have hapos : 0 < a := Nat.pos_of_ne_zero ha
        have hbpos : 0 < b := Nat.pos_of_ne_zero hb
        have habpos : 0 < a + b := by omega
        have hasum := digitSum10_rec ha
        have hbsum := digitSum10_rec hb
        have habsum := digitSum10_rec (Nat.ne_of_gt habpos)
        have hamod : a % 10 = a0 := rfl
        have hbmod : b % 10 = b0 := rfl
        have hadiv : a / 10 = a1 := rfl
        have hbdiv : b / 10 = b1 := rfl
        have hmodsum : (a + b) % 10 = d := by
          rw [← hsumdecomp]
          simp [Nat.add_mod, Nat.mod_eq_of_lt hd]
        have hdivsum : (a + b) / 10 = z := by
          rw [← hsumdecomp]
          simp [Nat.add_mul_div_left, Nat.div_eq_of_lt hd]
        rw [hmodsum, hdivsum] at habsum
        rw [hamod, hadiv] at hasum
        rw [hbmod, hbdiv] at hbsum
        rw [habsum, hasum, hbsum]
        rw [hcsum] at hIH2
        omega
  exact hP (x + y) x y rfl

/-- Subadditivity for any finite list. -/
theorem digitSum10_list_sum_le (L : List ℕ) :
    digitSum10 L.sum ≤ (L.map digitSum10).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.sum_cons, List.map_cons, List.sum_cons]
      exact le_trans (digitSum10_add_le a L.sum) (Nat.add_le_add_left ih _)

/-- `Good` is unchanged when `n` receives trailing decimal zeroes. -/
theorem good_pow_mul_iff (t n k : ℕ) : Good (10 ^ t * n) k ↔ Good n k := by
  simp only [Good]
  have hmul : k * (10 ^ t * n) = 10 ^ t * (k * n) := by ring
  rw [hmul, digitSum10_pow_mul]

/-- `MaxGood` is unchanged by appending trailing decimal zeroes to `n`. -/
theorem maxGood_pow_mul_iff (t n k : ℕ) : MaxGood (10 ^ t * n) k ↔ MaxGood n k := by
  constructor
  · rintro ⟨hk, hmax⟩
    refine ⟨(good_pow_mul_iff t n k).1 hk, ?_⟩
    intro j hj
    exact hmax j ((good_pow_mul_iff t n j).2 hj)
  · rintro ⟨hk, hmax⟩
    refine ⟨(good_pow_mul_iff t n k).2 hk, ?_⟩
    intro j hj
    exact hmax j ((good_pow_mul_iff t n j).1 hj)

/-- A unique positive Good multiplier is automatically maximal. -/
theorem maxGood_of_unique_positive {n p : ℕ}
    (hp : Good n p)
    (huniq : ∀ k, 0 < k → Good n k → k = p) :
    MaxGood n p := by
  refine ⟨hp, ?_⟩
  intro j hj
  by_cases hj0 : j = 0
  · simp [hj0]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    simpa [huniq j hjpos hj]

end A277223

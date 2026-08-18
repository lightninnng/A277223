import A277223.PeriodicCrossing.Seven
import A277223.PeriodicCrossing.Eleven

/-!
# Elementary realized values 0 and 9

`n=1` realizes 9.  `n=62` realizes 0; the latter proof is not imported from
OEIS data.  A Good multiplier for 62 must be divisible by nine, while a
digit-length estimate bounds it by 36, leaving only four explicit candidates.
-/

namespace A277223

/-- A list whose entries are at most nine has sum at most nine times its length. -/
theorem list_sum_le_nine_mul_length (L : List ℕ)
    (hL : ∀ d ∈ L, d ≤ 9) : L.sum ≤ 9 * L.length := by
  induction L with
  | nil => simp
  | cons d L ih =>
      have hd : d ≤ 9 := hL d (by simp)
      have htail : ∀ x ∈ L, x ≤ 9 := by
        intro x hx
        exact hL x (List.mem_cons_of_mem d hx)
      have hih := ih htail
      simp only [List.sum_cons, List.length_cons]
      omega

/-- Any decimal digit sum is at most nine times the number of digits. -/
theorem digitSum10_le_nine_mul_length (n : ℕ) :
    digitSum10 n ≤ 9 * (Nat.digits 10 n).length := by
  unfold digitSum10
  apply list_sum_le_nine_mul_length
  intro d hd
  have hlt := Nat.digits_lt_base (by norm_num : 1 < 10) hd
  omega

/-- For `k >= 10`, decimal digit sum is strictly smaller than `k`. -/
theorem digitSum10_lt_self_of_ten_le {k : ℕ} (hk : 10 ≤ k) :
    digitSum10 k < k := by
  have hk0 : k ≠ 0 := by omega
  have hrec := digitSum10_rec hk0
  have hqpos : 0 < k / 10 := Nat.div_pos hk (by norm_num)
  have hqle : digitSum10 (k / 10) ≤ k / 10 := by
    simpa [digitSum10] using Nat.digit_sum_le 10 (k / 10)
  have hdecomp : k % 10 + 10 * (k / 10) = k := Nat.mod_add_div k 10
  omega

/-- Nine is the unique largest Good multiplier for one. -/
theorem one_maxGood_nine : MaxGood 1 9 := by
  refine ⟨?_, ?_⟩
  · unfold Good
    norm_num
    decide
  · intro j hj
    by_contra hnot
    have hj10 : 10 ≤ j := by omega
    have hlt := digitSum10_lt_self_of_ten_le hj10
    have heq : digitSum10 j = j := by simpa [Good] using hj
    omega

/-- Elementary exponential estimate used in the `n=62` proof. -/
theorem five_fifty_eight_mul_lt_pow {L : ℕ} (hL : 5 ≤ L) :
    558 * L < 10 ^ (L - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hL
  induction d with
  | zero => norm_num
  | succ d ih =>
      have hratio : 558 * (5 + (d + 1)) < 10 * (558 * (5 + d)) := by
        omega
      have hmul : 10 * (558 * (5 + d)) < 10 * 10 ^ ((5 + d) - 1) := by
        exact Nat.mul_lt_mul_of_pos_left ih (by norm_num)
      calc
        558 * (5 + (d + 1)) < 10 * (558 * (5 + d)) := hratio
        _ < 10 * 10 ^ ((5 + d) - 1) := hmul
        _ = 10 ^ ((5 + (d + 1)) - 1) := by
              have : (5 + d) - 1 + 1 = (5 + (d + 1)) - 1 := by omega
              rw [← this]; simpa [Nat.pow_succ, Nat.mul_comm]

/-- A positive Good multiplier for 62 has size at most 36. -/
theorem good_62_le_36 {k : ℕ} (hkpos : 0 < k) (hk : Good 62 k) : k ≤ 36 := by
  let x := 62 * k
  let L := (Nat.digits 10 x).length
  have hxpos : 0 < x := by dsimp [x]; omega
  have hksum : digitSum10 x = k := by
    simpa [Good, x, Nat.mul_comm] using hk
  have hkle : k ≤ 9 * L := by
    rw [← hksum]
    simpa [L] using digitSum10_le_nine_mul_length x
  by_contra h36
  have hL5 : 5 ≤ L := by
    by_contra hL
    have hL4 : L ≤ 4 := by omega
    omega
  have hLpos : 0 < L := by omega
  have hpow : 10 ^ (L - 1) ≤ x := by
    have hpred : L - 1 < (Nat.digits 10 x).length := by simpa [L] using Nat.pred_lt hLpos
    exact (Nat.lt_digits_length_iff (by norm_num : 1 < 10) x).1 hpred
  have hxupper : x ≤ 558 * L := by
    dsimp [x]
    nlinarith
  have hstrict := five_fifty_eight_mul_lt_pow hL5
  omega

/-- Modulo nine, a Good multiplier for 62 must itself be divisible by nine. -/
theorem nine_dvd_good_62 {k : ℕ} (hk : Good 62 k) : 9 ∣ k := by
  have hmod := Nat.modEq_digits_sum 9 10 (by norm_num) (62 * k)
  have hsum : (Nat.digits 10 (62 * k)).sum = k := by
    simpa [Good, digitSum10, Nat.mul_comm] using hk
  rw [hsum] at hmod
  change (62 * k) % 9 = k % 9 at hmod
  have hmod' : (8 * (k % 9)) % 9 = k % 9 := by
    calc
      (8 * (k % 9)) % 9 = (62 * k) % 9 := by
        simp [Nat.mul_mod]
      _ = k % 9 := hmod
  let r := k % 9
  have hrlt : r < 9 := by
    dsimp [r]
    exact Nat.mod_lt _ (by norm_num)
  have hmodr : (8 * r) % 9 = r := by simpa [r] using hmod'
  have hr0 : r = 0 := by
    interval_cases r <;> norm_num at hmodr ⊢
  refine ⟨k / 9, ?_⟩
  have hdecomp := Nat.mod_add_div k 9
  rw [hr0] at hdecomp
  omega

/-- The four possible positive multipliers left by the preceding two lemmas all fail. -/
theorem no_positive_good_62 {k : ℕ} (hkpos : 0 < k) : ¬ Good 62 k := by
  intro hk
  have hk36 := good_62_le_36 hkpos hk
  obtain ⟨q, hkq⟩ := nine_dvd_good_62 hk
  have hqpos : 0 < q := by omega
  have hq4 : q ≤ 4 := by omega
  interval_cases q <;> subst k <;> norm_num [Good, digitSum10, Nat.digits] at hk

/-- Sixty-two has no positive Good multiplier, hence its maximum is zero. -/
theorem sixtyTwo_maxGood_zero : MaxGood 62 0 := by
  refine ⟨good_zero 62, ?_⟩
  intro j hj
  by_cases hj0 : j = 0
  · simp [hj0]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    exact (no_positive_good_62 hjpos hj).elim

end A277223

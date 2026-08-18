import A277223.Basic

/-!
# Carry obstruction: abstract theory

The mathematical mechanism is a decimal rescaling.  If `m = k*n`, a triple
`(c,j,z)` with

* `k < j`,
* `c*k = j*10^z`, and
* `s(c*m)=j`

turns a Good multiplier `k` into a strictly larger Good multiplier `j`.

The deeper `k=8,10` proofs are certified in `Certificate.lean`; this file
contains the general rescaling theory and the elementary targets `1,...,6`.
-/

namespace A277223
namespace CarryObstruction

/-- Any element of a list of naturals is at most the list sum. -/
theorem le_sum_of_mem_nat {d : ℕ} {L : List ℕ} (hd : d ∈ L) : d ≤ L.sum := by
  induction L with
  | nil => simp at hd
  | cons a L ih =>
      simp only [List.sum_cons]
      rcases List.mem_cons.mp hd with rfl | hd
      · omega
      · have hdle : d ≤ L.sum := ih hd
        omega

/-- Sum after multiplying every list entry by a fixed natural. -/
theorem sum_map_mul_left (c : ℕ) (L : List ℕ) :
    (L.map (fun d => c * d)).sum = c * L.sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, Nat.mul_add]

/--
If each decimal digit `d` of `m` satisfies `c*d < 10`, multiplication by `c`
creates no carry and the digit sum is multiplied by `c`.
-/
theorem digitSum10_mul_of_digitwise_lt_10 {c m : ℕ}
    (hvalid : ∀ d ∈ Nat.digits 10 m, c * d < 10) :
    digitSum10 (c * m) = c * digitSum10 m := by
  let L := Nat.digits 10 m
  have hvalid' : ∀ d ∈ L.map (fun d => c * d), d < 10 := by
    intro d hd
    rcases List.mem_map.mp hd with ⟨e, he, rfl⟩
    exact hvalid e (by simpa [L] using he)
  have hsumDigits := Nat.sum_digits_ofDigits_eq_sum
    (b := 10) (by norm_num : 1 < 10)
    (l := L.length) (L := L.map (fun d => c * d))
    (show (L.map (fun d => c * d)) ∈
        {K : List ℕ | K.length = L.length ∧ ∀ x ∈ K, x < 10} from
      ⟨by simp, hvalid'⟩)
  have hmul : c * m = Nat.ofDigits 10 (L.map (fun d => c * d)) := by
    calc
      c * m = c * Nat.ofDigits 10 L := by simp [L, Nat.ofDigits_digits]
      _ = Nat.ofDigits 10 (L.map (fun d => c * d)) := Nat.mul_ofDigits c
  rw [digitSum10, hmul, hsumDigits, sum_map_mul_left]
  rfl

/-- Doubling is carry-free when all decimal digits are at most four. -/
theorem digitSum10_two_mul_of_digits_le_four {m : ℕ}
    (hsmall : ∀ d ∈ Nat.digits 10 m, d ≤ 4) :
    digitSum10 (2 * m) = 2 * digitSum10 m := by
  apply digitSum10_mul_of_digitwise_lt_10
  intro d hd
  have := hsmall d hd
  omega

/-- In particular, digit sum at most four makes doubling carry-free. -/
theorem digitSum10_two_mul_of_le_four {m : ℕ} (hm : digitSum10 m ≤ 4) :
    digitSum10 (2 * m) = 2 * digitSum10 m := by
  apply digitSum10_two_mul_of_digits_le_four
  intro d hd
  have hdle : d ≤ digitSum10 m := by
    exact le_sum_of_mem_nat (by simpa [digitSum10] using hd)
  omega

/-- A decimal rescaling certificate for a number of digit sum `k`. -/
structure RescalingWitness (k m : ℕ) where
  c : ℕ
  j : ℕ
  z : ℕ
  larger : k < j
  scale : c * k = j * 10 ^ z
  digitSum : digitSum10 (c * m) = j

/-- Every number of digit sum `k` admits a rescaling to a larger target. -/
def CarryObstruction (k : ℕ) : Prop :=
  ∀ m : ℕ, digitSum10 m = k → Nonempty (RescalingWitness k m)

/-- Rescaling a Good product produces a larger Good multiplier. -/
theorem larger_good_of_witness {n k : ℕ} (hk : Good n k)
    {m : ℕ} (hm : m = k * n) (w : RescalingWitness k m) :
    Good n w.j := by
  have hcm : w.c * m = 10 ^ w.z * (w.j * n) := by
    subst m
    calc
      w.c * (k * n) = (w.c * k) * n := by ring
      _ = (w.j * 10 ^ w.z) * n := by rw [w.scale]
      _ = 10 ^ w.z * (w.j * n) := by ring
  have hs := w.digitSum
  rw [hcm, digitSum10_pow_mul] at hs
  exact hs

/-- A carry obstruction rules out maximality. -/
theorem not_maxGood_of_carryObstruction {n k : ℕ}
    (hobs : CarryObstruction k) (hk : Good n k) : ¬ MaxGood n k := by
  intro hmax
  obtain ⟨w⟩ := hobs (k * n) hk
  have hj : Good n w.j := larger_good_of_witness hk rfl w
  have hle := hmax.2 w.j hj
  have hlt : k < w.j := w.larger
  omega

/-- Targets `1,2,3,4` are carry-obstructed by simple doubling. -/
theorem carryObstruction_of_pos_le_four {k : ℕ} (hk0 : 0 < k) (hk4 : k ≤ 4) :
    CarryObstruction k := by
  intro m hm
  refine ⟨{
    c := 2
    j := 2 * k
    z := 0
    larger := by omega
    scale := by simp
    digitSum := ?_
  }⟩
  have hle : digitSum10 m ≤ 4 := by omega
  rw [digitSum10_two_mul_of_le_four hle, hm]

/-- A list of decimal coefficients with sum zero represents zero. -/
theorem ofDigits_eq_zero_of_sum_eq_zero (L : List ℕ) (h : L.sum = 0) :
    Nat.ofDigits 10 L = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      simp only [List.sum_cons] at h
      have ha : a = 0 := by omega
      have hL : L.sum = 0 := by omega
      simp [Nat.ofDigits, ha, ih hL]

/-- A coefficient list of total mass one is a single decimal unit. -/
theorem ofDigits_eq_pow_of_sum_eq_one (L : List ℕ) (h : L.sum = 1) :
    ∃ e : ℕ, Nat.ofDigits 10 L = 10 ^ e := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
      simp only [List.sum_cons] at h
      by_cases ha : a = 0
      · have hL : L.sum = 1 := by omega
        obtain ⟨e, he⟩ := ih hL
        refine ⟨e + 1, ?_⟩
        simp [Nat.ofDigits, ha, he, pow_succ'] <;> ring
      · have ha1 : a = 1 := by omega
        have hL0 : L.sum = 0 := by omega
        refine ⟨0, ?_⟩
        simp [Nat.ofDigits, ha1, ofDigits_eq_zero_of_sum_eq_zero L hL0]

/--
If a coefficient reaches the whole coefficient mass, the represented number is
one decimal monomial.
-/
theorem ofDigits_eq_monomial_of_sum_eq_of_large
    (L : List ℕ) (k : ℕ) (hs : L.sum = k)
    (hex : ∃ d ∈ L, k ≤ d) :
    ∃ e : ℕ, Nat.ofDigits 10 L = k * 10 ^ e := by
  induction L with
  | nil => simp at hex
  | cons a L ih =>
      simp only [List.sum_cons] at hs
      obtain ⟨d, hd, hkd⟩ := hex
      rcases List.mem_cons.mp hd with hda | hd
      · subst d
        have hak : a = k := by omega
        have hL0 : L.sum = 0 := by omega
        refine ⟨0, ?_⟩
        simp [Nat.ofDigits, hak, ofDigits_eq_zero_of_sum_eq_zero L hL0]
      · have hdle : d ≤ L.sum := le_sum_of_mem_nat hd
        have ha0 : a = 0 := by omega
        have hLs : L.sum = k := by omega
        obtain ⟨e, he⟩ := ih hLs ⟨d, hd, hkd⟩
        refine ⟨e + 1, ?_⟩
        simp [Nat.ofDigits, ha0, he, pow_succ] <;> ring

/-- Digit-sum form of the preceding monomial lemma. -/
theorem eq_monomial_of_digitSum_eq_of_large_digit {m k : ℕ}
    (hs : digitSum10 m = k)
    (hex : ∃ d ∈ Nat.digits 10 m, k ≤ d) :
    ∃ e : ℕ, m = k * 10 ^ e := by
  let L := Nat.digits 10 m
  have hsum : L.sum = k := by simpa [L, digitSum10] using hs
  obtain ⟨e, he⟩ :=
    ofDigits_eq_monomial_of_sum_eq_of_large L k hsum (by simpa [L] using hex)
  refine ⟨e, ?_⟩
  rw [← Nat.ofDigits_digits 10 m]
  exact he

/-- A coefficient list of mass six containing a `5` has shape `5+1`. -/
theorem ofDigits_sum_six_mem_five (L : List ℕ)
    (hs : L.sum = 6) (h5 : 5 ∈ L) :
    ∃ e f : ℕ, e ≠ f ∧ Nat.ofDigits 10 L = 5 * 10 ^ e + 10 ^ f := by
  induction L with
  | nil => simp at h5
  | cons a L ih =>
      simp only [List.sum_cons] at hs
      rcases List.mem_cons.mp h5 with rfl | h5L
      · have hLs : L.sum = 1 := by omega
        obtain ⟨f, hf⟩ := ofDigits_eq_pow_of_sum_eq_one L hLs
        refine ⟨0, f + 1, by omega, ?_⟩
        simp [Nat.ofDigits, hf, pow_succ'] <;> ring
      · have h5le : 5 ≤ L.sum := le_sum_of_mem_nat h5L
        have ha : a = 0 ∨ a = 1 := by omega
        rcases ha with rfl | rfl
        · have hLs : L.sum = 6 := by omega
          obtain ⟨e, f, hef, hval⟩ := ih hLs h5L
          refine ⟨e + 1, f + 1, by omega, ?_⟩
          simp [Nat.ofDigits, hval, pow_succ']
          ring
        · have hLs : L.sum = 5 := by omega
          obtain ⟨e, he⟩ :=
            ofDigits_eq_monomial_of_sum_eq_of_large L 5 hLs ⟨5, h5L, le_rfl⟩
          refine ⟨e + 1, 0, by omega, ?_⟩
          simp [Nat.ofDigits, he, pow_succ']
          ring

/--
`125*10^e` and `25*10^f` have digit sum fifteen at distinct decimal
positions. The two overlapping gaps are checked directly; from gap three on
the blocks are separated.
-/
theorem digitSum10_125_25_distinct {e f : ℕ} (hef : e ≠ f) :
    digitSum10 (125 * 10 ^ e + 25 * 10 ^ f) = 15 := by
  rcases lt_or_gt_of_ne hef with h | h
  · obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt h)
    have hqpos : 0 < q := by omega
    subst f
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hqpos)
    rw [pow_add, pow_succ']
    have hfactor :
        125 * 10 ^ e + 25 * (10 ^ e * (10 * 10 ^ d)) =
          (125 + 250 * 10 ^ d) * 10 ^ e := by ring
    rw [hfactor, digitSum10_mul_pow]
    cases d with
    | zero => decide
    | succ d =>
        cases d with
        | zero => decide
        | succ d =>
            have hx : 125 < 10 ^ (d + 3) := by
              have hpow : 1 ≤ 10 ^ d := by
                have hpos : 0 < 10 ^ d := by
                  positivity
                omega
              calc
                125 < 1000 := by norm_num
                _ ≤ 1000 * 10 ^ d := by
                      simpa using Nat.mul_le_mul_left 1000 hpow
                _ = 10 ^ (d + 3) := by
                      rw [show d + 3 = 3 + d by omega, Nat.pow_add]
            rw [show 125 + 250 * 10 ^ (d + 2) =
                125 + 10 ^ (d + 3) * 25 by
                  rw [show d + 3 = (d + 2) + 1 by omega, pow_succ']
                  ring]
            rw [digitSum10_append hx]
            decide
  · obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt h)
    have hqpos : 0 < q := by omega
    subst e
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hqpos)
    rw [Nat.pow_add]
    have hfactor :
        125 * (10 ^ f * 10 ^ (d + 1)) + 25 * 10 ^ f =
          (125 * 10 ^ (d + 1) + 25) * 10 ^ f := by ring
    rw [hfactor, digitSum10_mul_pow]
    cases d with
    | zero => decide
    | succ d =>
        have hrepr : 125 * 10 ^ (d + 2) + 25 = 25 + 10 ^ 2 * (125 * 10 ^ d) := by
          rw [show d + 2 = 2 + d by omega, Nat.pow_add]
          ring
        rw [hrepr, digitSum10_append (by norm_num : 25 < 10 ^ 2)]
        rw [digitSum10_mul_pow]
        decide

/-- Target five is carry-obstructed. -/
theorem carryObstruction_five : CarryObstruction 5 := by
  intro m hm
  by_cases hsmall : ∀ d ∈ Nat.digits 10 m, d ≤ 4
  · refine ⟨{
      c := 2, j := 10, z := 0,
      larger := by norm_num,
      scale := by norm_num,
      digitSum := ?_ }⟩
    rw [digitSum10_two_mul_of_digits_le_four hsmall, hm]
  · push_neg at hsmall
    obtain ⟨d, hd, hd5⟩ := hsmall
    have hdle : d ≤ digitSum10 m :=
      le_sum_of_mem_nat (by simpa [digitSum10] using hd)
    have hex : ∃ d ∈ Nat.digits 10 m, 5 ≤ d := ⟨d, hd, by omega⟩
    obtain ⟨e, rfl⟩ := eq_monomial_of_digitSum_eq_of_large_digit hm hex
    refine ⟨{
      c := 18, j := 9, z := 1,
      larger := by norm_num,
      scale := by norm_num,
      digitSum := ?_ }⟩
    rw [show 18 * (5 * 10 ^ e) = 90 * 10 ^ e by ring, digitSum10_mul_pow]
    decide

/-- Target six is carry-obstructed. -/
theorem carryObstruction_six : CarryObstruction 6 := by
  intro m hm
  by_cases hsmall : ∀ d ∈ Nat.digits 10 m, d ≤ 4
  · refine ⟨{
      c := 2, j := 12, z := 0,
      larger := by norm_num,
      scale := by norm_num,
      digitSum := ?_ }⟩
    rw [digitSum10_two_mul_of_digits_le_four hsmall, hm]
  · push_neg at hsmall
    obtain ⟨d, hd, hd5⟩ := hsmall
    have hdle : d ≤ 6 := by
      have : d ≤ digitSum10 m :=
        le_sum_of_mem_nat (by simpa [digitSum10] using hd)
      omega
    by_cases hd6 : 6 ≤ d
    · have hex : ∃ d ∈ Nat.digits 10 m, 6 ≤ d := ⟨d, hd, hd6⟩
      obtain ⟨e, rfl⟩ := eq_monomial_of_digitSum_eq_of_large_digit hm hex
      refine ⟨{
        c := 15, j := 9, z := 1,
        larger := by norm_num,
        scale := by norm_num,
        digitSum := ?_ }⟩
      rw [show 15 * (6 * 10 ^ e) = 90 * 10 ^ e by ring, digitSum10_mul_pow]
      decide
    · have hd_eq : d = 5 := by omega
      have h5 : 5 ∈ Nat.digits 10 m := by simpa [hd_eq] using hd
      let L := Nat.digits 10 m
      have hLs : L.sum = 6 := by simpa [L, digitSum10] using hm
      obtain ⟨e, f, hef, hval⟩ :=
        ofDigits_sum_six_mem_five L hLs (by simpa [L] using h5)
      have hmval : m = 5 * 10 ^ e + 10 ^ f := by
        rw [← Nat.ofDigits_digits 10 m]
        exact hval
      refine ⟨{
        c := 25, j := 15, z := 1,
        larger := by norm_num,
        scale := by norm_num,
        digitSum := ?_ }⟩
      rw [hmval]
      have hprod :
          25 * (5 * 10 ^ e + 10 ^ f) = 125 * 10 ^ e + 25 * 10 ^ f := by ring
      rw [hprod]
      exact digitSum10_125_25_distinct hef

end CarryObstruction
end A277223

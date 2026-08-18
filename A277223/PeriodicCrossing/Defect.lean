import A277223.Basic

/-!
# Periodic crossing: defect monotonicity

For a fixed `N`, the integer defect is

`Delta_N(k) = s(k*N) - k`.

If `p` is Good, digit-sum subadditivity implies
`Delta_N(k+p) <= Delta_N(k)`. Hence the defect is antitone on every
residue class modulo `p`. A single strict sign crossing therefore excludes
all zeroes in that residue class.
-/

namespace A277223
namespace PeriodicCrossing

/-- Integer-valued digit-sum defect. -/
def defect (N k : ℕ) : ℤ := (digitSum10 (k * N) : ℤ) - k

@[simp] theorem good_iff_defect_eq_zero {N k : ℕ} :
    Good N k ↔ defect N k = 0 := by
  simp [Good, defect]
  omega

/-- Adding a Good period cannot increase the defect. -/
theorem defect_add_period_le {N p k : ℕ} (hp : Good N p) :
    defect N (k + p) ≤ defect N k := by
  have hsNat : digitSum10 ((k + p) * N) ≤ digitSum10 (k * N) + p := by
    have hs := digitSum10_add_le (k * N) (p * N)
    have hp' : digitSum10 (p * N) = p := hp
    have hmul : (k + p) * N = k * N + p * N := by ring
    rw [← hmul] at hs
    simpa [hp'] using hs
  have hsInt :
      (digitSum10 ((k + p) * N) : ℤ) ≤
        (digitSum10 (k * N) : ℤ) + (p : ℤ) := by
    exact_mod_cast hsNat
  unfold defect
  push_cast
  omega

/-- Successive points in a fixed residue class have nonincreasing defect. -/
theorem defect_residue_succ_le {N p r q : ℕ} (hp : Good N p) :
    defect N (p * (q + 1) + r) ≤ defect N (p * q + r) := by
  have h := defect_add_period_le (N := N) (p := p) (k := p * q + r) hp
  convert h using 1 <;> ring

/-- Antitonicity between arbitrary two indices in one residue class. -/
theorem defect_residue_le_of_le {N p r q₁ q₂ : ℕ}
    (hp : Good N p) (hq : q₁ ≤ q₂) :
    defect N (p * q₂ + r) ≤ defect N (p * q₁ + r) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hq
  induction d with
  | zero => simp
  | succ d ih =>
      have hsucc := defect_residue_succ_le (N := N) (p := p) (r := r) (q := q₁ + d) hp
      calc
        defect N (p * (q₁ + (d + 1)) + r)
            ≤ defect N (p * (q₁ + d) + r) := by
                have harg : p * (q₁ + (d + 1)) + r = p * ((q₁ + d) + 1) + r := by ring
                rw [harg]
                exact hsucc
        _ ≤ defect N (p * q₁ + r) := ih (by omega)

/-- An antitone integer sequence with a strict adjacent sign crossing has no zero. -/
theorem no_zero_of_antitone_crossing {f : ℕ → ℤ} {q₀ : ℕ}
    (hanti : ∀ {a b : ℕ}, a ≤ b → f b ≤ f a)
    (hpos : 0 < f q₀) (hneg : f (q₀ + 1) < 0) :
    ∀ q : ℕ, f q ≠ 0 := by
  intro q hzero
  rcases le_total q q₀ with hq | hq
  · have hle : f q₀ ≤ f q := hanti hq
    rw [hzero] at hle
    omega
  · have hq' : q₀ + 1 ≤ q := by
      by_cases hEq : q = q₀
      · subst q
        omega
      · omega
    have hle : f q ≤ f (q₀ + 1) := hanti hq'
    rw [hzero] at hle
    omega

/--
Unique-positive-Good criterion from one crossing in every nonzero residue class.
The zero residue class is killed after `p` by the single inequality
`Delta_N(2p)<0`.
-/
theorem unique_good_of_crossings {N p : ℕ}
    (hp0 : 0 < p)
    (hp : Good N p)
    (hdouble : defect N (2 * p) < 0)
    (hcross : ∀ r : ℕ, 0 < r → r < p →
      ∃ q : ℕ,
        0 < defect N (p * q + r) ∧
        defect N (p * (q + 1) + r) < 0) :
    ∀ k : ℕ, 0 < k → Good N k → k = p := by
  intro k hkpos hgood
  have hzero : defect N k = 0 := good_iff_defect_eq_zero.mp hgood
  let q := k / p
  let r := k % p
  have hrlt : r < p := by
    dsimp [r]
    exact Nat.mod_lt k hp0
  have hkqr : k = p * q + r := by
    dsimp [q, r]
    have hdecomp := Nat.mod_add_div k p
    exact hdecomp.symm.trans (Nat.add_comm _ _)
  by_cases hr0 : r = 0
  · have hkq : k = p * q := by omega
    have hqpos : 0 < q := by
      by_contra hq
      have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
      rw [hq0, Nat.mul_zero] at hkq
      omega
    by_cases hq1 : q = 1
    · simpa [hq1] using hkq
    · have hq2 : 2 ≤ q := by omega
      have hle := defect_residue_le_of_le
        (N := N) (p := p) (r := 0) hp hq2
      have hkdef : defect N (p * q + 0) = 0 := by
        rw [← hkq]
        exact hzero
      rw [hkdef] at hle
      have h2 : defect N (p * 2 + 0) = defect N (2 * p) := by
        congr 1 <;> ring
      rw [h2] at hle
      omega
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    obtain ⟨q₀, hpos, hneg⟩ := hcross r hrpos hrlt
    have hno := no_zero_of_antitone_crossing
      (f := fun t => defect N (p * t + r))
      (q₀ := q₀)
      (hanti := by
        intro a b hab
        exact defect_residue_le_of_le (N := N) (p := p) (r := r) hp hab)
      hpos hneg q
    have hqzero : defect N (p * q + r) = 0 := by
      rw [← hkqr]
      exact hzero
    exact (hno hqzero).elim

/-- Crossing criterion packaged as maximality. -/
theorem maxGood_of_crossings {N p : ℕ}
    (hp0 : 0 < p)
    (hp : Good N p)
    (hdouble : defect N (2 * p) < 0)
    (hcross : ∀ r : ℕ, 0 < r → r < p →
      ∃ q : ℕ,
        0 < defect N (p * q + r) ∧
        defect N (p * (q + 1) + r) < 0) :
    MaxGood N p := by
  apply maxGood_of_unique_positive hp
  intro k hk hgood
  exact unique_good_of_crossings hp0 hp hdouble hcross k hk hgood

end PeriodicCrossing
end A277223

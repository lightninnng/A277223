import A277223.CarryObstruction.Small
import A277223.Witnesses
import A277223.PeriodicCrossing.SevenFamily
import A277223.PeriodicCrossing.ElevenFamily

/-!
# Complete small-value classification for A277223

The theorem is expressed through `MaxGood`, which is definitionally the
largest multiplier characterization used by OEIS A277223.  No global maximum
existence theorem is needed.
-/

namespace A277223

open CarryObstruction
open PeriodicCrossing

/-- If a maximal Good multiplier is below twelve, only 0, 7, 9, or 11 remain. -/
theorem maxGood_lt_twelve_classification {n k : ℕ}
    (hmax : MaxGood n k) (hk12 : k < 12) :
    k = 0 ∨ k = 7 ∨ k = 9 ∨ k = 11 := by
  by_cases h0 : k = 0
  · exact Or.inl h0
  by_cases h7 : k = 7
  · exact Or.inr (Or.inl h7)
  by_cases h9 : k = 9
  · exact Or.inr (Or.inr (Or.inl h9))
  by_cases h11 : k = 11
  · exact Or.inr (Or.inr (Or.inr h11))
  have hforbidden : ForbiddenSmall k := by
    unfold ForbiddenSmall
    interval_cases k <;> simp_all
  exact (forbiddenSmall_not_maxGood hforbidden hmax.1 hmax).elim

/-- All four surviving values are actually realized. -/
theorem small_values_realized :
    (∃ n, MaxGood n 0) ∧
    (∃ n, MaxGood n 7) ∧
    (∃ n, MaxGood n 9) ∧
    (∃ n, MaxGood n 11) := by
  refine ⟨⟨62, sixtyTwo_maxGood_zero⟩, ?_, ⟨1, one_maxGood_nine⟩,
    ⟨N11, N11_maxGood⟩⟩
  exact ⟨N7, N7_maxGood⟩

/-- Exact spectrum below twelve, stated without introducing a choice-based `a(n)`. -/
theorem small_value_spectrum_iff {k : ℕ} :
    (k < 12 ∧ ∃ n, MaxGood n k) ↔
      k = 0 ∨ k = 7 ∨ k = 9 ∨ k = 11 := by
  constructor
  · rintro ⟨hk12, n, hmax⟩
    exact maxGood_lt_twelve_classification hmax hk12
  · intro hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨by norm_num, 62, sixtyTwo_maxGood_zero⟩
    · exact ⟨by norm_num, N7, N7_maxGood⟩
    · exact ⟨by norm_num, 1, one_maxGood_nine⟩
    · exact ⟨by norm_num, N11, N11_maxGood⟩



/-- The two structural terminal values are realized by explicit parameterized families. -/
theorem infinite_family_members_realized (t : ℕ) :
    MaxGood (N7Family t) 7 ∧ MaxGood (N11Family t) 11 :=
  ⟨N7Family_maxGood t, N11Family_maxGood t⟩

/-- Both structural terminal values occur for infinitely many distinct integers. -/
theorem infinitely_many_structural_values :
    Set.Infinite {n : ℕ | MaxGood n 7} ∧
      Set.Infinite {n : ℕ | MaxGood n 11} :=
  ⟨infinitely_many_maxGood_seven, infinitely_many_maxGood_eleven⟩

/-- Trailing decimal zeroes preserve all four realized maximal values. -/
theorem scaled_small_values_realized (t : ℕ) :
    MaxGood (10 ^ t * 62) 0 ∧
    MaxGood (10 ^ t * N7) 7 ∧
    MaxGood (10 ^ t) 9 ∧
    MaxGood (10 ^ t * N11) 11 := by
  refine ⟨(maxGood_pow_mul_iff t 62 0).2 sixtyTwo_maxGood_zero, ?_, ?_, ?_⟩
  · exact (maxGood_pow_mul_iff t N7 7).2 N7_maxGood
  · simpa using (maxGood_pow_mul_iff t 1 9).2 one_maxGood_nine
  · exact (maxGood_pow_mul_iff t N11 11).2 N11_maxGood

end A277223

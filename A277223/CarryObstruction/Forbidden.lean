import A277223.CarryObstruction.Theory
import A277223.CarryObstruction.Eight
import A277223.CarryObstruction.Ten

/-!
# Unified exclusion of the forbidden small maximal values

This is the formal interface of the Carry-Obstruction module.  The elementary
values `1,...,6` are proved structurally in `Theory.lean`; `8` and `10` use the
proof-carrying exact digit-mass certificates generated from the same local
carry witnesses.
-/

namespace A277223
namespace CarryObstruction

/-- Carry obstruction for eight, re-exported from the certificate namespace. -/
theorem carryObstruction_eight : CarryObstruction 8 :=
  Certificate.carryObstruction_eight

/-- Carry obstruction for ten, re-exported from the certificate namespace. -/
theorem carryObstruction_ten : CarryObstruction 10 :=
  Certificate.carryObstruction_ten

/-- Exactly the small values excluded by Carry Obstruction. -/
def ForbiddenSmall (k : ℕ) : Prop :=
  k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 8 ∨ k = 10

/-- Every forbidden small target satisfies the abstract carry-obstruction property. -/
theorem carryObstruction_of_forbiddenSmall {k : ℕ} (hk : ForbiddenSmall k) :
    CarryObstruction k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact carryObstruction_of_pos_le_four (by norm_num) (by norm_num)
  · exact carryObstruction_of_pos_le_four (by norm_num) (by norm_num)
  · exact carryObstruction_of_pos_le_four (by norm_num) (by norm_num)
  · exact carryObstruction_of_pos_le_four (by norm_num) (by norm_num)
  · exact carryObstruction_five
  · exact carryObstruction_six
  · exact carryObstruction_eight
  · exact carryObstruction_ten

/-- A forbidden small Good multiplier can never be maximal. -/
theorem forbiddenSmall_not_maxGood {n k : ℕ}
    (hk : ForbiddenSmall k) (hgood : Good n k) : ¬ MaxGood n k :=
  not_maxGood_of_carryObstruction (carryObstruction_of_forbiddenSmall hk) hgood

end CarryObstruction
end A277223

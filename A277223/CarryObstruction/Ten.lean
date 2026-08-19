import A277223.CarryObstruction.TenData

/-!
Validity proof for the generated carry certificate of target `10`.
The packed data lives in `TenData.lean`; each bounded index range
is discharged by its own `decide +kernel`, and
`Certificate.valid_of_rangeOK` reassembles complete validity.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_chunk_0 : rangeOK 10 cert10 0 1024 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_chunk_1 : rangeOK 10 cert10 1024 1543 = true := by
  decide +kernel

theorem cert10_size : cert10.total = 1543 := by
  rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_header : cert10.initial < cert10.total ∧
    stateAt cert10 cert10.initial = initialState cert10.specs := by
  decide +kernel

theorem cert10_valid : cert10.Valid 10 := by
  refine valid_of_rangeOK cert10_header.1 cert10_header.2 ?_
  intro i hi
  rw [cert10_size] at hi
  by_cases h0 : i < 1024
  · exact ⟨0, 1024, by omega, by omega, cert10_chunk_0⟩
  · exact ⟨1024, 1543, by omega, by omega, cert10_chunk_1⟩
theorem carryObstruction_ten : CarryObstruction 10 :=
  carryObstruction_of_valid_certificate cert10_valid

end Certificate
end CarryObstruction
end A277223

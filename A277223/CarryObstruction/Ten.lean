import A277223.CarryObstruction.TenData

/-!
Validity proof for the generated carry certificate of target `10`.
The data lives in `TenData.lean`; each bounded index range is
discharged by its own `decide +kernel` (a whole-table single decide
does not fit in the memory of a 16 GB build host), and
`Certificate.valid_of_rangeOK` reassembles complete validity.
Final range part; earlier parts live in .
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_chunk_0 : rangeOK 10 cert10 0 512 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_chunk_1 : rangeOK 10 cert10 512 1024 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_chunk_2 : rangeOK 10 cert10 1024 1536 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_chunk_3 : rangeOK 10 cert10 1536 1543 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_size : cert10.states.size = 1543 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_header : cert10.next.size = 10 * cert10.states.size ∧
    cert10.initial < cert10.states.size ∧
    stateAt cert10 cert10.initial = initialState cert10.specs := by
  decide +kernel

theorem cert10_valid : cert10.Valid 10 := by
  refine valid_of_rangeOK cert10_header.1 cert10_header.2.1 cert10_header.2.2 ?_
  intro i hi
  rw [cert10_size] at hi
  by_cases h0 : i < 512
  · exact ⟨0, 512, by omega, by omega, cert10_chunk_0⟩
  by_cases h1 : i < 1024
  · exact ⟨512, 1024, by omega, by omega, cert10_chunk_1⟩
  by_cases h2 : i < 1536
  · exact ⟨1024, 1536, by omega, by omega, cert10_chunk_2⟩
  · exact ⟨1536, 1543, by omega, by omega, cert10_chunk_3⟩
theorem carryObstruction_ten : CarryObstruction 10 :=
  carryObstruction_of_valid_certificate cert10_valid

end Certificate
end CarryObstruction
end A277223

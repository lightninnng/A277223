import A277223.CarryObstruction.EightData

/-!
Validity proof for the generated carry certificate of target `8`.
The packed data lives in `EightData.lean`; each bounded index range
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
theorem cert8_chunk_0 : rangeOK 8 cert8 0 1024 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_1 : rangeOK 8 cert8 1024 2048 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_2 : rangeOK 8 cert8 2048 3072 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_3 : rangeOK 8 cert8 3072 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_4 : rangeOK 8 cert8 4096 5120 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_5 : rangeOK 8 cert8 5120 6144 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_6 : rangeOK 8 cert8 6144 7168 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_7 : rangeOK 8 cert8 7168 7608 = true := by
  decide +kernel

theorem cert8_size : cert8.total = 7608 := by
  rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_header : cert8.initial < cert8.total ∧
    stateAt cert8 cert8.initial = initialState cert8.specs := by
  decide +kernel

theorem cert8_valid : cert8.Valid 8 := by
  refine valid_of_rangeOK cert8_header.1 cert8_header.2 ?_
  intro i hi
  rw [cert8_size] at hi
  by_cases h0 : i < 1024
  · exact ⟨0, 1024, by omega, by omega, cert8_chunk_0⟩
  by_cases h1 : i < 2048
  · exact ⟨1024, 2048, by omega, by omega, cert8_chunk_1⟩
  by_cases h2 : i < 3072
  · exact ⟨2048, 3072, by omega, by omega, cert8_chunk_2⟩
  by_cases h3 : i < 4096
  · exact ⟨3072, 4096, by omega, by omega, cert8_chunk_3⟩
  by_cases h4 : i < 5120
  · exact ⟨4096, 5120, by omega, by omega, cert8_chunk_4⟩
  by_cases h5 : i < 6144
  · exact ⟨5120, 6144, by omega, by omega, cert8_chunk_5⟩
  by_cases h6 : i < 7168
  · exact ⟨6144, 7168, by omega, by omega, cert8_chunk_6⟩
  · exact ⟨7168, 7608, by omega, by omega, cert8_chunk_7⟩
theorem carryObstruction_eight : CarryObstruction 8 :=
  carryObstruction_of_valid_certificate cert8_valid

end Certificate
end CarryObstruction
end A277223

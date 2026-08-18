import A277223.CarryObstruction.EightB

/-!
Validity proof for the generated carry certificate of target `8`.
The data lives in `EightData.lean`; each bounded index range is
discharged by its own `decide +kernel` (a whole-table single decide
does not fit in the memory of a 16 GB build host), and
`Certificate.valid_of_rangeOK` reassembles complete validity.
Final range part; earlier parts live in EightA, EightB.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_10 : rangeOK 8 cert8 5120 5632 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_11 : rangeOK 8 cert8 5632 6144 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_12 : rangeOK 8 cert8 6144 6656 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_13 : rangeOK 8 cert8 6656 7168 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_14 : rangeOK 8 cert8 7168 7608 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_size : cert8.states.size = 7608 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_header : cert8.next.size = 10 * cert8.states.size ∧
    cert8.initial < cert8.states.size ∧
    stateAt cert8 cert8.initial = initialState cert8.specs := by
  decide +kernel

theorem cert8_valid : cert8.Valid 8 := by
  refine valid_of_rangeOK cert8_header.1 cert8_header.2.1 cert8_header.2.2 ?_
  intro i hi
  rw [cert8_size] at hi
  by_cases h0 : i < 512
  · exact ⟨0, 512, by omega, by omega, cert8_chunk_0⟩
  by_cases h1 : i < 1024
  · exact ⟨512, 1024, by omega, by omega, cert8_chunk_1⟩
  by_cases h2 : i < 1536
  · exact ⟨1024, 1536, by omega, by omega, cert8_chunk_2⟩
  by_cases h3 : i < 2048
  · exact ⟨1536, 2048, by omega, by omega, cert8_chunk_3⟩
  by_cases h4 : i < 2560
  · exact ⟨2048, 2560, by omega, by omega, cert8_chunk_4⟩
  by_cases h5 : i < 3072
  · exact ⟨2560, 3072, by omega, by omega, cert8_chunk_5⟩
  by_cases h6 : i < 3584
  · exact ⟨3072, 3584, by omega, by omega, cert8_chunk_6⟩
  by_cases h7 : i < 4096
  · exact ⟨3584, 4096, by omega, by omega, cert8_chunk_7⟩
  by_cases h8 : i < 4608
  · exact ⟨4096, 4608, by omega, by omega, cert8_chunk_8⟩
  by_cases h9 : i < 5120
  · exact ⟨4608, 5120, by omega, by omega, cert8_chunk_9⟩
  by_cases h10 : i < 5632
  · exact ⟨5120, 5632, by omega, by omega, cert8_chunk_10⟩
  by_cases h11 : i < 6144
  · exact ⟨5632, 6144, by omega, by omega, cert8_chunk_11⟩
  by_cases h12 : i < 6656
  · exact ⟨6144, 6656, by omega, by omega, cert8_chunk_12⟩
  by_cases h13 : i < 7168
  · exact ⟨6656, 7168, by omega, by omega, cert8_chunk_13⟩
  · exact ⟨7168, 7608, by omega, by omega, cert8_chunk_14⟩
theorem carryObstruction_eight : CarryObstruction 8 :=
  carryObstruction_of_valid_certificate cert8_valid

end Certificate
end CarryObstruction
end A277223

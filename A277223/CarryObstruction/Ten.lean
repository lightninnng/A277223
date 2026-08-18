import A277223.CarryObstruction.TenA

/-!
Validity proof for the generated carry certificate of target `10`.
The data lives in `TenData.lean`; each bounded index range is
discharged by its own `decide +kernel` (a whole-table single decide
does not fit in the memory of a 16 GB build host), and
`Certificate.valid_of_rangeOK` reassembles complete validity.
Final range part; earlier parts live in TenA.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_chunk_10 : rangeOK 10 cert10 1280 1408 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_chunk_11 : rangeOK 10 cert10 1408 1536 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_chunk_12 : rangeOK 10 cert10 1536 1543 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_size : cert10.states.size = 1543 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert10_header : cert10.next.size = cert10.states.size ∧
    cert10.initial < cert10.states.size ∧
    stateAt cert10 cert10.initial = initialState cert10.specs := by
  decide +kernel

theorem cert10_valid : cert10.Valid 10 := by
  refine valid_of_rangeOK cert10_header.1 cert10_header.2.1 cert10_header.2.2 ?_
  intro i hi
  rw [cert10_size] at hi
  by_cases h0 : i < 128
  · exact ⟨0, 128, by omega, by omega, cert10_chunk_0⟩
  by_cases h1 : i < 256
  · exact ⟨128, 256, by omega, by omega, cert10_chunk_1⟩
  by_cases h2 : i < 384
  · exact ⟨256, 384, by omega, by omega, cert10_chunk_2⟩
  by_cases h3 : i < 512
  · exact ⟨384, 512, by omega, by omega, cert10_chunk_3⟩
  by_cases h4 : i < 640
  · exact ⟨512, 640, by omega, by omega, cert10_chunk_4⟩
  by_cases h5 : i < 768
  · exact ⟨640, 768, by omega, by omega, cert10_chunk_5⟩
  by_cases h6 : i < 896
  · exact ⟨768, 896, by omega, by omega, cert10_chunk_6⟩
  by_cases h7 : i < 1024
  · exact ⟨896, 1024, by omega, by omega, cert10_chunk_7⟩
  by_cases h8 : i < 1152
  · exact ⟨1024, 1152, by omega, by omega, cert10_chunk_8⟩
  by_cases h9 : i < 1280
  · exact ⟨1152, 1280, by omega, by omega, cert10_chunk_9⟩
  by_cases h10 : i < 1408
  · exact ⟨1280, 1408, by omega, by omega, cert10_chunk_10⟩
  by_cases h11 : i < 1536
  · exact ⟨1408, 1536, by omega, by omega, cert10_chunk_11⟩
  · exact ⟨1536, 1543, by omega, by omega, cert10_chunk_12⟩
theorem carryObstruction_ten : CarryObstruction 10 :=
  carryObstruction_of_valid_certificate cert10_valid

end Certificate
end CarryObstruction
end A277223

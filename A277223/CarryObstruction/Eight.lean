import A277223.CarryObstruction.EightE

/-!
Validity proof for the generated carry certificate of target `8`.
The data lives in `EightData.lean`; each bounded index range is
discharged by its own `decide +kernel` (a whole-table single decide
does not fit in the memory of a 16 GB build host), and
`Certificate.valid_of_rangeOK` reassembles complete validity.
Final range part; earlier parts live in EightA, EightB, EightC, EightD, EightE.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_50 : rangeOK 8 cert8 6400 6528 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_51 : rangeOK 8 cert8 6528 6656 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_52 : rangeOK 8 cert8 6656 6784 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_53 : rangeOK 8 cert8 6784 6912 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_54 : rangeOK 8 cert8 6912 7040 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_55 : rangeOK 8 cert8 7040 7168 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_56 : rangeOK 8 cert8 7168 7296 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_57 : rangeOK 8 cert8 7296 7424 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_58 : rangeOK 8 cert8 7424 7552 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_59 : rangeOK 8 cert8 7552 7608 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_size : cert8.states.size = 7608 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_header : cert8.next.size = cert8.states.size ∧
    cert8.initial < cert8.states.size ∧
    stateAt cert8 cert8.initial = initialState cert8.specs := by
  decide +kernel

theorem cert8_valid : cert8.Valid 8 := by
  refine valid_of_rangeOK cert8_header.1 cert8_header.2.1 cert8_header.2.2 ?_
  intro i hi
  rw [cert8_size] at hi
  by_cases h0 : i < 128
  · exact ⟨0, 128, by omega, by omega, cert8_chunk_0⟩
  by_cases h1 : i < 256
  · exact ⟨128, 256, by omega, by omega, cert8_chunk_1⟩
  by_cases h2 : i < 384
  · exact ⟨256, 384, by omega, by omega, cert8_chunk_2⟩
  by_cases h3 : i < 512
  · exact ⟨384, 512, by omega, by omega, cert8_chunk_3⟩
  by_cases h4 : i < 640
  · exact ⟨512, 640, by omega, by omega, cert8_chunk_4⟩
  by_cases h5 : i < 768
  · exact ⟨640, 768, by omega, by omega, cert8_chunk_5⟩
  by_cases h6 : i < 896
  · exact ⟨768, 896, by omega, by omega, cert8_chunk_6⟩
  by_cases h7 : i < 1024
  · exact ⟨896, 1024, by omega, by omega, cert8_chunk_7⟩
  by_cases h8 : i < 1152
  · exact ⟨1024, 1152, by omega, by omega, cert8_chunk_8⟩
  by_cases h9 : i < 1280
  · exact ⟨1152, 1280, by omega, by omega, cert8_chunk_9⟩
  by_cases h10 : i < 1408
  · exact ⟨1280, 1408, by omega, by omega, cert8_chunk_10⟩
  by_cases h11 : i < 1536
  · exact ⟨1408, 1536, by omega, by omega, cert8_chunk_11⟩
  by_cases h12 : i < 1664
  · exact ⟨1536, 1664, by omega, by omega, cert8_chunk_12⟩
  by_cases h13 : i < 1792
  · exact ⟨1664, 1792, by omega, by omega, cert8_chunk_13⟩
  by_cases h14 : i < 1920
  · exact ⟨1792, 1920, by omega, by omega, cert8_chunk_14⟩
  by_cases h15 : i < 2048
  · exact ⟨1920, 2048, by omega, by omega, cert8_chunk_15⟩
  by_cases h16 : i < 2176
  · exact ⟨2048, 2176, by omega, by omega, cert8_chunk_16⟩
  by_cases h17 : i < 2304
  · exact ⟨2176, 2304, by omega, by omega, cert8_chunk_17⟩
  by_cases h18 : i < 2432
  · exact ⟨2304, 2432, by omega, by omega, cert8_chunk_18⟩
  by_cases h19 : i < 2560
  · exact ⟨2432, 2560, by omega, by omega, cert8_chunk_19⟩
  by_cases h20 : i < 2688
  · exact ⟨2560, 2688, by omega, by omega, cert8_chunk_20⟩
  by_cases h21 : i < 2816
  · exact ⟨2688, 2816, by omega, by omega, cert8_chunk_21⟩
  by_cases h22 : i < 2944
  · exact ⟨2816, 2944, by omega, by omega, cert8_chunk_22⟩
  by_cases h23 : i < 3072
  · exact ⟨2944, 3072, by omega, by omega, cert8_chunk_23⟩
  by_cases h24 : i < 3200
  · exact ⟨3072, 3200, by omega, by omega, cert8_chunk_24⟩
  by_cases h25 : i < 3328
  · exact ⟨3200, 3328, by omega, by omega, cert8_chunk_25⟩
  by_cases h26 : i < 3456
  · exact ⟨3328, 3456, by omega, by omega, cert8_chunk_26⟩
  by_cases h27 : i < 3584
  · exact ⟨3456, 3584, by omega, by omega, cert8_chunk_27⟩
  by_cases h28 : i < 3712
  · exact ⟨3584, 3712, by omega, by omega, cert8_chunk_28⟩
  by_cases h29 : i < 3840
  · exact ⟨3712, 3840, by omega, by omega, cert8_chunk_29⟩
  by_cases h30 : i < 3968
  · exact ⟨3840, 3968, by omega, by omega, cert8_chunk_30⟩
  by_cases h31 : i < 4096
  · exact ⟨3968, 4096, by omega, by omega, cert8_chunk_31⟩
  by_cases h32 : i < 4224
  · exact ⟨4096, 4224, by omega, by omega, cert8_chunk_32⟩
  by_cases h33 : i < 4352
  · exact ⟨4224, 4352, by omega, by omega, cert8_chunk_33⟩
  by_cases h34 : i < 4480
  · exact ⟨4352, 4480, by omega, by omega, cert8_chunk_34⟩
  by_cases h35 : i < 4608
  · exact ⟨4480, 4608, by omega, by omega, cert8_chunk_35⟩
  by_cases h36 : i < 4736
  · exact ⟨4608, 4736, by omega, by omega, cert8_chunk_36⟩
  by_cases h37 : i < 4864
  · exact ⟨4736, 4864, by omega, by omega, cert8_chunk_37⟩
  by_cases h38 : i < 4992
  · exact ⟨4864, 4992, by omega, by omega, cert8_chunk_38⟩
  by_cases h39 : i < 5120
  · exact ⟨4992, 5120, by omega, by omega, cert8_chunk_39⟩
  by_cases h40 : i < 5248
  · exact ⟨5120, 5248, by omega, by omega, cert8_chunk_40⟩
  by_cases h41 : i < 5376
  · exact ⟨5248, 5376, by omega, by omega, cert8_chunk_41⟩
  by_cases h42 : i < 5504
  · exact ⟨5376, 5504, by omega, by omega, cert8_chunk_42⟩
  by_cases h43 : i < 5632
  · exact ⟨5504, 5632, by omega, by omega, cert8_chunk_43⟩
  by_cases h44 : i < 5760
  · exact ⟨5632, 5760, by omega, by omega, cert8_chunk_44⟩
  by_cases h45 : i < 5888
  · exact ⟨5760, 5888, by omega, by omega, cert8_chunk_45⟩
  by_cases h46 : i < 6016
  · exact ⟨5888, 6016, by omega, by omega, cert8_chunk_46⟩
  by_cases h47 : i < 6144
  · exact ⟨6016, 6144, by omega, by omega, cert8_chunk_47⟩
  by_cases h48 : i < 6272
  · exact ⟨6144, 6272, by omega, by omega, cert8_chunk_48⟩
  by_cases h49 : i < 6400
  · exact ⟨6272, 6400, by omega, by omega, cert8_chunk_49⟩
  by_cases h50 : i < 6528
  · exact ⟨6400, 6528, by omega, by omega, cert8_chunk_50⟩
  by_cases h51 : i < 6656
  · exact ⟨6528, 6656, by omega, by omega, cert8_chunk_51⟩
  by_cases h52 : i < 6784
  · exact ⟨6656, 6784, by omega, by omega, cert8_chunk_52⟩
  by_cases h53 : i < 6912
  · exact ⟨6784, 6912, by omega, by omega, cert8_chunk_53⟩
  by_cases h54 : i < 7040
  · exact ⟨6912, 7040, by omega, by omega, cert8_chunk_54⟩
  by_cases h55 : i < 7168
  · exact ⟨7040, 7168, by omega, by omega, cert8_chunk_55⟩
  by_cases h56 : i < 7296
  · exact ⟨7168, 7296, by omega, by omega, cert8_chunk_56⟩
  by_cases h57 : i < 7424
  · exact ⟨7296, 7424, by omega, by omega, cert8_chunk_57⟩
  by_cases h58 : i < 7552
  · exact ⟨7424, 7552, by omega, by omega, cert8_chunk_58⟩
  · exact ⟨7552, 7608, by omega, by omega, cert8_chunk_59⟩
theorem carryObstruction_eight : CarryObstruction 8 :=
  carryObstruction_of_valid_certificate cert8_valid

end Certificate
end CarryObstruction
end A277223

import A277223.CarryObstruction.EightData

/-!
Range checks 0..2560 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_0 : rangeOK 8 cert8 0 512 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_1 : rangeOK 8 cert8 512 1024 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_2 : rangeOK 8 cert8 1024 1536 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_3 : rangeOK 8 cert8 1536 2048 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_4 : rangeOK 8 cert8 2048 2560 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

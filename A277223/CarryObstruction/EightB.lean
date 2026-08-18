import A277223.CarryObstruction.EightA

/-!
Range checks 2560..5120 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_5 : rangeOK 8 cert8 2560 3072 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_6 : rangeOK 8 cert8 3072 3584 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_7 : rangeOK 8 cert8 3584 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_8 : rangeOK 8 cert8 4096 4608 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_9 : rangeOK 8 cert8 4608 5120 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

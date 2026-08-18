import A277223.CarryObstruction.EightP07

/-!
Range checks 2048..2304 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_16 : rangeOK 8 cert8 2048 2176 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_17 : rangeOK 8 cert8 2176 2304 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

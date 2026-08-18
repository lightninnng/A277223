import A277223.CarryObstruction.EightP04

/-!
Range checks 1280..1536 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_10 : rangeOK 8 cert8 1280 1408 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_11 : rangeOK 8 cert8 1408 1536 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

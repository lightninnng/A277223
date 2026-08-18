import A277223.CarryObstruction.EightP03

/-!
Range checks 1024..1280 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_8 : rangeOK 8 cert8 1024 1152 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_9 : rangeOK 8 cert8 1152 1280 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

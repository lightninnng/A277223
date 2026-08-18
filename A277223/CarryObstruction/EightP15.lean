import A277223.CarryObstruction.EightP14

/-!
Range checks 3840..4096 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_30 : rangeOK 8 cert8 3840 3968 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_31 : rangeOK 8 cert8 3968 4096 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

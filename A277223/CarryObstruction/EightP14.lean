import A277223.CarryObstruction.EightP13

/-!
Range checks 3584..3840 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_28 : rangeOK 8 cert8 3584 3712 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_29 : rangeOK 8 cert8 3712 3840 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

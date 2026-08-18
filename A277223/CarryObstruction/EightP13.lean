import A277223.CarryObstruction.EightP12

/-!
Range checks 3328..3584 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_26 : rangeOK 8 cert8 3328 3456 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_27 : rangeOK 8 cert8 3456 3584 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

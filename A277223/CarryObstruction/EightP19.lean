import A277223.CarryObstruction.EightP18

/-!
Range checks 4864..5120 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_38 : rangeOK 8 cert8 4864 4992 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_39 : rangeOK 8 cert8 4992 5120 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

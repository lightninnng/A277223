import A277223.CarryObstruction.EightP06

/-!
Range checks 1792..2048 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_14 : rangeOK 8 cert8 1792 1920 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_15 : rangeOK 8 cert8 1920 2048 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

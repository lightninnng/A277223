import A277223.CarryObstruction.EightP01

/-!
Range checks 512..768 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_4 : rangeOK 8 cert8 512 640 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_5 : rangeOK 8 cert8 640 768 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

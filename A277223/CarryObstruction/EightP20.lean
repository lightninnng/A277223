import A277223.CarryObstruction.EightP19

/-!
Range checks 5120..5376 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_40 : rangeOK 8 cert8 5120 5248 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_41 : rangeOK 8 cert8 5248 5376 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

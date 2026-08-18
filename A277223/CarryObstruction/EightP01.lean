import A277223.CarryObstruction.EightP00

/-!
Range checks 256..512 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_2 : rangeOK 8 cert8 256 384 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_3 : rangeOK 8 cert8 384 512 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

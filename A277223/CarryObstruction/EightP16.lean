import A277223.CarryObstruction.EightP15

/-!
Range checks 4096..4352 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_32 : rangeOK 8 cert8 4096 4224 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_33 : rangeOK 8 cert8 4224 4352 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

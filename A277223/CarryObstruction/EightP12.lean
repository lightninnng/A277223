import A277223.CarryObstruction.EightP11

/-!
Range checks 3072..3328 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_24 : rangeOK 8 cert8 3072 3200 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_25 : rangeOK 8 cert8 3200 3328 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

import A277223.CarryObstruction.EightP16

/-!
Range checks 4352..4608 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_34 : rangeOK 8 cert8 4352 4480 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_35 : rangeOK 8 cert8 4480 4608 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

import A277223.CarryObstruction.EightP17

/-!
Range checks 4608..4864 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_36 : rangeOK 8 cert8 4608 4736 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_37 : rangeOK 8 cert8 4736 4864 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

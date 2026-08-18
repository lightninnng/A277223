import A277223.CarryObstruction.EightP09

/-!
Range checks 2560..2816 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_20 : rangeOK 8 cert8 2560 2688 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_21 : rangeOK 8 cert8 2688 2816 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

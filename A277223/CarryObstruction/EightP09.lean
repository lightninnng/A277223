import A277223.CarryObstruction.EightP08

/-!
Range checks 2304..2560 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_18 : rangeOK 8 cert8 2304 2432 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_19 : rangeOK 8 cert8 2432 2560 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

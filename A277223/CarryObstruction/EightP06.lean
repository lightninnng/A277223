import A277223.CarryObstruction.EightP05

/-!
Range checks 1536..1792 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_12 : rangeOK 8 cert8 1536 1664 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_13 : rangeOK 8 cert8 1664 1792 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

import A277223.CarryObstruction.EightP10

/-!
Range checks 2816..3072 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_22 : rangeOK 8 cert8 2816 2944 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_23 : rangeOK 8 cert8 2944 3072 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

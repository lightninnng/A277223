import A277223.CarryObstruction.EightP27

/-!
Range checks 7168..7424 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_56 : rangeOK 8 cert8 7168 7296 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_57 : rangeOK 8 cert8 7296 7424 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

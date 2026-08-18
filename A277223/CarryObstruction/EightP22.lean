import A277223.CarryObstruction.EightP21

/-!
Range checks 5632..5888 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_44 : rangeOK 8 cert8 5632 5760 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_45 : rangeOK 8 cert8 5760 5888 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

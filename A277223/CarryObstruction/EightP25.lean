import A277223.CarryObstruction.EightP24

/-!
Range checks 6400..6656 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_50 : rangeOK 8 cert8 6400 6528 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_51 : rangeOK 8 cert8 6528 6656 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

import A277223.CarryObstruction.EightP23

/-!
Range checks 6144..6400 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_48 : rangeOK 8 cert8 6144 6272 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_49 : rangeOK 8 cert8 6272 6400 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

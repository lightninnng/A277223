import A277223.CarryObstruction.EightP22

/-!
Range checks 5888..6144 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_46 : rangeOK 8 cert8 5888 6016 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_47 : rangeOK 8 cert8 6016 6144 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

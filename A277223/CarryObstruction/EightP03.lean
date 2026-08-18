import A277223.CarryObstruction.EightP02

/-!
Range checks 768..1024 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_6 : rangeOK 8 cert8 768 896 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_7 : rangeOK 8 cert8 896 1024 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

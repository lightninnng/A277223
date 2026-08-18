import A277223.CarryObstruction.EightP20

/-!
Range checks 5376..5632 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_42 : rangeOK 8 cert8 5376 5504 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_43 : rangeOK 8 cert8 5504 5632 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

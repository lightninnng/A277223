import A277223.CarryObstruction.EightP25

/-!
Range checks 6656..6912 of the generated carry
certificate for target `8`, split out to bound process memory.
-/

namespace A277223
namespace CarryObstruction
namespace Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_52 : rangeOK 8 cert8 6656 6784 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem cert8_chunk_53 : rangeOK 8 cert8 6784 6912 = true := by
  decide +kernel

end Certificate
end CarryObstruction
end A277223

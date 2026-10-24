import FiniteExclusionThirtyNineHamiltonianBase
set_option maxRecDepth 65536
set_option maxHeartbeats 200000000
namespace Delivery.FiniteExclusion.Thirty9Minimum
open RotationBounds Extremal
def piece_8_5_data : Tree :=
.minimum

theorem piece_8_5 : UpperPrefix a [8,5] 30 :=
  sound a [8,5] 30 piece_8_5_data (by decide +kernel)

end Delivery.FiniteExclusion.Thirty9Minimum

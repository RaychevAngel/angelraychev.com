import FiniteExclusionThirtyNineHamiltonianBase
set_option maxRecDepth 65536
set_option maxHeartbeats 200000000
namespace Delivery.FiniteExclusion.Thirty9Minimum
open RotationBounds Extremal
def piece_5_3_data : Tree :=
.minimum

theorem piece_5_3 : UpperPrefix a [5,3] 30 :=
  sound a [5,3] 30 piece_5_3_data (by decide +kernel)

end Delivery.FiniteExclusion.Thirty9Minimum

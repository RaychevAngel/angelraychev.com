import FiniteExclusionThirtyNineHamiltonianBase
set_option maxRecDepth 65536
set_option maxHeartbeats 200000000
namespace Delivery.FiniteExclusion.Thirty9Minimum
open RotationBounds Extremal
def piece_4_3_data : Tree :=
.minimum

theorem piece_4_3 : UpperPrefix a [4,3] 30 :=
  sound a [4,3] 30 piece_4_3_data (by decide +kernel)

end Delivery.FiniteExclusion.Thirty9Minimum

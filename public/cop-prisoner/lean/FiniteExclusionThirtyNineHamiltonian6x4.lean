import FiniteExclusionThirtyNineHamiltonianBase
set_option maxRecDepth 65536
set_option maxHeartbeats 200000000
namespace Delivery.FiniteExclusion.Thirty9Minimum
open RotationBounds Extremal
def piece_6_4_data : Tree :=
.minimum

theorem piece_6_4 : UpperPrefix a [6,4] 30 :=
  sound a [6,4] 30 piece_6_4_data (by decide +kernel)

end Delivery.FiniteExclusion.Thirty9Minimum

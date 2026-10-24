import FiniteExclusionThirtyNineHamiltonianBase
set_option maxRecDepth 65536
set_option maxHeartbeats 200000000
namespace Delivery.FiniteExclusion.Thirty9Minimum
open RotationBounds Extremal
def piece_7_6_data : Tree :=
.minimum

theorem piece_7_6 : UpperPrefix a [7,6] 30 :=
  sound a [7,6] 30 piece_7_6_data (by decide +kernel)

end Delivery.FiniteExclusion.Thirty9Minimum

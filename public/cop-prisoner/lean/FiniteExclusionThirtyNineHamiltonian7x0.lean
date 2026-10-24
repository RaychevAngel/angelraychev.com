import FiniteExclusionThirtyNineHamiltonianBase
set_option maxRecDepth 65536
set_option maxHeartbeats 200000000
namespace Delivery.FiniteExclusion.Thirty9Minimum
open RotationBounds Extremal
def piece_7_0_1_2_data : Tree :=
(.branch fun v => match v.val with
  | 3 => (.branch fun v => match v.val with
  | 4 => (.leaf ⟨⟨352,480,480,480,448,384,288,96,224⟩,[],[(1,2,1),(2,3,2),(3,4,3),(4,5,4)],⟨131,7,14,28,56,112,480,480,353⟩,⟨131,7,14,28,56,112,192,384,257⟩,[⟨0,1212475681878726955238400,⟨254,62,30,28,56,112,240,504,508⟩⟩]⟩)
  | 8 => .minimum
  | _ => .invalid)
  | 6 => .minimum
  | 8 => .minimum
  | _ => .invalid)

theorem piece_7_0_1_2 : UpperPrefix a [7,0,1,2] 30 :=
  sound a [7,0,1,2] 30 piece_7_0_1_2_data (by decide +kernel)

def piece_7_0_1_5_data : Tree :=
.minimum

theorem piece_7_0_1_5 : UpperPrefix a [7,0,1,5] 30 :=
  sound a [7,0,1,5] 30 piece_7_0_1_5_data (by decide +kernel)

def piece_7_0_1_6_data : Tree :=
.minimum

theorem piece_7_0_1_6 : UpperPrefix a [7,0,1,6] 30 :=
  sound a [7,0,1,6] 30 piece_7_0_1_6_data (by decide +kernel)

def piece_7_0_1_8_data : Tree :=
.minimum

theorem piece_7_0_1_8 : UpperPrefix a [7,0,1,8] 30 :=
  sound a [7,0,1,8] 30 piece_7_0_1_8_data (by decide +kernel)

def piece_7_0_4_data : Tree :=
.minimum

theorem piece_7_0_4 : UpperPrefix a [7,0,4] 30 :=
  sound a [7,0,4] 30 piece_7_0_4_data (by decide +kernel)

def piece_7_0_5_data : Tree :=
.minimum

theorem piece_7_0_5 : UpperPrefix a [7,0,5] 30 :=
  sound a [7,0,5] 30 piece_7_0_5_data (by decide +kernel)

def piece_7_0_6_data : Tree :=
.minimum

theorem piece_7_0_6 : UpperPrefix a [7,0,6] 30 :=
  sound a [7,0,6] 30 piece_7_0_6_data (by decide +kernel)

def piece_7_0_8_data : Tree :=
.minimum

theorem piece_7_0_8 : UpperPrefix a [7,0,8] 30 :=
  sound a [7,0,8] 30 piece_7_0_8_data (by decide +kernel)

theorem piece_7_0_1 : UpperPrefix a [7,0,1] 30 :=
  branch_upper a [7,0,1] 30 (by decide) (fin9_cases _
    (invalid_upper a [7,0,1,0] 30 (by decide +kernel))
    (invalid_upper a [7,0,1,1] 30 (by decide +kernel))
    piece_7_0_1_2
    (invalid_upper a [7,0,1,3] 30 (by decide +kernel))
    (invalid_upper a [7,0,1,4] 30 (by decide +kernel))
    piece_7_0_1_5
    piece_7_0_1_6
    (invalid_upper a [7,0,1,7] 30 (by decide +kernel))
    piece_7_0_1_8)

theorem piece_7_0 : UpperPrefix a [7,0] 30 :=
  branch_upper a [7,0] 30 (by decide) (fin9_cases _
    (invalid_upper a [7,0,0] 30 (by decide +kernel))
    piece_7_0_1
    (invalid_upper a [7,0,2] 30 (by decide +kernel))
    (invalid_upper a [7,0,3] 30 (by decide +kernel))
    piece_7_0_4
    piece_7_0_5
    piece_7_0_6
    (invalid_upper a [7,0,7] 30 (by decide +kernel))
    piece_7_0_8)

end Delivery.FiniteExclusion.Thirty9Minimum

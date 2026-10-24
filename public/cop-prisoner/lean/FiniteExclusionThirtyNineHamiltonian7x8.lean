import FiniteExclusionThirtyNineHamiltonianBase
set_option maxRecDepth 65536
set_option maxHeartbeats 200000000
namespace Delivery.FiniteExclusion.Thirty9Minimum
open RotationBounds Extremal
def piece_7_8_0_1_data : Tree :=
(.branch fun v => match v.val with
  | 2 => (.branch fun v => match v.val with
  | 3 => (.branch fun v => match v.val with
  | 4 => (.camp ⟨⟨352,225,226,228,200,144,32,96,224⟩,[],[(8,1,0),(0,2,1),(1,3,2),(2,4,3),(3,5,4),(4,6,5)]⟩)
  | 5 => (.branch fun v => match v.val with
  | 4 => .minimum
  | 6 => (.camp ⟨⟨304,177,178,164,136,144,16,48,176⟩,[],[(8,1,0),(0,2,1),(1,3,2),(2,4,3),(3,5,4),(6,7,6)]⟩)
  | _ => .invalid)
  | _ => .invalid)
  | 4 => (.branch fun v => match v.val with
  | 3 => .minimum
  | 5 => (.camp ⟨⟨344,217,210,196,200,136,24,88,216⟩,[],[(8,1,0),(0,2,1),(1,3,2),(2,4,3),(5,6,5)]⟩)
  | _ => .invalid)
  | _ => .invalid)
  | 3 => (.branch fun v => match v.val with
  | 2 => .minimum
  | 4 => (.branch fun v => match v.val with
  | 2 => .minimum
  | 5 => (.camp ⟨⟨332,201,194,196,196,140,12,76,204⟩,[],[(8,1,0),(0,2,1),(1,3,2),(4,5,4),(5,6,5)]⟩)
  | _ => .invalid)
  | _ => .invalid)
  | 6 => .minimum
  | _ => .invalid)

theorem piece_7_8_0_1 : UpperPrefix a [7,8,0,1] 30 :=
  sound a [7,8,0,1] 30 piece_7_8_0_1_data (by decide +kernel)

def piece_7_8_0_2_data : Tree :=
(.branch fun v => match v.val with
  | 1 => .minimum
  | 3 => (.branch fun v => match v.val with
  | 1 => .minimum
  | 4 => (.leaf ⟨⟨352,225,226,226,194,130,34,98,226⟩,[],[(8,1,0),(0,2,1),(3,4,3),(4,5,4)],⟨131,262,13,28,56,112,226,482,355⟩,⟨131,262,13,28,56,112,192,384,257⟩,[⟨2,1224302389103697579738115,⟨483,499,505,56,56,112,192,384,449⟩⟩]⟩)
  | _ => .invalid)
  | 6 => .minimum
  | _ => .invalid)

theorem piece_7_8_0_2 : UpperPrefix a [7,8,0,2] 30 :=
  sound a [7,8,0,2] 30 piece_7_8_0_2_data (by decide +kernel)

def piece_7_8_0_5_data : Tree :=
.minimum

theorem piece_7_8_0_5 : UpperPrefix a [7,8,0,5] 30 :=
  sound a [7,8,0,5] 30 piece_7_8_0_5_data (by decide +kernel)

def piece_7_8_0_6_data : Tree :=
.minimum

theorem piece_7_8_0_6 : UpperPrefix a [7,8,0,6] 30 :=
  sound a [7,8,0,6] 30 piece_7_8_0_6_data (by decide +kernel)

def piece_7_8_1_0_data : Tree :=
.minimum

theorem piece_7_8_1_0 : UpperPrefix a [7,8,1,0] 30 :=
  sound a [7,8,1,0] 30 piece_7_8_1_0_data (by decide +kernel)

def piece_7_8_1_2_data : Tree :=
(.branch fun v => match v.val with
  | 0 => .minimum
  | 3 => (.branch fun v => match v.val with
  | 0 => .minimum
  | 4 => (.leaf ⟨⟨352,225,225,225,193,129,33,97,224⟩,[],[(8,1,0),(2,3,2),(3,4,3),(4,5,4)],⟨131,262,14,28,56,112,225,481,353⟩,⟨131,262,14,28,56,112,192,384,257⟩,[⟨1,1217204977193844158234625,⟨505,508,60,28,56,112,192,480,497⟩⟩]⟩)
  | _ => .invalid)
  | 6 => .minimum
  | _ => .invalid)

theorem piece_7_8_1_2 : UpperPrefix a [7,8,1,2] 30 :=
  sound a [7,8,1,2] 30 piece_7_8_1_2_data (by decide +kernel)

def piece_7_8_1_5_data : Tree :=
.minimum

theorem piece_7_8_1_5 : UpperPrefix a [7,8,1,5] 30 :=
  sound a [7,8,1,5] 30 piece_7_8_1_5_data (by decide +kernel)

def piece_7_8_1_6_data : Tree :=
.minimum

theorem piece_7_8_1_6 : UpperPrefix a [7,8,1,6] 30 :=
  sound a [7,8,1,6] 30 piece_7_8_1_6_data (by decide +kernel)

def piece_7_8_4_data : Tree :=
.minimum

theorem piece_7_8_4 : UpperPrefix a [7,8,4] 30 :=
  sound a [7,8,4] 30 piece_7_8_4_data (by decide +kernel)

def piece_7_8_5_data : Tree :=
.minimum

theorem piece_7_8_5 : UpperPrefix a [7,8,5] 30 :=
  sound a [7,8,5] 30 piece_7_8_5_data (by decide +kernel)

def piece_7_8_6_data : Tree :=
.minimum

theorem piece_7_8_6 : UpperPrefix a [7,8,6] 30 :=
  sound a [7,8,6] 30 piece_7_8_6_data (by decide +kernel)

theorem piece_7_8_0 : UpperPrefix a [7,8,0] 30 :=
  branch_upper a [7,8,0] 30 (by decide) (fin9_cases _
    (invalid_upper a [7,8,0,0] 30 (by decide +kernel))
    piece_7_8_0_1
    piece_7_8_0_2
    (invalid_upper a [7,8,0,3] 30 (by decide +kernel))
    (invalid_upper a [7,8,0,4] 30 (by decide +kernel))
    piece_7_8_0_5
    piece_7_8_0_6
    (invalid_upper a [7,8,0,7] 30 (by decide +kernel))
    (invalid_upper a [7,8,0,8] 30 (by decide +kernel)))

theorem piece_7_8_1 : UpperPrefix a [7,8,1] 30 :=
  branch_upper a [7,8,1] 30 (by decide) (fin9_cases _
    piece_7_8_1_0
    (invalid_upper a [7,8,1,1] 30 (by decide +kernel))
    piece_7_8_1_2
    (invalid_upper a [7,8,1,3] 30 (by decide +kernel))
    (invalid_upper a [7,8,1,4] 30 (by decide +kernel))
    piece_7_8_1_5
    piece_7_8_1_6
    (invalid_upper a [7,8,1,7] 30 (by decide +kernel))
    (invalid_upper a [7,8,1,8] 30 (by decide +kernel)))

theorem piece_7_8 : UpperPrefix a [7,8] 30 :=
  branch_upper a [7,8] 30 (by decide) (fin9_cases _
    piece_7_8_0
    piece_7_8_1
    (invalid_upper a [7,8,2] 30 (by decide +kernel))
    (invalid_upper a [7,8,3] 30 (by decide +kernel))
    piece_7_8_4
    piece_7_8_5
    piece_7_8_6
    (invalid_upper a [7,8,7] 30 (by decide +kernel))
    (invalid_upper a [7,8,8] 30 (by decide +kernel)))

end Delivery.FiniteExclusion.Thirty9Minimum

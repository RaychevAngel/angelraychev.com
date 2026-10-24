import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0167
import IrregularNine14P06C0168

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28740 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 388 25 28 98 98 226 354), lower := (rows 7 35 388 25 28 32 64 128 256), losses := [] }

theorem u28740 : Upper (D 6) (R 6) [6,33,384,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28740
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28741 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 388 25 50 108 76 204 332), lower := (rows 7 35 388 25 50 32 64 128 256), losses := [] }

theorem u28741 : Upper (D 6) (R 6) [6,33,384,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28741
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28742 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 388 25 52 106 74 202 330), lower := (rows 7 35 388 25 52 32 64 128 256), losses := [] }

theorem u28742 : Upper (D 6) (R 6) [6,33,384,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28742
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28743 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 388 25 56 102 70 198 326), lower := (rows 7 35 388 25 56 32 64 128 256), losses := [] }

theorem u28743 : Upper (D 6) (R 6) [6,33,384,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28743
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28744 : Route 9 := (fun mask => (mask,id))

def c28744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28744 : Upper (D 6) (R 6) [6,33,384,17,66] 13 := by
  apply FastRouting.sound _ _ [6,33,384,17,66] 13 (by decide) (choices 1) [4,8,64] r28744 c28744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10050
  · exact u10051
  · exact u10052

def r28745 : Route 9 := (fun mask => (mask,id))

def c28745 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28745 : Upper (D 6) (R 6) [6,33,384,17,68] 13 := by
  apply FastRouting.sound _ _ [6,33,384,17,68] 13 (by decide) (choices 1) [2,8,64] r28745 c28745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10053
  · exact u10054
  · exact u10055

def r28746 : Route 9 := (fun mask => (mask,id))

def c28746 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28746 : Upper (D 6) (R 6) [6,33,384,17,72] 13 := by
  apply FastRouting.sound _ _ [6,33,384,17,72] 13 (by decide) (choices 1) [2,4,64] r28746 c28746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10056
  · exact u10057
  · exact u10058

def r28747 : Route 9 := (fun mask => (mask,id))

def c28747 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28747 : Upper (D 6) (R 6) [6,33,384,17,96] 13 := by
  apply FastRouting.sound _ _ [6,33,384,17,96] 13 (by decide) (choices 1) [2,4,8,64] r28747 c28747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10059
  · exact u10060
  · exact u10061
  · exact u10062

def b28748 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 388 26 28 97 97 225 353), lower := (rows 7 35 388 26 28 32 64 128 256), losses := [] }

theorem u28748 : Upper (D 6) (R 6) [6,33,384,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28748
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28749 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 388 26 49 108 76 204 332), lower := (rows 7 35 388 26 49 32 64 128 256), losses := [] }

theorem u28749 : Upper (D 6) (R 6) [6,33,384,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28749
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28750 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 388 26 52 105 73 201 329), lower := (rows 7 35 388 26 52 32 64 128 256), losses := [] }

theorem u28750 : Upper (D 6) (R 6) [6,33,384,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28750
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28751 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 24, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 388 26 56 101 69 197 325), lower := (rows 7 35 388 26 56 32 64 128 256), losses := [] }

theorem u28751 : Upper (D 6) (R 6) [6,33,384,18,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28751
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28752 : Route 9 := (fun mask => (mask,id))

def c28752 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28752 : Upper (D 6) (R 6) [6,33,384,18,65] 13 := by
  apply FastRouting.sound _ _ [6,33,384,18,65] 13 (by decide) (choices 1) [4,8,64] r28752 c28752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10063
  · exact u10064
  · exact u10065

def r28753 : Route 9 := (fun mask => (mask,id))

def c28753 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28753 : Upper (D 6) (R 6) [6,33,384,18,68] 13 := by
  apply FastRouting.sound _ _ [6,33,384,18,68] 13 (by decide) (choices 1) [1,8,64] r28753 c28753
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10066
  · exact u10067
  · exact u10068

def r28754 : Route 9 := (fun mask => (mask,id))

def c28754 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28754 : Upper (D 6) (R 6) [6,33,384,18,72] 13 := by
  apply FastRouting.sound _ _ [6,33,384,18,72] 13 (by decide) (choices 1) [1,4,64] r28754 c28754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10069
  · exact u10070
  · exact u10071

def r28755 : Route 9 := (fun mask => (mask,id))

def c28755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28755 : Upper (D 6) (R 6) [6,33,384,18,96] 13 := by
  apply FastRouting.sound _ _ [6,33,384,18,96] 13 (by decide) (choices 1) [1,4,8,64] r28755 c28755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10072
  · exact u10073
  · exact u10074
  · exact u10075

def b28756 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 16, targets := 68 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 388 28 49 106 74 202 330), lower := (rows 7 35 388 28 49 32 64 128 256), losses := [] }

theorem u28756 : Upper (D 6) (R 6) [6,33,384,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28756
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28757 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 7 35 388 28 50 105 73 201 329), lower := (rows 7 35 388 28 50 32 64 128 256), losses := [] }

theorem u28757 : Upper (D 6) (R 6) [6,33,384,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28757
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28758 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 98, targets := 4 }], pairs := [(0,5),(1,2),(2,5)], upper := (rows 7 35 388 28 56 99 67 195 323), lower := (rows 7 35 388 28 56 32 64 128 256), losses := [] }

theorem u28758 : Upper (D 6) (R 6) [6,33,384,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28758
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28759 : Route 9 := (fun mask => (mask,id))

def c28759 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28759 : Upper (D 6) (R 6) [6,33,384,20,65] 13 := by
  apply FastRouting.sound _ _ [6,33,384,20,65] 13 (by decide) (choices 1) [2,8,64] r28759 c28759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10076
  · exact u10077
  · exact u10078

def r28760 : Route 9 := (fun mask => (mask,id))

def c28760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28760 : Upper (D 6) (R 6) [6,33,384,20,66] 13 := by
  apply FastRouting.sound _ _ [6,33,384,20,66] 13 (by decide) (choices 1) [1,8,64] r28760 c28760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10079
  · exact u10080
  · exact u10081

def r28761 : Route 9 := (fun mask => (mask,id))

def c28761 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28761 : Upper (D 6) (R 6) [6,33,384,20,72] 13 := by
  apply FastRouting.sound _ _ [6,33,384,20,72] 13 (by decide) (choices 1) [1,2,64] r28761 c28761
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10082
  · exact u10083
  · exact u10084

def r28762 : Route 9 := (fun mask => (mask,id))

def c28762 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28762 : Upper (D 6) (R 6) [6,33,384,20,96] 13 := by
  apply FastRouting.sound _ _ [6,33,384,20,96] 13 (by decide) (choices 1) [1,2,8,64] r28762 c28762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10085
  · exact u10086
  · exact u10087
  · exact u10088

def b28763 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 388 41 82 124 92 220 348), lower := (rows 7 35 388 41 82 32 64 128 256), losses := [] }

theorem u28763 : Upper (D 6) (R 6) [6,33,384,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28763
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28764 : PairBound 9 := { available := 90, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 388 41 84 122 90 218 346), lower := (rows 7 35 388 41 84 32 64 128 256), losses := [] }

theorem u28764 : Upper (D 6) (R 6) [6,33,384,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28764
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28765 : PairBound 9 := { available := 86, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 388 41 88 118 86 214 342), lower := (rows 7 35 388 41 88 32 64 128 256), losses := [] }

theorem u28765 : Upper (D 6) (R 6) [6,33,384,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28765
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28766 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 388 42 81 124 92 220 348), lower := (rows 7 35 388 42 81 32 64 128 256), losses := [] }

theorem u28766 : Upper (D 6) (R 6) [6,33,384,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28766
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28767 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 388 42 84 121 89 217 345), lower := (rows 7 35 388 42 84 32 64 128 256), losses := [] }

theorem u28767 : Upper (D 6) (R 6) [6,33,384,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28767
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28768 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 388 42 88 117 85 213 341), lower := (rows 7 35 388 42 88 32 64 128 256), losses := [] }

theorem u28768 : Upper (D 6) (R 6) [6,33,384,34,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28768
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28769 : Route 9 := (fun mask => (mask,id))

def c28769 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28769 : Upper (D 6) (R 6) [6,33,384,36,65] 13 := by
  apply FastRouting.sound _ _ [6,33,384,36,65] 13 (by decide) (choices 1) [2,8,16,64] r28769 c28769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10089
  · exact u10090
  · exact u10091
  · exact u10092

def r28770 : Route 9 := (fun mask => (mask,id))

def c28770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28770 : Upper (D 6) (R 6) [6,33,384,36,66] 13 := by
  apply FastRouting.sound _ _ [6,33,384,36,66] 13 (by decide) (choices 1) [1,8,16,64] r28770 c28770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10093
  · exact u10094
  · exact u10095
  · exact u10096

def r28771 : Route 9 := (fun mask => (mask,id))

def c28771 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28771 : Upper (D 6) (R 6) [6,33,384,36,72] 13 := by
  apply FastRouting.sound _ _ [6,33,384,36,72] 13 (by decide) (choices 1) [1,2,16,64] r28771 c28771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10097
  · exact u10098
  · exact u10099
  · exact u10100

def r28772 : Route 9 := (fun mask => (mask,id))

def c28772 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28772 : Upper (D 6) (R 6) [6,33,384,48,65] 13 := by
  apply FastRouting.sound _ _ [6,33,384,48,65] 13 (by decide) (choices 1) [2,4,8,64] r28772 c28772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10101
  · exact u10102
  · exact u10103
  · exact u10104

def r28773 : Route 9 := (fun mask => (mask,id))

def c28773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28773 : Upper (D 6) (R 6) [6,33,384,48,66] 13 := by
  apply FastRouting.sound _ _ [6,33,384,48,66] 13 (by decide) (choices 1) [1,4,8,64] r28773 c28773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10105
  · exact u10106
  · exact u10107
  · exact u10108

def r28774 : Route 9 := (fun mask => (mask,id))

def c28774 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28774 : Upper (D 6) (R 6) [6,33,384,48,68] 13 := by
  apply FastRouting.sound _ _ [6,33,384,48,68] 13 (by decide) (choices 1) [1,2,8,64] r28774 c28774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10109
  · exact u10110
  · exact u10111
  · exact u10112

def r28775 : Route 9 := (fun mask => (mask,id))

def c28775 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28775 : Upper (D 6) (R 6) [6,33,384,48,72] 13 := by
  apply FastRouting.sound _ _ [6,33,384,48,72] 13 (by decide) (choices 1) [1,2,4,64] r28775 c28775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10113
  · exact u10114
  · exact u10115
  · exact u10116

def r28776 : Route 9 := (fun mask => (mask,id))

def c28776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28776 : Upper (D 6) (R 6) [6,33,384,65,66] 13 := by
  apply FastRouting.sound _ _ [6,33,384,65,66] 13 (by decide) (choices 1) [4,8,16] r28776 c28776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10117
  · exact u10118
  · exact u10119

def r28777 : Route 9 := (fun mask => (mask,id))

def c28777 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28777 : Upper (D 6) (R 6) [6,33,384,65,68] 13 := by
  apply FastRouting.sound _ _ [6,33,384,65,68] 13 (by decide) (choices 1) [2,8,16] r28777 c28777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10120
  · exact u10121
  · exact u10122

def b28778 : PairBound 9 := { available := 54, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 388 73 88 54 118 182 310), lower := (rows 7 35 388 73 88 32 64 128 256), losses := [] }

theorem u28778 : Upper (D 6) (R 6) [6,33,384,65,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28778
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28779 : Route 9 := (fun mask => (mask,id))

def c28779 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28779 : Upper (D 6) (R 6) [6,33,384,65,96] 13 := by
  apply FastRouting.sound _ _ [6,33,384,65,96] 13 (by decide) (choices 1) [2,4,8,16] r28779 c28779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10123
  · exact u10124
  · exact u10125
  · exact u10126

def r28780 : Route 9 := (fun mask => (mask,id))

def c28780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28780 : Upper (D 6) (R 6) [6,33,384,66,68] 13 := by
  apply FastRouting.sound _ _ [6,33,384,66,68] 13 (by decide) (choices 1) [1,8,16] r28780 c28780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10127
  · exact u10128
  · exact u10129

def b28781 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 388 74 88 53 117 181 309), lower := (rows 7 35 388 74 88 32 64 128 256), losses := [] }

theorem u28781 : Upper (D 6) (R 6) [6,33,384,66,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28781
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28782 : Route 9 := (fun mask => (mask,id))

def c28782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28782 : Upper (D 6) (R 6) [6,33,384,66,96] 13 := by
  apply FastRouting.sound _ _ [6,33,384,66,96] 13 (by decide) (choices 1) [1,4,8,16] r28782 c28782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10130
  · exact u10131
  · exact u10132
  · exact u10133

def b28783 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 388 76 88 51 115 179 307), lower := (rows 7 35 388 76 88 32 64 128 256), losses := [] }

theorem u28783 : Upper (D 6) (R 6) [6,33,384,68,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28783
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28784 : Route 9 := (fun mask => (mask,id))

def c28784 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28784 : Upper (D 6) (R 6) [6,33,384,68,96] 13 := by
  apply FastRouting.sound _ _ [6,33,384,68,96] 13 (by decide) (choices 1) [1,2,8,16] r28784 c28784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u10134
  · exact u10135
  · exact u10136
  · exact u10137

def b28785 : PairBound 9 := { available := 39, camps := [{ cop := 6, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 388 88 88 39 103 167 295), lower := (rows 7 35 388 88 88 32 64 128 256), losses := [] }

theorem u28785 : Upper (D 6) (R 6) [6,33,384,80,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28785
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28786 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 388 88 112 47 79 143 271), lower := (rows 7 35 388 88 112 32 64 128 256), losses := [] }

theorem u28786 : Upper (D 6) (R 6) [6,33,384,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28786
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28787 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 11 81 484 452 452 452), lower := (rows 7 42 52 11 81 32 64 128 256), losses := [] }

theorem u28787 : Upper (D 6) (R 6) [6,40,48,3,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28787
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28788 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 11 145 356 324 452 324), lower := (rows 7 42 52 11 145 32 64 128 256), losses := [] }

theorem u28788 : Upper (D 6) (R 6) [6,40,48,3,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28788
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28789 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 11 208 357 325 453 325), lower := (rows 7 42 52 11 208 32 64 128 256), losses := [] }

theorem u28789 : Upper (D 6) (R 6) [6,40,48,3,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28789
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28790 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 11 400 101 69 197 325), lower := (rows 7 42 52 11 400 32 64 128 256), losses := [] }

theorem u28790 : Upper (D 6) (R 6) [6,40,48,3,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28790
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28791 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 13 81 482 450 450 450), lower := (rows 7 42 52 13 81 32 64 128 256), losses := [] }

theorem u28791 : Upper (D 6) (R 6) [6,40,48,5,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28791
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28792 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 13 145 354 322 450 322), lower := (rows 7 42 52 13 145 32 64 128 256), losses := [] }

theorem u28792 : Upper (D 6) (R 6) [6,40,48,5,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28792
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28793 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 13 208 355 323 451 323), lower := (rows 7 42 52 13 208 32 64 128 256), losses := [] }

theorem u28793 : Upper (D 6) (R 6) [6,40,48,5,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28793
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28794 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 13 400 99 67 195 323), lower := (rows 7 42 52 13 400 32 64 128 256), losses := [] }

theorem u28794 : Upper (D 6) (R 6) [6,40,48,5,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28794
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28795 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 14 81 481 449 449 449), lower := (rows 7 42 52 14 81 32 64 128 256), losses := [] }

theorem u28795 : Upper (D 6) (R 6) [6,40,48,6,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28795
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28796 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 14 145 353 321 449 321), lower := (rows 7 42 52 14 145 32 64 128 256), losses := [] }

theorem u28796 : Upper (D 6) (R 6) [6,40,48,6,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28796
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28797 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 14 208 353 321 449 321), lower := (rows 7 42 52 14 208 32 64 128 256), losses := [] }

theorem u28797 : Upper (D 6) (R 6) [6,40,48,6,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28797
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28798 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 52 14 400 97 65 193 321), lower := (rows 7 42 52 14 400 32 64 128 256), losses := [] }

theorem u28798 : Upper (D 6) (R 6) [6,40,48,6,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28798
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28799 : PairBound 9 := { available := 390, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 7 42 52 73 81 422 454 390 390), lower := (rows 7 42 52 73 81 32 64 128 256), losses := [] }

theorem u28799 : Upper (D 6) (R 6) [6,40,48,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28799
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28799
end Delivery.IrregularNine14.P06

import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0026
import IrregularNine14P01C0027

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5040 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 44 74 18 225 193 193 449), lower := (rows 277 50 44 74 18 32 64 128 256), losses := [] }

theorem u5040 : Upper (D 1) (R 1) [276,48,40,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5040
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5041 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 44 74 80 163 195 131 387), lower := (rows 277 50 44 74 80 32 64 128 256), losses := [] }

theorem u5041 : Upper (D 1) (R 1) [276,48,40,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5041
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5042 : Route 9 := (fun mask => (mask,id))

def c5042 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5042 : Upper (D 1) (R 1) [276,48,40,66,128] 13 := by
  apply FastRouting.sound _ _ [276,48,40,66,128] 13 (by decide) (choices 1) [1,2,64,128] r5042 c5042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1619
  · exact u1620
  · exact u1621
  · exact u1622

def b5043 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 50 44 200 17 226 194 194 450), lower := (rows 277 50 44 200 17 32 64 128 256), losses := [] }

theorem u5043 : Upper (D 1) (R 1) [276,48,40,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5043
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5044 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 44 200 18 227 195 195 451), lower := (rows 277 50 44 200 18 32 64 128 256), losses := [] }

theorem u5044 : Upper (D 1) (R 1) [276,48,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5044
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5045 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 44 200 80 163 195 131 387), lower := (rows 277 50 44 200 80 32 64 128 256), losses := [] }

theorem u5045 : Upper (D 1) (R 1) [276,48,40,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5045
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5046 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 50 70 41 18 232 200 200 456), lower := (rows 277 50 70 41 18 32 64 128 256), losses := [] }

theorem u5046 : Upper (D 1) (R 1) [276,48,66,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5046
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5047 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 50 70 41 24 226 194 194 450), lower := (rows 277 50 70 41 24 32 64 128 256), losses := [] }

theorem u5047 : Upper (D 1) (R 1) [276,48,66,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5047
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5048 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 70 41 80 170 202 138 394), lower := (rows 277 50 70 41 80 32 64 128 256), losses := [] }

theorem u5048 : Upper (D 1) (R 1) [276,48,66,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5048
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5049 : Route 9 := (fun mask => (mask,id))

def c5049 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5049 : Upper (D 1) (R 1) [276,48,66,33,128] 13 := by
  apply FastRouting.sound _ _ [276,48,66,33,128] 13 (by decide) (choices 1) [2,8,64,128] r5049 c5049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1623
  · exact u1624
  · exact u1625
  · exact u1626

def b5050 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 277 50 70 104 17 170 202 138 394), lower := (rows 277 50 70 104 17 32 64 128 256), losses := [] }

theorem u5050 : Upper (D 1) (R 1) [276,48,66,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5050
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5051 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 50 70 104 18 169 201 137 393), lower := (rows 277 50 70 104 18 32 64 128 256), losses := [] }

theorem u5051 : Upper (D 1) (R 1) [276,48,66,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5051
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5052 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 277 50 70 104 24 163 195 131 387), lower := (rows 277 50 70 104 24 32 64 128 256), losses := [] }

theorem u5052 : Upper (D 1) (R 1) [276,48,66,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5052
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5053 : Route 9 := (fun mask => (mask,id))

def c5053 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5053 : Upper (D 1) (R 1) [276,48,66,96,128] 13 := by
  apply FastRouting.sound _ _ [276,48,66,96,128] 13 (by decide) (choices 1) [1,2,8,128] r5053 c5053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1627
  · exact u1628
  · exact u1629
  · exact u1630

def b5054 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 50 70 137 18 232 232 232 488), lower := (rows 277 50 70 137 18 32 64 128 256), losses := [] }

theorem u5054 : Upper (D 1) (R 1) [276,48,66,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5054
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5055 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 277 50 70 137 24 226 226 226 482), lower := (rows 277 50 70 137 24 32 64 128 256), losses := [] }

theorem u5055 : Upper (D 1) (R 1) [276,48,66,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5055
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5056 : PairBound 9 := { available := 202, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 277 50 70 137 48 234 202 202 458), lower := (rows 277 50 70 137 48 32 64 128 256), losses := [] }

theorem u5056 : Upper (D 1) (R 1) [276,48,66,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5056
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5057 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 70 137 80 170 234 170 426), lower := (rows 277 50 70 137 80 32 64 128 256), losses := [] }

theorem u5057 : Upper (D 1) (R 1) [276,48,66,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5057
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5058 : Route 9 := (fun mask => (mask,id))

def c5058 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5058 : Upper (D 1) (R 1) [276,48,66,129,128] 13 := by
  apply FastRouting.sound _ _ [276,48,66,129,128] 13 (by decide) (choices 1) [2,8,64] r5058 c5058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1631
  · exact u1632
  · exact u1633

def b5059 : PairBound 9 := { available := 232, camps := [], pairs := [], upper := (rows 277 50 70 138 17 232 232 232 488), lower := (rows 277 50 70 138 17 32 64 128 256), losses := [] }

theorem u5059 : Upper (D 1) (R 1) [276,48,66,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5059
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5060 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 277 50 70 138 24 225 225 225 481), lower := (rows 277 50 70 138 24 32 64 128 256), losses := [] }

theorem u5060 : Upper (D 1) (R 1) [276,48,66,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5060
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5061 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 277 50 70 138 48 233 201 201 457), lower := (rows 277 50 70 138 48 32 64 128 256), losses := [] }

theorem u5061 : Upper (D 1) (R 1) [276,48,66,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5061
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5062 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 70 138 80 169 233 169 425), lower := (rows 277 50 70 138 80 32 64 128 256), losses := [] }

theorem u5062 : Upper (D 1) (R 1) [276,48,66,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5062
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5063 : Route 9 := (fun mask => (mask,id))

def c5063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5063 : Upper (D 1) (R 1) [276,48,66,130,128] 13 := by
  apply FastRouting.sound _ _ [276,48,66,130,128] 13 (by decide) (choices 1) [1,8,64] r5063 c5063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1634
  · exact u1635
  · exact u1636

def b5064 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 277 50 70 168 17 234 202 202 458), lower := (rows 277 50 70 168 17 32 64 128 256), losses := [] }

theorem u5064 : Upper (D 1) (R 1) [276,48,66,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5064
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5065 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 50 70 168 18 233 201 201 457), lower := (rows 277 50 70 168 18 32 64 128 256), losses := [] }

theorem u5065 : Upper (D 1) (R 1) [276,48,66,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5065
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5066 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 277 50 70 168 24 227 195 195 451), lower := (rows 277 50 70 168 24 32 64 128 256), losses := [] }

theorem u5066 : Upper (D 1) (R 1) [276,48,66,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5066
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5067 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 70 168 80 171 203 139 395), lower := (rows 277 50 70 168 80 32 64 128 256), losses := [] }

theorem u5067 : Upper (D 1) (R 1) [276,48,66,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5067
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5068 : PairBound 9 := { available := 75, camps := [{ cop := 3, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 70 168 144 107 75 203 331), lower := (rows 277 50 70 168 144 32 64 128 256), losses := [] }

theorem u5068 : Upper (D 1) (R 1) [276,48,66,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5068
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5069 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 277 50 70 200 17 170 234 170 426), lower := (rows 277 50 70 200 17 32 64 128 256), losses := [] }

theorem u5069 : Upper (D 1) (R 1) [276,48,66,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5069
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5070 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 50 70 200 18 169 233 169 425), lower := (rows 277 50 70 200 18 32 64 128 256), losses := [] }

theorem u5070 : Upper (D 1) (R 1) [276,48,66,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5070
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5071 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 277 50 70 200 24 163 227 163 419), lower := (rows 277 50 70 200 24 32 64 128 256), losses := [] }

theorem u5071 : Upper (D 1) (R 1) [276,48,66,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5071
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5072 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 277 50 70 200 48 171 203 139 395), lower := (rows 277 50 70 200 48 32 64 128 256), losses := [] }

theorem u5072 : Upper (D 1) (R 1) [276,48,66,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5072
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5073 : Route 9 := (fun mask => (mask,id))

def c5073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5073 : Upper (D 1) (R 1) [276,48,66,192,128] 13 := by
  apply FastRouting.sound _ _ [276,48,66,192,128] 13 (by decide) (choices 1) [1,2,8] r5073 c5073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1637
  · exact u1638
  · exact u1639

def b5074 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 76 41 18 226 194 194 450), lower := (rows 277 50 76 41 18 32 64 128 256), losses := [] }

theorem u5074 : Upper (D 1) (R 1) [276,48,72,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5074
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5075 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 76 41 80 162 194 130 386), lower := (rows 277 50 76 41 80 32 64 128 256), losses := [] }

theorem u5075 : Upper (D 1) (R 1) [276,48,72,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5075
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5076 : Route 9 := (fun mask => (mask,id))

def c5076 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5076 : Upper (D 1) (R 1) [276,48,72,33,128] 13 := by
  apply FastRouting.sound _ _ [276,48,72,33,128] 13 (by decide) (choices 1) [2,64,128] r5076 c5076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1640
  · exact u1641
  · exact u1642

def b5077 : PairBound 9 := { available := 226, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 76 137 18 226 226 226 482), lower := (rows 277 50 76 137 18 32 64 128 256), losses := [] }

theorem u5077 : Upper (D 1) (R 1) [276,48,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5077
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5078 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 277 50 76 137 48 226 194 194 450), lower := (rows 277 50 76 137 48 32 64 128 256), losses := [] }

theorem u5078 : Upper (D 1) (R 1) [276,48,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5078
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5079 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 76 137 80 162 226 162 418), lower := (rows 277 50 76 137 80 32 64 128 256), losses := [] }

theorem u5079 : Upper (D 1) (R 1) [276,48,72,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5079
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5080 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 50 76 137 144 98 98 226 354), lower := (rows 277 50 76 137 144 32 64 128 256), losses := [] }

theorem u5080 : Upper (D 1) (R 1) [276,48,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5080
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5081 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 277 50 76 138 17 226 226 226 482), lower := (rows 277 50 76 138 17 32 64 128 256), losses := [] }

theorem u5081 : Upper (D 1) (R 1) [276,48,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5081
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5082 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 76 138 18 225 225 225 481), lower := (rows 277 50 76 138 18 32 64 128 256), losses := [] }

theorem u5082 : Upper (D 1) (R 1) [276,48,72,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5082
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5083 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 277 50 76 138 48 227 195 195 451), lower := (rows 277 50 76 138 48 32 64 128 256), losses := [] }

theorem u5083 : Upper (D 1) (R 1) [276,48,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5083
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5084 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 76 138 80 163 227 163 419), lower := (rows 277 50 76 138 80 32 64 128 256), losses := [] }

theorem u5084 : Upper (D 1) (R 1) [276,48,72,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5084
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5085 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 50 76 138 144 99 99 227 355), lower := (rows 277 50 76 138 144 32 64 128 256), losses := [] }

theorem u5085 : Upper (D 1) (R 1) [276,48,72,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5085
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5086 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 50 76 168 17 226 194 194 450), lower := (rows 277 50 76 168 17 32 64 128 256), losses := [] }

theorem u5086 : Upper (D 1) (R 1) [276,48,72,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5086
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5087 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 76 168 18 227 195 195 451), lower := (rows 277 50 76 168 18 32 64 128 256), losses := [] }

theorem u5087 : Upper (D 1) (R 1) [276,48,72,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5087
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5088 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 76 168 80 163 195 131 387), lower := (rows 277 50 76 168 80 32 64 128 256), losses := [] }

theorem u5088 : Upper (D 1) (R 1) [276,48,72,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5088
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5089 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 50 76 168 144 99 67 195 323), lower := (rows 277 50 76 168 144 32 64 128 256), losses := [] }

theorem u5089 : Upper (D 1) (R 1) [276,48,72,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5089
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5090 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 277 50 100 74 17 170 202 138 394), lower := (rows 277 50 100 74 17 32 64 128 256), losses := [] }

theorem u5090 : Upper (D 1) (R 1) [276,48,96,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5090
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5091 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 18, targets := 128 }], pairs := [(1,7)], upper := (rows 277 50 100 74 18 169 201 137 393), lower := (rows 277 50 100 74 18 32 64 128 256), losses := [] }

theorem u5091 : Upper (D 1) (R 1) [276,48,96,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5091
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5092 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 277 50 100 74 24 163 195 131 387), lower := (rows 277 50 100 74 24 32 64 128 256), losses := [] }

theorem u5092 : Upper (D 1) (R 1) [276,48,96,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5092
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5093 : Route 9 := (fun mask => (mask,id))

def c5093 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5093 : Upper (D 1) (R 1) [276,48,96,66,128] 13 := by
  apply FastRouting.sound _ _ [276,48,96,66,128] 13 (by decide) (choices 1) [1,2,8,128] r5093 c5093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1643
  · exact u1644
  · exact u1645
  · exact u1646

def b5094 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 100 137 18 234 202 202 458), lower := (rows 277 50 100 137 18 32 64 128 256), losses := [] }

theorem u5094 : Upper (D 1) (R 1) [276,48,96,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5094
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5095 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 50 100 137 24 226 194 194 450), lower := (rows 277 50 100 137 24 32 64 128 256), losses := [] }

theorem u5095 : Upper (D 1) (R 1) [276,48,96,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5095
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5096 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 100 137 80 170 202 138 394), lower := (rows 277 50 100 137 80 32 64 128 256), losses := [] }

theorem u5096 : Upper (D 1) (R 1) [276,48,96,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5096
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5097 : Route 9 := (fun mask => (mask,id))

def c5097 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5097 : Upper (D 1) (R 1) [276,48,96,129,128] 13 := by
  apply FastRouting.sound _ _ [276,48,96,129,128] 13 (by decide) (choices 1) [2,8,64] r5097 c5097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1647
  · exact u1648
  · exact u1649

def b5098 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 277 50 100 138 17 234 202 202 458), lower := (rows 277 50 100 138 17 32 64 128 256), losses := [] }

theorem u5098 : Upper (D 1) (R 1) [276,48,96,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5098
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5099 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 100 138 18 233 201 201 457), lower := (rows 277 50 100 138 18 32 64 128 256), losses := [] }

theorem u5099 : Upper (D 1) (R 1) [276,48,96,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5099
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u5099
end Delivery.IrregularNine14.P01

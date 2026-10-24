import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0027
import IrregularNine14P01C0028

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5100 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 277 50 100 138 24 227 195 195 451), lower := (rows 277 50 100 138 24 32 64 128 256), losses := [] }

theorem u5100 : Upper (D 1) (R 1) [276,48,96,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5100
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5101 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 100 138 80 171 203 139 395), lower := (rows 277 50 100 138 80 32 64 128 256), losses := [] }

theorem u5101 : Upper (D 1) (R 1) [276,48,96,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5101
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5102 : Route 9 := (fun mask => (mask,id))

def c5102 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5102 : Upper (D 1) (R 1) [276,48,96,130,128] 13 := by
  apply FastRouting.sound _ _ [276,48,96,130,128] 13 (by decide) (choices 1) [1,2,8,64] r5102 c5102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1650
  · exact u1651
  · exact u1652
  · exact u1653

def b5103 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 277 50 100 200 17 170 202 138 394), lower := (rows 277 50 100 200 17 32 64 128 256), losses := [] }

theorem u5103 : Upper (D 1) (R 1) [276,48,96,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5103
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5104 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 100 200 18 171 203 139 395), lower := (rows 277 50 100 200 18 32 64 128 256), losses := [] }

theorem u5104 : Upper (D 1) (R 1) [276,48,96,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5104
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5105 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 277 50 100 200 24 163 195 131 387), lower := (rows 277 50 100 200 24 32 64 128 256), losses := [] }

theorem u5105 : Upper (D 1) (R 1) [276,48,96,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5105
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5106 : Route 9 := (fun mask => (mask,id))

def c5106 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5106 : Upper (D 1) (R 1) [276,48,96,192,128] 13 := by
  apply FastRouting.sound _ _ [276,48,96,192,128] 13 (by decide) (choices 1) [1,2,8] r5106 c5106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1654
  · exact u1655
  · exact u1656

def b5107 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 196 41 18 234 202 202 458), lower := (rows 277 50 196 41 18 32 64 128 256), losses := [] }

theorem u5107 : Upper (D 1) (R 1) [276,48,192,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5107
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5108 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 50 196 41 24 226 194 194 450), lower := (rows 277 50 196 41 24 32 64 128 256), losses := [] }

theorem u5108 : Upper (D 1) (R 1) [276,48,192,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5108
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5109 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 196 41 80 170 202 138 394), lower := (rows 277 50 196 41 80 32 64 128 256), losses := [] }

theorem u5109 : Upper (D 1) (R 1) [276,48,192,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5109
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5110 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 277 50 196 74 17 170 234 170 426), lower := (rows 277 50 196 74 17 32 64 128 256), losses := [] }

theorem u5110 : Upper (D 1) (R 1) [276,48,192,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5110
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5111 : PairBound 9 := { available := 169, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 196 74 18 169 233 169 425), lower := (rows 277 50 196 74 18 32 64 128 256), losses := [] }

theorem u5111 : Upper (D 1) (R 1) [276,48,192,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5111
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5112 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 277 50 196 74 24 163 227 163 419), lower := (rows 277 50 196 74 24 32 64 128 256), losses := [] }

theorem u5112 : Upper (D 1) (R 1) [276,48,192,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5112
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5113 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 277 50 196 74 48 171 203 139 395), lower := (rows 277 50 196 74 48 32 64 128 256), losses := [] }

theorem u5113 : Upper (D 1) (R 1) [276,48,192,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5113
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5114 : PairBound 9 := { available := 43, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 50 196 74 144 43 107 171 299), lower := (rows 277 50 196 74 144 32 64 128 256), losses := [] }

theorem u5114 : Upper (D 1) (R 1) [276,48,192,66,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5114
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5115 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 277 50 196 104 17 170 202 138 394), lower := (rows 277 50 196 104 17 32 64 128 256), losses := [] }

theorem u5115 : Upper (D 1) (R 1) [276,48,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5115
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5116 : PairBound 9 := { available := 139, camps := [{ cop := 3, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 196 104 18 171 203 139 395), lower := (rows 277 50 196 104 18 32 64 128 256), losses := [] }

theorem u5116 : Upper (D 1) (R 1) [276,48,192,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5116
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5117 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 277 50 196 104 24 163 195 131 387), lower := (rows 277 50 196 104 24 32 64 128 256), losses := [] }

theorem u5117 : Upper (D 1) (R 1) [276,48,192,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5117
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5118 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 50 196 104 144 43 75 139 267), lower := (rows 277 50 196 104 144 32 64 128 256), losses := [] }

theorem u5118 : Upper (D 1) (R 1) [276,48,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5118
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5119 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 277 98 7 138 24 240 240 240 496), lower := (rows 277 98 7 138 24 32 64 128 256), losses := [] }

theorem u5119 : Upper (D 1) (R 1) [276,96,3,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5119
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5120 : PairBound 9 := { available := 216, camps := [], pairs := [(3,5)], upper := (rows 277 98 7 138 48 248 216 216 472), lower := (rows 277 98 7 138 48 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 16 0 65 129 257), good := (rows 477 66 463 138 16 0 64 128 256) }] }

theorem u5120 : Upper (D 1) (R 1) [276,96,3,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5120
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5121 : Route 9 := (fun mask => (mask,id))

def c5121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5121 : Upper (D 1) (R 1) [276,96,3,130,128] 13 := by
  apply FastRouting.sound _ _ [276,96,3,130,128] 13 (by decide) (choices 1) [8,16,64] r5121 c5121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1657
  · exact u1658
  · exact u1659

def b5122 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 7 168 18 248 216 216 472), lower := (rows 277 98 7 168 18 32 64 128 256), losses := [] }

theorem u5122 : Upper (D 1) (R 1) [276,96,3,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5122
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5123 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 277 98 7 168 24 242 210 210 466), lower := (rows 277 98 7 168 24 32 64 128 256), losses := [] }

theorem u5123 : Upper (D 1) (R 1) [276,96,3,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5123
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5124 : Route 9 := (fun mask => (mask,id))

def c5124 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5124 : Upper (D 1) (R 1) [276,96,3,160,64] 13 := by
  apply FastRouting.sound _ _ [276,96,3,160,64] 13 (by decide) (choices 1) [2,8,16,128] r5124 c5124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1660
  · exact u1661
  · exact u1662
  · exact u1663

def r5125 : Route 9 := (fun mask => (mask,id))

def c5125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5125 : Upper (D 1) (R 1) [276,96,3,160,128] 13 := by
  apply FastRouting.sound _ _ [276,96,3,160,128] 13 (by decide) (choices 1) [2,8,16,64] r5125 c5125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1664
  · exact u1665
  · exact u1666
  · exact u1667

def r5126 : Route 9 := (fun mask => (mask,id))

def c5126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5126 : Upper (D 1) (R 1) [276,96,9,130,2] 13 := by
  apply FastRouting.sound _ _ [276,96,9,130,2] 13 (by decide) (choices 1) [16,64,128] r5126 c5126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1668
  · exact u1669
  · exact u1670

def r5127 : Route 9 := (fun mask => (mask,id))

def c5127 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5127 : Upper (D 1) (R 1) [276,96,9,130,32] 13 := by
  apply FastRouting.sound _ _ [276,96,9,130,32] 13 (by decide) (choices 1) [2,16,64,128] r5127 c5127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1671
  · exact u1672
  · exact u1673
  · exact u1674

def b5128 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 13 138 144 114 114 242 370), lower := (rows 277 98 13 138 144 32 64 128 256), losses := [] }

theorem u5128 : Upper (D 1) (R 1) [276,96,9,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5128
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5129 : Route 9 := (fun mask => (mask,id))

def c5129 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5129 : Upper (D 1) (R 1) [276,96,9,160,2] 13 := by
  apply FastRouting.sound _ _ [276,96,9,160,2] 13 (by decide) (choices 1) [2,16,64,128] r5129 c5129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1675
  · exact u1676
  · exact u1677
  · exact u1678

def r5130 : Route 9 := (fun mask => (mask,id))

def c5130 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5130 : Upper (D 1) (R 1) [276,96,9,160,64] 13 := by
  apply FastRouting.sound _ _ [276,96,9,160,64] 13 (by decide) (choices 1) [2,16,128] r5130 c5130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1679
  · exact u1680
  · exact u1681

def b5131 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 13 168 144 114 82 210 338), lower := (rows 277 98 13 168 144 32 64 128 256), losses := [] }

theorem u5131 : Upper (D 1) (R 1) [276,96,9,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5131
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5132 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 14 137 18 240 240 240 496), lower := (rows 277 98 14 137 18 32 64 128 256), losses := [] }

theorem u5132 : Upper (D 1) (R 1) [276,96,10,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5132
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5133 : Route 9 := (fun mask => (mask,id))

def c5133 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5133 : Upper (D 1) (R 1) [276,96,10,129,32] 13 := by
  apply FastRouting.sound _ _ [276,96,10,129,32] 13 (by decide) (choices 1) [2,16,64,128] r5133 c5133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1682
  · exact u1683
  · exact u1684
  · exact u1685

def b5134 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 14 137 144 114 114 242 370), lower := (rows 277 98 14 137 144 32 64 128 256), losses := [] }

theorem u5134 : Upper (D 1) (R 1) [276,96,10,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5134
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5135 : PairBound 9 := { available := 146, camps := [], pairs := [(3,5)], upper := (rows 277 98 44 73 18 178 210 146 402), lower := (rows 277 98 44 73 18 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 18 0 82 146 274), good := (rows 477 466 12 73 466 0 64 128 256) }] }

theorem u5135 : Upper (D 1) (R 1) [276,96,40,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5135
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5136 : Route 9 := (fun mask => (mask,id))

def c5136 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5136 : Upper (D 1) (R 1) [276,96,40,65,128] 13 := by
  apply FastRouting.sound _ _ [276,96,40,65,128] 13 (by decide) (choices 1) [2,16,128] r5136 c5136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1686
  · exact u1687
  · exact u1688

def b5137 : PairBound 9 := { available := 210, camps := [], pairs := [(3,5)], upper := (rows 277 98 44 137 18 242 210 210 466), lower := (rows 277 98 44 137 18 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 18 0 82 146 274), good := (rows 477 466 12 137 466 0 64 128 256) }] }

theorem u5137 : Upper (D 1) (R 1) [276,96,40,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5137
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5138 : Route 9 := (fun mask => (mask,id))

def c5138 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5138 : Upper (D 1) (R 1) [276,96,40,129,64] 13 := by
  apply FastRouting.sound _ _ [276,96,40,129,64] 13 (by decide) (choices 1) [2,16,128] r5138 c5138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1689
  · exact u1690
  · exact u1691

def b5139 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 44 137 144 114 82 210 338), lower := (rows 277 98 44 137 144 32 64 128 256), losses := [] }

theorem u5139 : Upper (D 1) (R 1) [276,96,40,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5139
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5140 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 277 98 44 138 17 242 210 210 466), lower := (rows 277 98 44 138 17 32 64 128 256), losses := [] }

theorem u5140 : Upper (D 1) (R 1) [276,96,40,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5140
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5141 : PairBound 9 := { available := 209, camps := [], pairs := [(0,5)], upper := (rows 277 98 44 138 18 241 209 209 465), lower := (rows 277 98 44 138 18 32 64 128 256), losses := [{ target := 5, region := (rows 5 2 4 8 26 0 69 133 261), good := (rows 469 82 477 154 18 0 64 128 256) }] }

theorem u5141 : Upper (D 1) (R 1) [276,96,40,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5141
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5142 : Route 9 := (fun mask => (mask,id))

def c5142 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5142 : Upper (D 1) (R 1) [276,96,40,130,64] 13 := by
  apply FastRouting.sound _ _ [276,96,40,130,64] 13 (by decide) (choices 1) [1,2,16,128] r5142 c5142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1692
  · exact u1693
  · exact u1694
  · exact u1695

def b5143 : PairBound 9 := { available := 83, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 44 138 144 115 83 211 339), lower := (rows 277 98 44 138 144 32 64 128 256), losses := [] }

theorem u5143 : Upper (D 1) (R 1) [276,96,40,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5143
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5144 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 98 44 200 17 178 210 146 402), lower := (rows 277 98 44 200 17 32 64 128 256), losses := [] }

theorem u5144 : Upper (D 1) (R 1) [276,96,40,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5144
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5145 : Route 9 := (fun mask => (mask,id))

def c5145 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5145 : Upper (D 1) (R 1) [276,96,40,192,2] 13 := by
  apply FastRouting.sound _ _ [276,96,40,192,2] 13 (by decide) (choices 1) [1,2,16,128] r5145 c5145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1696
  · exact u1697
  · exact u1698
  · exact u1699

def b5146 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 44 200 144 51 83 147 275), lower := (rows 277 98 44 200 144 32 64 128 256), losses := [] }

theorem u5146 : Upper (D 1) (R 1) [276,96,40,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5146
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5147 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 277 98 134 11 24 240 240 240 496), lower := (rows 277 98 134 11 24 32 64 128 256), losses := [] }

theorem u5147 : Upper (D 1) (R 1) [276,96,130,3,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5147
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5148 : Route 9 := (fun mask => (mask,id))

def c5148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u5148 : Upper (D 1) (R 1) [276,96,130,3,32] 13 := by
  apply FastRouting.sound _ _ [276,96,130,3,32] 13 (by decide) (choices 1) [8,16,64,128] r5148 c5148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1700
  · exact u1701
  · exact u1702
  · exact u1703

def b5149 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 134 11 144 120 120 248 376), lower := (rows 277 98 134 11 144 32 64 128 256), losses := [] }

theorem u5149 : Upper (D 1) (R 1) [276,96,130,3,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5149
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5150 : PairBound 9 := { available := 232, camps := [], pairs := [], upper := (rows 277 98 134 26 17 232 232 232 488), lower := (rows 277 98 134 26 17 32 64 128 256), losses := [] }

theorem u5150 : Upper (D 1) (R 1) [276,96,130,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5150
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5151 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 277 98 134 26 24 225 225 225 481), lower := (rows 277 98 134 26 24 32 64 128 256), losses := [] }

theorem u5151 : Upper (D 1) (R 1) [276,96,130,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5151
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5152 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 277 98 134 26 48 233 201 201 457), lower := (rows 277 98 134 26 48 32 64 128 256), losses := [] }

theorem u5152 : Upper (D 1) (R 1) [276,96,130,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5152
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5153 : PairBound 9 := { available := 105, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 134 26 144 105 105 233 361), lower := (rows 277 98 134 26 144 32 64 128 256), losses := [] }

theorem u5153 : Upper (D 1) (R 1) [276,96,130,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5153
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5154 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 134 41 18 248 216 216 472), lower := (rows 277 98 134 41 18 32 64 128 256), losses := [] }

theorem u5154 : Upper (D 1) (R 1) [276,96,130,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5154
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5155 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 277 98 134 41 24 242 210 210 466), lower := (rows 277 98 134 41 24 32 64 128 256), losses := [] }

theorem u5155 : Upper (D 1) (R 1) [276,96,130,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5155
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5156 : Route 9 := (fun mask => (mask,id))

def c5156 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5156 : Upper (D 1) (R 1) [276,96,130,33,64] 13 := by
  apply FastRouting.sound _ _ [276,96,130,33,64] 13 (by decide) (choices 1) [2,8,16,128] r5156 c5156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1704
  · exact u1705
  · exact u1706
  · exact u1707

def b5157 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 134 41 144 122 90 218 346), lower := (rows 277 98 134 41 144 32 64 128 256), losses := [] }

theorem u5157 : Upper (D 1) (R 1) [276,96,130,33,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5157
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5158 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 277 98 134 56 17 234 202 202 458), lower := (rows 277 98 134 56 17 32 64 128 256), losses := [] }

theorem u5158 : Upper (D 1) (R 1) [276,96,130,48,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5158
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5159 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 277 98 134 56 18 233 201 201 457), lower := (rows 277 98 134 56 18 32 64 128 256), losses := [] }

theorem u5159 : Upper (D 1) (R 1) [276,96,130,48,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5159
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u5159
end Delivery.IrregularNine14.P01

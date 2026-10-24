import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0028
import IrregularNine14P01C0029

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5160 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 277 98 134 56 24 227 195 195 451), lower := (rows 277 98 134 56 24 32 64 128 256), losses := [] }

theorem u5160 : Upper (D 1) (R 1) [276,96,130,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5160
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5161 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 24, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 134 56 80 171 203 139 395), lower := (rows 277 98 134 56 80 32 64 128 256), losses := [] }

theorem u5161 : Upper (D 1) (R 1) [276,96,130,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5161
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5162 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 134 56 144 107 75 203 331), lower := (rows 277 98 134 56 144 32 64 128 256), losses := [] }

theorem u5162 : Upper (D 1) (R 1) [276,96,130,48,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5162
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5163 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 277 98 134 152 17 106 106 234 362), lower := (rows 277 98 134 152 17 32 64 128 256), losses := [] }

theorem u5163 : Upper (D 1) (R 1) [276,96,130,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5163
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5164 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 277 98 134 152 18 105 105 233 361), lower := (rows 277 98 134 152 18 32 64 128 256), losses := [] }

theorem u5164 : Upper (D 1) (R 1) [276,96,130,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5164
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5165 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 277 98 134 152 24 99 99 227 355), lower := (rows 277 98 134 152 24 32 64 128 256), losses := [] }

theorem u5165 : Upper (D 1) (R 1) [276,96,130,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5165
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5166 : PairBound 9 := { available := 75, camps := [], pairs := [(3,1)], upper := (rows 277 98 134 152 48 107 75 203 331), lower := (rows 277 98 134 152 48 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 50 32 64 128 256), good := (rows 285 112 156 152 48 48 64 128 256) }] }

theorem u5166 : Upper (D 1) (R 1) [276,96,130,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5166
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5167 : PairBound 9 := { available := 90, camps := [], pairs := [], upper := (rows 277 98 134 168 17 122 90 218 346), lower := (rows 277 98 134 168 17 32 64 128 256), losses := [] }

theorem u5167 : Upper (D 1) (R 1) [276,96,130,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5167
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5168 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 134 168 18 121 89 217 345), lower := (rows 277 98 134 168 18 32 64 128 256), losses := [] }

theorem u5168 : Upper (D 1) (R 1) [276,96,130,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5168
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5169 : PairBound 9 := { available := 83, camps := [], pairs := [], upper := (rows 277 98 134 168 24 115 83 211 339), lower := (rows 277 98 134 168 24 32 64 128 256), losses := [] }

theorem u5169 : Upper (D 1) (R 1) [276,96,130,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5169
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5170 : Route 9 := (fun mask => (mask,id))

def c5170 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5170 : Upper (D 1) (R 1) [276,96,130,160,64] 13 := by
  apply FastRouting.sound _ _ [276,96,130,160,64] 13 (by decide) (choices 1) [1,2,8,16] r5170 c5170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1708
  · exact u1709
  · exact u1710
  · exact u1711

def b5171 : PairBound 9 := { available := 240, camps := [], pairs := [(2,1)], upper := (rows 277 98 140 11 18 240 240 240 496), lower := (rows 277 98 140 11 18 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 81 145 273), good := (rows 501 96 140 493 496 32 64 128 256) }] }

theorem u5171 : Upper (D 1) (R 1) [276,96,136,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5171
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5172 : Route 9 := (fun mask => (mask,id))

def c5172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5172 : Upper (D 1) (R 1) [276,96,136,3,32] 13 := by
  apply FastRouting.sound _ _ [276,96,136,3,32] 13 (by decide) (choices 1) [2,16,64,128] r5172 c5172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1712
  · exact u1713
  · exact u1714
  · exact u1715

def b5173 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 140 11 144 114 114 242 370), lower := (rows 277 98 140 11 144 32 64 128 256), losses := [] }

theorem u5173 : Upper (D 1) (R 1) [276,96,136,3,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5173
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5174 : Route 9 := (fun mask => (mask,id))

def c5174 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u5174 : Upper (D 1) (R 1) [276,96,136,33,2] 13 := by
  apply FastRouting.sound _ _ [276,96,136,33,2] 13 (by decide) (choices 1) [2,16,64,128] r5174 c5174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1716
  · exact u1717
  · exact u1718
  · exact u1719

def r5175 : Route 9 := (fun mask => (mask,id))

def c5175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5175 : Upper (D 1) (R 1) [276,96,136,33,64] 13 := by
  apply FastRouting.sound _ _ [276,96,136,33,64] 13 (by decide) (choices 1) [2,16,128] r5175 c5175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1720
  · exact u1721
  · exact u1722

def b5176 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 140 41 144 114 82 210 338), lower := (rows 277 98 140 41 144 32 64 128 256), losses := [] }

theorem u5176 : Upper (D 1) (R 1) [276,96,136,33,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5176
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5177 : Route 9 := (fun mask => (mask,id))

def c5177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u5177 : Upper (D 1) (R 1) [276,96,160,3,2] 13 := by
  apply FastRouting.sound _ _ [276,96,160,3,2] 13 (by decide) (choices 1) [8,16,64,128] r5177 c5177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1723
  · exact u1724
  · exact u1725
  · exact u1726

def b5178 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 277 98 164 11 24 242 210 210 466), lower := (rows 277 98 164 11 24 32 64 128 256), losses := [] }

theorem u5178 : Upper (D 1) (R 1) [276,96,160,3,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5178
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5179 : Route 9 := (fun mask => (mask,id))

def c5179 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5179 : Upper (D 1) (R 1) [276,96,160,3,64] 13 := by
  apply FastRouting.sound _ _ [276,96,160,3,64] 13 (by decide) (choices 1) [2,8,16,128] r5179 c5179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1727
  · exact u1728
  · exact u1729
  · exact u1730

def b5180 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 164 11 144 122 90 218 346), lower := (rows 277 98 164 11 144 32 64 128 256), losses := [] }

theorem u5180 : Upper (D 1) (R 1) [276,96,160,3,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5180
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5181 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 277 98 164 26 17 234 202 202 458), lower := (rows 277 98 164 26 17 32 64 128 256), losses := [] }

theorem u5181 : Upper (D 1) (R 1) [276,96,160,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5181
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5182 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 277 98 164 26 18 233 201 201 457), lower := (rows 277 98 164 26 18 32 64 128 256), losses := [] }

theorem u5182 : Upper (D 1) (R 1) [276,96,160,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5182
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5183 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 277 98 164 26 24 227 195 195 451), lower := (rows 277 98 164 26 24 32 64 128 256), losses := [] }

theorem u5183 : Upper (D 1) (R 1) [276,96,160,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5183
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5184 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 277 98 164 26 80 171 203 139 395), lower := (rows 277 98 164 26 80 32 64 128 256), losses := [] }

theorem u5184 : Upper (D 1) (R 1) [276,96,160,18,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5184
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5185 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 164 26 144 107 75 203 331), lower := (rows 277 98 164 26 144 32 64 128 256), losses := [] }

theorem u5185 : Upper (D 1) (R 1) [276,96,160,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5185
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5186 : Route 9 := (fun mask => (mask,id))

def c5186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5186 : Upper (D 1) (R 1) [276,96,160,65,2] 13 := by
  apply FastRouting.sound _ _ [276,96,160,65,2] 13 (by decide) (choices 1) [2,8,16,128] r5186 c5186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1731
  · exact u1732
  · exact u1733
  · exact u1734

def b5187 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 98 164 73 24 178 210 146 402), lower := (rows 277 98 164 73 24 32 64 128 256), losses := [] }

theorem u5187 : Upper (D 1) (R 1) [276,96,160,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5187
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5188 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 164 73 144 58 90 154 282), lower := (rows 277 98 164 73 144 32 64 128 256), losses := [] }

theorem u5188 : Upper (D 1) (R 1) [276,96,160,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5188
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5189 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 277 98 164 88 17 170 202 138 394), lower := (rows 277 98 164 88 17 32 64 128 256), losses := [] }

theorem u5189 : Upper (D 1) (R 1) [276,96,160,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5189
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5190 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 277 98 164 88 18 171 203 139 395), lower := (rows 277 98 164 88 18 32 64 128 256), losses := [] }

theorem u5190 : Upper (D 1) (R 1) [276,96,160,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5190
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5191 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 277 98 164 88 24 163 195 131 387), lower := (rows 277 98 164 88 24 32 64 128 256), losses := [] }

theorem u5191 : Upper (D 1) (R 1) [276,96,160,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5191
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5192 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 164 88 144 43 75 139 267), lower := (rows 277 98 164 88 144 32 64 128 256), losses := [] }

theorem u5192 : Upper (D 1) (R 1) [276,96,160,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5192
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5193 : PairBound 9 := { available := 90, camps := [], pairs := [], upper := (rows 277 98 164 138 17 122 90 218 346), lower := (rows 277 98 164 138 17 32 64 128 256), losses := [] }

theorem u5193 : Upper (D 1) (R 1) [276,96,160,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5193
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5194 : Route 9 := (fun mask => (mask,id))

def c5194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5194 : Upper (D 1) (R 1) [276,96,160,130,2] 13 := by
  apply FastRouting.sound _ _ [276,96,160,130,2] 13 (by decide) (choices 1) [1,8,16,64] r5194 c5194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1735
  · exact u1736
  · exact u1737
  · exact u1738

def b5195 : PairBound 9 := { available := 83, camps := [], pairs := [], upper := (rows 277 98 164 138 24 115 83 211 339), lower := (rows 277 98 164 138 24 32 64 128 256), losses := [] }

theorem u5195 : Upper (D 1) (R 1) [276,96,160,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5195
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5196 : Route 9 := (fun mask => (mask,id))

def c5196 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5196 : Upper (D 1) (R 1) [276,96,160,130,64] 13 := by
  apply FastRouting.sound _ _ [276,96,160,130,64] 13 (by decide) (choices 1) [1,2,8,16] r5196 c5196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1739
  · exact u1740
  · exact u1741
  · exact u1742

def b5197 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 277 98 164 152 17 106 74 202 330), lower := (rows 277 98 164 152 17 32 64 128 256), losses := [] }

theorem u5197 : Upper (D 1) (R 1) [276,96,160,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5197
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5198 : Route 9 := (fun mask => (mask,id))

def c5198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5198 : Upper (D 1) (R 1) [276,96,160,144,2] 13 := by
  apply FastRouting.sound _ _ [276,96,160,144,2] 13 (by decide) (choices 1) [1,2,8,64] r5198 c5198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1743
  · exact u1744
  · exact u1745
  · exact u1746

def b5199 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 277 98 164 152 24 99 67 195 323), lower := (rows 277 98 164 152 24 32 64 128 256), losses := [] }

theorem u5199 : Upper (D 1) (R 1) [276,96,160,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5199
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5200 : Route 9 := (fun mask => (mask,id))

def c5200 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5200 : Upper (D 1) (R 1) [276,96,160,144,64] 13 := by
  apply FastRouting.sound _ _ [276,96,160,144,64] 13 (by decide) (choices 1) [1,2,8] r5200 c5200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1747
  · exact u1748
  · exact u1749

def b5201 : PairBound 9 := { available := 26, camps := [], pairs := [], upper := (rows 277 98 164 200 17 58 90 154 282), lower := (rows 277 98 164 200 17 32 64 128 256), losses := [] }

theorem u5201 : Upper (D 1) (R 1) [276,96,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5201
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5202 : Route 9 := (fun mask => (mask,id))

def c5202 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5202 : Upper (D 1) (R 1) [276,96,160,192,2] 13 := by
  apply FastRouting.sound _ _ [276,96,160,192,2] 13 (by decide) (choices 1) [1,2,8,16] r5202 c5202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1750
  · exact u1751
  · exact u1752
  · exact u1753

def b5203 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 277 98 164 200 24 51 83 147 275), lower := (rows 277 98 164 200 24 32 64 128 256), losses := [] }

theorem u5203 : Upper (D 1) (R 1) [276,96,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5203
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5204 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 14 88 18 224 224 224 480), lower := (rows 305 7 14 88 18 32 64 128 256), losses := [] }

theorem u5204 : Upper (D 1) (R 1) [304,5,10,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5204
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5205 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 14 88 48 226 194 194 450), lower := (rows 305 7 14 88 48 32 64 128 256), losses := [] }

theorem u5205 : Upper (D 1) (R 1) [304,5,10,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5205
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5206 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 14 88 80 162 226 162 418), lower := (rows 305 7 14 88 80 32 64 128 256), losses := [] }

theorem u5206 : Upper (D 1) (R 1) [304,5,10,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5206
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5207 : Route 9 := (fun mask => (mask,id))

def c5207 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5207 : Upper (D 1) (R 1) [304,5,10,80,128] 13 := by
  apply FastRouting.sound _ _ [304,5,10,80,128] 13 (by decide) (choices 1) [2,64,128] r5207 c5207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1754
  · exact u1755
  · exact u1756

def b5208 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 14 200 18 240 240 240 496), lower := (rows 305 7 14 200 18 32 64 128 256), losses := [] }

theorem u5208 : Upper (D 1) (R 1) [304,5,10,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5208
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5209 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 14 200 48 242 210 210 466), lower := (rows 305 7 14 200 48 32 64 128 256), losses := [] }

theorem u5209 : Upper (D 1) (R 1) [304,5,10,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5209
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m5210_2 : Upper (D 1) (R 1) [304,5,10,192,64,2] 13 :=
  permutation_upper _ _ _ [304,5,10,192,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1757

theorem m5210_16 : Upper (D 1) (R 1) [304,5,10,192,64,16] 13 :=
  permutation_upper _ _ _ [304,5,10,192,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1758

def r5210 : Route 9 := (fun mask => (mask,id))

def c5210 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5210 : Upper (D 1) (R 1) [304,5,10,192,64] 13 := by
  apply FastRouting.sound _ _ [304,5,10,192,64] 13 (by decide) (choices 1) [2,16,128] r5210 c5210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5210_2
  · exact m5210_16
  · exact u1759

def b5211 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 7 70 88 18 168 232 168 424), lower := (rows 305 7 70 88 18 32 64 128 256), losses := [] }

theorem u5211 : Upper (D 1) (R 1) [304,5,66,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5211
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5212 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 7 70 88 24 162 226 162 418), lower := (rows 305 7 70 88 24 32 64 128 256), losses := [] }

theorem u5212 : Upper (D 1) (R 1) [304,5,66,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5212
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5213 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 70 88 48 170 202 138 394), lower := (rows 305 7 70 88 48 32 64 128 256), losses := [] }

theorem u5213 : Upper (D 1) (R 1) [304,5,66,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5213
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5214 : Route 9 := (fun mask => (mask,id))

def c5214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5214 : Upper (D 1) (R 1) [304,5,66,80,128] 13 := by
  apply FastRouting.sound _ _ [304,5,66,80,128] 13 (by decide) (choices 1) [2,8,128] r5214 c5214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1760
  · exact u1761
  · exact u1762

def b5215 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 70 152 18 232 232 232 488), lower := (rows 305 7 70 152 18 32 64 128 256), losses := [] }

theorem u5215 : Upper (D 1) (R 1) [304,5,66,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5215
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5216 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 7 70 152 24 226 226 226 482), lower := (rows 305 7 70 152 24 32 64 128 256), losses := [] }

theorem u5216 : Upper (D 1) (R 1) [304,5,66,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5216
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5217 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 70 152 48 234 202 202 458), lower := (rows 305 7 70 152 48 32 64 128 256), losses := [] }

theorem u5217 : Upper (D 1) (R 1) [304,5,66,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5217
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5218 : Route 9 := (fun mask => (mask,id))

def c5218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5218 : Upper (D 1) (R 1) [304,5,66,144,64] 13 := by
  apply FastRouting.sound _ _ [304,5,66,144,64] 13 (by decide) (choices 1) [2,8,128] r5218 c5218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1763
  · exact u1764
  · exact u1765

def b5219 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 305 7 70 152 144 106 106 234 362), lower := (rows 305 7 70 152 144 32 64 128 256), losses := [] }

theorem u5219 : Upper (D 1) (R 1) [304,5,66,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5219
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u5219
end Delivery.IrregularNine14.P01

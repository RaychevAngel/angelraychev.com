import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0028
import IrregularNine14P07C0029

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13140 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(2,0),(3,6),(4,6)], upper := (rows 7 42 84 137 273 96 226 162 418), lower := (rows 7 42 84 137 273 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 127 75 139 267), good := (rows 486 490 116 490 500 96 96 128 256) },{ target := 6, region := (rows 1 2 4 9 17 32 0 130 258), good := (rows 415 426 20 153 281 32 0 128 256) }] }

theorem u13140 : Upper (D 7) (R 7) [6,40,80,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13141 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 84 137 273 160 98 226 354), lower := (rows 7 42 84 137 273 160 64 128 256), losses := [] }

theorem u13141 : Upper (D 7) (R 7) [6,40,80,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13142 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 84 137 274 33 224 224 480), lower := (rows 7 42 84 137 274 33 64 128 256), losses := [] }

theorem u13142 : Upper (D 7) (R 7) [6,40,80,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13143 : Route 9 := (fun mask => (mask,id))

def c13143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13143 : Upper (D 7) (R 7) [6,40,80,129,258,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,258,64] 13 (by decide) (choices 1) [1,32,128] r13143 c13143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1697
  · exact u1698
  · exact u1699

def b13144 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 84 137 274 160 97 225 353), lower := (rows 7 42 84 137 274 160 64 128 256), losses := [] }

theorem u13144 : Upper (D 7) (R 7) [6,40,80,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13145 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 84 137 304 33 194 194 450), lower := (rows 7 42 84 137 304 33 64 128 256), losses := [] }

theorem u13145 : Upper (D 7) (R 7) [6,40,80,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13146 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 7 42 84 137 304 34 193 193 449), lower := (rows 7 42 84 137 304 34 64 128 256), losses := [] }

theorem u13146 : Upper (D 7) (R 7) [6,40,80,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13147 : Route 9 := (fun mask => (mask,id))

def c13147 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13147 : Upper (D 7) (R 7) [6,40,80,129,288,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,288,64] 13 (by decide) (choices 1) [1,2,128] r13147 c13147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1700
  · exact u1701
  · exact u1702

def b13148 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 84 137 304 160 67 195 323), lower := (rows 7 42 84 137 304 160 64 128 256), losses := [] }

theorem u13148 : Upper (D 7) (R 7) [6,40,80,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13149 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 84 137 400 33 98 226 354), lower := (rows 7 42 84 137 400 33 64 128 256), losses := [] }

theorem u13149 : Upper (D 7) (R 7) [6,40,80,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13150 : Route 9 := (fun mask => (mask,id))

def c13150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13150 : Upper (D 7) (R 7) [6,40,80,129,384,2] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,384,2] 13 (by decide) (choices 1) [1,32] r13150 c13150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1703
  · exact u1704

def r13151 : Route 9 := (fun mask => (mask,id))

def c13151 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13151 : Upper (D 7) (R 7) [6,40,80,129,384,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,384,64] 13 (by decide) (choices 1) [1,2,32] r13151 c13151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1705
  · exact u1706
  · exact u1707

def b13152 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 42, targets := 64 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 42 84 138 145 33 352 480 352), lower := (rows 7 42 84 138 145 33 64 128 256), losses := [] }

theorem u13152 : Upper (D 7) (R 7) [6,40,80,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13153 : Route 9 := (fun mask => (mask,id))

def c13153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u13153 : Upper (D 7) (R 7) [6,40,80,130,129,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,129,64] 13 (by decide) (choices 1) [1,32,256] r13153 c13153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1708
  · exact u1709
  · exact u1710

def b13154 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 356, targets := 128 }], pairs := [(2,1),(2,7),(4,1)], upper := (rows 7 42 84 138 145 288 97 225 353), lower := (rows 7 42 84 138 145 288 64 128 256), losses := [] }

theorem u13154 : Upper (D 7) (R 7) [6,40,80,130,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13154 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13155 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 5, region := 202, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 84 138 273 33 224 224 480), lower := (rows 7 42 84 138 273 33 64 128 256), losses := [] }

theorem u13155 : Upper (D 7) (R 7) [6,40,80,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13156 : Route 9 := (fun mask => (mask,id))

def c13156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13156 : Upper (D 7) (R 7) [6,40,80,130,257,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,257,64] 13 (by decide) (choices 1) [1,32,128] r13156 c13156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1711
  · exact u1712
  · exact u1713

def b13157 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 84 138 273 160 97 225 353), lower := (rows 7 42 84 138 273 160 64 128 256), losses := [] }

theorem u13157 : Upper (D 7) (R 7) [6,40,80,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13158 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(2,5),(3,5),(4,1)], upper := (rows 7 42 84 138 304 33 193 193 449), lower := (rows 7 42 84 138 304 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 11 16 0 97 161 289), good := (rows 463 458 84 138 468 457 64 128 256) }] }

theorem u13158 : Upper (D 7) (R 7) [6,40,80,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13159 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 136, targets := 32 },{ cop := 0, region := 136, targets := 64 }], pairs := [(2,1),(3,5),(3,6),(4,1)], upper := (rows 7 42 84 138 304 96 193 129 385), lower := (rows 7 42 84 138 304 96 64 128 256), losses := [] }

theorem u13159 : Upper (D 7) (R 7) [6,40,80,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13160 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 84 138 304 160 65 193 321), lower := (rows 7 42 84 138 304 160 64 128 256), losses := [] }

theorem u13160 : Upper (D 7) (R 7) [6,40,80,130,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13161 : Route 9 := (fun mask => (mask,id))

def c13161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13161 : Upper (D 7) (R 7) [6,40,80,130,384,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,384,1] 13 (by decide) (choices 1) [1,32] r13161 c13161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1714
  · exact u1715

def r13162 : Route 9 := (fun mask => (mask,id))

def c13162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13162 : Upper (D 7) (R 7) [6,40,80,130,384,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,384,64] 13 (by decide) (choices 1) [1,32] r13162 c13162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1716
  · exact u1717

def b13163 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 84 200 49 33 450 386 386), lower := (rows 7 42 84 200 49 33 64 128 256), losses := [] }

theorem u13163 : Upper (D 7) (R 7) [6,40,80,192,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13164 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 84 200 49 34 449 385 385), lower := (rows 7 42 84 200 49 34 64 128 256), losses := [] }

theorem u13164 : Upper (D 7) (R 7) [6,40,80,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13165 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 84 200 49 160 323 387 259), lower := (rows 7 42 84 200 49 160 64 128 256), losses := [] }

theorem u13165 : Upper (D 7) (R 7) [6,40,80,192,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13166 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(2,5),(3,5),(4,6)], upper := (rows 7 42 84 200 49 288 195 131 387), lower := (rows 7 42 84 200 49 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 25 16 0 65 129 257), good := (rows 463 10 92 200 477 256 64 128 256) }] }

theorem u13166 : Upper (D 7) (R 7) [6,40,80,192,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13166 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13167 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 458, targets := 1 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(2,7),(3,0),(4,6)], upper := (rows 7 42 84 200 145 33 354 418 290), lower := (rows 7 42 84 200 145 33 64 128 256), losses := [{ target := 7, region := (rows 1 2 20 8 16 49 67 0 259), good := (rows 359 362 116 72 373 353 64 0 256) }] }

theorem u13167 : Upper (D 7) (R 7) [6,40,80,192,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13168 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 42 84 200 145 34 353 417 289), lower := (rows 7 42 84 200 145 34 64 128 256), losses := [] }

theorem u13168 : Upper (D 7) (R 7) [6,40,80,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13169 : Route 9 := (fun mask => (mask,id))

def c13169 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13169 : Upper (D 7) (R 7) [6,40,80,192,129,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,129,256] 13 (by decide) (choices 1) [1,2,32] r13169 c13169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1718
  · exact u1719
  · exact u1720

def r13170 : Route 9 := (fun mask => (mask,id))

def c13170 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u13170 : Upper (D 7) (R 7) [6,40,80,192,160,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,160,1] 13 (by decide) (choices 1) [1,2,256] r13170 c13170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1721
  · exact u1722
  · exact u1723

def b13171 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 54, targets := 1 },{ cop := 0, region := 456, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 42 84 200 176 34 321 385 257), lower := (rows 7 42 84 200 176 34 64 128 256), losses := [] }

theorem u13171 : Upper (D 7) (R 7) [6,40,80,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13172 : Route 9 := (fun mask => (mask,id))

def c13172 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13172 : Upper (D 7) (R 7) [6,40,80,192,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,160,256] 13 (by decide) (choices 1) [1,2] r13172 c13172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1724
  · exact u1725

def r13173 : Route 9 := (fun mask => (mask,id))

def c13173 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13173 : Upper (D 7) (R 7) [6,40,80,192,257,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,257,1] 13 (by decide) (choices 1) [2,32,128] r13173 c13173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1726
  · exact u1727
  · exact u1728

def b13174 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 42 84 200 273 34 225 161 417), lower := (rows 7 42 84 200 273 34 64 128 256), losses := [] }

theorem u13174 : Upper (D 7) (R 7) [6,40,80,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13175 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 84 200 273 160 99 163 291), lower := (rows 7 42 84 200 273 160 64 128 256), losses := [] }

theorem u13175 : Upper (D 7) (R 7) [6,40,80,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13176 : Route 9 := (fun mask => (mask,id))

def c13176 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13176 : Upper (D 7) (R 7) [6,40,80,192,258,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,258,1] 13 (by decide) (choices 1) [1,32,128] r13176 c13176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1729
  · exact u1730
  · exact u1731

def b13177 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 84 200 274 160 97 161 289), lower := (rows 7 42 84 200 274 160 64 128 256), losses := [] }

theorem u13177 : Upper (D 7) (R 7) [6,40,80,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13178 : Route 9 := (fun mask => (mask,id))

def c13178 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13178 : Upper (D 7) (R 7) [6,40,80,192,288,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,288,1] 13 (by decide) (choices 1) [1,2,128] r13178 c13178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1732
  · exact u1733
  · exact u1734

def b13179 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 7 42 84 200 304 34 193 129 385), lower := (rows 7 42 84 200 304 34 64 128 256), losses := [] }

theorem u13179 : Upper (D 7) (R 7) [6,40,80,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13180 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 84 200 304 160 67 131 259), lower := (rows 7 42 84 200 304 160 64 128 256), losses := [] }

theorem u13180 : Upper (D 7) (R 7) [6,40,80,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13181 : Route 9 := (fun mask => (mask,id))

def c13181 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13181 : Upper (D 7) (R 7) [6,40,80,192,384,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,384,1] 13 (by decide) (choices 1) [1,2,32] r13181 c13181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1735
  · exact u1736
  · exact u1737

def b13182 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 42 84 200 400 34 97 161 289), lower := (rows 7 42 84 200 400 34 64 128 256), losses := [] }

theorem u13182 : Upper (D 7) (R 7) [6,40,80,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13183 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 34, targets := 192 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 7 42 84 265 145 34 224 224 480), lower := (rows 7 42 84 265 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 43 123 187 315), good := (rows 486 490 468 490 500 482 64 128 256) }] }

theorem u13183 : Upper (D 7) (R 7) [6,40,80,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13184 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(2,0),(3,6),(4,6)], upper := (rows 7 42 84 265 145 96 226 162 418), lower := (rows 7 42 84 265 145 96 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 127 75 139 267), good := (rows 486 490 116 490 500 96 96 128 256) },{ target := 6, region := (rows 1 2 4 9 17 32 0 130 258), good := (rows 415 426 20 281 153 32 0 128 256) }] }

theorem u13184 : Upper (D 7) (R 7) [6,40,80,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13185 : Route 9 := (fun mask => (mask,id))

def c13185 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13185 : Upper (D 7) (R 7) [6,40,80,257,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,80,257,129,128] 13 (by decide) (choices 1) [2,32] r13185 c13185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1738
  · exact u1739

def b13186 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 84 265 146 33 224 224 480), lower := (rows 7 42 84 265 146 33 64 128 256), losses := [] }

theorem u13186 : Upper (D 7) (R 7) [6,40,80,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13187 : Route 9 := (fun mask => (mask,id))

def c13187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13187 : Upper (D 7) (R 7) [6,40,80,257,130,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,257,130,64] 13 (by decide) (choices 1) [1,32,128] r13187 c13187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1740
  · exact u1741
  · exact u1742

def r13188 : Route 9 := (fun mask => (mask,id))

def c13188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13188 : Upper (D 7) (R 7) [6,40,80,257,130,128] 13 := by
  apply FastRouting.sound _ _ [6,40,80,257,130,128] 13 (by decide) (choices 1) [1,32] r13188 c13188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1743
  · exact u1744

def b13189 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 84 265 176 33 194 194 450), lower := (rows 7 42 84 265 176 33 64 128 256), losses := [] }

theorem u13189 : Upper (D 7) (R 7) [6,40,80,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13190 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 456, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(3,1)], upper := (rows 7 42 84 265 176 34 193 193 449), lower := (rows 7 42 84 265 176 34 64 128 256), losses := [] }

theorem u13190 : Upper (D 7) (R 7) [6,40,80,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13191 : Route 9 := (fun mask => (mask,id))

def c13191 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13191 : Upper (D 7) (R 7) [6,40,80,257,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,257,160,64] 13 (by decide) (choices 1) [1,2,128] r13191 c13191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1745
  · exact u1746
  · exact u1747

def b13192 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 84 265 176 160 67 195 323), lower := (rows 7 42 84 265 176 160 64 128 256), losses := [] }

theorem u13192 : Upper (D 7) (R 7) [6,40,80,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13193 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 84 266 145 33 224 224 480), lower := (rows 7 42 84 266 145 33 64 128 256), losses := [] }

theorem u13193 : Upper (D 7) (R 7) [6,40,80,258,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13194 : Route 9 := (fun mask => (mask,id))

def c13194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13194 : Upper (D 7) (R 7) [6,40,80,258,129,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,258,129,64] 13 (by decide) (choices 1) [1,32,128] r13194 c13194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1748
  · exact u1749
  · exact u1750

def r13195 : Route 9 := (fun mask => (mask,id))

def c13195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13195 : Upper (D 7) (R 7) [6,40,80,258,129,128] 13 := by
  apply FastRouting.sound _ _ [6,40,80,258,129,128] 13 (by decide) (choices 1) [1,32] r13195 c13195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1751
  · exact u1752

def b13196 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 456, targets := 32 }], pairs := [(2,1),(2,5),(3,5),(4,1)], upper := (rows 7 42 84 266 176 33 193 193 449), lower := (rows 7 42 84 266 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 11 16 0 97 161 289), good := (rows 463 458 84 266 468 457 64 128 256) }] }

theorem u13196 : Upper (D 7) (R 7) [6,40,80,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13197 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 392, targets := 32 },{ cop := 0, region := 392, targets := 64 }], pairs := [(2,1),(3,5),(3,6),(4,1)], upper := (rows 7 42 84 266 176 96 193 129 385), lower := (rows 7 42 84 266 176 96 64 128 256), losses := [] }

theorem u13197 : Upper (D 7) (R 7) [6,40,80,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13198 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 84 266 176 160 65 193 321), lower := (rows 7 42 84 266 176 160 64 128 256), losses := [] }

theorem u13198 : Upper (D 7) (R 7) [6,40,80,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13199 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 84 328 49 33 194 130 386), lower := (rows 7 42 84 328 49 33 64 128 256), losses := [] }

theorem u13199 : Upper (D 7) (R 7) [6,40,80,320,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13199
end Delivery.IrregularNine14.P07

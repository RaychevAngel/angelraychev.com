import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0102

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21120 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 14 73 176 48 193 193 449), lower := (rows 35 262 14 73 176 48 64 128 256), losses := [] }

theorem u21120 : Upper (D 7) (R 7) [34,260,10,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21120 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21121 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,6),(3,1),(4,1),(4,6)], upper := (rows 35 262 14 73 176 96 209 145 401), lower := (rows 35 262 14 73 176 96 64 128 256), losses := [{ target := 6, region := (rows 1 14 12 8 17 32 0 137 265), good := (rows 435 262 398 415 176 32 0 128 256) }] }

theorem u21121 : Upper (D 7) (R 7) [34,260,10,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21122 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 14 73 176 160 81 209 337), lower := (rows 35 262 14 73 176 160 64 128 256), losses := [] }

theorem u21122 : Upper (D 7) (R 7) [34,260,10,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21123 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 14 73 208 33 240 176 432), lower := (rows 35 262 14 73 208 33 64 128 256), losses := [] }

theorem u21123 : Upper (D 7) (R 7) [34,260,10,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21124 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 }], pairs := [(1,6),(3,1),(4,1)], upper := (rows 35 262 14 73 208 48 225 161 417), lower := (rows 35 262 14 73 208 48 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 16 48 0 129 257), good := (rows 419 262 14 399 176 48 0 128 256) }] }

theorem u21124 : Upper (D 7) (R 7) [34,260,10,65,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21124 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21125 : Route 9 := (fun mask => (mask,id))

def c21125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21125 : Upper (D 7) (R 7) [34,260,10,65,192,128] 13 := by
  apply FastRouting.sound _ _ [34,260,10,65,192,128] 13 (by decide) (choices 1) [1,16,32] r21125 c21125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6146
  · exact u6147
  · exact u6148

def b21126 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 14 88 145 33 224 224 480), lower := (rows 35 262 14 88 145 33 64 128 256), losses := [] }

theorem u21126 : Upper (D 7) (R 7) [34,260,10,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21127 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,7),(3,1),(4,1),(4,6)], upper := (rows 35 262 14 88 145 96 225 161 417), lower := (rows 35 262 14 88 145 96 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 8 16 104 64 0 256), good := (rows 35 263 47 120 17 96 96 0 256) }] }

theorem u21127 : Upper (D 7) (R 7) [34,260,10,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21128 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 216, targets := 2 }], pairs := [(1,7),(2,7),(3,1),(4,1)], upper := (rows 35 262 14 88 145 160 97 225 353), lower := (rows 35 262 14 88 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 18 28 24 16 32 65 0 257), good := (rows 355 262 14 94 351 32 64 0 256) }] }

theorem u21128 : Upper (D 7) (R 7) [34,260,10,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21129 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 14 88 176 33 193 193 449), lower := (rows 35 262 14 88 176 33 64 128 256), losses := [] }

theorem u21129 : Upper (D 7) (R 7) [34,260,10,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21130 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,7),(3,1),(4,1),(4,6)], upper := (rows 35 262 14 88 176 96 193 129 385), lower := (rows 35 262 14 88 176 96 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 8 16 104 64 0 256), good := (rows 35 263 47 120 48 96 96 0 256) }] }

theorem u21130 : Upper (D 7) (R 7) [34,260,10,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21131 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 14 88 176 160 65 193 321), lower := (rows 35 262 14 88 176 160 64 128 256), losses := [] }

theorem u21131 : Upper (D 7) (R 7) [34,260,10,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21132 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 14 104 81 33 208 144 400), lower := (rows 35 262 14 104 81 33 64 128 256), losses := [] }

theorem u21132 : Upper (D 7) (R 7) [34,260,10,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21133 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 262 14 104 81 48 193 129 385), lower := (rows 35 262 14 104 81 48 64 128 256), losses := [] }

theorem u21133 : Upper (D 7) (R 7) [34,260,10,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21133 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21134 : Route 9 := (fun mask => (mask,id))

def c21134 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21134 : Upper (D 7) (R 7) [34,260,10,96,65,128] 13 := by
  apply FastRouting.sound _ _ [34,260,10,96,65,128] 13 (by decide) (choices 1) [1,16,128] r21134 c21134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6149
  · exact u6150
  · exact u6151

def b21135 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 14 104 145 33 208 208 464), lower := (rows 35 262 14 104 145 33 64 128 256), losses := [] }

theorem u21135 : Upper (D 7) (R 7) [34,260,10,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21136 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 35 262 14 104 145 48 193 193 449), lower := (rows 35 262 14 104 145 48 64 128 256), losses := [] }

theorem u21136 : Upper (D 7) (R 7) [34,260,10,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21136 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21137 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 35 262 14 104 145 96 209 145 401), lower := (rows 35 262 14 104 145 96 64 128 256), losses := [] }

theorem u21137 : Upper (D 7) (R 7) [34,260,10,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21138 : Route 9 := (fun mask => (mask,id))

def c21138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21138 : Upper (D 7) (R 7) [34,260,10,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,10,96,129,128] 13 (by decide) (choices 1) [1,16] r21138 c21138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6152
  · exact u6153

def b21139 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 14 104 208 33 209 145 401), lower := (rows 35 262 14 104 208 33 64 128 256), losses := [] }

theorem u21139 : Upper (D 7) (R 7) [34,260,10,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21140 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 262 14 104 208 48 193 129 385), lower := (rows 35 262 14 104 208 48 64 128 256), losses := [] }

theorem u21140 : Upper (D 7) (R 7) [34,260,10,96,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21140 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21141 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 40, targets := 1 }], pairs := [(3,0),(3,1),(4,1),(4,5)], upper := (rows 35 262 14 104 208 160 81 145 273), lower := (rows 35 262 14 104 208 160 64 128 256), losses := [] }

theorem u21141 : Upper (D 7) (R 7) [34,260,10,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21142 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 14 200 81 33 240 176 432), lower := (rows 35 262 14 200 81 33 64 128 256), losses := [] }

theorem u21142 : Upper (D 7) (R 7) [34,260,10,192,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21143 : Route 9 := (fun mask => (mask,id))

def c21143 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21143 : Upper (D 7) (R 7) [34,260,10,192,65,16] 13 := by
  apply FastRouting.sound _ _ [34,260,10,192,65,16] 13 (by decide) (choices 1) [1,32,128] r21143 c21143
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6154
  · exact u6155
  · exact u6156

def b21144 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 80, targets := 128 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 262 14 200 81 160 113 177 305), lower := (rows 35 262 14 200 81 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 184 0 144 272), good := (rows 35 263 47 168 433 160 0 160 256) }] }

theorem u21144 : Upper (D 7) (R 7) [34,260,10,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21145 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 14 200 112 33 209 145 401), lower := (rows 35 262 14 200 112 33 64 128 256), losses := [] }

theorem u21145 : Upper (D 7) (R 7) [34,260,10,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21146 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 14 200 112 48 193 129 385), lower := (rows 35 262 14 200 112 48 64 128 256), losses := [] }

theorem u21146 : Upper (D 7) (R 7) [34,260,10,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21146 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21147 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 80, targets := 128 },{ cop := 3, region := 48, targets := 1 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 35 262 14 200 112 160 81 145 273), lower := (rows 35 262 14 200 112 160 64 128 256), losses := [] }

theorem u21147 : Upper (D 7) (R 7) [34,260,10,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21148 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 262 28 73 82 33 224 160 416), lower := (rows 35 262 28 73 82 33 64 128 256), losses := [] }

theorem u21148 : Upper (D 7) (R 7) [34,260,24,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21149 : Route 9 := (fun mask => (mask,id))

def c21149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21149 : Upper (D 7) (R 7) [34,260,24,65,66,128] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65,66,128] 13 (by decide) (choices 1) [1,32,128] r21149 c21149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6157
  · exact u6158
  · exact u6159

def b21150 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 52, targets := 130 }], pairs := [(2,1),(2,7),(4,1),(4,7)], upper := (rows 35 262 28 73 112 33 194 130 386), lower := (rows 35 262 28 73 112 33 64 128 256), losses := [] }

theorem u21150 : Upper (D 7) (R 7) [34,260,24,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21151 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 28 73 112 34 193 129 385), lower := (rows 35 262 28 73 112 34 64 128 256), losses := [] }

theorem u21151 : Upper (D 7) (R 7) [34,260,24,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21152 : Route 9 := (fun mask => (mask,id))

def c21152 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21152 : Upper (D 7) (R 7) [34,260,24,65,96,128] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65,96,128] 13 (by decide) (choices 1) [1,2,128] r21152 c21152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6160
  · exact u6161
  · exact u6162

def b21153 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 28 73 145 34 224 224 480), lower := (rows 35 262 28 73 145 34 64 128 256), losses := [] }

theorem u21153 : Upper (D 7) (R 7) [34,260,24,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21154 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 144, targets := 64 },{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0),(1,6),(2,6),(4,6)], upper := (rows 35 262 28 73 145 96 226 162 418), lower := (rows 35 262 28 73 145 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 25 32 0 129 257), good := (rows 435 262 30 415 401 32 0 128 256) }] }

theorem u21154 : Upper (D 7) (R 7) [34,260,24,65,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21155 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 1 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,6),(0,7),(3,1),(4,0)], upper := (rows 35 262 28 73 146 33 224 224 480), lower := (rows 35 262 28 73 146 33 64 128 256), losses := [] }

theorem u21155 : Upper (D 7) (R 7) [34,260,24,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21156 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 200, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,6),(2,6),(3,1),(4,6)], upper := (rows 35 262 28 73 146 96 225 161 417), lower := (rows 35 262 28 73 146 96 64 128 256), losses := [{ target := 6, region := (rows 1 10 12 8 25 32 0 129 257), good := (rows 435 262 30 415 146 32 0 128 256) }] }

theorem u21156 : Upper (D 7) (R 7) [34,260,24,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21157 : Route 9 := (fun mask => (mask,id))

def c21157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21157 : Upper (D 7) (R 7) [34,260,24,65,130,128] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65,130,128] 13 (by decide) (choices 1) [1,32] r21157 c21157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6163
  · exact u6164

def b21158 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 450, targets := 33 }], pairs := [(0,6),(0,7),(1,0),(1,5)], upper := (rows 35 262 28 73 176 33 194 194 450), lower := (rows 35 262 28 73 176 33 64 128 256), losses := [] }

theorem u21158 : Upper (D 7) (R 7) [34,260,24,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21159 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 28 73 176 34 193 193 449), lower := (rows 35 262 28 73 176 34 64 128 256), losses := [] }

theorem u21159 : Upper (D 7) (R 7) [34,260,24,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21160 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,6),(2,6),(3,5),(4,6)], upper := (rows 35 262 28 73 176 96 195 131 387), lower := (rows 35 262 28 73 176 96 64 128 256), losses := [{ target := 6, region := (rows 1 14 12 8 17 32 0 137 265), good := (rows 435 262 414 415 176 32 0 128 256) }] }

theorem u21160 : Upper (D 7) (R 7) [34,260,24,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21161 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 28 73 176 160 67 195 323), lower := (rows 35 262 28 73 176 160 64 128 256), losses := [] }

theorem u21161 : Upper (D 7) (R 7) [34,260,24,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21162 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 1 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(4,0)], upper := (rows 35 262 28 73 208 33 226 162 418), lower := (rows 35 262 28 73 208 33 64 128 256), losses := [] }

theorem u21162 : Upper (D 7) (R 7) [34,260,24,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21163 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 28 73 208 34 225 161 417), lower := (rows 35 262 28 73 208 34 64 128 256), losses := [] }

theorem u21163 : Upper (D 7) (R 7) [34,260,24,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21164 : Route 9 := (fun mask => (mask,id))

def c21164 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21164 : Upper (D 7) (R 7) [34,260,24,65,192,128] 13 := by
  apply FastRouting.sound _ _ [34,260,24,65,192,128] 13 (by decide) (choices 1) [1,2,32] r21164 c21164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6165
  · exact u6166
  · exact u6167

def b21165 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(0,6),(0,7),(3,5),(4,1)], upper := (rows 35 262 28 74 176 33 193 193 449), lower := (rows 35 262 28 74 176 33 64 128 256), losses := [] }

theorem u21165 : Upper (D 7) (R 7) [34,260,24,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21166 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 2 },{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 144, targets := 64 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(3,5),(4,1),(4,6)], upper := (rows 35 262 28 74 176 96 193 129 385), lower := (rows 35 262 28 74 176 96 64 128 256), losses := [] }

theorem u21166 : Upper (D 7) (R 7) [34,260,24,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21167 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 28 74 176 160 65 193 321), lower := (rows 35 262 28 74 176 160 64 128 256), losses := [] }

theorem u21167 : Upper (D 7) (R 7) [34,260,24,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21168 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(4,1)], upper := (rows 35 262 28 74 208 33 225 161 417), lower := (rows 35 262 28 74 208 33 64 128 256), losses := [] }

theorem u21168 : Upper (D 7) (R 7) [34,260,24,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21169 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 2 },{ cop := 0, region := 72, targets := 128 }], pairs := [(0,6),(1,6),(3,7),(4,1)], upper := (rows 35 262 28 74 208 160 97 161 289), lower := (rows 35 262 28 74 208 160 64 128 256), losses := [] }

theorem u21169 : Upper (D 7) (R 7) [34,260,24,66,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21170 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 32 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(4,5)], upper := (rows 35 262 28 104 208 33 195 131 387), lower := (rows 35 262 28 104 208 33 64 128 256), losses := [] }

theorem u21170 : Upper (D 7) (R 7) [34,260,24,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21171 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 28 104 208 34 193 129 385), lower := (rows 35 262 28 104 208 34 64 128 256), losses := [] }

theorem u21171 : Upper (D 7) (R 7) [34,260,24,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21172 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 35 262 28 104 208 160 67 131 259), lower := (rows 35 262 28 104 208 160 64 128 256), losses := [] }

theorem u21172 : Upper (D 7) (R 7) [34,260,24,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21173 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 262 44 25 208 33 194 194 450), lower := (rows 35 262 44 25 208 33 64 128 256), losses := [] }

theorem u21173 : Upper (D 7) (R 7) [34,260,40,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21174 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 262 44 25 208 34 193 193 449), lower := (rows 35 262 44 25 208 34 64 128 256), losses := [] }

theorem u21174 : Upper (D 7) (R 7) [34,260,40,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21175 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,5),(4,5)], upper := (rows 35 262 44 25 208 96 195 131 387), lower := (rows 35 262 44 25 208 96 64 128 256), losses := [] }

theorem u21175 : Upper (D 7) (R 7) [34,260,40,17,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21176 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 262 44 26 208 33 193 193 449), lower := (rows 35 262 44 26 208 33 64 128 256), losses := [] }

theorem u21176 : Upper (D 7) (R 7) [34,260,40,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21177 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(3,5),(4,5)], upper := (rows 35 262 44 26 208 96 193 129 385), lower := (rows 35 262 44 26 208 96 64 128 256), losses := [] }

theorem u21177 : Upper (D 7) (R 7) [34,260,40,18,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21178 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 262 44 73 145 34 208 208 464), lower := (rows 35 262 44 73 145 34 64 128 256), losses := [] }

theorem u21178 : Upper (D 7) (R 7) [34,260,40,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21179 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 35 262 44 73 145 48 194 194 450), lower := (rows 35 262 44 73 145 48 64 128 256), losses := [] }

theorem u21179 : Upper (D 7) (R 7) [34,260,40,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21179 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u21179
end Delivery.IrregularNine14.P07

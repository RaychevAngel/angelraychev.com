import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0018
import IrregularNine14P07C0019

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r12120 : Route 9 := (fun mask => (mask,id))

def c12120 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12120 : Upper (D 7) (R 7) [6,33,65,80,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,65,80,160,256] 13 (by decide) (choices 1) [2,8,128] r12120 c12120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1119
  · exact u1120
  · exact u1121

def b12121 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 88 274 40 224 160 416), lower := (rows 7 35 69 88 274 40 64 128 256), losses := [] }

theorem u12121 : Upper (D 7) (R 7) [6,33,65,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12121 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12122 : Route 9 := (fun mask => (mask,id))

def c12122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12122 : Upper (D 7) (R 7) [6,33,65,80,258,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,80,258,128] 13 (by decide) (choices 1) [8,32,128] r12122 c12122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1122
  · exact u1123
  · exact u1124

def b12123 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 88 304 34 200 136 392), lower := (rows 7 35 69 88 304 34 64 128 256), losses := [] }

theorem u12123 : Upper (D 7) (R 7) [6,33,65,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12124 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 88 304 40 194 130 386), lower := (rows 7 35 69 88 304 40 64 128 256), losses := [] }

theorem u12124 : Upper (D 7) (R 7) [6,33,65,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12124 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12125 : Route 9 := (fun mask => (mask,id))

def c12125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u12125 : Upper (D 7) (R 7) [6,33,65,80,288,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,80,288,128] 13 (by decide) (choices 1) [2,8,128] r12125 c12125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1125
  · exact u1126
  · exact u1127

def b12126 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 88 400 34 232 168 424), lower := (rows 7 35 69 88 400 34 64 128 256), losses := [] }

theorem u12126 : Upper (D 7) (R 7) [6,33,65,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12127 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 88 400 40 226 162 418), lower := (rows 7 35 69 88 400 40 64 128 256), losses := [] }

theorem u12127 : Upper (D 7) (R 7) [6,33,65,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12127 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12128 : Route 9 := (fun mask => (mask,id))

def c12128 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12128 : Upper (D 7) (R 7) [6,33,65,80,384,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,80,384,128] 13 (by decide) (choices 1) [2,8,32] r12128 c12128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1128
  · exact u1129
  · exact u1130

def b12129 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 138 176 40 336 464 336), lower := (rows 7 35 69 138 176 40 64 128 256), losses := [] }

theorem u12129 : Upper (D 7) (R 7) [6,33,65,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12129 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12130 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 69 138 176 48 328 456 328), lower := (rows 7 35 69 138 176 48 64 128 256), losses := [] }

theorem u12130 : Upper (D 7) (R 7) [6,33,65,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12130 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12131 : PairBound 9 := { available := 280, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 138 176 96 344 408 280), lower := (rows 7 35 69 138 176 96 64 128 256), losses := [] }

theorem u12131 : Upper (D 7) (R 7) [6,33,65,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12132 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 368, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 35 69 138 176 288 88 216 344), lower := (rows 7 35 69 138 176 288 64 128 256), losses := [] }

theorem u12132 : Upper (D 7) (R 7) [6,33,65,130,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12132 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12133 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 468, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 69 138 208 40 368 432 304), lower := (rows 7 35 69 138 208 40 64 128 256), losses := [] }

theorem u12133 : Upper (D 7) (R 7) [6,33,65,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12133 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12134 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 138 208 48 360 424 296), lower := (rows 7 35 69 138 208 48 64 128 256), losses := [] }

theorem u12134 : Upper (D 7) (R 7) [6,33,65,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12134 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12135 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 368, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 35 69 138 208 288 120 184 312), lower := (rows 7 35 69 138 208 288 64 128 256), losses := [] }

theorem u12135 : Upper (D 7) (R 7) [6,33,65,130,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12135 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12136 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 196, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 69 138 280 48 224 224 480), lower := (rows 7 35 69 138 280 48 64 128 256), losses := [] }

theorem u12136 : Upper (D 7) (R 7) [6,33,65,130,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12136 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12137 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 138 280 96 240 176 432), lower := (rows 7 35 69 138 280 96 64 128 256), losses := [] }

theorem u12137 : Upper (D 7) (R 7) [6,33,65,130,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12138 : Route 9 := (fun mask => (mask,id))

def c12138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12138 : Upper (D 7) (R 7) [6,33,65,130,264,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,264,128] 13 (by decide) (choices 1) [16,32] r12138 c12138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1131
  · exact u1132

def b12139 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 468, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 69 138 304 40 208 208 464), lower := (rows 7 35 69 138 304 40 64 128 256), losses := [] }

theorem u12139 : Upper (D 7) (R 7) [6,33,65,130,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12139 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12140 : PairBound 9 := { available := 200, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 35 69 138 304 48 200 200 456), lower := (rows 7 35 69 138 304 48 64 128 256), losses := [] }

theorem u12140 : Upper (D 7) (R 7) [6,33,65,130,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12140 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12141 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 138 304 96 216 152 408), lower := (rows 7 35 69 138 304 96 64 128 256), losses := [] }

theorem u12141 : Upper (D 7) (R 7) [6,33,65,130,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12142 : Route 9 := (fun mask => (mask,id))

def c12142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12142 : Upper (D 7) (R 7) [6,33,65,130,288,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,288,128] 13 (by decide) (choices 1) [8,16] r12142 c12142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1133
  · exact u1134

def b12143 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 468, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 69 138 336 40 240 176 432), lower := (rows 7 35 69 138 336 40 64 128 256), losses := [] }

theorem u12143 : Upper (D 7) (R 7) [6,33,65,130,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12143 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12144 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 138 336 48 232 168 424), lower := (rows 7 35 69 138 336 48 64 128 256), losses := [] }

theorem u12144 : Upper (D 7) (R 7) [6,33,65,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12144 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12145 : Route 9 := (fun mask => (mask,id))

def c12145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12145 : Upper (D 7) (R 7) [6,33,65,130,320,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,320,128] 13 (by decide) (choices 1) [8,16,32] r12145 c12145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1135
  · exact u1136
  · exact u1137

def b12146 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 468, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 69 138 400 40 112 240 368), lower := (rows 7 35 69 138 400 40 64 128 256), losses := [] }

theorem u12146 : Upper (D 7) (R 7) [6,33,65,130,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12146 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12147 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 368, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 35 69 138 400 48 104 232 360), lower := (rows 7 35 69 138 400 48 64 128 256), losses := [] }

theorem u12147 : Upper (D 7) (R 7) [6,33,65,130,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12147 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12148 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 138 400 96 120 184 312), lower := (rows 7 35 69 138 400 96 64 128 256), losses := [] }

theorem u12148 : Upper (D 7) (R 7) [6,33,65,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12149 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 196, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 69 152 274 40 224 224 480), lower := (rows 7 35 69 152 274 40 64 128 256), losses := [] }

theorem u12149 : Upper (D 7) (R 7) [6,33,65,144,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12149 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12150 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 152 274 96 232 168 424), lower := (rows 7 35 69 152 274 96 64 128 256), losses := [] }

theorem u12150 : Upper (D 7) (R 7) [6,33,65,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12151 : Route 9 := (fun mask => (mask,id))

def c12151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12151 : Upper (D 7) (R 7) [6,33,65,144,258,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,258,128] 13 (by decide) (choices 1) [8,32] r12151 c12151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1138
  · exact u1139

def b12152 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 152 280 34 224 224 480), lower := (rows 7 35 69 152 280 34 64 128 256), losses := [] }

theorem u12152 : Upper (D 7) (R 7) [6,33,65,144,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12153 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 152 280 96 226 162 418), lower := (rows 7 35 69 152 280 96 64 128 256), losses := [] }

theorem u12153 : Upper (D 7) (R 7) [6,33,65,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12154 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 152 280 160 98 226 354), lower := (rows 7 35 69 152 280 160 64 128 256), losses := [] }

theorem u12154 : Upper (D 7) (R 7) [6,33,65,144,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12155 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 152 304 34 200 200 456), lower := (rows 7 35 69 152 304 34 64 128 256), losses := [] }

theorem u12155 : Upper (D 7) (R 7) [6,33,65,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12156 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 35 69 152 304 40 194 194 450), lower := (rows 7 35 69 152 304 40 64 128 256), losses := [] }

theorem u12156 : Upper (D 7) (R 7) [6,33,65,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12156 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12157 : PairBound 9 := { available := 138, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 152 304 96 202 138 394), lower := (rows 7 35 69 152 304 96 64 128 256), losses := [] }

theorem u12157 : Upper (D 7) (R 7) [6,33,65,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12158 : Route 9 := (fun mask => (mask,id))

def c12158 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12158 : Upper (D 7) (R 7) [6,33,65,144,288,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,288,128] 13 (by decide) (choices 1) [2,8] r12158 c12158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1140
  · exact u1141

def b12159 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 152 336 34 232 168 424), lower := (rows 7 35 69 152 336 34 64 128 256), losses := [] }

theorem u12159 : Upper (D 7) (R 7) [6,33,65,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12160 : Route 9 := (fun mask => (mask,id))

def c12160 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12160 : Upper (D 7) (R 7) [6,33,65,144,320,8] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,320,8] 13 (by decide) (choices 1) [2,32,128] r12160 c12160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1142
  · exact u1143
  · exact u1144

def r12161 : Route 9 := (fun mask => (mask,id))

def c12161 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12161 : Upper (D 7) (R 7) [6,33,65,144,320,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,320,128] 13 (by decide) (choices 1) [2,8,32] r12161 c12161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1145
  · exact u1146
  · exact u1147

def b12162 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 168 208 34 344 408 280), lower := (rows 7 35 69 168 208 34 64 128 256), losses := [] }

theorem u12162 : Upper (D 7) (R 7) [6,33,65,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12163 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 69 168 208 40 338 402 274), lower := (rows 7 35 69 168 208 40 64 128 256), losses := [] }

theorem u12163 : Upper (D 7) (R 7) [6,33,65,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12163 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12164 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 168 208 48 330 394 266), lower := (rows 7 35 69 168 208 48 64 128 256), losses := [] }

theorem u12164 : Upper (D 7) (R 7) [6,33,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12164 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12165 : Route 9 := (fun mask => (mask,id))

def c12165 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12165 : Upper (D 7) (R 7) [6,33,65,160,192,256] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,192,256] 13 (by decide) (choices 1) [2,8,16] r12165 c12165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1148
  · exact u1149
  · exact u1150

def b12166 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 69 168 274 40 208 208 464), lower := (rows 7 35 69 168 274 40 64 128 256), losses := [] }

theorem u12166 : Upper (D 7) (R 7) [6,33,65,160,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12166 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12167 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 35 69 168 274 48 200 200 456), lower := (rows 7 35 69 168 274 48 64 128 256), losses := [] }

theorem u12167 : Upper (D 7) (R 7) [6,33,65,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12167 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12168 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 168 274 96 216 152 408), lower := (rows 7 35 69 168 274 96 64 128 256), losses := [] }

theorem u12168 : Upper (D 7) (R 7) [6,33,65,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12169 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 69 168 274 160 88 216 344), lower := (rows 7 35 69 168 274 160 64 128 256), losses := [] }

theorem u12169 : Upper (D 7) (R 7) [6,33,65,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12170 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 168 280 34 208 208 464), lower := (rows 7 35 69 168 280 34 64 128 256), losses := [] }

theorem u12170 : Upper (D 7) (R 7) [6,33,65,160,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12171 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 35 69 168 280 48 194 194 450), lower := (rows 7 35 69 168 280 48 64 128 256), losses := [] }

theorem u12171 : Upper (D 7) (R 7) [6,33,65,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12171 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12172 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 168 280 96 210 146 402), lower := (rows 7 35 69 168 280 96 64 128 256), losses := [] }

theorem u12172 : Upper (D 7) (R 7) [6,33,65,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12173 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 69 168 280 160 82 210 338), lower := (rows 7 35 69 168 280 160 64 128 256), losses := [] }

theorem u12173 : Upper (D 7) (R 7) [6,33,65,160,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12174 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 168 336 34 216 152 408), lower := (rows 7 35 69 168 336 34 64 128 256), losses := [] }

theorem u12174 : Upper (D 7) (R 7) [6,33,65,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12175 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 69 168 336 40 210 146 402), lower := (rows 7 35 69 168 336 40 64 128 256), losses := [] }

theorem u12175 : Upper (D 7) (R 7) [6,33,65,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12175 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12176 : PairBound 9 := { available := 138, camps := [{ cop := 4, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 168 336 48 202 138 394), lower := (rows 7 35 69 168 336 48 64 128 256), losses := [] }

theorem u12176 : Upper (D 7) (R 7) [6,33,65,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12176 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12177 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 69 168 336 160 90 154 282), lower := (rows 7 35 69 168 336 160 64 128 256), losses := [] }

theorem u12177 : Upper (D 7) (R 7) [6,33,65,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12178 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 69 168 400 34 88 216 344), lower := (rows 7 35 69 168 400 34 64 128 256), losses := [] }

theorem u12178 : Upper (D 7) (R 7) [6,33,65,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12179 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 69 168 400 40 82 210 338), lower := (rows 7 35 69 168 400 40 64 128 256), losses := [] }

theorem u12179 : Upper (D 7) (R 7) [6,33,65,160,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12179 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12179
end Delivery.IrregularNine14.P07

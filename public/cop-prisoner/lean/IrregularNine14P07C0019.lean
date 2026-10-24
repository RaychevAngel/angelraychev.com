import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0000

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1140 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 152 304 160 66 200 328), lower := (rows 7 35 69 152 304 160 66 128 256), losses := [] }

theorem u1140 : Upper (D 7) (R 7) [6,33,65,144,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1141 : Route 9 := (fun mask => (mask,id))

def c1141 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1141 : Upper (D 7) (R 7) [6,33,65,144,288,128,8] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,288,128,8] 13 (by decide) (choices 1) [2,64] r1141 c1141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18
  · exact u19

def b1142 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 152 336 40 66 160 416), lower := (rows 7 35 69 152 336 40 66 128 256), losses := [] }

theorem u1142 : Upper (D 7) (R 7) [6,33,65,144,320,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1142 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1143 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 152 336 40 96 130 386), lower := (rows 7 35 69 152 336 40 96 128 256), losses := [] }

theorem u1143 : Upper (D 7) (R 7) [6,33,65,144,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1143 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1144 : Route 9 := (fun mask => (mask,id))

def c1144 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1144 : Upper (D 7) (R 7) [6,33,65,144,320,8,128] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,320,8,128] 13 (by decide) (choices 1) [2,32] r1144 c1144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20
  · exact u21

def b1145 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 152 336 160 66 168 296), lower := (rows 7 35 69 152 336 160 66 128 256), losses := [] }

theorem u1145 : Upper (D 7) (R 7) [6,33,65,144,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1146 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 69 152 336 160 72 162 290), lower := (rows 7 35 69 152 336 160 72 128 256), losses := [] }

theorem u1146 : Upper (D 7) (R 7) [6,33,65,144,320,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1146 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1147 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 152 336 160 96 138 266), lower := (rows 7 35 69 152 336 160 96 128 256), losses := [] }

theorem u1147 : Upper (D 7) (R 7) [6,33,65,144,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1148 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 168 208 288 66 152 280), lower := (rows 7 35 69 168 208 288 66 128 256), losses := [] }

theorem u1148 : Upper (D 7) (R 7) [6,33,65,160,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1148 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1149 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 69 168 208 288 72 146 274), lower := (rows 7 35 69 168 208 288 72 128 256), losses := [] }

theorem u1149 : Upper (D 7) (R 7) [6,33,65,160,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1149 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1150 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 69 168 208 288 80 138 266), lower := (rows 7 35 69 168 208 288 80 128 256), losses := [] }

theorem u1150 : Upper (D 7) (R 7) [6,33,65,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1150 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1151 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 69 200 274 160 72 176 304), lower := (rows 7 35 69 200 274 160 72 128 256), losses := [] }

theorem u1151 : Upper (D 7) (R 7) [6,33,65,192,258,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1151 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1152 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 200 274 160 80 168 296), lower := (rows 7 35 69 200 274 160 80 128 256), losses := [] }

theorem u1152 : Upper (D 7) (R 7) [6,33,65,192,258,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1152 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1153 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 200 274 160 96 152 280), lower := (rows 7 35 69 200 274 160 96 128 256), losses := [] }

theorem u1153 : Upper (D 7) (R 7) [6,33,65,192,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1154 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 200 280 48 66 160 416), lower := (rows 7 35 69 200 280 48 66 128 256), losses := [] }

theorem u1154 : Upper (D 7) (R 7) [6,33,65,192,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1154 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1155 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 103, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 200 280 48 96 130 386), lower := (rows 7 35 69 200 280 48 96 128 256), losses := [] }

theorem u1155 : Upper (D 7) (R 7) [6,33,65,192,264,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1155 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1156 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 200 280 48 192 162 290), lower := (rows 7 35 69 200 280 48 192 128 256), losses := [] }

theorem u1156 : Upper (D 7) (R 7) [6,33,65,192,264,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1156 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1157 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 200 280 160 66 176 304), lower := (rows 7 35 69 200 280 160 66 128 256), losses := [] }

theorem u1157 : Upper (D 7) (R 7) [6,33,65,192,264,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1158 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 69 200 280 160 80 162 290), lower := (rows 7 35 69 200 280 160 80 128 256), losses := [] }

theorem u1158 : Upper (D 7) (R 7) [6,33,65,192,264,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1158 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1159 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 200 280 160 96 146 274), lower := (rows 7 35 69 200 280 160 96 128 256), losses := [] }

theorem u1159 : Upper (D 7) (R 7) [6,33,65,192,264,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1160 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 200 304 160 66 152 280), lower := (rows 7 35 69 200 304 160 66 128 256), losses := [] }

theorem u1160 : Upper (D 7) (R 7) [6,33,65,192,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1161 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 69 200 304 160 72 146 274), lower := (rows 7 35 69 200 304 160 72 128 256), losses := [] }

theorem u1161 : Upper (D 7) (R 7) [6,33,65,192,288,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1161 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1162 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 200 304 160 80 138 266), lower := (rows 7 35 69 200 304 160 80 128 256), losses := [] }

theorem u1162 : Upper (D 7) (R 7) [6,33,65,192,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1162 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1163 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 200 400 48 66 168 296), lower := (rows 7 35 69 200 400 48 66 128 256), losses := [] }

theorem u1163 : Upper (D 7) (R 7) [6,33,65,192,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1163 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1164 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 69 200 400 48 72 162 290), lower := (rows 7 35 69 200 400 48 72 128 256), losses := [] }

theorem u1164 : Upper (D 7) (R 7) [6,33,65,192,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1164 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1165 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 103, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 200 400 48 96 138 266), lower := (rows 7 35 69 200 400 48 96 128 256), losses := [] }

theorem u1165 : Upper (D 7) (R 7) [6,33,65,192,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1165 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1166 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 228, targets := 3 },{ cop := 0, region := 496, targets := 1 }], pairs := [(2,0),(2,1),(3,5),(4,0)], upper := (rows 7 35 76 25 274 160 96 192 448), lower := (rows 7 35 76 25 274 160 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 11 17 0 64 196 324), good := (rows 415 27 460 25 282 128 448 128 256) }] }

theorem u1166 : Upper (D 7) (R 7) [6,33,72,17,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1167 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 228, targets := 3 },{ cop := 0, region := 496, targets := 1 }], pairs := [(0,6),(2,0),(2,1),(4,0)], upper := (rows 7 35 76 25 274 160 192 224 352), lower := (rows 7 35 76 25 274 160 192 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 224 0 128 256), good := (rows 7 35 47 25 274 160 160 160 256) }] }

theorem u1167 : Upper (D 7) (R 7) [6,33,72,17,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1168 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 25 304 160 66 192 448), lower := (rows 7 35 76 25 304 160 66 128 256), losses := [] }

theorem u1168 : Upper (D 7) (R 7) [6,33,72,17,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1169 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 496, targets := 1 }], pairs := [(0,6),(2,0),(2,5),(4,0)], upper := (rows 7 35 76 25 304 160 192 194 322), lower := (rows 7 35 76 25 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 235 235 131 259), good := (rows 502 498 124 508 368 224 224 224 256) },{ target := 5, region := (rows 1 2 12 8 16 0 235 131 259), good := (rows 455 451 76 477 336 192 192 192 256) },{ target := 6, region := (rows 5 6 4 8 16 224 0 128 256), good := (rows 7 35 47 25 304 160 160 160 256) }] }

theorem u1169 : Upper (D 7) (R 7) [6,33,72,17,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1170 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 228, targets := 3 },{ cop := 0, region := 496, targets := 2 }], pairs := [(2,0),(2,1),(3,5),(4,1)], upper := (rows 7 35 76 26 273 160 96 192 448), lower := (rows 7 35 76 26 273 160 96 128 256), losses := [{ target := 5, region := (rows 1 2 4 11 17 0 64 196 324), good := (rows 415 27 460 26 281 128 448 128 256) }] }

theorem u1170 : Upper (D 7) (R 7) [6,33,72,18,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1171 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 228, targets := 3 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,6),(2,0),(2,1),(4,1)], upper := (rows 7 35 76 26 273 160 192 224 352), lower := (rows 7 35 76 26 273 160 192 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 224 0 128 256), good := (rows 7 35 47 26 273 160 160 160 256) }] }

theorem u1171 : Upper (D 7) (R 7) [6,33,72,18,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1172 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(4,5)], upper := (rows 7 35 76 56 273 160 66 192 448), lower := (rows 7 35 76 56 273 160 66 128 256), losses := [] }

theorem u1172 : Upper (D 7) (R 7) [6,33,72,48,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1173 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(2,1),(3,0),(4,5)], upper := (rows 7 35 76 56 273 160 192 194 322), lower := (rows 7 35 76 56 273 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 243 243 131 259), good := (rows 486 482 108 124 508 224 224 224 256) },{ target := 1, region := (rows 1 0 12 8 16 224 224 128 256), good := (rows 5 97 108 124 273 224 224 224 256) }] }

theorem u1173 : Upper (D 7) (R 7) [6,33,72,48,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1174 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(4,5)], upper := (rows 7 35 76 56 274 160 65 192 448), lower := (rows 7 35 76 56 274 160 65 128 256), losses := [] }

theorem u1174 : Upper (D 7) (R 7) [6,33,72,48,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1175 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(2,0),(2,1),(3,1),(4,5)], upper := (rows 7 35 76 56 274 160 192 193 321), lower := (rows 7 35 76 56 274 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 224 224 128 256), good := (rows 6 98 108 124 274 224 224 224 256) },{ target := 1, region := (rows 1 0 28 24 16 243 243 131 259), good := (rows 485 481 108 124 508 224 224 224 256) }] }

theorem u1175 : Upper (D 7) (R 7) [6,33,72,48,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1176 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 7 35 76 56 336 160 65 130 386), lower := (rows 7 35 76 56 336 160 65 128 256), losses := [] }

theorem u1176 : Upper (D 7) (R 7) [6,33,72,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1177 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 7 35 76 56 336 160 66 129 385), lower := (rows 7 35 76 56 336 160 66 128 256), losses := [] }

theorem u1177 : Upper (D 7) (R 7) [6,33,72,48,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1178 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(1,6),(2,0),(4,5)], upper := (rows 7 35 76 56 336 160 192 131 259), lower := (rows 7 35 76 56 336 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 224 224 128 256), good := (rows 6 98 108 124 380 224 224 224 256) }] }

theorem u1178 : Upper (D 7) (R 7) [6,33,72,48,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1179 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 137 82 288 80 160 416), lower := (rows 7 35 76 137 82 288 80 128 256), losses := [] }

theorem u1179 : Upper (D 7) (R 7) [6,33,72,129,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1179 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1180 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 76 137 82 288 96 144 400), lower := (rows 7 35 76 137 82 288 96 128 256), losses := [] }

theorem u1180 : Upper (D 7) (R 7) [6,33,72,129,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1180 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1181 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 137 82 288 192 176 304), lower := (rows 7 35 76 137 82 288 192 128 256), losses := [] }

theorem u1181 : Upper (D 7) (R 7) [6,33,72,129,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1181 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1182 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 432, targets := 3 },{ cop := 1, region := 80, targets := 128 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 7 35 76 137 112 288 66 144 400), lower := (rows 7 35 76 137 112 288 66 128 256), losses := [] }

theorem u1182 : Upper (D 7) (R 7) [6,33,72,129,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1182 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1183 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 137 112 288 80 130 386), lower := (rows 7 35 76 137 112 288 80 128 256), losses := [] }

theorem u1183 : Upper (D 7) (R 7) [6,33,72,129,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1183 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1184 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 137 112 288 192 146 274), lower := (rows 7 35 76 137 112 288 192 128 256), losses := [] }

theorem u1184 : Upper (D 7) (R 7) [6,33,72,129,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1184 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1185 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 76 137 146 288 80 224 352), lower := (rows 7 35 76 137 146 288 80 128 256), losses := [] }

theorem u1185 : Upper (D 7) (R 7) [6,33,72,129,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1185 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1186 : Route 9 := (fun mask => (mask,id))

def c1186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1186 : Upper (D 7) (R 7) [6,33,72,129,130,256,32] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,130,256,32] 13 (by decide) (choices 1) [16,64] r1186 c1186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22
  · exact u23

def b1187 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 432, targets := 3 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 7 35 76 137 176 288 66 208 336), lower := (rows 7 35 76 137 176 288 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 95 367 67 207 335), good := (rows 502 498 508 508 176 288 498 128 288) }] }

theorem u1187 : Upper (D 7) (R 7) [6,33,72,129,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1187 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1188 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 76 137 176 288 80 194 322), lower := (rows 7 35 76 137 176 288 80 128 256), losses := [] }

theorem u1188 : Upper (D 7) (R 7) [6,33,72,129,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1188 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1189 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 432, targets := 3 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 7 35 76 137 208 288 66 176 304), lower := (rows 7 35 76 137 208 288 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 95 383 67 223 351), good := (rows 502 498 508 508 496 288 498 128 288) }] }

theorem u1189 : Upper (D 7) (R 7) [6,33,72,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1189 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1190 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 76 137 208 288 80 162 290), lower := (rows 7 35 76 137 208 288 80 128 256), losses := [] }

theorem u1190 : Upper (D 7) (R 7) [6,33,72,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1190 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1191 : Route 9 := (fun mask => (mask,id))

def c1191 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1191 : Upper (D 7) (R 7) [6,33,72,129,192,256,32] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,192,256,32] 13 (by decide) (choices 1) [2,16] r1191 c1191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24
  · exact u25

def b1192 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 432, targets := 3 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 7 35 76 137 400 48 66 224 352), lower := (rows 7 35 76 137 400 48 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 95 127 67 207 335), good := (rows 502 498 508 508 432 48 498 128 256) }] }

theorem u1192 : Upper (D 7) (R 7) [6,33,72,129,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1192 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1193 : Route 9 := (fun mask => (mask,id))

def c1193 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1193 : Upper (D 7) (R 7) [6,33,72,129,384,16,32] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,384,16,32] 13 (by decide) (choices 1) [2,64] r1193 c1193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u26
  · exact u27

def b1194 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 76 138 112 288 65 144 400), lower := (rows 7 35 76 138 112 288 65 128 256), losses := [] }

theorem u1194 : Upper (D 7) (R 7) [6,33,72,130,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1194 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1195 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 138 112 288 80 129 385), lower := (rows 7 35 76 138 112 288 80 128 256), losses := [] }

theorem u1195 : Upper (D 7) (R 7) [6,33,72,130,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1195 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1196 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 76 138 112 288 192 145 273), lower := (rows 7 35 76 138 112 288 192 128 256), losses := [] }

theorem u1196 : Upper (D 7) (R 7) [6,33,72,130,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1196 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1197 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 76 138 176 288 65 208 336), lower := (rows 7 35 76 138 176 288 65 128 256), losses := [] }

theorem u1197 : Upper (D 7) (R 7) [6,33,72,130,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1197 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1198 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 76 138 176 288 80 193 321), lower := (rows 7 35 76 138 176 288 80 128 256), losses := [] }

theorem u1198 : Upper (D 7) (R 7) [6,33,72,130,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1198 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1199 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 85, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 76 138 208 288 65 176 304), lower := (rows 7 35 76 138 208 288 65 128 256), losses := [] }

theorem u1199 : Upper (D 7) (R 7) [6,33,72,130,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1199 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1199
end Delivery.IrregularNine14.P07

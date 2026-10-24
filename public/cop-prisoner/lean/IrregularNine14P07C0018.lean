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

def b1080 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 13 328 208 48 66 160 416), lower := (rows 7 35 13 328 208 48 66 128 256), losses := [] }

theorem u1080 : Upper (D 7) (R 7) [6,33,9,320,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1080 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1081 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 7, region := 112, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 35 13 328 208 48 96 130 386), lower := (rows 7 35 13 328 208 48 96 128 256), losses := [] }

theorem u1081 : Upper (D 7) (R 7) [6,33,9,320,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1081 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1082 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 13 328 208 48 192 162 290), lower := (rows 7 35 13 328 208 48 192 128 256), losses := [] }

theorem u1082 : Upper (D 7) (R 7) [6,33,9,320,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1082 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1083 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 35 13 328 208 160 66 176 304), lower := (rows 7 35 13 328 208 160 66 128 256), losses := [] }

theorem u1083 : Upper (D 7) (R 7) [6,33,9,320,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1084 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 13 328 208 160 80 162 290), lower := (rows 7 35 13 328 208 160 80 128 256), losses := [] }

theorem u1084 : Upper (D 7) (R 7) [6,33,9,320,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1084 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1085 : Route 9 := (fun mask => (mask,id))

def c1085 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1085 : Upper (D 7) (R 7) [6,33,9,320,192,128,32] 13 := by
  apply FastRouting.sound _ _ [6,33,9,320,192,128,32] 13 (by decide) (choices 1) [2,16] r1085 c1085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16
  · exact u17

def b1086 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 28 73 304 160 66 192 448), lower := (rows 7 35 28 73 304 160 66 128 256), losses := [] }

theorem u1086 : Upper (D 7) (R 7) [6,33,24,65,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1087 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,0),(3,1),(3,5),(4,0)], upper := (rows 7 35 28 73 304 160 192 194 322), lower := (rows 7 35 28 73 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 235 235 131 259), good := (rows 502 498 124 508 368 224 224 224 256) },{ target := 1, region := (rows 1 0 4 10 16 224 224 128 256), good := (rows 13 105 28 105 368 224 224 224 256) }] }

theorem u1087 : Upper (D 7) (R 7) [6,33,24,65,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1088 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 28 74 304 160 65 192 448), lower := (rows 7 35 28 74 304 160 65 128 256), losses := [] }

theorem u1088 : Upper (D 7) (R 7) [6,33,24,66,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1089 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 496, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,0),(3,5),(4,1)], upper := (rows 7 35 28 74 304 160 192 193 321), lower := (rows 7 35 28 74 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 224 224 128 256), good := (rows 14 106 28 106 368 224 224 224 256) },{ target := 1, region := (rows 1 0 12 8 27 235 235 131 259), good := (rows 501 497 124 508 368 224 224 224 256) }] }

theorem u1089 : Upper (D 7) (R 7) [6,33,24,66,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1090 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 168, targets := 3 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 72, targets := 128 }], pairs := [(3,0),(3,1),(3,7),(4,5)], upper := (rows 7 35 28 104 273 160 66 192 448), lower := (rows 7 35 28 104 273 160 66 128 256), losses := [] }

theorem u1090 : Upper (D 7) (R 7) [6,33,24,96,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1091 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 28 104 273 160 192 194 322), lower := (rows 7 35 28 104 273 160 192 128 256), losses := [] }

theorem u1091 : Upper (D 7) (R 7) [6,33,24,96,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1092 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 168, targets := 3 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 72, targets := 128 }], pairs := [(3,0),(3,1),(3,7),(4,5)], upper := (rows 7 35 28 104 274 160 65 192 448), lower := (rows 7 35 28 104 274 160 65 128 256), losses := [] }

theorem u1092 : Upper (D 7) (R 7) [6,33,24,96,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1093 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 28 104 274 160 192 193 321), lower := (rows 7 35 28 104 274 160 192 128 256), losses := [] }

theorem u1093 : Upper (D 7) (R 7) [6,33,24,96,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1094 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 72, targets := 2 }], pairs := [(0,6),(1,6),(3,1),(4,5)], upper := (rows 7 35 28 104 336 160 65 130 386), lower := (rows 7 35 28 104 336 160 65 128 256), losses := [] }

theorem u1094 : Upper (D 7) (R 7) [6,33,24,96,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1095 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 72, targets := 129 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(3,7)], upper := (rows 7 35 28 104 336 160 66 129 385), lower := (rows 7 35 28 104 336 160 66 128 256), losses := [] }

theorem u1095 : Upper (D 7) (R 7) [6,33,24,96,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1096 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 28 104 336 160 192 131 259), lower := (rows 7 35 28 104 336 160 192 128 256), losses := [] }

theorem u1096 : Upper (D 7) (R 7) [6,33,24,96,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1097 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(1,6),(2,0),(4,7)], upper := (rows 7 35 28 200 336 160 65 162 290), lower := (rows 7 35 28 200 336 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 92 72 80 235 64 131 259), good := (rows 422 418 60 252 380 160 508 160 256) }] }

theorem u1097 : Upper (D 7) (R 7) [6,33,24,192,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1098 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(1,6),(2,1),(4,7)], upper := (rows 7 35 28 200 336 160 66 161 289), lower := (rows 7 35 28 200 336 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 92 72 80 235 64 131 259), good := (rows 421 417 60 252 380 160 508 160 256) }] }

theorem u1098 : Upper (D 7) (R 7) [6,33,24,192,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1099 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 5, region := 72, targets := 3 }], pairs := [(0,6),(1,6),(3,0),(3,1)], upper := (rows 7 35 28 200 336 160 96 131 259), lower := (rows 7 35 28 200 336 160 96 128 256), losses := [] }

theorem u1099 : Upper (D 7) (R 7) [6,33,24,192,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1100 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 26 208 160 72 416 288), lower := (rows 7 35 69 26 208 160 72 128 256), losses := [] }

theorem u1100 : Upper (D 7) (R 7) [6,33,65,18,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1100 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1101 : PairBound 9 := { available := 264, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 26 208 160 96 392 264), lower := (rows 7 35 69 26 208 160 96 128 256), losses := [] }

theorem u1101 : Upper (D 7) (R 7) [6,33,65,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1102 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 496, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 35 69 26 208 160 320 168 296), lower := (rows 7 35 69 26 208 160 320 128 256), losses := [] }

theorem u1102 : Upper (D 7) (R 7) [6,33,65,18,192,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1102 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1103 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 26 336 160 72 160 416), lower := (rows 7 35 69 26 336 160 72 128 256), losses := [] }

theorem u1103 : Upper (D 7) (R 7) [6,33,65,18,320,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1103 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1104 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 26 336 160 96 136 392), lower := (rows 7 35 69 26 336 160 96 128 256), losses := [] }

theorem u1104 : Upper (D 7) (R 7) [6,33,65,18,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1105 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 496, targets := 2 }], pairs := [(2,1),(3,0),(4,0),(4,1)], upper := (rows 7 35 69 26 336 160 192 168 296), lower := (rows 7 35 69 26 336 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 6 8 24 232 232 136 264), good := (rows 5 101 101 508 368 224 224 224 256) }] }

theorem u1105 : Upper (D 7) (R 7) [6,33,65,18,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1105 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1106 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 26 400 160 72 224 352), lower := (rows 7 35 69 26 400 160 72 128 256), losses := [] }

theorem u1106 : Upper (D 7) (R 7) [6,33,65,18,384,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1106 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1107 : PairBound 9 := { available := 72, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 26 400 160 96 200 328), lower := (rows 7 35 69 26 400 160 96 128 256), losses := [] }

theorem u1107 : Upper (D 7) (R 7) [6,33,65,18,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1107 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1108 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 56 208 288 66 136 392), lower := (rows 7 35 69 56 208 288 66 128 256), losses := [] }

theorem u1108 : Upper (D 7) (R 7) [6,33,65,48,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1108 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1109 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 69 56 208 288 72 130 386), lower := (rows 7 35 69 56 208 288 72 128 256), losses := [] }

theorem u1109 : Upper (D 7) (R 7) [6,33,65,48,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1109 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1110 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 56 208 288 192 138 266), lower := (rows 7 35 69 56 208 288 192 128 256), losses := [] }

theorem u1110 : Upper (D 7) (R 7) [6,33,65,48,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1110 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1111 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 56 274 160 72 192 448), lower := (rows 7 35 69 56 274 160 72 128 256), losses := [] }

theorem u1111 : Upper (D 7) (R 7) [6,33,65,48,258,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1111 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1112 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 232, targets := 2 }], pairs := [(2,1),(3,0),(3,1),(4,0)], upper := (rows 7 35 69 56 274 160 192 200 328), lower := (rows 7 35 69 56 274 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 6 24 16 248 248 152 280), good := (rows 5 101 101 504 508 224 224 224 256) }] }

theorem u1112 : Upper (D 7) (R 7) [6,33,65,48,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1113 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 56 336 160 66 136 392), lower := (rows 7 35 69 56 336 160 66 128 256), losses := [] }

theorem u1113 : Upper (D 7) (R 7) [6,33,65,48,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1114 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 56 336 160 72 130 386), lower := (rows 7 35 69 56 336 160 72 128 256), losses := [] }

theorem u1114 : Upper (D 7) (R 7) [6,33,65,48,320,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1114 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1115 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(3,1),(4,0)], upper := (rows 7 35 69 56 336 160 192 138 266), lower := (rows 7 35 69 56 336 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 6 24 16 224 224 128 256), good := (rows 5 101 101 120 376 224 224 224 256) }] }

theorem u1115 : Upper (D 7) (R 7) [6,33,65,48,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1116 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 88 146 160 72 416 288), lower := (rows 7 35 69 88 146 160 72 128 256), losses := [] }

theorem u1116 : Upper (D 7) (R 7) [6,33,65,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1116 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1117 : PairBound 9 := { available := 264, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 88 146 160 96 392 264), lower := (rows 7 35 69 88 146 160 96 128 256), losses := [] }

theorem u1117 : Upper (D 7) (R 7) [6,33,65,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1118 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 69 88 146 160 320 168 296), lower := (rows 7 35 69 88 146 160 320 128 256), losses := [] }

theorem u1118 : Upper (D 7) (R 7) [6,33,65,80,130,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1118 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1119 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 88 176 288 66 136 392), lower := (rows 7 35 69 88 176 288 66 128 256), losses := [] }

theorem u1119 : Upper (D 7) (R 7) [6,33,65,80,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1119 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1120 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 69 88 176 288 72 130 386), lower := (rows 7 35 69 88 176 288 72 128 256), losses := [] }

theorem u1120 : Upper (D 7) (R 7) [6,33,65,80,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1120 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1121 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 88 176 288 192 138 266), lower := (rows 7 35 69 88 176 288 192 128 256), losses := [] }

theorem u1121 : Upper (D 7) (R 7) [6,33,65,80,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1121 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1122 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 77, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 88 274 160 72 160 416), lower := (rows 7 35 69 88 274 160 72 128 256), losses := [] }

theorem u1122 : Upper (D 7) (R 7) [6,33,65,80,258,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1122 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1123 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 88 274 160 96 136 392), lower := (rows 7 35 69 88 274 160 96 128 256), losses := [] }

theorem u1123 : Upper (D 7) (R 7) [6,33,65,80,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1124 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 232, targets := 2 }], pairs := [(2,1),(3,0),(3,1),(4,0)], upper := (rows 7 35 69 88 274 160 192 168 296), lower := (rows 7 35 69 88 274 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 6 24 16 248 248 152 280), good := (rows 5 101 101 504 508 224 224 224 256) }] }

theorem u1124 : Upper (D 7) (R 7) [6,33,65,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1125 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 88 304 160 66 136 392), lower := (rows 7 35 69 88 304 160 66 128 256), losses := [] }

theorem u1125 : Upper (D 7) (R 7) [6,33,65,80,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1126 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 88 304 160 72 130 386), lower := (rows 7 35 69 88 304 160 72 128 256), losses := [] }

theorem u1126 : Upper (D 7) (R 7) [6,33,65,80,288,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1126 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1127 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(2,1),(3,0),(3,1),(4,0)], upper := (rows 7 35 69 88 304 160 192 138 266), lower := (rows 7 35 69 88 304 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 6 24 16 224 224 128 256), good := (rows 5 101 101 120 376 224 224 224 256) }] }

theorem u1127 : Upper (D 7) (R 7) [6,33,65,80,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1128 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 88 400 160 66 168 296), lower := (rows 7 35 69 88 400 160 66 128 256), losses := [] }

theorem u1128 : Upper (D 7) (R 7) [6,33,65,80,384,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1129 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 69 88 400 160 72 162 290), lower := (rows 7 35 69 88 400 160 72 128 256), losses := [] }

theorem u1129 : Upper (D 7) (R 7) [6,33,65,80,384,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1129 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1130 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 88 400 160 96 138 266), lower := (rows 7 35 69 88 400 160 96 128 256), losses := [] }

theorem u1130 : Upper (D 7) (R 7) [6,33,65,80,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1131 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 368, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 35 69 138 280 160 80 224 352), lower := (rows 7 35 69 138 280 160 80 128 256), losses := [] }

theorem u1131 : Upper (D 7) (R 7) [6,33,65,130,264,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1131 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1132 : PairBound 9 := { available := 80, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 138 280 160 96 208 336), lower := (rows 7 35 69 138 280 160 96 128 256), losses := [] }

theorem u1132 : Upper (D 7) (R 7) [6,33,65,130,264,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1133 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 138 304 160 72 208 336), lower := (rows 7 35 69 138 304 160 72 128 256), losses := [] }

theorem u1133 : Upper (D 7) (R 7) [6,33,65,130,288,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1133 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1134 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 69 138 304 160 80 200 328), lower := (rows 7 35 69 138 304 160 80 128 256), losses := [] }

theorem u1134 : Upper (D 7) (R 7) [6,33,65,130,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1134 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1135 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 35 69 138 336 160 72 176 304), lower := (rows 7 35 69 138 336 160 72 128 256), losses := [] }

theorem u1135 : Upper (D 7) (R 7) [6,33,65,130,320,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1135 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1136 : PairBound 9 := { available := 40, camps := [{ cop := 8, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 69 138 336 160 80 168 296), lower := (rows 7 35 69 138 336 160 80 128 256), losses := [] }

theorem u1136 : Upper (D 7) (R 7) [6,33,65,130,320,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1136 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1137 : PairBound 9 := { available := 24, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 138 336 160 96 152 280), lower := (rows 7 35 69 138 336 160 96 128 256), losses := [] }

theorem u1137 : Upper (D 7) (R 7) [6,33,65,130,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1138 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 232, targets := 2 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 69 152 274 160 72 224 352), lower := (rows 7 35 69 152 274 160 72 128 256), losses := [] }

theorem u1138 : Upper (D 7) (R 7) [6,33,65,144,258,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1138 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1139 : PairBound 9 := { available := 72, camps := [{ cop := 5, region := 71, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 152 274 160 96 200 328), lower := (rows 7 35 69 152 274 160 96 128 256), losses := [] }

theorem u1139 : Upper (D 7) (R 7) [6,33,65,144,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1139
end Delivery.IrregularNine14.P07

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0001

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1140 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 280 208 160 97 161 289), lower := (rows 7 42 69 280 208 160 64 128 256), losses := [] }

theorem u1140 : Upper (D 8) (R 8) [6,40,65,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1141 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 392 112 33 240 176 432), lower := (rows 7 42 69 392 112 33 64 128 256), losses := [] }

theorem u1141 : Upper (D 8) (R 8) [6,40,65,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1142 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 42 69 392 112 48 225 161 417), lower := (rows 7 42 69 392 112 48 64 128 256), losses := [] }

theorem u1142 : Upper (D 8) (R 8) [6,40,65,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1142 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1143 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 392 112 160 113 177 305), lower := (rows 7 42 69 392 112 160 64 128 256), losses := [] }

theorem u1143 : Upper (D 8) (R 8) [6,40,65,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1144 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 392 176 33 112 240 368), lower := (rows 7 42 69 392 176 33 64 128 256), losses := [] }

theorem u1144 : Upper (D 8) (R 8) [6,40,65,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1145 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 42 69 392 176 48 97 225 353), lower := (rows 7 42 69 392 176 48 64 128 256), losses := [] }

theorem u1145 : Upper (D 8) (R 8) [6,40,65,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1145 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1146 : Route 9 := (fun mask => (mask,id))

def c1146 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1146 : Upper (D 8) (R 8) [6,40,65,384,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,160,64] 13 (by decide) (choices 1) [1,16,32] r1146 c1146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u74
  · exact u75
  · exact u76

def b1147 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 392 208 33 112 176 304), lower := (rows 7 42 69 392 208 33 64 128 256), losses := [] }

theorem u1147 : Upper (D 8) (R 8) [6,40,65,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1148 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 42 69 392 208 48 97 161 289), lower := (rows 7 42 69 392 208 48 64 128 256), losses := [] }

theorem u1148 : Upper (D 8) (R 8) [6,40,65,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1148 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1149 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 84 137 304 33 224 224 480), lower := (rows 7 42 84 137 304 33 64 128 256), losses := [] }

theorem u1149 : Upper (D 8) (R 8) [6,40,80,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1150 : Route 9 := (fun mask => (mask,id))

def c1150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1150 : Upper (D 8) (R 8) [6,40,80,129,288,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,288,64] 13 (by decide) (choices 1) [1,32,128] r1150 c1150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u77
  · exact u78
  · exact u79

def b1151 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 84 137 304 160 97 225 353), lower := (rows 7 42 84 137 304 160 64 128 256), losses := [] }

theorem u1151 : Upper (D 8) (R 8) [6,40,80,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1152 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 84 265 176 33 224 224 480), lower := (rows 7 42 84 265 176 33 64 128 256), losses := [] }

theorem u1152 : Upper (D 8) (R 8) [6,40,80,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1153 : Route 9 := (fun mask => (mask,id))

def c1153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1153 : Upper (D 8) (R 8) [6,40,80,257,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,257,160,64] 13 (by decide) (choices 1) [1,32,128] r1153 c1153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u80
  · exact u81
  · exact u82

def b1154 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 84 265 176 160 97 225 353), lower := (rows 7 42 84 265 176 160 64 128 256), losses := [] }

theorem u1154 : Upper (D 8) (R 8) [6,40,80,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1155 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 392 49 33 224 224 480), lower := (rows 7 42 84 392 49 33 64 128 256), losses := [] }

theorem u1155 : Upper (D 8) (R 8) [6,40,80,384,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1156 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 84 392 49 96 225 161 417), lower := (rows 7 42 84 392 49 96 64 128 256), losses := [] }

theorem u1156 : Upper (D 8) (R 8) [6,40,80,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1157 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 84 392 49 160 97 225 353), lower := (rows 7 42 84 392 49 160 64 128 256), losses := [] }

theorem u1157 : Upper (D 8) (R 8) [6,40,80,384,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1158 : PairBound 9 := { available := 97, camps := [], pairs := [(2,7)], upper := (rows 7 42 84 392 176 33 97 225 353), lower := (rows 7 42 84 392 176 33 64 128 256), losses := [{ target := 7, region := (rows 1 2 20 8 16 33 97 0 289), good := (rows 359 362 84 264 372 353 64 0 256) }] }

theorem u1158 : Upper (D 8) (R 8) [6,40,80,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1159 : Route 9 := (fun mask => (mask,id))

def c1159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1159 : Upper (D 8) (R 8) [6,40,80,384,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,160,64] 13 (by decide) (choices 1) [1,32] r1159 c1159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u83
  · exact u84

def b1160 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 25 176 33 448 448 448), lower := (rows 7 42 100 25 176 33 64 128 256), losses := [] }

theorem u1160 : Upper (D 8) (R 8) [6,40,96,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1161 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 25 176 96 449 385 385), lower := (rows 7 42 100 25 176 96 64 128 256), losses := [] }

theorem u1161 : Upper (D 8) (R 8) [6,40,96,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1162 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 25 176 160 321 449 321), lower := (rows 7 42 100 25 176 160 64 128 256), losses := [] }

theorem u1162 : Upper (D 8) (R 8) [6,40,96,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1163 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 42 100 25 176 288 193 193 449), lower := (rows 7 42 100 25 176 288 64 128 256), losses := [] }

theorem u1163 : Upper (D 8) (R 8) [6,40,96,17,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1163 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1164 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 25 304 33 192 192 448), lower := (rows 7 42 100 25 304 33 64 128 256), losses := [] }

theorem u1164 : Upper (D 8) (R 8) [6,40,96,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1165 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 25 304 96 193 129 385), lower := (rows 7 42 100 25 304 96 64 128 256), losses := [] }

theorem u1165 : Upper (D 8) (R 8) [6,40,96,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1166 : Route 9 := (fun mask => (mask,id))

def c1166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1166 : Upper (D 8) (R 8) [6,40,96,17,288,128] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,288,128] 13 (by decide) (choices 1) [1,128] r1166 c1166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u85
  · exact u86

def b1167 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 25 400 33 224 224 480), lower := (rows 7 42 100 25 400 33 64 128 256), losses := [] }

theorem u1167 : Upper (D 8) (R 8) [6,40,96,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1168 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 25 400 96 225 161 417), lower := (rows 7 42 100 25 400 96 64 128 256), losses := [] }

theorem u1168 : Upper (D 8) (R 8) [6,40,96,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1169 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 25 400 160 97 225 353), lower := (rows 7 42 100 25 400 160 64 128 256), losses := [] }

theorem u1169 : Upper (D 8) (R 8) [6,40,96,17,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1170 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 137 176 33 336 464 336), lower := (rows 7 42 100 137 176 33 64 128 256), losses := [] }

theorem u1170 : Upper (D 8) (R 8) [6,40,96,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1171 : PairBound 9 := { available := 321, camps := [], pairs := [], upper := (rows 7 42 100 137 176 48 321 449 321), lower := (rows 7 42 100 137 176 48 64 128 256), losses := [] }

theorem u1171 : Upper (D 8) (R 8) [6,40,96,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1171 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1172 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 137 176 96 337 401 273), lower := (rows 7 42 100 137 176 96 64 128 256), losses := [] }

theorem u1172 : Upper (D 8) (R 8) [6,40,96,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1173 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 7 42 100 137 176 288 81 209 337), lower := (rows 7 42 100 137 176 288 64 128 256), losses := [] }

theorem u1173 : Upper (D 8) (R 8) [6,40,96,129,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1173 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1174 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 137 208 33 368 432 304), lower := (rows 7 42 100 137 208 33 64 128 256), losses := [] }

theorem u1174 : Upper (D 8) (R 8) [6,40,96,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1175 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 7 42 100 137 208 48 353 417 289), lower := (rows 7 42 100 137 208 48 64 128 256), losses := [] }

theorem u1175 : Upper (D 8) (R 8) [6,40,96,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1175 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1176 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 42 100 137 208 288 113 177 305), lower := (rows 7 42 100 137 208 288 64 128 256), losses := [] }

theorem u1176 : Upper (D 8) (R 8) [6,40,96,129,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1176 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1177 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 137 304 33 208 208 464), lower := (rows 7 42 100 137 304 33 64 128 256), losses := [] }

theorem u1177 : Upper (D 8) (R 8) [6,40,96,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1178 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 42 100 137 304 48 193 193 449), lower := (rows 7 42 100 137 304 48 64 128 256), losses := [] }

theorem u1178 : Upper (D 8) (R 8) [6,40,96,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1178 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1179 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 137 304 96 209 145 401), lower := (rows 7 42 100 137 304 96 64 128 256), losses := [] }

theorem u1179 : Upper (D 8) (R 8) [6,40,96,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1180 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 137 304 160 81 209 337), lower := (rows 7 42 100 137 304 160 64 128 256), losses := [] }

theorem u1180 : Upper (D 8) (R 8) [6,40,96,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1180 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1181 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 137 336 33 240 176 432), lower := (rows 7 42 100 137 336 33 64 128 256), losses := [] }

theorem u1181 : Upper (D 8) (R 8) [6,40,96,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1182 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 42 100 137 336 48 225 161 417), lower := (rows 7 42 100 137 336 48 64 128 256), losses := [] }

theorem u1182 : Upper (D 8) (R 8) [6,40,96,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1182 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1183 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 137 336 160 113 177 305), lower := (rows 7 42 100 137 336 160 64 128 256), losses := [] }

theorem u1183 : Upper (D 8) (R 8) [6,40,96,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1184 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 137 400 33 112 240 368), lower := (rows 7 42 100 137 400 33 64 128 256), losses := [] }

theorem u1184 : Upper (D 8) (R 8) [6,40,96,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1184 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1185 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 42 100 137 400 48 97 225 353), lower := (rows 7 42 100 137 400 48 64 128 256), losses := [] }

theorem u1185 : Upper (D 8) (R 8) [6,40,96,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1185 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1186 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 137 400 96 113 177 305), lower := (rows 7 42 100 137 400 96 64 128 256), losses := [] }

theorem u1186 : Upper (D 8) (R 8) [6,40,96,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1186 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1187 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 152 273 33 224 224 480), lower := (rows 7 42 100 152 273 33 64 128 256), losses := [] }

theorem u1187 : Upper (D 8) (R 8) [6,40,96,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1188 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 152 273 96 225 161 417), lower := (rows 7 42 100 152 273 96 64 128 256), losses := [] }

theorem u1188 : Upper (D 8) (R 8) [6,40,96,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1188 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1189 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 152 273 160 97 225 353), lower := (rows 7 42 100 152 273 160 64 128 256), losses := [] }

theorem u1189 : Upper (D 8) (R 8) [6,40,96,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1190 : PairBound 9 := { available := 193, camps := [], pairs := [(3,5)], upper := (rows 7 42 100 152 304 33 193 193 449), lower := (rows 7 42 100 152 304 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 97 161 289), good := (rows 455 458 452 152 472 449 64 128 256) }] }

theorem u1190 : Upper (D 8) (R 8) [6,40,96,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1191 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 152 304 96 193 129 385), lower := (rows 7 42 100 152 304 96 64 128 256), losses := [] }

theorem u1191 : Upper (D 8) (R 8) [6,40,96,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1192 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 152 304 160 65 193 321), lower := (rows 7 42 100 152 304 160 64 128 256), losses := [] }

theorem u1192 : Upper (D 8) (R 8) [6,40,96,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1193 : Route 9 := (fun mask => (mask,id))

def c1193 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1193 : Upper (D 8) (R 8) [6,40,96,144,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,320,1] 13 (by decide) (choices 1) [1,32,128] r1193 c1193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u87
  · exact u88
  · exact u89

def b1194 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 152 336 160 97 161 289), lower := (rows 7 42 100 152 336 160 64 128 256), losses := [] }

theorem u1194 : Upper (D 8) (R 8) [6,40,96,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1194 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1195 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 265 176 33 208 208 464), lower := (rows 7 42 100 265 176 33 64 128 256), losses := [] }

theorem u1195 : Upper (D 8) (R 8) [6,40,96,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1195 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1196 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 42 100 265 176 48 193 193 449), lower := (rows 7 42 100 265 176 48 64 128 256), losses := [] }

theorem u1196 : Upper (D 8) (R 8) [6,40,96,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1196 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1197 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 265 176 96 209 145 401), lower := (rows 7 42 100 265 176 96 64 128 256), losses := [] }

theorem u1197 : Upper (D 8) (R 8) [6,40,96,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1198 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 265 176 160 81 209 337), lower := (rows 7 42 100 265 176 160 64 128 256), losses := [] }

theorem u1198 : Upper (D 8) (R 8) [6,40,96,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1198 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1199 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 265 208 33 240 176 432), lower := (rows 7 42 100 265 208 33 64 128 256), losses := [] }

theorem u1199 : Upper (D 8) (R 8) [6,40,96,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1199
end Delivery.IrregularNine14.P08

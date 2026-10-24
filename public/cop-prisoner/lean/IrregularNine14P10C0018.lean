import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0004
import IrregularNine14P10C0005

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1080 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 340, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 292 168 336 33 120 184 312), lower := (rows 67 134 292 168 336 33 64 128 256), losses := [] }

theorem u1080 : Upper (D 10) (R 10) [66,132,288,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1080 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1081 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 67 134 292 168 336 40 113 177 305), lower := (rows 67 134 292 168 336 40 64 128 256), losses := [] }

theorem u1081 : Upper (D 10) (R 10) [66,132,288,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1081 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1082 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 203, targets := 256 }], pairs := [(0,8)], upper := (rows 67 134 292 168 336 48 105 169 297), lower := (rows 67 134 292 168 336 48 64 128 256), losses := [] }

theorem u1082 : Upper (D 10) (R 10) [66,132,288,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1082 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1083 : Route 9 := (fun mask => (mask,id))

def c1083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1083 : Upper (D 10) (R 10) [66,132,288,192,264,1] 13 := by
  apply FastRouting.sound _ _ [66,132,288,192,264,1] 13 (by decide) (choices 1) [16,32] r1083 c1083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u275
  · exact u276

def b1084 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 195, targets := 256 }], pairs := [(0,8)], upper := (rows 67 134 292 200 280 48 97 161 289), lower := (rows 67 134 292 200 280 48 64 128 256), losses := [] }

theorem u1084 : Upper (D 10) (R 10) [66,132,288,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1084 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1085 : Route 9 := (fun mask => (mask,id))

def c1085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1085 : Upper (D 10) (R 10) [66,160,72,288,384,1] 13 := by
  apply FastRouting.sound _ _ [66,160,72,288,384,1] 13 (by decide) (choices 1) [4,16,32] r1085 c1085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u277
  · exact u278
  · exact u279

def b1086 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 76 296 400 48 101 165 293), lower := (rows 67 162 76 296 400 48 64 128 256), losses := [] }

theorem u1086 : Upper (D 10) (R 10) [66,160,72,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1086 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1087 : Route 9 := (fun mask => (mask,id))

def c1087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1087 : Upper (D 10) (R 10) [66,160,72,384,288,1] 13 := by
  apply FastRouting.sound _ _ [66,160,72,384,288,1] 13 (by decide) (choices 1) [4,16,32] r1087 c1087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u280
  · exact u281
  · exact u282

def b1088 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 76 392 304 36 113 177 305), lower := (rows 67 162 76 392 304 36 64 128 256), losses := [] }

theorem u1088 : Upper (D 10) (R 10) [66,160,72,384,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1088 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1089 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 76 392 304 48 101 165 293), lower := (rows 67 162 76 392 304 48 64 128 256), losses := [] }

theorem u1089 : Upper (D 10) (R 10) [66,160,72,384,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1089 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1090 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 100 140 304 33 344 408 280), lower := (rows 67 162 100 140 304 33 64 128 256), losses := [] }

theorem u1090 : Upper (D 10) (R 10) [66,160,96,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1090 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1091 : PairBound 9 := { available := 265, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 67 162 100 140 304 48 329 393 265), lower := (rows 67 162 100 140 304 48 64 128 256), losses := [] }

theorem u1091 : Upper (D 10) (R 10) [66,160,96,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1091 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1092 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 67 162 100 140 304 288 89 153 281), lower := (rows 67 162 100 140 304 288 64 128 256), losses := [] }

theorem u1092 : Upper (D 10) (R 10) [66,160,96,132,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1092 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1093 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 100 152 304 33 332 396 268), lower := (rows 67 162 100 152 304 33 64 128 256), losses := [] }

theorem u1093 : Upper (D 10) (R 10) [66,160,96,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1093 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1094 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 100 152 304 36 329 393 265), lower := (rows 67 162 100 152 304 36 64 128 256), losses := [] }

theorem u1094 : Upper (D 10) (R 10) [66,160,96,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1094 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1095 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 100 152 304 40 325 389 261), lower := (rows 67 162 100 152 304 40 64 128 256), losses := [] }

theorem u1095 : Upper (D 10) (R 10) [66,160,96,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1095 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1096 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 67 162 100 152 304 288 77 141 269), lower := (rows 67 162 100 152 304 288 64 128 256), losses := [] }

theorem u1096 : Upper (D 10) (R 10) [66,160,96,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1096 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1097 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 100 268 400 33 120 184 312), lower := (rows 67 162 100 268 400 33 64 128 256), losses := [] }

theorem u1097 : Upper (D 10) (R 10) [66,160,96,260,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1097 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1098 : Route 9 := (fun mask => (mask,id))

def c1098 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1098 : Upper (D 10) (R 10) [66,160,96,260,384,8] 13 := by
  apply FastRouting.sound _ _ [66,160,96,260,384,8] 13 (by decide) (choices 1) [1,16,32] r1098 c1098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u283
  · exact u284
  · exact u285

def b1099 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 100 268 400 48 105 169 297), lower := (rows 67 162 100 268 400 48 64 128 256), losses := [] }

theorem u1099 : Upper (D 10) (R 10) [66,160,96,260,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1099 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1100 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 100 296 400 33 92 156 284), lower := (rows 67 162 100 296 400 33 64 128 256), losses := [] }

theorem u1100 : Upper (D 10) (R 10) [66,160,96,288,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1100 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1101 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 100 296 400 36 89 153 281), lower := (rows 67 162 100 296 400 36 64 128 256), losses := [] }

theorem u1101 : Upper (D 10) (R 10) [66,160,96,288,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1101 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1102 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 42, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 100 296 400 40 85 149 277), lower := (rows 67 162 100 296 400 40 64 128 256), losses := [] }

theorem u1102 : Upper (D 10) (R 10) [66,160,96,288,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1102 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1103 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 100 296 400 48 77 141 269), lower := (rows 67 162 100 296 400 48 64 128 256), losses := [] }

theorem u1103 : Upper (D 10) (R 10) [66,160,96,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1103 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1104 : Route 9 := (fun mask => (mask,id))

def c1104 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1104 : Upper (D 10) (R 10) [66,160,136,320,288,1] 13 := by
  apply FastRouting.sound _ _ [66,160,136,320,288,1] 13 (by decide) (choices 1) [4,16,32] r1104 c1104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u286
  · exact u287
  · exact u288

def b1105 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 140 328 304 36 113 177 305), lower := (rows 67 162 140 328 304 36 64 128 256), losses := [] }

theorem u1105 : Upper (D 10) (R 10) [66,160,136,320,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1105 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1106 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 67 162 140 328 304 48 101 165 293), lower := (rows 67 162 140 328 304 48 64 128 256), losses := [] }

theorem u1106 : Upper (D 10) (R 10) [66,160,136,320,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1106 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1107 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 35, targets := 256 }], pairs := [(0,8)], upper := (rows 67 162 196 268 304 33 120 184 312), lower := (rows 67 162 196 268 304 33 64 128 256), losses := [] }

theorem u1107 : Upper (D 10) (R 10) [66,160,192,260,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1107 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1108 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 195, targets := 256 }], pairs := [(0,8)], upper := (rows 67 162 196 268 304 40 113 177 305), lower := (rows 67 162 196 268 304 40 64 128 256), losses := [] }

theorem u1108 : Upper (D 10) (R 10) [66,160,192,260,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1108 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1109 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 67 162 196 268 304 48 105 169 297), lower := (rows 67 162 196 268 304 48 64 128 256), losses := [] }

theorem u1109 : Upper (D 10) (R 10) [66,160,192,260,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1109 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1110 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 100 168 304 33 92 156 284), lower := (rows 67 386 100 168 304 33 64 128 256), losses := [] }

theorem u1110 : Upper (D 10) (R 10) [66,384,96,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1110 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1111 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 100 168 304 36 89 153 281), lower := (rows 67 386 100 168 304 36 64 128 256), losses := [] }

theorem u1111 : Upper (D 10) (R 10) [66,384,96,160,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1111 [(5,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1112 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 67 386 100 168 304 40 85 149 277), lower := (rows 67 386 100 168 304 40 64 128 256), losses := [] }

theorem u1112 : Upper (D 10) (R 10) [66,384,96,160,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1112 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1113 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 23, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 11 52 104 112 416 448 384 384), lower := (rows 7 11 52 104 112 32 64 128 256), losses := [] }

theorem u1113 : Upper (D 10) (R 10) [6,9,48,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1113 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1114 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 7 11 52 104 176 480 448 448 448), lower := (rows 7 11 52 104 176 32 64 128 256), losses := [] }

theorem u1114 : Upper (D 10) (R 10) [6,9,48,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1114 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1115 : Route 9 := (fun mask => (mask,id))

def c1115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1115 : Upper (D 10) (R 10) [6,9,48,96,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,192] 13 (by decide) (choices 1) [128,256] r1115 c1115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u289
  · exact u290

def r1116 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1116 : Upper (D 10) (R 10) [6,9,48,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,384] 13 (by decide) (choices 1) [64,128] r1116 c1116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u291
  · exact u292

def b1117 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 4, targets := 384 }], pairs := [(2,7),(2,8)], upper := (rows 7 11 52 200 112 416 480 416 416), lower := (rows 7 11 52 200 112 32 64 128 256), losses := [] }

theorem u1117 : Upper (D 10) (R 10) [6,9,48,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1117 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1118 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 16, targets := 288 }], pairs := [(4,5),(4,8)], upper := (rows 7 11 52 200 208 288 352 416 288), lower := (rows 7 11 52 200 208 32 64 128 256), losses := [] }

theorem u1118 : Upper (D 10) (R 10) [6,9,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1118 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1119 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 7 11 52 200 304 480 480 480 480), lower := (rows 7 11 52 200 304 32 64 128 256), losses := [] }

theorem u1119 : Upper (D 10) (R 10) [6,9,48,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1119 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1120 : Route 9 := (fun mask => (mask,id))

def c1120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1120 : Upper (D 10) (R 10) [6,9,48,192,320] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320] 13 (by decide) (choices 1) [128,256] r1120 c1120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u293
  · exact u294

def r1121 : Route 9 := (fun mask => (mask,id))

def c1121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1121 : Upper (D 10) (R 10) [6,9,80,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,80,96,160] 13 (by decide) (choices 1) [128,256] r1121 c1121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u295
  · exact u296

def r1122 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1122 : Upper (D 10) (R 10) [6,9,80,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,80,96,384] 13 (by decide) (choices 1) [128] r1122 c1122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u297

def b1123 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 84 168 112 416 480 416 416), lower := (rows 7 11 84 168 112 32 64 128 256), losses := [] }

theorem u1123 : Upper (D 10) (R 10) [6,9,80,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1123 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1124 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 16, targets := 320 }], pairs := [(4,6),(4,8)], upper := (rows 7 11 84 168 176 352 352 480 352), lower := (rows 7 11 84 168 176 32 64 128 256), losses := [] }

theorem u1124 : Upper (D 10) (R 10) [6,9,80,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1124 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1125 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 84 168 208 288 352 416 288), lower := (rows 7 11 84 168 208 32 64 128 256), losses := [] }

theorem u1125 : Upper (D 10) (R 10) [6,9,80,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1125 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1126 : Route 9 := (fun mask => (mask,id))

def c1126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1126 : Upper (D 10) (R 10) [6,9,80,160,288] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,288] 13 (by decide) (choices 1) [64,128,256] r1126 c1126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u298
  · exact u299
  · exact u300

def b1127 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 84 168 336 416 480 416 416), lower := (rows 7 11 84 168 336 32 64 128 256), losses := [] }

theorem u1127 : Upper (D 10) (R 10) [6,9,80,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1127 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1128 : Route 9 := (fun mask => (mask,id))

def c1128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1128 : Upper (D 10) (R 10) [6,9,80,160,384] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160,384] 13 (by decide) (choices 1) [64,256] r1128 c1128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u301
  · exact u302

def b1129 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 324, targets := 128 }], pairs := [(2,7),(4,6)], upper := (rows 7 11 84 200 176 288 352 416 288), lower := (rows 7 11 84 200 176 32 64 128 256), losses := [] }

theorem u1129 : Upper (D 10) (R 10) [6,9,80,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1129 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1130 : Route 9 := (fun mask => (mask,id))

def c1130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1130 : Upper (D 10) (R 10) [6,9,80,192,288] 13 := by
  apply FastRouting.sound _ _ [6,9,80,192,288] 13 (by decide) (choices 1) [128,256] r1130 c1130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u303
  · exact u304

def b1131 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 100, targets := 128 }], pairs := [(2,7),(4,6)], upper := (rows 7 11 84 200 400 288 352 416 288), lower := (rows 7 11 84 200 400 32 64 128 256), losses := [] }

theorem u1131 : Upper (D 10) (R 10) [6,9,80,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1131 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1132 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 84 392 112 416 480 416 416), lower := (rows 7 11 84 392 112 32 64 128 256), losses := [] }

theorem u1132 : Upper (D 10) (R 10) [6,9,80,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1132 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1133 : Route 9 := (fun mask => (mask,id))

def c1133 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1133 : Upper (D 10) (R 10) [6,9,80,384,160] 13 := by
  apply FastRouting.sound _ _ [6,9,80,384,160] 13 (by decide) (choices 1) [64,256] r1133 c1133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u305
  · exact u306

def b1134 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 84 392 208 288 352 416 288), lower := (rows 7 11 84 392 208 32 64 128 256), losses := [] }

theorem u1134 : Upper (D 10) (R 10) [6,9,80,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1134 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1135 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 11 84 392 400 96 96 224 352), lower := (rows 7 11 84 392 400 32 64 128 256), losses := [] }

theorem u1135 : Upper (D 10) (R 10) [6,9,80,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1135 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1136 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 11 100 104 176 432 464 400 400), lower := (rows 7 11 100 104 176 32 64 128 256), losses := [] }

theorem u1136 : Upper (D 10) (R 10) [6,9,96,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1136 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1137 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 11 100 104 400 432 496 432 432), lower := (rows 7 11 100 104 400 32 64 128 256), losses := [] }

theorem u1137 : Upper (D 10) (R 10) [6,9,96,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1137 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1138 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 16, targets := 384 }], pairs := [(4,7),(4,8)], upper := (rows 7 11 100 168 112 432 464 400 400), lower := (rows 7 11 100 168 112 32 64 128 256), losses := [] }

theorem u1138 : Upper (D 10) (R 10) [6,9,96,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1138 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1139 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 296, targets := 64 },{ cop := 4, region := 292, targets := 128 }], pairs := [(2,7),(3,6)], upper := (rows 7 11 100 168 208 304 368 432 304), lower := (rows 7 11 100 168 208 32 64 128 256), losses := [] }

theorem u1139 : Upper (D 10) (R 10) [6,9,96,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1139 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1139
end Delivery.IrregularNine14.P10

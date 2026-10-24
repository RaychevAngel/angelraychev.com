import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0001

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r1080 : Route 9 := (fun mask => (mask,id))

def c1080 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1080 : Upper (D 6) (R 6) [6,33,136,20,288,64,2] 13 := by
  apply FastRouting.sound _ _ [6,33,136,20,288,64,2] 13 (by decide) (choices 1) [1,64] r1080 c1080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u60
  · exact u61

def r1081 : Route 9 := (fun mask => (mask,id))

def c1081 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1081 : Upper (D 6) (R 6) [6,33,136,20,320,64,1] 13 := by
  apply FastRouting.sound _ _ [6,33,136,20,320,64,1] 13 (by decide) (choices 1) [2,32] r1081 c1081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u62
  · exact u63

def b1082 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 7 35 140 28 336 96 66 161 289), lower := (rows 7 35 140 28 336 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 70 120 80 112 64 130 258), good := (rows 389 429 140 60 380 124 508 128 256) }] }

theorem u1082 : Upper (D 6) (R 6) [6,33,136,20,320,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1082
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1083 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 140 28 336 96 96 131 259), lower := (rows 7 35 140 28 336 96 96 128 256), losses := [] }

theorem u1083 : Upper (D 6) (R 6) [6,33,136,20,320,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1083
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1084 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 98, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,2),(2,1),(4,5)], upper := (rows 7 35 140 56 274 96 65 196 324), lower := (rows 7 35 140 56 274 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 28 24 16 115 67 145 273), good := (rows 485 481 140 444 508 96 481 128 256) }] }

theorem u1084 : Upper (D 6) (R 6) [6,33,136,48,258,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1084
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1085 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 32 }], pairs := [(2,1),(3,0),(4,5)], upper := (rows 7 35 140 56 274 96 68 193 321), lower := (rows 7 35 140 56 274 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 103 69 128 256), good := (rows 102 98 236 56 314 96 100 128 256) },{ target := 1, region := (rows 1 0 20 24 16 127 93 131 259), good := (rows 485 481 236 124 508 96 100 128 256) }] }

theorem u1085 : Upper (D 6) (R 6) [6,33,136,48,258,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1085
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1086 : Route 9 := (fun mask => (mask,id))

def c1086 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1086 : Upper (D 6) (R 6) [6,33,136,48,260,64,1] 13 := by
  apply FastRouting.sound _ _ [6,33,136,48,260,64,1] 13 (by decide) (choices 1) [2,64] r1086 c1086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u64
  · exact u65

def r1087 : Route 9 := (fun mask => (mask,id))

def c1087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1087 : Upper (D 6) (R 6) [6,33,136,48,260,64,2] 13 := by
  apply FastRouting.sound _ _ [6,33,136,48,260,64,2] 13 (by decide) (choices 1) [1,64] r1087 c1087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u66
  · exact u67

def b1088 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 140 74 112 288 65 148 276), lower := (rows 7 35 140 74 112 288 65 128 256), losses := [] }

theorem u1088 : Upper (D 6) (R 6) [6,33,136,66,96,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1088
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1089 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 72, targets := 1 },{ cop := 0, region := 368, targets := 2 }], pairs := [(3,0),(4,1)], upper := (rows 7 35 140 74 112 288 68 145 273), lower := (rows 7 35 140 74 112 288 68 128 256), losses := [] }

theorem u1089 : Upper (D 6) (R 6) [6,33,136,66,96,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1089
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1090 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 140 74 112 288 80 133 261), lower := (rows 7 35 140 74 112 288 80 128 256), losses := [] }

theorem u1090 : Upper (D 6) (R 6) [6,33,136,66,96,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1090
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1091 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 0, region := 72, targets := 1 }], pairs := [(3,0),(4,2),(4,6)], upper := (rows 7 35 140 74 273 96 68 176 304), lower := (rows 7 35 140 74 273 96 68 128 256), losses := [] }

theorem u1091 : Upper (D 6) (R 6) [6,33,136,66,257,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1091
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1092 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 140 74 273 96 80 164 292), lower := (rows 7 35 140 74 273 96 80 128 256), losses := [] }

theorem u1092 : Upper (D 6) (R 6) [6,33,136,66,257,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1092
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1093 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 405, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 140 74 273 96 96 148 276), lower := (rows 7 35 140 74 273 96 96 128 256), losses := [] }

theorem u1093 : Upper (D 6) (R 6) [6,33,136,66,257,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1093
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1094 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 140 74 336 48 65 164 292), lower := (rows 7 35 140 74 336 48 65 128 256), losses := [] }

theorem u1094 : Upper (D 6) (R 6) [6,33,136,66,320,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1094
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1095 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 72, targets := 1 },{ cop := 0, region := 368, targets := 2 }], pairs := [(3,0),(4,1)], upper := (rows 7 35 140 74 336 48 68 161 289), lower := (rows 7 35 140 74 336 48 68 128 256), losses := [] }

theorem u1095 : Upper (D 6) (R 6) [6,33,136,66,320,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1095
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1096 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 133, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 140 74 336 48 96 133 261), lower := (rows 7 35 140 74 336 48 96 128 256), losses := [] }

theorem u1096 : Upper (D 6) (R 6) [6,33,136,66,320,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1096
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1097 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 164, targets := 3 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 7 35 140 88 273 96 66 164 292), lower := (rows 7 35 140 88 273 96 66 128 256), losses := [] }

theorem u1097 : Upper (D 6) (R 6) [6,33,136,80,257,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1097
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1098 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 68 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 7 35 140 88 273 96 68 162 290), lower := (rows 7 35 140 88 273 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 127 93 131 259), good := (rows 486 482 236 124 508 96 100 128 256) }] }

theorem u1098 : Upper (D 6) (R 6) [6,33,136,80,257,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1098
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1099 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 272, targets := 96 },{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0),(4,5),(4,6)], upper := (rows 7 35 140 88 273 96 96 134 262), lower := (rows 7 35 140 88 273 96 96 128 256), losses := [] }

theorem u1099 : Upper (D 6) (R 6) [6,33,136,80,257,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1099
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1100 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 164, targets := 3 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 7 35 140 88 274 96 65 164 292), lower := (rows 7 35 140 88 274 96 65 128 256), losses := [] }

theorem u1100 : Upper (D 6) (R 6) [6,33,136,80,258,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1100
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1101 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 272, targets := 68 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 7 35 140 88 274 96 68 161 289), lower := (rows 7 35 140 88 274 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 127 93 131 259), good := (rows 485 481 236 124 508 96 100 128 256) }] }

theorem u1101 : Upper (D 6) (R 6) [6,33,136,80,258,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1101
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1102 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 140 88 274 96 96 133 261), lower := (rows 7 35 140 88 274 96 96 128 256), losses := [] }

theorem u1102 : Upper (D 6) (R 6) [6,33,136,80,258,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1102
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1103 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 140 88 276 96 65 162 290), lower := (rows 7 35 140 88 276 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 17 104 64 130 258), good := (rows 406 434 172 120 276 104 120 128 256) }] }

theorem u1103 : Upper (D 6) (R 6) [6,33,136,80,260,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1103
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1104 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 7 35 140 88 276 96 66 161 289), lower := (rows 7 35 140 88 276 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 70 104 83 104 64 130 258), good := (rows 405 445 172 124 276 124 508 128 256) }] }

theorem u1104 : Upper (D 6) (R 6) [6,33,136,80,260,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1104
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1105 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 140 88 276 96 96 131 259), lower := (rows 7 35 140 88 276 96 96 128 256), losses := [] }

theorem u1105 : Upper (D 6) (R 6) [6,33,136,80,260,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1105
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1106 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 7 35 140 88 304 96 65 134 262), lower := (rows 7 35 140 88 304 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 70 104 82 104 64 131 259), good := (rows 406 446 172 124 312 124 508 128 256) }] }

theorem u1106 : Upper (D 6) (R 6) [6,33,136,80,288,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1106
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1107 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 7 35 140 88 304 96 66 133 261), lower := (rows 7 35 140 88 304 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 70 104 82 104 64 131 259), good := (rows 405 445 172 124 312 124 508 128 256) }] }

theorem u1107 : Upper (D 6) (R 6) [6,33,136,80,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1107
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1108 : Route 9 := (fun mask => (mask,id))

def c1108 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1108 : Upper (D 6) (R 6) [6,33,136,80,288,64,4] 13 := by
  apply FastRouting.sound _ _ [6,33,136,80,288,64,4] 13 (by decide) (choices 1) [1,2] r1108 c1108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u68
  · exact u69

def b1109 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 140 104 81 288 66 148 276), lower := (rows 7 35 140 104 81 288 66 128 256), losses := [] }

theorem u1109 : Upper (D 6) (R 6) [6,33,136,96,65,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1109
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1110 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 140 104 81 288 68 146 274), lower := (rows 7 35 140 104 81 288 68 128 256), losses := [] }

theorem u1110 : Upper (D 6) (R 6) [6,33,136,96,65,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1110
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1111 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 140 104 81 288 80 134 262), lower := (rows 7 35 140 104 81 288 80 128 256), losses := [] }

theorem u1111 : Upper (D 6) (R 6) [6,33,136,96,65,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1111
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1112 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 140 104 82 288 65 148 276), lower := (rows 7 35 140 104 82 288 65 128 256), losses := [] }

theorem u1112 : Upper (D 6) (R 6) [6,33,136,96,66,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1112
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1113 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,0),(4,5)], upper := (rows 7 35 140 104 82 288 68 145 273), lower := (rows 7 35 140 104 82 288 68 128 256), losses := [] }

theorem u1113 : Upper (D 6) (R 6) [6,33,136,96,66,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1113
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1114 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 140 104 82 288 80 133 261), lower := (rows 7 35 140 104 82 288 80 128 256), losses := [] }

theorem u1114 : Upper (D 6) (R 6) [6,33,136,96,66,256,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1114
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1115 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 35 140 265 82 96 68 176 304), lower := (rows 7 35 140 265 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 127 77 155 283), good := (rows 502 498 492 508 498 96 100 128 256) }] }

theorem u1115 : Upper (D 6) (R 6) [6,33,136,257,66,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1115
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1116 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 265 82 96 80 164 292), lower := (rows 7 35 140 265 82 96 80 128 256), losses := [] }

theorem u1116 : Upper (D 6) (R 6) [6,33,136,257,66,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1116
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1117 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 397, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 140 265 82 96 96 148 276), lower := (rows 7 35 140 265 82 96 96 128 256), losses := [] }

theorem u1117 : Upper (D 6) (R 6) [6,33,136,257,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1117
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1118 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 98, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,2),(4,0),(4,5)], upper := (rows 7 35 140 265 84 96 66 176 304), lower := (rows 7 35 140 265 84 96 66 128 256), losses := [] }

theorem u1118 : Upper (D 6) (R 6) [6,33,136,257,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1118
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1119 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 265 84 96 80 162 290), lower := (rows 7 35 140 265 84 96 80 128 256), losses := [] }

theorem u1119 : Upper (D 6) (R 6) [6,33,136,257,68,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1119
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1120 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(4,0),(4,1)], upper := (rows 7 35 140 265 84 96 96 146 274), lower := (rows 7 35 140 265 84 96 96 128 256), losses := [] }

theorem u1120 : Upper (D 6) (R 6) [6,33,136,257,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1120
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1121 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 98, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,2),(4,1),(4,5)], upper := (rows 7 35 140 266 84 96 65 176 304), lower := (rows 7 35 140 266 84 96 65 128 256), losses := [] }

theorem u1121 : Upper (D 6) (R 6) [6,33,136,258,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1121
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1122 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 266 84 96 80 161 289), lower := (rows 7 35 140 266 84 96 80 128 256), losses := [] }

theorem u1122 : Upper (D 6) (R 6) [6,33,136,258,68,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1122
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1123 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(4,0),(4,1)], upper := (rows 7 35 140 266 84 96 96 145 273), lower := (rows 7 35 140 266 84 96 96 128 256), losses := [] }

theorem u1123 : Upper (D 6) (R 6) [6,33,136,258,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1123
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1124 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 268 81 96 66 176 304), lower := (rows 7 35 140 268 81 96 66 128 256), losses := [] }

theorem u1124 : Upper (D 6) (R 6) [6,33,136,260,65,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1124
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1125 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 268 81 96 80 162 290), lower := (rows 7 35 140 268 81 96 80 128 256), losses := [] }

theorem u1125 : Upper (D 6) (R 6) [6,33,136,260,65,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1125
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1126 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 114, targets := 4 },{ cop := 0, region := 112, targets := 2 }], pairs := [(1,2),(4,1),(4,2)], upper := (rows 7 35 140 268 81 96 96 146 274), lower := (rows 7 35 140 268 81 96 96 128 256), losses := [] }

theorem u1126 : Upper (D 6) (R 6) [6,33,136,260,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1126
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1127 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 268 82 96 65 176 304), lower := (rows 7 35 140 268 82 96 65 128 256), losses := [] }

theorem u1127 : Upper (D 6) (R 6) [6,33,136,260,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1127
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1128 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 268 82 96 80 161 289), lower := (rows 7 35 140 268 82 96 80 128 256), losses := [] }

theorem u1128 : Upper (D 6) (R 6) [6,33,136,260,66,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1128
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1129 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 397, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 140 268 82 96 96 145 273), lower := (rows 7 35 140 268 82 96 96 128 256), losses := [] }

theorem u1129 : Upper (D 6) (R 6) [6,33,136,260,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1129
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1130 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 280 82 96 65 164 292), lower := (rows 7 35 140 280 82 96 65 128 256), losses := [] }

theorem u1130 : Upper (D 6) (R 6) [6,33,136,272,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1130
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1131 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,0),(4,5)], upper := (rows 7 35 140 280 82 96 68 161 289), lower := (rows 7 35 140 280 82 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 127 93 131 259), good := (rows 485 481 236 380 508 96 100 128 256) }] }

theorem u1131 : Upper (D 6) (R 6) [6,33,136,272,66,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1131
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1132 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 397, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 140 280 82 96 96 133 261), lower := (rows 7 35 140 280 82 96 96 128 256), losses := [] }

theorem u1132 : Upper (D 6) (R 6) [6,33,136,272,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1132
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1133 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 98, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,2),(4,1),(4,5)], upper := (rows 7 35 140 280 84 96 65 162 290), lower := (rows 7 35 140 280 84 96 65 128 256), losses := [] }

theorem u1133 : Upper (D 6) (R 6) [6,33,136,272,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1133
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1134 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 98, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,2),(4,0),(4,5)], upper := (rows 7 35 140 280 84 96 66 161 289), lower := (rows 7 35 140 280 84 96 66 128 256), losses := [] }

theorem u1134 : Upper (D 6) (R 6) [6,33,136,272,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1134
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1135 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(4,0),(4,1)], upper := (rows 7 35 140 280 84 96 96 131 259), lower := (rows 7 35 140 280 84 96 96 128 256), losses := [] }

theorem u1135 : Upper (D 6) (R 6) [6,33,136,272,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1135
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1136 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 296 81 96 66 148 276), lower := (rows 7 35 140 296 81 96 66 128 256), losses := [] }

theorem u1136 : Upper (D 6) (R 6) [6,33,136,288,65,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1136
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1137 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,2),(3,2),(4,1)], upper := (rows 7 35 140 296 81 96 68 146 274), lower := (rows 7 35 140 296 81 96 68 128 256), losses := [] }

theorem u1137 : Upper (D 6) (R 6) [6,33,136,288,65,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1137
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1138 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 296 81 96 80 134 262), lower := (rows 7 35 140 296 81 96 80 128 256), losses := [] }

theorem u1138 : Upper (D 6) (R 6) [6,33,136,288,65,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1138
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1139 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 140 296 82 96 65 148 276), lower := (rows 7 35 140 296 82 96 65 128 256), losses := [] }

theorem u1139 : Upper (D 6) (R 6) [6,33,136,288,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1139
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1139
end Delivery.IrregularNine14.P06

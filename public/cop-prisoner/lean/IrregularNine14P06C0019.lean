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

def r1140 : Route 9 := (fun mask => (mask,id))

def c1140 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1140 : Upper (D 6) (R 6) [6,33,136,288,66,64,4] 13 := by
  apply FastRouting.sound _ _ [6,33,136,288,66,64,4] 13 (by decide) (choices 1) [1,16] r1140 c1140
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u70
  · exact u71

def b1141 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 296 82 96 80 133 261), lower := (rows 7 35 140 296 82 96 80 128 256), losses := [] }

theorem u1141 : Upper (D 6) (R 6) [6,33,136,288,66,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1141
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1142 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 98, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,2),(4,1),(4,5)], upper := (rows 7 35 140 296 84 96 65 146 274), lower := (rows 7 35 140 296 84 96 65 128 256), losses := [] }

theorem u1142 : Upper (D 6) (R 6) [6,33,136,288,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1142
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1143 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 98, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,2),(4,0),(4,5)], upper := (rows 7 35 140 296 84 96 66 145 273), lower := (rows 7 35 140 296 84 96 66 128 256), losses := [] }

theorem u1143 : Upper (D 6) (R 6) [6,33,136,288,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1143
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1144 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 296 84 96 80 131 259), lower := (rows 7 35 140 296 84 96 80 128 256), losses := [] }

theorem u1144 : Upper (D 6) (R 6) [6,33,136,288,68,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1144
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1145 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 88, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 35 196 25 112 288 66 140 268), lower := (rows 7 35 196 25 112 288 66 128 256), losses := [] }

theorem u1145 : Upper (D 6) (R 6) [6,33,192,17,96,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1145
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1146 : PairBound 9 := { available := 10, camps := [{ cop := 7, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 25 112 288 68 138 266), lower := (rows 7 35 196 25 112 288 68 128 256), losses := [] }

theorem u1146 : Upper (D 6) (R 6) [6,33,192,17,96,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1146
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1147 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 88, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 196 25 112 288 72 134 262), lower := (rows 7 35 196 25 112 288 72 128 256), losses := [] }

theorem u1147 : Upper (D 6) (R 6) [6,33,192,17,96,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1147
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1148 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 56 81 288 66 140 268), lower := (rows 7 35 196 56 81 288 66 128 256), losses := [] }

theorem u1148 : Upper (D 6) (R 6) [6,33,192,48,65,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1148
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1149 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 298, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 35 196 56 81 288 68 138 266), lower := (rows 7 35 196 56 81 288 68 128 256), losses := [] }

theorem u1149 : Upper (D 6) (R 6) [6,33,192,48,65,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1149
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1150 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 88, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 196 56 81 288 72 134 262), lower := (rows 7 35 196 56 81 288 72 128 256), losses := [] }

theorem u1150 : Upper (D 6) (R 6) [6,33,192,48,65,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1150
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1151 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 56 82 288 65 140 268), lower := (rows 7 35 196 56 82 288 65 128 256), losses := [] }

theorem u1151 : Upper (D 6) (R 6) [6,33,192,48,66,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1151
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1152 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 56 82 288 68 137 265), lower := (rows 7 35 196 56 82 288 68 128 256), losses := [] }

theorem u1152 : Upper (D 6) (R 6) [6,33,192,48,66,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1152
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1153 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 56 82 288 72 133 261), lower := (rows 7 35 196 56 82 288 72 128 256), losses := [] }

theorem u1153 : Upper (D 6) (R 6) [6,33,192,48,66,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1153
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1154 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 73 280 48 66 164 292), lower := (rows 7 35 196 73 280 48 66 128 256), losses := [] }

theorem u1154 : Upper (D 6) (R 6) [6,33,192,65,264,16,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1154
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1155 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 306, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 35 196 73 280 48 68 162 290), lower := (rows 7 35 196 73 280 48 68 128 256), losses := [] }

theorem u1155 : Upper (D 6) (R 6) [6,33,192,65,264,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1155
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1156 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 196, targets := 1 },{ cop := 1, region := 72, targets := 2 }], pairs := [(2,0),(3,1)], upper := (rows 7 35 196 73 280 48 96 134 262), lower := (rows 7 35 196 73 280 48 96 128 256), losses := [] }

theorem u1156 : Upper (D 6) (R 6) [6,33,192,65,264,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1156
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1157 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 88 273 40 66 164 292), lower := (rows 7 35 196 88 273 40 66 128 256), losses := [] }

theorem u1157 : Upper (D 6) (R 6) [6,33,192,80,257,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1157
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1158 : PairBound 9 := { available := 34, camps := [{ cop := 7, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 88 273 40 68 162 290), lower := (rows 7 35 196 88 273 40 68 128 256), losses := [] }

theorem u1158 : Upper (D 6) (R 6) [6,33,192,80,257,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1158
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1159 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 272, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 35 196 88 273 40 96 134 262), lower := (rows 7 35 196 88 273 40 96 128 256), losses := [] }

theorem u1159 : Upper (D 6) (R 6) [6,33,192,80,257,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1159
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1160 : PairBound 9 := { available := 34, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 88 276 40 65 162 290), lower := (rows 7 35 196 88 276 40 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 76 81 125 64 131 259), good := (rows 446 434 252 124 316 40 508 128 256) }] }

theorem u1160 : Upper (D 6) (R 6) [6,33,192,80,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1160
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1161 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(3,1)], upper := (rows 7 35 196 88 276 40 66 161 289), lower := (rows 7 35 196 88 276 40 66 128 256), losses := [{ target := 1, region := (rows 1 0 68 76 81 125 64 131 259), good := (rows 445 433 252 124 316 40 508 128 256) }] }

theorem u1161 : Upper (D 6) (R 6) [6,33,192,80,260,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1161
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1162 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 196 88 276 40 96 131 259), lower := (rows 7 35 196 88 276 40 96 128 256), losses := [] }

theorem u1162 : Upper (D 6) (R 6) [6,33,192,80,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1162
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1163 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 80, targets := 1 }], pairs := [(3,5),(4,0),(4,5)], upper := (rows 7 35 388 25 84 96 66 168 296), lower := (rows 7 35 388 25 84 96 66 128 256), losses := [] }

theorem u1163 : Upper (D 6) (R 6) [6,33,384,17,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1163
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1164 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 388 25 84 96 72 162 290), lower := (rows 7 35 388 25 84 96 72 128 256), losses := [] }

theorem u1164 : Upper (D 6) (R 6) [6,33,384,17,68,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1164
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1165 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 0, region := 112, targets := 1 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 7 35 388 25 84 96 96 138 266), lower := (rows 7 35 388 25 84 96 96 128 256), losses := [] }

theorem u1165 : Upper (D 6) (R 6) [6,33,384,17,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1165
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1166 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 88, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 35 388 26 84 96 65 168 296), lower := (rows 7 35 388 26 84 96 65 128 256), losses := [] }

theorem u1166 : Upper (D 6) (R 6) [6,33,384,18,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1166
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1167 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 388 26 84 96 72 161 289), lower := (rows 7 35 388 26 84 96 72 128 256), losses := [] }

theorem u1167 : Upper (D 6) (R 6) [6,33,384,18,68,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1167
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1168 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 389, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 388 26 84 96 96 137 265), lower := (rows 7 35 388 26 84 96 96 128 256), losses := [] }

theorem u1168 : Upper (D 6) (R 6) [6,33,384,18,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1168
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1169 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 388 28 81 96 66 168 296), lower := (rows 7 35 388 28 81 96 66 128 256), losses := [] }

theorem u1169 : Upper (D 6) (R 6) [6,33,384,20,65,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1169
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1170 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 388 28 81 96 72 162 290), lower := (rows 7 35 388 28 81 96 72 128 256), losses := [] }

theorem u1170 : Upper (D 6) (R 6) [6,33,384,20,65,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1170
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1171 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(3,1),(4,1)], upper := (rows 7 35 388 28 81 96 96 138 266), lower := (rows 7 35 388 28 81 96 96 128 256), losses := [] }

theorem u1171 : Upper (D 6) (R 6) [6,33,384,20,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1171
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1172 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 388 28 82 96 65 168 296), lower := (rows 7 35 388 28 82 96 65 128 256), losses := [] }

theorem u1172 : Upper (D 6) (R 6) [6,33,384,20,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1172
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1173 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 388 28 82 96 72 161 289), lower := (rows 7 35 388 28 82 96 72 128 256), losses := [] }

theorem u1173 : Upper (D 6) (R 6) [6,33,384,20,66,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1173
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1174 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 397, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 388 28 82 96 96 137 265), lower := (rows 7 35 388 28 82 96 96 128 256), losses := [] }

theorem u1174 : Upper (D 6) (R 6) [6,33,384,20,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1174
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1175 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 388 44 82 96 65 152 280), lower := (rows 7 35 388 44 82 96 65 128 256), losses := [] }

theorem u1175 : Upper (D 6) (R 6) [6,33,384,36,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1175
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1176 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 389, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 7 35 388 44 82 96 72 145 273), lower := (rows 7 35 388 44 82 96 72 128 256), losses := [] }

theorem u1176 : Upper (D 6) (R 6) [6,33,384,36,66,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1176
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1177 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 388 44 82 96 80 137 265), lower := (rows 7 35 388 44 82 96 80 128 256), losses := [] }

theorem u1177 : Upper (D 6) (R 6) [6,33,384,36,66,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1177
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1178 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 7 42 52 200 336 33 65 134 262), lower := (rows 7 42 52 200 336 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 80 32 64 129 257), good := (rows 390 42 52 216 344 416 472 128 256) }] }

theorem u1178 : Upper (D 6) (R 6) [6,40,48,192,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1178
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1179 : Route 9 := (fun mask => (mask,id))

def c1179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1179 : Upper (D 6) (R 6) [6,40,48,192,320,1,2] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,320,1,2] 13 (by decide) (choices 1) [1,4] r1179 c1179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u72
  · exact u73

def b1180 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 84 137 273 34 96 196 324), lower := (rows 7 42 84 137 273 34 96 128 256), losses := [] }

theorem u1180 : Upper (D 6) (R 6) [6,40,80,129,257,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1180
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1181 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 7 42 84 137 273 36 96 194 322), lower := (rows 7 42 84 137 273 36 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 53 127 139 267), good := (rows 486 490 116 490 500 100 96 128 256) }] }

theorem u1181 : Upper (D 6) (R 6) [6,40,80,129,257,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1181
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1182 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 84 137 273 96 96 134 262), lower := (rows 7 42 84 137 273 96 96 128 256), losses := [] }

theorem u1182 : Upper (D 6) (R 6) [6,40,80,129,257,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1182
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1183 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 69, targets := 32 },{ cop := 0, region := 232, targets := 2 }], pairs := [(0,5),(2,5),(3,1)], upper := (rows 7 42 84 137 274 96 65 164 292), lower := (rows 7 42 84 137 274 96 65 128 256), losses := [] }

theorem u1183 : Upper (D 6) (R 6) [6,40,80,129,258,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1183
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1184 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 68, targets := 3 },{ cop := 4, region := 69, targets := 32 }], pairs := [(0,5),(2,0),(2,1)], upper := (rows 7 42 84 137 274 96 68 161 289), lower := (rows 7 42 84 137 274 96 68 128 256), losses := [] }

theorem u1184 : Upper (D 6) (R 6) [6,40,80,129,258,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1184
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1185 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 84 137 274 96 96 133 261), lower := (rows 7 42 84 137 274 96 96 128 256), losses := [] }

theorem u1185 : Upper (D 6) (R 6) [6,40,80,129,258,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1185
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1186 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 234, targets := 4 }], pairs := [(1,2),(2,0),(3,2)], upper := (rows 7 42 84 137 276 96 65 162 290), lower := (rows 7 42 84 137 276 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 100 8 83 100 64 131 259), good := (rows 438 446 116 408 308 116 500 128 256) }] }

theorem u1186 : Upper (D 6) (R 6) [6,40,80,129,260,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1186
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1187 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 234, targets := 4 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(1,2),(3,2)], upper := (rows 7 42 84 137 276 96 66 161 289), lower := (rows 7 42 84 137 276 96 66 128 256), losses := [] }

theorem u1187 : Upper (D 6) (R 6) [6,40,80,129,260,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1187
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1188 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 42 84 137 276 96 96 131 259), lower := (rows 7 42 84 137 276 96 96 128 256), losses := [] }

theorem u1188 : Upper (D 6) (R 6) [6,40,80,129,260,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1188
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1189 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 136, targets := 32 },{ cop := 0, region := 136, targets := 64 },{ cop := 3, region := 98, targets := 4 }], pairs := [(1,2),(3,5),(3,6)], upper := (rows 7 42 84 137 304 96 65 134 262), lower := (rows 7 42 84 137 304 96 65 128 256), losses := [] }

theorem u1189 : Upper (D 6) (R 6) [6,40,80,129,288,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1189
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1190 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 7 42 84 137 304 96 66 133 261), lower := (rows 7 42 84 137 304 96 66 128 256), losses := [] }

theorem u1190 : Upper (D 6) (R 6) [6,40,80,129,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1190
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1191 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 42 84 137 304 96 68 131 259), lower := (rows 7 42 84 137 304 96 68 128 256), losses := [] }

theorem u1191 : Upper (D 6) (R 6) [6,40,80,129,288,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1191
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1192 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 304, targets := 64 }], pairs := [(3,0),(3,5),(4,6)], upper := (rows 7 42 84 200 304 33 65 134 262), lower := (rows 7 42 84 200 304 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 48 32 64 129 257), good := (rows 390 58 92 200 304 432 456 128 256) }] }

theorem u1192 : Upper (D 6) (R 6) [6,40,80,192,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1192
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1193 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 304, targets := 66 },{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 84 200 304 33 66 133 261), lower := (rows 7 42 84 200 304 33 66 128 256), losses := [] }

theorem u1193 : Upper (D 6) (R 6) [6,40,80,192,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1193
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1194 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 42 84 200 304 33 68 131 259), lower := (rows 7 42 84 200 304 33 68 128 256), losses := [] }

theorem u1194 : Upper (D 6) (R 6) [6,40,80,192,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1194
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1195 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 42 100 152 276 33 65 194 322), lower := (rows 7 42 100 152 276 33 65 128 256), losses := [] }

theorem u1195 : Upper (D 6) (R 6) [6,40,96,144,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1195
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1196 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 100 152 276 33 66 193 321), lower := (rows 7 42 100 152 276 33 66 128 256), losses := [] }

theorem u1196 : Upper (D 6) (R 6) [6,40,96,144,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1196
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1197 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 42 100 152 336 33 65 134 262), lower := (rows 7 42 100 152 336 33 65 128 256), losses := [] }

theorem u1197 : Upper (D 6) (R 6) [6,40,96,144,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1197
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1198 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 100 152 336 33 66 133 261), lower := (rows 7 42 100 152 336 33 66 128 256), losses := [] }

theorem u1198 : Upper (D 6) (R 6) [6,40,96,144,320,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1198
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1199 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 5, region := 68, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 100 152 336 33 68 131 259), lower := (rows 7 42 100 152 336 33 68 128 256), losses := [] }

theorem u1199 : Upper (D 6) (R 6) [6,40,96,144,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1199
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1199
end Delivery.IrregularNine14.P06

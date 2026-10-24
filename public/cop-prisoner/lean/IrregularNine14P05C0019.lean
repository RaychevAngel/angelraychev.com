import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0001

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1140 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 76 140 280 33 96 131 259), lower := (rows 19 38 76 140 280 33 96 128 256), losses := [] }

theorem u1140 : Upper (D 5) (R 5) [18,36,72,132,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1140
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1141 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 19 38 76 168 280 33 65 134 262), lower := (rows 19 38 76 168 280 33 65 128 256), losses := [] }

theorem u1141 : Upper (D 5) (R 5) [18,36,72,160,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1141
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1142 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 76 168 280 33 66 133 261), lower := (rows 19 38 76 168 280 33 66 128 256), losses := [] }

theorem u1142 : Upper (D 5) (R 5) [18,36,72,160,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1142
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1143 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 409, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 19 38 76 168 280 33 68 131 259), lower := (rows 19 38 76 168 280 33 68 128 256), losses := [] }

theorem u1143 : Upper (D 5) (R 5) [18,36,72,160,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1143
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1144 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 38 196 268 25 40 65 162 290), lower := (rows 19 38 196 268 25 40 65 128 256), losses := [] }

theorem u1144 : Upper (D 5) (R 5) [18,36,192,260,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1144
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m1145_1 : Upper (D 5) (R 5) [18,36,192,260,9,8,2,1] 13 :=
  permutation_upper _ _ _ [18,36,192,260,9,8,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u62

def r1145 : Route 9 := (fun mask => (mask,id))

def c1145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1145 : Upper (D 5) (R 5) [18,36,192,260,9,8,2] 13 := by
  apply FastRouting.sound _ _ [18,36,192,260,9,8,2] 13 (by decide) (choices 1) [1,32] r1145 c1145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m1145_1
  · exact u63

def b1146 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 38 196 268 25 40 96 131 259), lower := (rows 19 38 196 268 25 40 96 128 256), losses := [] }

theorem u1146 : Upper (D 5) (R 5) [18,36,192,260,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1146
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1147 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 66, targets := 8 }], pairs := [(1,3)], upper := (rows 19 67 37 42 152 288 68 140 268), lower := (rows 19 67 37 42 152 288 68 128 256), losses := [] }

theorem u1147 : Upper (D 5) (R 5) [18,65,33,34,136,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1147
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1148 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 67, targets := 4 }], pairs := [(0,2)], upper := (rows 19 67 37 42 152 288 72 132 260), lower := (rows 19 67 37 42 152 288 72 128 256), losses := [] }

theorem u1148 : Upper (D 5) (R 5) [18,65,33,34,136,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1148
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1149 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 67 37 138 276 40 68 168 296), lower := (rows 19 67 37 138 276 40 68 128 256), losses := [] }

theorem u1149 : Upper (D 5) (R 5) [18,65,33,130,260,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1149
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1150 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 37 138 276 40 72 164 292), lower := (rows 19 67 37 138 276 40 72 128 256), losses := [] }

theorem u1150 : Upper (D 5) (R 5) [18,65,33,130,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1150
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1151 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 66, targets := 4 },{ cop := 2, region := 66, targets := 8 }], pairs := [(1,2),(1,3)], upper := (rows 19 67 37 138 276 40 96 140 268), lower := (rows 19 67 37 138 276 40 96 128 256), losses := [] }

theorem u1151 : Upper (D 5) (R 5) [18,65,33,130,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1151
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1152 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 67, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 37 140 276 40 66 168 296), lower := (rows 19 67 37 140 276 40 66 128 256), losses := [] }

theorem u1152 : Upper (D 5) (R 5) [18,65,33,132,260,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1152
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1153 : PairBound 9 := { available := 34, camps := [], pairs := [(3,0),(4,0)], upper := (rows 19 67 37 140 276 40 72 162 290), lower := (rows 19 67 37 140 276 40 72 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 124 124 131 259), good := (rows 498 482 508 252 380 104 104 128 256) }] }

theorem u1153 : Upper (D 5) (R 5) [18,65,33,132,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1153
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1154 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 66, targets := 4 },{ cop := 2, region := 66, targets := 8 }], pairs := [(1,2),(1,3)], upper := (rows 19 67 37 140 276 40 96 138 266), lower := (rows 19 67 37 140 276 40 96 128 256), losses := [] }

theorem u1154 : Upper (D 5) (R 5) [18,65,33,132,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1154
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1155 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 67 38 137 276 40 68 168 296), lower := (rows 19 67 38 137 276 40 68 128 256), losses := [] }

theorem u1155 : Upper (D 5) (R 5) [18,65,34,129,260,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1155
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1156 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 38 137 276 40 72 164 292), lower := (rows 19 67 38 137 276 40 72 128 256), losses := [] }

theorem u1156 : Upper (D 5) (R 5) [18,65,34,129,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1156
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1157 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 67 38 137 276 40 96 140 268), lower := (rows 19 67 38 137 276 40 96 128 256), losses := [] }

theorem u1157 : Upper (D 5) (R 5) [18,65,34,129,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1157
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1158 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 67 38 137 304 40 68 140 268), lower := (rows 19 67 38 137 304 40 68 128 256), losses := [] }

theorem u1158 : Upper (D 5) (R 5) [18,65,34,129,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1158
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1159 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 67 38 137 304 40 72 132 260), lower := (rows 19 67 38 137 304 40 72 128 256), losses := [] }

theorem u1159 : Upper (D 5) (R 5) [18,65,34,129,288,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1159
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1160 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 136, targets := 1 }], pairs := [(3,0)], upper := (rows 19 67 38 140 56 288 65 140 268), lower := (rows 19 67 38 140 56 288 65 128 256), losses := [] }

theorem u1160 : Upper (D 5) (R 5) [18,65,34,132,40,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1160
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1161 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3)], upper := (rows 19 67 38 140 56 288 68 137 265), lower := (rows 19 67 38 140 56 288 68 128 256), losses := [] }

theorem u1161 : Upper (D 5) (R 5) [18,65,34,132,40,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1161
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1162 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 67, targets := 4 }], pairs := [(0,2)], upper := (rows 19 67 38 140 56 288 72 133 261), lower := (rows 19 67 38 140 56 288 72 128 256), losses := [] }

theorem u1162 : Upper (D 5) (R 5) [18,65,34,132,40,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1162
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1163 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 67, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 38 140 276 40 65 168 296), lower := (rows 19 67 38 140 276 40 65 128 256), losses := [] }

theorem u1163 : Upper (D 5) (R 5) [18,65,34,132,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1163
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1164 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 273, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 67 38 140 276 40 72 161 289), lower := (rows 19 67 38 140 276 40 72 128 256), losses := [] }

theorem u1164 : Upper (D 5) (R 5) [18,65,34,132,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1164
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1165 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 67 38 140 276 40 96 137 265), lower := (rows 19 67 38 140 276 40 96 128 256), losses := [] }

theorem u1165 : Upper (D 5) (R 5) [18,65,34,132,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1165
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1166 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 140 280 40 65 164 292), lower := (rows 19 67 38 140 280 40 65 128 256), losses := [] }

theorem u1166 : Upper (D 5) (R 5) [18,65,34,132,264,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1166
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1167 : PairBound 9 := { available := 33, camps := [], pairs := [(2,0),(3,1)], upper := (rows 19 67 38 140 280 40 68 161 289), lower := (rows 19 67 38 140 280 40 68 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 56 79 128 256), good := (rows 118 70 102 236 376 104 68 128 256) },{ target := 1, region := (rows 1 0 4 12 20 124 76 131 259), good := (rows 433 481 508 252 376 104 124 128 256) }] }

theorem u1167 : Upper (D 5) (R 5) [18,65,34,132,264,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1167
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1168 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 67 38 140 280 40 96 133 261), lower := (rows 19 67 38 140 280 40 96 128 256), losses := [] }

theorem u1168 : Upper (D 5) (R 5) [18,65,34,132,264,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1168
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1169 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 140 304 40 65 140 268), lower := (rows 19 67 38 140 304 40 65 128 256), losses := [] }

theorem u1169 : Upper (D 5) (R 5) [18,65,34,132,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1169
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1170 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 67 38 140 304 40 68 137 265), lower := (rows 19 67 38 140 304 40 68 128 256), losses := [] }

theorem u1170 : Upper (D 5) (R 5) [18,65,34,132,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1170
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1171 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 273, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 67 38 140 304 40 72 133 261), lower := (rows 19 67 38 140 304 40 72 128 256), losses := [] }

theorem u1171 : Upper (D 5) (R 5) [18,65,34,132,288,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1171
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1172 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 392, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 38 392 28 40 65 164 292), lower := (rows 19 67 38 392 28 40 65 128 256), losses := [] }

theorem u1172 : Upper (D 5) (R 5) [18,65,34,384,12,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1172
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1173 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 67 38 392 28 40 68 161 289), lower := (rows 19 67 38 392 28 40 68 128 256), losses := [] }

theorem u1173 : Upper (D 5) (R 5) [18,65,34,384,12,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1173
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1174 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 67 38 392 28 40 96 133 261), lower := (rows 19 67 38 392 28 40 96 128 256), losses := [] }

theorem u1174 : Upper (D 5) (R 5) [18,65,34,384,12,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1174
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1175 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 140, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 140 276 33 66 168 296), lower := (rows 19 67 44 140 276 33 66 128 256), losses := [] }

theorem u1175 : Upper (D 5) (R 5) [18,65,40,132,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1175
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1176 : PairBound 9 := { available := 34, camps := [], pairs := [(0,2),(1,2)], upper := (rows 19 67 44 140 276 33 72 162 290), lower := (rows 19 67 44 140 276 33 72 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 51 76 147 275), good := (rows 435 483 104 200 499 417 72 128 256) }] }

theorem u1176 : Upper (D 5) (R 5) [18,65,40,132,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1176
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1177 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 140 276 33 96 138 266), lower := (rows 19 67 44 140 276 33 96 128 256), losses := [] }

theorem u1177 : Upper (D 5) (R 5) [18,65,40,132,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1177
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1178 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 140, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 140 276 34 65 168 296), lower := (rows 19 67 44 140 276 34 65 128 256), losses := [] }

theorem u1178 : Upper (D 5) (R 5) [18,65,40,132,260,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1178
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1179 : PairBound 9 := { available := 33, camps := [], pairs := [(0,2),(1,2)], upper := (rows 19 67 44 140 276 34 72 161 289), lower := (rows 19 67 44 140 276 34 72 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 51 76 147 275), good := (rows 435 483 104 200 499 418 72 128 256) }] }

theorem u1179 : Upper (D 5) (R 5) [18,65,40,132,260,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1179
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1180 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 140 276 34 96 137 265), lower := (rows 19 67 44 140 276 34 96 128 256), losses := [] }

theorem u1180 : Upper (D 5) (R 5) [18,65,40,132,260,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1180
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1181 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 140, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 140 280 33 66 164 292), lower := (rows 19 67 44 140 280 33 66 128 256), losses := [] }

theorem u1181 : Upper (D 5) (R 5) [18,65,40,132,264,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1181
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1182 : PairBound 9 := { available := 34, camps := [], pairs := [(0,3),(1,3)], upper := (rows 19 67 44 140 280 33 68 162 290), lower := (rows 19 67 44 140 280 33 68 128 256), losses := [{ target := 3, region := (rows 17 18 4 0 16 51 76 147 275), good := (rows 435 483 100 196 499 417 68 128 256) }] }

theorem u1182 : Upper (D 5) (R 5) [18,65,40,132,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1182
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1183 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 140 280 33 96 134 262), lower := (rows 19 67 44 140 280 33 96 128 256), losses := [] }

theorem u1183 : Upper (D 5) (R 5) [18,65,40,132,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1183
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1184 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 140, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 140 280 34 65 164 292), lower := (rows 19 67 44 140 280 34 65 128 256), losses := [] }

theorem u1184 : Upper (D 5) (R 5) [18,65,40,132,264,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1184
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1185 : PairBound 9 := { available := 33, camps := [], pairs := [(0,3),(1,3)], upper := (rows 19 67 44 140 280 34 68 161 289), lower := (rows 19 67 44 140 280 34 68 128 256), losses := [{ target := 3, region := (rows 17 18 4 0 16 51 76 147 275), good := (rows 435 483 100 196 499 418 68 128 256) }] }

theorem u1185 : Upper (D 5) (R 5) [18,65,40,132,264,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1185
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1186 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 99, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 44 140 280 34 96 133 261), lower := (rows 19 67 44 140 280 34 96 128 256), losses := [] }

theorem u1186 : Upper (D 5) (R 5) [18,65,40,132,264,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1186
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1187 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 140, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 44 140 304 34 65 140 268), lower := (rows 19 67 44 140 304 34 65 128 256), losses := [] }

theorem u1187 : Upper (D 5) (R 5) [18,65,40,132,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1187
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1188 : PairBound 9 := { available := 9, camps := [], pairs := [(2,1),(3,1)], upper := (rows 19 67 44 140 304 34 68 137 265), lower := (rows 19 67 44 140 304 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 52 41 48 32 125 131 259), good := (rows 477 457 124 204 380 508 68 128 256) }] }

theorem u1188 : Upper (D 5) (R 5) [18,65,40,132,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1188
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1189 : Route 9 := (fun mask => (mask,id))

def c1189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1189 : Upper (D 5) (R 5) [18,65,40,132,288,2,8] 13 := by
  apply FastRouting.sound _ _ [18,65,40,132,288,2,8] 13 (by decide) (choices 1) [1,4] r1189 c1189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u64
  · exact u65

def b1190 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 67 133 266 52 40 68 168 296), lower := (rows 19 67 133 266 52 40 68 128 256), losses := [] }

theorem u1190 : Upper (D 5) (R 5) [18,65,129,258,36,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1190
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1191 : PairBound 9 := { available := 36, camps := [], pairs := [(3,0),(4,0)], upper := (rows 19 67 133 266 52 40 72 164 292), lower := (rows 19 67 133 266 52 40 72 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 20 111 111 148 276), good := (rows 506 106 508 362 500 104 104 128 256) }] }

theorem u1191 : Upper (D 5) (R 5) [18,65,129,258,36,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1191
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1192 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 67, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 133 266 52 40 96 140 268), lower := (rows 19 67 133 266 52 40 96 128 256), losses := [] }

theorem u1192 : Upper (D 5) (R 5) [18,65,129,258,36,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1192
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1193 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 8 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,3),(1,5)], upper := (rows 19 67 133 266 56 36 68 168 296), lower := (rows 19 67 133 266 56 36 68 128 256), losses := [] }

theorem u1193 : Upper (D 5) (R 5) [18,65,129,258,40,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1193
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1194 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 67, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 67 133 266 56 36 72 164 292), lower := (rows 19 67 133 266 56 36 72 128 256), losses := [] }

theorem u1194 : Upper (D 5) (R 5) [18,65,129,258,40,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1194
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1195 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 67, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 67 133 266 56 36 96 140 268), lower := (rows 19 67 133 266 56 36 96 128 256), losses := [] }

theorem u1195 : Upper (D 5) (R 5) [18,65,129,258,40,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1195
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1196 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 67 134 296 28 36 65 168 296), lower := (rows 19 67 134 296 28 36 65 128 256), losses := [] }

theorem u1196 : Upper (D 5) (R 5) [18,65,130,288,12,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1196
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1197 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 67, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 67 134 296 28 36 72 161 289), lower := (rows 19 67 134 296 28 36 72 128 256), losses := [] }

theorem u1197 : Upper (D 5) (R 5) [18,65,130,288,12,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1197
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1198 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 99, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 67 134 296 28 36 96 137 265), lower := (rows 19 67 134 296 28 36 96 128 256), losses := [] }

theorem u1198 : Upper (D 5) (R 5) [18,65,130,288,12,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1198
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1199 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 140 268 52 33 66 168 296), lower := (rows 19 67 140 268 52 33 66 128 256), losses := [] }

theorem u1199 : Upper (D 5) (R 5) [18,65,136,260,36,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1199
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1199
end Delivery.IrregularNine14.P05

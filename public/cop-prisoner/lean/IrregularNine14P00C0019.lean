import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0004
import IrregularNine14P00C0005

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1140 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 268 137 144 113 113 241 369), lower := (rows 23 98 268 137 144 32 64 128 256), losses := [] }

theorem u1140 : Upper (D 0) (R 0) [22,96,264,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1140
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1141 : Route 9 := (fun mask => (mask,id))

def c1141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1141 : Upper (D 0) (R 0) [22,96,264,160,1] 13 := by
  apply FastRouting.sound _ _ [22,96,264,160,1] 13 (by decide) (choices 1) [1,16,64,128] r1141 c1141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u286
  · exact u287
  · exact u288
  · exact u289

def b1142 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 268 168 80 177 209 145 401), lower := (rows 23 98 268 168 80 32 64 128 256), losses := [] }

theorem u1142 : Upper (D 0) (R 0) [22,96,264,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1142
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1143 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 268 168 144 113 81 209 337), lower := (rows 23 98 268 168 144 32 64 128 256), losses := [] }

theorem u1143 : Upper (D 0) (R 0) [22,96,264,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1143
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1144 : Route 9 := (fun mask => (mask,id))

def c1144 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1144 : Upper (D 0) (R 0) [22,96,384,48,1] 13 := by
  apply FastRouting.sound _ _ [22,96,384,48,1] 13 (by decide) (choices 1) [1,8,64,128] r1144 c1144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u290
  · exact u291
  · exact u292
  · exact u293

def b1145 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 23 98 388 56 24 225 193 193 449), lower := (rows 23 98 388 56 24 32 64 128 256), losses := [] }

theorem u1145 : Upper (D 0) (R 0) [22,96,384,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1145
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1146 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 388 56 80 169 201 137 393), lower := (rows 23 98 388 56 80 32 64 128 256), losses := [] }

theorem u1146 : Upper (D 0) (R 0) [22,96,384,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1146
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1147 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 23 98 388 56 144 105 73 201 329), lower := (rows 23 98 388 56 144 32 64 128 256), losses := [] }

theorem u1147 : Upper (D 0) (R 0) [22,96,384,48,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1147
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1148 : Route 9 := (fun mask => (mask,id))

def c1148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1148 : Upper (D 0) (R 0) [22,96,384,144,1] 13 := by
  apply FastRouting.sound _ _ [22,96,384,144,1] 13 (by decide) (choices 1) [1,8,64] r1148 c1148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u294
  · exact u295
  · exact u296

def b1149 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 23 98 388 152 24 97 97 225 353), lower := (rows 23 98 388 152 24 32 64 128 256), losses := [] }

theorem u1149 : Upper (D 0) (R 0) [22,96,384,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1149
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1150 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 388 152 48 105 73 201 329), lower := (rows 23 98 388 152 48 32 64 128 256), losses := [] }

theorem u1150 : Upper (D 0) (R 0) [22,96,384,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1150
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1151 : Route 9 := (fun mask => (mask,id))

def c1151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1151 : Upper (D 0) (R 0) [22,96,384,160,1] 13 := by
  apply FastRouting.sound _ _ [22,96,384,160,1] 13 (by decide) (choices 1) [1,8,16,64] r1151 c1151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u297
  · exact u298
  · exact u299
  · exact u300

def b1152 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 23 98 388 168 24 113 81 209 337), lower := (rows 23 98 388 168 24 32 64 128 256), losses := [] }

theorem u1152 : Upper (D 0) (R 0) [22,96,384,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1152
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1153 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 388 168 80 57 89 153 281), lower := (rows 23 98 388 168 80 32 64 128 256), losses := [] }

theorem u1153 : Upper (D 0) (R 0) [22,96,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1153
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1154 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 76 152 17 480 480 480 480), lower := (rows 51 7 76 152 17 32 64 128 256), losses := [] }

theorem u1154 : Upper (D 0) (R 0) [50,5,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1154
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1155 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 76 152 48 481 449 449 449), lower := (rows 51 7 76 152 48 32 64 128 256), losses := [] }

theorem u1155 : Upper (D 0) (R 0) [50,5,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1155
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1156 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 76 152 80 417 481 417 417), lower := (rows 51 7 76 152 80 32 64 128 256), losses := [] }

theorem u1156 : Upper (D 0) (R 0) [50,5,72,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1156
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1157 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 7 76 152 144 353 353 481 353), lower := (rows 51 7 76 152 144 32 64 128 256), losses := [] }

theorem u1157 : Upper (D 0) (R 0) [50,5,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1157
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1158 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 7 76 152 272 225 225 225 481), lower := (rows 51 7 76 152 272 32 64 128 256), losses := [] }

theorem u1158 : Upper (D 0) (R 0) [50,5,72,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1158
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1159 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 76 280 17 224 224 224 480), lower := (rows 51 7 76 280 17 32 64 128 256), losses := [] }

theorem u1159 : Upper (D 0) (R 0) [50,5,72,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1159
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1160 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 76 280 48 225 193 193 449), lower := (rows 51 7 76 280 48 32 64 128 256), losses := [] }

theorem u1160 : Upper (D 0) (R 0) [50,5,72,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1160
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1161 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 76 280 80 161 225 161 417), lower := (rows 51 7 76 280 80 32 64 128 256), losses := [] }

theorem u1161 : Upper (D 0) (R 0) [50,5,72,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1161
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1162 : Route 9 := (fun mask => (mask,id))

def c1162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1162 : Upper (D 0) (R 0) [50,5,72,272,128] 13 := by
  apply FastRouting.sound _ _ [50,5,72,272,128] 13 (by decide) (choices 1) [1,64,128] r1162 c1162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u301
  · exact u302
  · exact u303

def b1163 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 76 392 17 240 240 240 496), lower := (rows 51 7 76 392 17 32 64 128 256), losses := [] }

theorem u1163 : Upper (D 0) (R 0) [50,5,72,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1163
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1164 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 76 392 48 241 209 209 465), lower := (rows 51 7 76 392 48 32 64 128 256), losses := [] }

theorem u1164 : Upper (D 0) (R 0) [50,5,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1164
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1165 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 76 392 80 177 241 177 433), lower := (rows 51 7 76 392 80 32 64 128 256), losses := [] }

theorem u1165 : Upper (D 0) (R 0) [50,5,72,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1165
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1166_1 : Upper (D 0) (R 0) [50,5,72,384,128,1] 13 :=
  permutation_upper _ _ _ [50,5,72,384,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u304

theorem m1166_16 : Upper (D 0) (R 0) [50,5,72,384,128,16] 13 :=
  permutation_upper _ _ _ [50,5,72,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u305

theorem m1166_64 : Upper (D 0) (R 0) [50,5,72,384,128,64] 13 :=
  permutation_upper _ _ _ [50,5,72,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u306

def r1166 : Route 9 := (fun mask => (mask,id))

def c1166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1166 : Upper (D 0) (R 0) [50,5,72,384,128] 13 := by
  apply FastRouting.sound _ _ [50,5,72,384,128] 13 (by decide) (choices 1) [1,16,64] r1166 c1166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1166_1
  · exact m1166_16
  · exact m1166_64

def b1167 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 196 88 17 424 488 424 424), lower := (rows 51 7 196 88 17 32 64 128 256), losses := [] }

theorem u1167 : Upper (D 0) (R 0) [50,5,192,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1167
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1168 : PairBound 9 := { available := 417, camps := [], pairs := [], upper := (rows 51 7 196 88 24 417 481 417 417), lower := (rows 51 7 196 88 24 32 64 128 256), losses := [] }

theorem u1168 : Upper (D 0) (R 0) [50,5,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1168
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1169 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 196 88 48 425 457 393 393), lower := (rows 51 7 196 88 48 32 64 128 256), losses := [] }

theorem u1169 : Upper (D 0) (R 0) [50,5,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1169
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1170 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 51 7 196 88 144 297 361 425 297), lower := (rows 51 7 196 88 144 32 64 128 256), losses := [] }

theorem u1170 : Upper (D 0) (R 0) [50,5,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1170
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1171 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 51 7 196 88 272 169 233 169 425), lower := (rows 51 7 196 88 272 32 64 128 256), losses := [] }

theorem u1171 : Upper (D 0) (R 0) [50,5,192,80,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1171
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1172 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 196 280 17 232 232 232 488), lower := (rows 51 7 196 280 17 32 64 128 256), losses := [] }

theorem u1172 : Upper (D 0) (R 0) [50,5,192,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1172
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1173 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 7 196 280 24 225 225 225 481), lower := (rows 51 7 196 280 24 32 64 128 256), losses := [] }

theorem u1173 : Upper (D 0) (R 0) [50,5,192,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1173
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1174 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 196 280 48 233 201 201 457), lower := (rows 51 7 196 280 48 32 64 128 256), losses := [] }

theorem u1174 : Upper (D 0) (R 0) [50,5,192,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1174
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1175 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 196 280 80 169 233 169 425), lower := (rows 51 7 196 280 80 32 64 128 256), losses := [] }

theorem u1175 : Upper (D 0) (R 0) [50,5,192,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1175
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1176 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 196 328 17 184 248 184 440), lower := (rows 51 7 196 328 17 32 64 128 256), losses := [] }

theorem u1176 : Upper (D 0) (R 0) [50,5,192,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1176
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1177 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 7 196 328 24 177 241 177 433), lower := (rows 51 7 196 328 24 32 64 128 256), losses := [] }

theorem u1177 : Upper (D 0) (R 0) [50,5,192,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1177
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1178 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 196 328 48 185 217 153 409), lower := (rows 51 7 196 328 48 32 64 128 256), losses := [] }

theorem u1178 : Upper (D 0) (R 0) [50,5,192,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1178
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1179 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 7 196 328 144 57 121 185 313), lower := (rows 51 7 196 328 144 32 64 128 256), losses := [] }

theorem u1179 : Upper (D 0) (R 0) [50,5,192,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1179
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1180 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 268 88 17 224 224 224 480), lower := (rows 51 7 268 88 17 32 64 128 256), losses := [] }

theorem u1180 : Upper (D 0) (R 0) [50,5,264,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1180
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1181 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 268 88 48 225 193 193 449), lower := (rows 51 7 268 88 48 32 64 128 256), losses := [] }

theorem u1181 : Upper (D 0) (R 0) [50,5,264,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1181
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1182 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 51 7 268 88 80 161 225 161 417), lower := (rows 51 7 268 88 80 32 64 128 256), losses := [] }

theorem u1182 : Upper (D 0) (R 0) [50,5,264,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1182
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1183 : Route 9 := (fun mask => (mask,id))

def c1183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1183 : Upper (D 0) (R 0) [50,5,264,80,128] 13 := by
  apply FastRouting.sound _ _ [50,5,264,80,128] 13 (by decide) (choices 1) [1,64,128] r1183 c1183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u307
  · exact u308
  · exact u309

def b1184 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 268 200 17 240 240 240 496), lower := (rows 51 7 268 200 17 32 64 128 256), losses := [] }

theorem u1184 : Upper (D 0) (R 0) [50,5,264,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1184
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1185 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 268 200 48 241 209 209 465), lower := (rows 51 7 268 200 48 32 64 128 256), losses := [] }

theorem u1185 : Upper (D 0) (R 0) [50,5,264,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1185
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1186_1 : Upper (D 0) (R 0) [50,5,264,192,64,1] 13 :=
  permutation_upper _ _ _ [50,5,264,192,1,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u310

theorem m1186_16 : Upper (D 0) (R 0) [50,5,264,192,64,16] 13 :=
  permutation_upper _ _ _ [50,5,264,192,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u311

def r1186 : Route 9 := (fun mask => (mask,id))

def c1186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1186 : Upper (D 0) (R 0) [50,5,264,192,64] 13 := by
  apply FastRouting.sound _ _ [50,5,264,192,64] 13 (by decide) (choices 1) [1,16,128] r1186 c1186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1186_1
  · exact m1186_16
  · exact u312

def b1187 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 324 88 17 168 232 168 424), lower := (rows 51 7 324 88 17 32 64 128 256), losses := [] }

theorem u1187 : Upper (D 0) (R 0) [50,5,320,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1187
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1188 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 7 324 88 24 161 225 161 417), lower := (rows 51 7 324 88 24 32 64 128 256), losses := [] }

theorem u1188 : Upper (D 0) (R 0) [50,5,320,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1188
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1189 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 324 88 48 169 201 137 393), lower := (rows 51 7 324 88 48 32 64 128 256), losses := [] }

theorem u1189 : Upper (D 0) (R 0) [50,5,320,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1189
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1190 : Route 9 := (fun mask => (mask,id))

def c1190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1190 : Upper (D 0) (R 0) [50,5,320,80,128] 13 := by
  apply FastRouting.sound _ _ [50,5,320,80,128] 13 (by decide) (choices 1) [1,8,128] r1190 c1190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u313
  · exact u314
  · exact u315

def b1191 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 324 152 17 232 232 232 488), lower := (rows 51 7 324 152 17 32 64 128 256), losses := [] }

theorem u1191 : Upper (D 0) (R 0) [50,5,320,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1191
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1192 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 7 324 152 24 225 225 225 481), lower := (rows 51 7 324 152 24 32 64 128 256), losses := [] }

theorem u1192 : Upper (D 0) (R 0) [50,5,320,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1192
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1193 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 324 152 48 233 201 201 457), lower := (rows 51 7 324 152 48 32 64 128 256), losses := [] }

theorem u1193 : Upper (D 0) (R 0) [50,5,320,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1193
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1194 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 324 152 80 169 233 169 425), lower := (rows 51 7 324 152 80 32 64 128 256), losses := [] }

theorem u1194 : Upper (D 0) (R 0) [50,5,320,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1194
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1195 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 7 324 152 144 105 105 233 361), lower := (rows 51 7 324 152 144 32 64 128 256), losses := [] }

theorem u1195 : Upper (D 0) (R 0) [50,5,320,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1195
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1196 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 7 324 200 17 184 248 184 440), lower := (rows 51 7 324 200 17 32 64 128 256), losses := [] }

theorem u1196 : Upper (D 0) (R 0) [50,5,320,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1196
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1197 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 7 324 200 24 177 241 177 433), lower := (rows 51 7 324 200 24 32 64 128 256), losses := [] }

theorem u1197 : Upper (D 0) (R 0) [50,5,320,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1197
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1198 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 324 200 48 185 217 153 409), lower := (rows 51 7 324 200 48 32 64 128 256), losses := [] }

theorem u1198 : Upper (D 0) (R 0) [50,5,320,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1198
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1199_1 : Upper (D 0) (R 0) [50,5,320,192,128,1] 13 :=
  permutation_upper _ _ _ [50,5,320,192,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u316

theorem m1199_8 : Upper (D 0) (R 0) [50,5,320,192,128,8] 13 :=
  permutation_upper _ _ _ [50,5,320,192,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u317

theorem m1199_16 : Upper (D 0) (R 0) [50,5,320,192,128,16] 13 :=
  permutation_upper _ _ _ [50,5,320,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u318

def r1199 : Route 9 := (fun mask => (mask,id))

def c1199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1199 : Upper (D 0) (R 0) [50,5,320,192,128] 13 := by
  apply FastRouting.sound _ _ [50,5,320,192,128] 13 (by decide) (choices 1) [1,8,16] r1199 c1199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1199_1
  · exact m1199_8
  · exact m1199_16

#print axioms u1199
end Delivery.IrregularNine14.P00

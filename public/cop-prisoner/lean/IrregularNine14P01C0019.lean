import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0002

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1140 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 134 276 42 18 40 193 193 449), lower := (rows 113 134 276 42 18 40 64 128 256), losses := [] }

theorem u1140 : Upper (D 1) (R 1) [112,132,272,34,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1140
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1141 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 276 42 18 96 201 137 393), lower := (rows 113 134 276 42 18 96 64 128 256), losses := [] }

theorem u1141 : Upper (D 1) (R 1) [112,132,272,34,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1141
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1142 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 113 134 276 42 18 160 73 201 329), lower := (rows 113 134 276 42 18 160 64 128 256), losses := [] }

theorem u1142 : Upper (D 1) (R 1) [112,132,272,34,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1142
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1143 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 134 276 42 144 33 74 202 330), lower := (rows 113 134 276 42 144 33 64 128 256), losses := [] }

theorem u1143 : Upper (D 1) (R 1) [112,132,272,34,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1143
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1144 : PairBound 9 := { available := 73, camps := [{ cop := 5, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 134 276 42 144 34 73 201 329), lower := (rows 113 134 276 42 144 34 64 128 256), losses := [] }

theorem u1144 : Upper (D 1) (R 1) [112,132,272,34,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1144
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1145 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 134 276 42 144 40 67 195 323), lower := (rows 113 134 276 42 144 40 64 128 256), losses := [] }

theorem u1145 : Upper (D 1) (R 1) [112,132,272,34,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1145
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1146 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 276 42 144 96 75 139 267), lower := (rows 113 134 276 42 144 96 64 128 256), losses := [] }

theorem u1146 : Upper (D 1) (R 1) [112,132,272,34,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1146
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1147 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 113 134 276 137 18 34 104 232 360), lower := (rows 113 134 276 137 18 34 64 128 256), losses := [] }

theorem u1147 : Upper (D 1) (R 1) [112,132,272,129,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1147
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1148 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 134 276 137 18 40 98 226 354), lower := (rows 113 134 276 137 18 40 64 128 256), losses := [] }

theorem u1148 : Upper (D 1) (R 1) [112,132,272,129,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1148
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1149 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 276 137 18 96 106 170 298), lower := (rows 113 134 276 137 18 96 64 128 256), losses := [] }

theorem u1149 : Upper (D 1) (R 1) [112,132,272,129,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1149
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1150 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 134 276 168 18 33 74 202 330), lower := (rows 113 134 276 168 18 33 64 128 256), losses := [] }

theorem u1150 : Upper (D 1) (R 1) [112,132,272,160,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1150
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1151 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 113 134 276 168 18 34 73 201 329), lower := (rows 113 134 276 168 18 34 64 128 256), losses := [] }

theorem u1151 : Upper (D 1) (R 1) [112,132,272,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1151
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1152 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 134 276 168 18 40 67 195 323), lower := (rows 113 134 276 168 18 40 64 128 256), losses := [] }

theorem u1152 : Upper (D 1) (R 1) [112,132,272,160,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1152
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1153 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 276 168 18 96 75 139 267), lower := (rows 113 134 276 168 18 96 64 128 256), losses := [] }

theorem u1153 : Upper (D 1) (R 1) [112,132,272,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1153
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1154 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 113 259 14 152 18 36 224 224 480), lower := (rows 113 259 14 152 18 36 64 128 256), losses := [] }

theorem u1154 : Upper (D 1) (R 1) [112,257,10,144,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1154
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1155 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 259 14 152 18 96 228 164 420), lower := (rows 113 259 14 152 18 96 64 128 256), losses := [] }

theorem u1155 : Upper (D 1) (R 1) [112,257,10,144,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1155
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m1156_4 : Upper (D 1) (R 1) [112,257,10,144,2,128,4] 13 :=
  permutation_upper _ _ _ [112,257,10,144,2,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u145

theorem m1156_32 : Upper (D 1) (R 1) [112,257,10,144,2,128,32] 13 :=
  permutation_upper _ _ _ [112,257,10,144,2,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u146

def r1156 : Route 9 := (fun mask => (mask,id))

def c1156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1156 : Upper (D 1) (R 1) [112,257,10,144,2,128] 13 := by
  apply FastRouting.sound _ _ [112,257,10,144,2,128] 13 (by decide) (choices 1) [4,32] r1156 c1156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m1156_4
  · exact m1156_32

def b1157 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 113 259 28 168 18 34 196 196 452), lower := (rows 113 259 28 168 18 34 64 128 256), losses := [] }

theorem u1157 : Upper (D 1) (R 1) [112,257,24,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1157
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1158 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 259 28 168 18 36 194 194 450), lower := (rows 113 259 28 168 18 36 64 128 256), losses := [] }

theorem u1158 : Upper (D 1) (R 1) [112,257,24,160,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1158
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1159 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 259 28 168 18 96 198 134 390), lower := (rows 113 259 28 168 18 96 64 128 256), losses := [] }

theorem u1159 : Upper (D 1) (R 1) [112,257,24,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1159
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1160 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 113 259 28 168 18 160 70 198 326), lower := (rows 113 259 28 168 18 160 64 128 256), losses := [] }

theorem u1160 : Upper (D 1) (R 1) [112,257,24,160,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1160
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1161 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 113 259 148 168 18 34 76 204 332), lower := (rows 113 259 148 168 18 34 64 128 256), losses := [] }

theorem u1161 : Upper (D 1) (R 1) [112,257,144,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1161
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1162 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 259 148 168 18 36 74 202 330), lower := (rows 113 259 148 168 18 36 64 128 256), losses := [] }

theorem u1162 : Upper (D 1) (R 1) [112,257,144,160,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1162
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1163 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 259 148 168 18 40 70 198 326), lower := (rows 113 259 148 168 18 40 64 128 256), losses := [] }

theorem u1163 : Upper (D 1) (R 1) [112,257,144,160,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1163
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1164 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 259 148 168 18 96 78 142 270), lower := (rows 113 259 148 168 18 96 64 128 256), losses := [] }

theorem u1164 : Upper (D 1) (R 1) [112,257,144,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1164
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1165 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 13 138 18 160 112 240 368), lower := (rows 113 262 13 138 18 160 64 128 256), losses := [] }

theorem u1165 : Upper (D 1) (R 1) [112,260,9,130,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1165
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1166 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 13 138 48 160 82 210 338), lower := (rows 113 262 13 138 48 160 64 128 256), losses := [] }

theorem u1166 : Upper (D 1) (R 1) [112,260,9,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1166
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1167 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 13 138 80 160 114 178 306), lower := (rows 113 262 13 138 80 160 64 128 256), losses := [] }

theorem u1167 : Upper (D 1) (R 1) [112,260,9,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1167
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1168 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 14 137 18 160 112 240 368), lower := (rows 113 262 14 137 18 160 64 128 256), losses := [] }

theorem u1168 : Upper (D 1) (R 1) [112,260,10,129,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1168
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1169 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 14 137 48 160 82 210 338), lower := (rows 113 262 14 137 48 160 64 128 256), losses := [] }

theorem u1169 : Upper (D 1) (R 1) [112,260,10,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1169
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1170 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 14 137 80 160 114 178 306), lower := (rows 113 262 14 137 80 160 64 128 256), losses := [] }

theorem u1170 : Upper (D 1) (R 1) [112,260,10,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1170
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1171 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 217, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 22 137 144 34 104 232 360), lower := (rows 113 262 22 137 144 34 64 128 256), losses := [] }

theorem u1171 : Upper (D 1) (R 1) [112,260,18,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1171
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1172 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 262 22 137 144 40 98 226 354), lower := (rows 113 262 22 137 144 40 64 128 256), losses := [] }

theorem u1172 : Upper (D 1) (R 1) [112,260,18,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1172
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1173 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 22 137 144 96 106 170 298), lower := (rows 113 262 22 137 144 96 64 128 256), losses := [] }

theorem u1173 : Upper (D 1) (R 1) [112,260,18,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1173
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1174 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 262 22 168 144 33 74 202 330), lower := (rows 113 262 22 168 144 33 64 128 256), losses := [] }

theorem u1174 : Upper (D 1) (R 1) [112,260,18,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1174
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1175 : PairBound 9 := { available := 73, camps := [{ cop := 5, region := 217, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 22 168 144 34 73 201 329), lower := (rows 113 262 22 168 144 34 64 128 256), losses := [] }

theorem u1175 : Upper (D 1) (R 1) [112,260,18,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1175
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1176 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 262 22 168 144 40 67 195 323), lower := (rows 113 262 22 168 144 40 64 128 256), losses := [] }

theorem u1176 : Upper (D 1) (R 1) [112,260,18,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1176
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1177 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 22 168 144 96 75 139 267), lower := (rows 113 262 22 168 144 96 64 128 256), losses := [] }

theorem u1177 : Upper (D 1) (R 1) [112,260,18,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1177
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1178 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 262 28 42 144 33 194 194 450), lower := (rows 113 262 28 42 144 33 64 128 256), losses := [] }

theorem u1178 : Upper (D 1) (R 1) [112,260,24,34,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1178
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1179 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 113 262 28 42 144 34 193 193 449), lower := (rows 113 262 28 42 144 34 64 128 256), losses := [] }

theorem u1179 : Upper (D 1) (R 1) [112,260,24,34,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1179
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1180 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 28 42 144 96 195 131 387), lower := (rows 113 262 28 42 144 96 64 128 256), losses := [] }

theorem u1180 : Upper (D 1) (R 1) [112,260,24,34,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1180
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1181 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 262 28 42 144 160 67 195 323), lower := (rows 113 262 28 42 144 160 64 128 256), losses := [] }

theorem u1181 : Upper (D 1) (R 1) [112,260,24,34,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1181
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1182 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 262 28 168 18 33 194 194 450), lower := (rows 113 262 28 168 18 33 64 128 256), losses := [] }

theorem u1182 : Upper (D 1) (R 1) [112,260,24,160,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1182
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1183 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 113 262 28 168 18 34 193 193 449), lower := (rows 113 262 28 168 18 34 64 128 256), losses := [] }

theorem u1183 : Upper (D 1) (R 1) [112,260,24,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1183
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1184 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 28 168 18 96 195 131 387), lower := (rows 113 262 28 168 18 96 64 128 256), losses := [] }

theorem u1184 : Upper (D 1) (R 1) [112,260,24,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1184
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1185 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 113 262 28 168 18 160 67 195 323), lower := (rows 113 262 28 168 18 160 64 128 256), losses := [] }

theorem u1185 : Upper (D 1) (R 1) [112,260,24,160,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1185
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1186 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 113 262 133 152 18 34 104 232 360), lower := (rows 113 262 133 152 18 34 64 128 256), losses := [] }

theorem u1186 : Upper (D 1) (R 1) [112,260,129,144,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1186
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1187 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 262 133 152 18 40 98 226 354), lower := (rows 113 262 133 152 18 40 64 128 256), losses := [] }

theorem u1187 : Upper (D 1) (R 1) [112,260,129,144,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1187
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1188 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 133 152 18 96 106 170 298), lower := (rows 113 262 133 152 18 96 64 128 256), losses := [] }

theorem u1188 : Upper (D 1) (R 1) [112,260,129,144,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1188
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1189 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 140 11 18 160 112 240 368), lower := (rows 113 262 140 11 18 160 64 128 256), losses := [] }

theorem u1189 : Upper (D 1) (R 1) [112,260,136,3,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1189
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1190 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 262 140 11 48 160 82 210 338), lower := (rows 113 262 140 11 48 160 64 128 256), losses := [] }

theorem u1190 : Upper (D 1) (R 1) [112,260,136,3,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1190
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1191 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 140 11 80 160 114 178 306), lower := (rows 113 262 140 11 80 160 64 128 256), losses := [] }

theorem u1191 : Upper (D 1) (R 1) [112,260,136,3,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1191
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1192 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 113 262 148 11 18 40 224 224 480), lower := (rows 113 262 148 11 18 40 64 128 256), losses := [] }

theorem u1192 : Upper (D 1) (R 1) [112,260,144,3,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1192
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1193 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 148 11 18 96 232 168 424), lower := (rows 113 262 148 11 18 96 64 128 256), losses := [] }

theorem u1193 : Upper (D 1) (R 1) [112,260,144,3,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1193
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m1194_8 : Upper (D 1) (R 1) [112,260,144,3,2,128,8] 13 :=
  permutation_upper _ _ _ [112,260,144,3,2,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u147

theorem m1194_32 : Upper (D 1) (R 1) [112,260,144,3,2,128,32] 13 :=
  permutation_upper _ _ _ [112,260,144,3,2,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u148

def r1194 : Route 9 := (fun mask => (mask,id))

def c1194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1194 : Upper (D 1) (R 1) [112,260,144,3,2,128] 13 := by
  apply FastRouting.sound _ _ [112,260,144,3,2,128] 13 (by decide) (choices 1) [8,32] r1194 c1194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m1194_8
  · exact m1194_32

def b1195 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 113 262 148 42 18 33 200 200 456), lower := (rows 113 262 148 42 18 33 64 128 256), losses := [] }

theorem u1195 : Upper (D 1) (R 1) [112,260,144,34,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1195
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1196 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 113 262 148 42 18 40 193 193 449), lower := (rows 113 262 148 42 18 40 64 128 256), losses := [] }

theorem u1196 : Upper (D 1) (R 1) [112,260,144,34,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1196
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1197 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 148 42 18 96 201 137 393), lower := (rows 113 262 148 42 18 96 64 128 256), losses := [] }

theorem u1197 : Upper (D 1) (R 1) [112,260,144,34,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1197
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1198 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 113 262 148 42 18 160 73 201 329), lower := (rows 113 262 148 42 18 160 64 128 256), losses := [] }

theorem u1198 : Upper (D 1) (R 1) [112,260,144,34,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1198
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1199 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 113 262 148 137 18 34 104 232 360), lower := (rows 113 262 148 137 18 34 64 128 256), losses := [] }

theorem u1199 : Upper (D 1) (R 1) [112,260,144,129,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1199
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1199
end Delivery.IrregularNine14.P01

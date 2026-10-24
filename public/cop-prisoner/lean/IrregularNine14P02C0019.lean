import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0008

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1140 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 113 131 140 280 18 356 356 484 356), lower := (rows 113 131 140 280 18 32 64 128 256), losses := [] }

theorem u1140 : Upper (D 2) (R 2) [112,129,136,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1140
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1141 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 386, targets := 16 }], pairs := [(1,4)], upper := (rows 113 131 140 280 20 354 354 482 354), lower := (rows 113 131 140 280 20 32 64 128 256), losses := [] }

theorem u1141 : Upper (D 2) (R 2) [112,129,136,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1141
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1142 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 131 140 280 48 358 326 454 326), lower := (rows 113 131 140 280 48 32 64 128 256), losses := [] }

theorem u1142 : Upper (D 2) (R 2) [112,129,136,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1142
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1143 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 113 131 140 280 272 102 102 230 358), lower := (rows 113 131 140 280 272 32 64 128 256), losses := [] }

theorem u1143 : Upper (D 2) (R 2) [112,129,136,272,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1143
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1144 : PairBound 9 := { available := 360, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 148 266 20 360 360 488 360), lower := (rows 113 131 148 266 20 32 64 128 256), losses := [] }

theorem u1144 : Upper (D 2) (R 2) [112,129,144,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1144
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1145 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 113 131 148 266 24 356 356 484 356), lower := (rows 113 131 148 266 24 32 64 128 256), losses := [] }

theorem u1145 : Upper (D 2) (R 2) [112,129,144,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1145
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1146 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 131 148 266 48 364 332 460 332), lower := (rows 113 131 148 266 48 32 64 128 256), losses := [] }

theorem u1146 : Upper (D 2) (R 2) [112,129,144,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1146
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1147 : Route 9 := (fun mask => (mask,id))

def c1147 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1147 : Upper (D 2) (R 2) [112,129,144,258,256] 13 := by
  apply FastRouting.sound _ _ [112,129,144,258,256] 13 (by decide) (choices 1) [4,8,64] r1147 c1147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u485
  · exact u486
  · exact u487

def b1148 : PairBound 9 := { available := 360, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 148 268 18 360 360 488 360), lower := (rows 113 131 148 268 18 32 64 128 256), losses := [] }

theorem u1148 : Upper (D 2) (R 2) [112,129,144,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1148
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1149 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 386, targets := 16 }], pairs := [(1,4)], upper := (rows 113 131 148 268 24 354 354 482 354), lower := (rows 113 131 148 268 24 32 64 128 256), losses := [] }

theorem u1149 : Upper (D 2) (R 2) [112,129,144,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1149
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1150 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 131 148 268 48 362 330 458 330), lower := (rows 113 131 148 268 48 32 64 128 256), losses := [] }

theorem u1150 : Upper (D 2) (R 2) [112,129,144,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1150
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1151 : Route 9 := (fun mask => (mask,id))

def c1151 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1151 : Upper (D 2) (R 2) [112,129,144,260,256] 13 := by
  apply FastRouting.sound _ _ [112,129,144,260,256] 13 (by decide) (choices 1) [2,8,64] r1151 c1151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u488
  · exact u489
  · exact u490

def b1152 : PairBound 9 := { available := 332, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 148 296 18 364 332 460 332), lower := (rows 113 131 148 296 18 32 64 128 256), losses := [] }

theorem u1152 : Upper (D 2) (R 2) [112,129,144,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1152
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1153 : PairBound 9 := { available := 330, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 148 296 20 362 330 458 330), lower := (rows 113 131 148 296 20 32 64 128 256), losses := [] }

theorem u1153 : Upper (D 2) (R 2) [112,129,144,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1153
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1154 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 148 296 24 358 326 454 326), lower := (rows 113 131 148 296 24 32 64 128 256), losses := [] }

theorem u1154 : Upper (D 2) (R 2) [112,129,144,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1154
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1155 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 131 148 296 80 302 334 398 270), lower := (rows 113 131 148 296 80 32 64 128 256), losses := [] }

theorem u1155 : Upper (D 2) (R 2) [112,129,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1155
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1156 : Route 9 := (fun mask => (mask,id))

def c1156 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1156 : Upper (D 2) (R 2) [112,129,144,288,256] 13 := by
  apply FastRouting.sound _ _ [112,129,144,288,256] 13 (by decide) (choices 1) [2,4,8,64] r1156 c1156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u491
  · exact u492
  · exact u493
  · exact u494

def b1157 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 131 262 280 20 232 232 232 488), lower := (rows 113 131 262 280 20 32 64 128 256), losses := [] }

theorem u1157 : Upper (D 2) (R 2) [112,129,258,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1157
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1158 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 131 262 280 24 228 228 228 484), lower := (rows 113 131 262 280 24 32 64 128 256), losses := [] }

theorem u1158 : Upper (D 2) (R 2) [112,129,258,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1158
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1159 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 131 262 280 48 236 204 204 460), lower := (rows 113 131 262 280 48 32 64 128 256), losses := [] }

theorem u1159 : Upper (D 2) (R 2) [112,129,258,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1159
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1160 : PairBound 9 := { available := 108, camps := [], pairs := [(3,5),(3,6)], upper := (rows 113 131 262 280 144 108 108 236 364), lower := (rows 113 131 262 280 144 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 12 146 0 64 128 256), good := (rows 81 147 286 280 144 0 64 144 256) },{ target := 6, region := (rows 1 2 4 12 146 32 0 128 256), good := (rows 49 147 286 280 144 32 0 144 256) }] }

theorem u1160 : Upper (D 2) (R 2) [112,129,258,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1160
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1161 : Route 9 := (fun mask => (mask,id))

def c1161 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1161 : Upper (D 2) (R 2) [112,129,258,384,4] 13 := by
  apply FastRouting.sound _ _ [112,129,258,384,4] 13 (by decide) (choices 1) [8,16,64] r1161 c1161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u495
  · exact u496
  · exact u497

theorem m1162_4 : Upper (D 2) (R 2) [112,129,258,384,8,4] 13 :=
  permutation_upper _ _ _ [112,129,258,384,4,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u495

def r1162 : Route 9 := (fun mask => (mask,id))

def c1162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1162 : Upper (D 2) (R 2) [112,129,258,384,8] 13 := by
  apply FastRouting.sound _ _ [112,129,258,384,8] 13 (by decide) (choices 1) [4,16,64] r1162 c1162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1162_4
  · exact u498
  · exact u499

def b1163 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 131 262 392 48 124 92 220 348), lower := (rows 113 131 262 392 48 32 64 128 256), losses := [] }

theorem u1163 : Upper (D 2) (R 2) [112,129,258,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1163
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1164 : PairBound 9 := { available := 204, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 131 276 296 18 236 204 204 460), lower := (rows 113 131 276 296 18 32 64 128 256), losses := [] }

theorem u1164 : Upper (D 2) (R 2) [112,129,272,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1164
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1165 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 276 296 20 234 202 202 458), lower := (rows 113 131 276 296 20 32 64 128 256), losses := [] }

theorem u1165 : Upper (D 2) (R 2) [112,129,272,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1165
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1166 : PairBound 9 := { available := 198, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 276 296 24 230 198 198 454), lower := (rows 113 131 276 296 24 32 64 128 256), losses := [] }

theorem u1166 : Upper (D 2) (R 2) [112,129,272,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1166
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1167 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 131 276 296 80 174 206 142 398), lower := (rows 113 131 276 296 80 32 64 128 256), losses := [] }

theorem u1167 : Upper (D 2) (R 2) [112,129,272,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1167
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1168_2 : Upper (D 2) (R 2) [112,129,272,288,128,2] 13 :=
  permutation_upper _ _ _ [112,129,272,288,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u500

theorem m1168_4 : Upper (D 2) (R 2) [112,129,272,288,128,4] 13 :=
  permutation_upper _ _ _ [112,129,272,288,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u502

theorem m1168_8 : Upper (D 2) (R 2) [112,129,272,288,128,8] 13 :=
  permutation_upper _ _ _ [112,129,272,288,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u501

theorem m1168_64 : Upper (D 2) (R 2) [112,129,272,288,128,64] 13 :=
  permutation_upper _ _ _ [112,129,272,288,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u503

def r1168 : Route 9 := (fun mask => (mask,id))

def c1168 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1168 : Upper (D 2) (R 2) [112,129,272,288,128] 13 := by
  apply FastRouting.sound _ _ [112,129,272,288,128] 13 (by decide) (choices 1) [2,4,8,64] r1168 c1168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m1168_2
  · exact m1168_4
  · exact m1168_8
  · exact m1168_64

def b1169 : PairBound 9 := { available := 108, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 131 276 392 18 108 108 236 364), lower := (rows 113 131 276 392 18 32 64 128 256), losses := [] }

theorem u1169 : Upper (D 2) (R 2) [112,129,272,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1169
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1170 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 276 392 20 106 106 234 362), lower := (rows 113 131 276 392 20 32 64 128 256), losses := [] }

theorem u1170 : Upper (D 2) (R 2) [112,129,272,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1170
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1171 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 276 392 24 102 102 230 358), lower := (rows 113 131 276 392 24 32 64 128 256), losses := [] }

theorem u1171 : Upper (D 2) (R 2) [112,129,272,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1171
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1172 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 131 276 392 48 110 78 206 334), lower := (rows 113 131 276 392 48 32 64 128 256), losses := [] }

theorem u1172 : Upper (D 2) (R 2) [112,129,272,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1172
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1173 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 358, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 262 152 17 360 360 488 360), lower := (rows 113 134 262 152 17 32 64 128 256), losses := [] }

theorem u1173 : Upper (D 2) (R 2) [112,132,258,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1173
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1174 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 134 262 152 24 353 353 481 353), lower := (rows 113 134 262 152 24 32 64 128 256), losses := [] }

theorem u1174 : Upper (D 2) (R 2) [112,132,258,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1174
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1175 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 134 262 152 48 361 329 457 329), lower := (rows 113 134 262 152 48 32 64 128 256), losses := [] }

theorem u1175 : Upper (D 2) (R 2) [112,132,258,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1175
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1176 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 233, targets := 256 }], pairs := [(0,8),(3,8)], upper := (rows 113 134 262 152 272 105 105 233 361), lower := (rows 113 134 262 152 272 32 64 128 256), losses := [] }

theorem u1176 : Upper (D 2) (R 2) [112,132,258,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1176
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1177 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 358, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 268 152 17 354 354 482 354), lower := (rows 113 134 268 152 17 32 64 128 256), losses := [] }

theorem u1177 : Upper (D 2) (R 2) [112,132,264,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1177
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1178 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 134 268 152 18 353 353 481 353), lower := (rows 113 134 268 152 18 32 64 128 256), losses := [] }

theorem u1178 : Upper (D 2) (R 2) [112,132,264,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1178
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1179 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 134 268 152 48 355 323 451 323), lower := (rows 113 134 268 152 48 32 64 128 256), losses := [] }

theorem u1179 : Upper (D 2) (R 2) [112,132,264,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1179
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1180 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(3,5)], upper := (rows 113 134 268 152 272 99 99 227 355), lower := (rows 113 134 268 152 272 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 276 0 64 128 256), good := (rows 81 158 284 152 272 0 64 128 272) }] }

theorem u1180 : Upper (D 2) (R 2) [112,132,264,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1180
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1181 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 276 168 17 362 330 458 330), lower := (rows 113 134 276 168 17 32 64 128 256), losses := [] }

theorem u1181 : Upper (D 2) (R 2) [112,132,272,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1181
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1182 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 134 276 168 18 361 329 457 329), lower := (rows 113 134 276 168 18 32 64 128 256), losses := [] }

theorem u1182 : Upper (D 2) (R 2) [112,132,272,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1182
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1183 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 276 168 24 355 323 451 323), lower := (rows 113 134 276 168 24 32 64 128 256), losses := [] }

theorem u1183 : Upper (D 2) (R 2) [112,132,272,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1183
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1184 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 134 276 168 80 299 331 395 267), lower := (rows 113 134 276 168 80 32 64 128 256), losses := [] }

theorem u1184 : Upper (D 2) (R 2) [112,132,272,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1184
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1185 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 235, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 113 134 276 168 272 107 75 203 331), lower := (rows 113 134 276 168 272 32 64 128 256), losses := [] }

theorem u1185 : Upper (D 2) (R 2) [112,132,272,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1185
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1186 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 276 296 17 234 202 202 458), lower := (rows 113 134 276 296 17 32 64 128 256), losses := [] }

theorem u1186 : Upper (D 2) (R 2) [112,132,272,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1186
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1187 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 113 134 276 296 18 233 201 201 457), lower := (rows 113 134 276 296 18 32 64 128 256), losses := [] }

theorem u1187 : Upper (D 2) (R 2) [112,132,272,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1187
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1188 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 134 276 296 24 227 195 195 451), lower := (rows 113 134 276 296 24 32 64 128 256), losses := [] }

theorem u1188 : Upper (D 2) (R 2) [112,132,272,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1188
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1189 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 134 276 296 80 171 203 139 395), lower := (rows 113 134 276 296 80 32 64 128 256), losses := [] }

theorem u1189 : Upper (D 2) (R 2) [112,132,272,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1189
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1190 : Route 9 := (fun mask => (mask,id))

def c1190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1190 : Upper (D 2) (R 2) [112,132,272,288,128] 13 := by
  apply FastRouting.sound _ _ [112,132,272,288,128] 13 (by decide) (choices 1) [1,2,8,64] r1190 c1190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u504
  · exact u505
  · exact u506
  · exact u507

def b1191 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 113 134 276 392 17 106 106 234 362), lower := (rows 113 134 276 392 17 32 64 128 256), losses := [] }

theorem u1191 : Upper (D 2) (R 2) [112,132,272,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1191
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1192 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 276 392 18 105 105 233 361), lower := (rows 113 134 276 392 18 32 64 128 256), losses := [] }

theorem u1192 : Upper (D 2) (R 2) [112,132,272,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1192
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1193 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 276 392 24 99 99 227 355), lower := (rows 113 134 276 392 24 32 64 128 256), losses := [] }

theorem u1193 : Upper (D 2) (R 2) [112,132,272,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1193
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1194 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 134 276 392 48 107 75 203 331), lower := (rows 113 134 276 392 48 32 64 128 256), losses := [] }

theorem u1194 : Upper (D 2) (R 2) [112,132,272,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1194
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1195 : PairBound 9 := { available := 270, camps := [{ cop := 1, region := 364, targets := 16 }], pairs := [(2,4)], upper := (rows 113 146 164 328 17 302 334 398 270), lower := (rows 113 146 164 328 17 32 64 128 256), losses := [] }

theorem u1195 : Upper (D 2) (R 2) [112,144,160,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1195
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1196 : PairBound 9 := { available := 269, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 164 328 18 301 333 397 269), lower := (rows 113 146 164 328 18 32 64 128 256), losses := [] }

theorem u1196 : Upper (D 2) (R 2) [112,144,160,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1196
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1197 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 164 328 20 299 331 395 267), lower := (rows 113 146 164 328 20 32 64 128 256), losses := [] }

theorem u1197 : Upper (D 2) (R 2) [112,144,160,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1197
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1198 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 113 146 164 328 24 295 327 391 263), lower := (rows 113 146 164 328 24 32 64 128 256), losses := [] }

theorem u1198 : Upper (D 2) (R 2) [112,144,160,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1198
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1199_1 : Upper (D 2) (R 2) [112,144,160,320,256,1] 13 :=
  permutation_upper _ _ _ [112,144,160,320,1,256] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u508

theorem m1199_2 : Upper (D 2) (R 2) [112,144,160,320,256,2] 13 :=
  permutation_upper _ _ _ [112,144,160,320,4,256] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u510

theorem m1199_4 : Upper (D 2) (R 2) [112,144,160,320,256,4] 13 :=
  permutation_upper _ _ _ [112,144,160,320,2,256] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u509

theorem m1199_8 : Upper (D 2) (R 2) [112,144,160,320,256,8] 13 :=
  permutation_upper _ _ _ [112,144,160,320,8,256] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u511

def r1199 : Route 9 := (fun mask => (mask,id))

def c1199 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1199 : Upper (D 2) (R 2) [112,144,160,320,256] 13 := by
  apply FastRouting.sound _ _ [112,144,160,320,256] 13 (by decide) (choices 1) [1,2,4,8] r1199 c1199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m1199_1
  · exact m1199_2
  · exact m1199_4
  · exact m1199_8

#print axioms u1199
end Delivery.IrregularNine14.P02

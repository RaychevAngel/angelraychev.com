import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0008
import IrregularNine14P02C0009

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1200 : PairBound 9 := { available := 78, camps := [{ cop := 1, region := 364, targets := 16 }], pairs := [(2,4)], upper := (rows 113 146 292 392 17 110 78 206 334), lower := (rows 113 146 292 392 17 32 64 128 256), losses := [] }

theorem u1200 : Upper (D 2) (R 2) [112,144,288,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1200
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1201 : PairBound 9 := { available := 77, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 292 392 18 109 77 205 333), lower := (rows 113 146 292 392 18 32 64 128 256), losses := [] }

theorem u1201 : Upper (D 2) (R 2) [112,144,288,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1201
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1202 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 394, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 292 392 20 107 75 203 331), lower := (rows 113 146 292 392 20 32 64 128 256), losses := [] }

theorem u1202 : Upper (D 2) (R 2) [112,144,288,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1202
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1203 : PairBound 9 := { available := 71, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 146 292 392 24 103 71 199 327), lower := (rows 113 146 292 392 24 32 64 128 256), losses := [] }

theorem u1203 : Upper (D 2) (R 2) [112,144,288,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1203
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1204 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 146 292 392 80 47 79 143 271), lower := (rows 113 146 292 392 80 32 64 128 256), losses := [] }

theorem u1204 : Upper (D 2) (R 2) [112,144,288,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1204
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1205 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 488, targets := 16 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(3,4)], upper := (rows 15 19 52 104 464 480 448 448 448), lower := (rows 15 19 52 104 16 32 64 128 256), losses := [] }

theorem u1205 : Upper (D 2) (R 2) [14,17,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1205
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1206 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1206 : Upper (D 2) (R 2) [14,17,48,192] 13 := by
  apply FastRouting.sound _ _ [14,17,48,192] 13 (by decide) (choices 1) [32,64,256] r1206 c1206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u512
  · exact u513
  · exact u514

def b1207 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 8, targets := 144 }], pairs := [(3,4),(3,7)], upper := (rows 15 19 100 104 400 432 464 400 400), lower := (rows 15 19 100 104 16 32 64 128 256), losses := [] }

theorem u1207 : Upper (D 2) (R 2) [14,17,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1207
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1208_128 : Upper (D 2) (R 2) [14,17,96,160,128] 13 :=
  permutation_upper _ _ _ [14,17,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u515

def r1208 : Route 9 := (fun mask => (mask,id))

def c1208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1208 : Upper (D 2) (R 2) [14,17,96,160] 13 := by
  apply FastRouting.sound _ _ [14,17,96,160] 13 (by decide) (choices 1) [64,128,256] r1208 c1208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u515
  · exact m1208_128
  · exact u516

theorem m1209_128 : Upper (D 2) (R 2) [14,17,96,384,128] 13 :=
  permutation_upper _ _ _ [14,17,96,384,32] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u517

def r1209 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1209 : Upper (D 2) (R 2) [14,17,96,384] 13 := by
  apply FastRouting.sound _ _ [14,17,96,384] 13 (by decide) (choices 1) [32,128] r1209 c1209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u517
  · exact m1209_128

def b1210 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 15 50 52 200 465 481 449 449 449), lower := (rows 15 50 52 200 16 32 64 128 256), losses := [] }

theorem u1210 : Upper (D 2) (R 2) [14,48,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1210
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1211 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 488, targets := 16 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(3,4)], upper := (rows 15 50 84 104 401 417 449 385 385), lower := (rows 15 50 84 104 16 32 64 128 256), losses := [] }

theorem u1211 : Upper (D 2) (R 2) [14,48,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1211
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1212 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 488, targets := 16 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(3,4)], upper := (rows 15 50 84 168 465 481 449 449 449), lower := (rows 15 50 84 168 16 32 64 128 256), losses := [] }

theorem u1212 : Upper (D 2) (R 2) [14,48,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1212
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1213_64 : Upper (D 2) (R 2) [14,48,80,384,64] 13 :=
  permutation_upper _ _ _ [14,48,80,384,32] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u519

def r1213 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1213 : Upper (D 2) (R 2) [14,48,80,384] 13 := by
  apply FastRouting.sound _ _ [14,48,80,384] 13 (by decide) (choices 1) [1,32,64,128] r1213 c1213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u518
  · exact u519
  · exact m1213_64
  · exact u520

def r1214 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1214 : Upper (D 2) (R 2) [22,9,96,48] 13 := by
  apply FastRouting.sound _ _ [22,9,96,48] 13 (by decide) (choices 1) [64,128] r1214 c1214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u521
  · exact u522

def b1215 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 8, targets := 144 }], pairs := [(3,4),(3,7)], upper := (rows 23 11 100 104 400 432 464 400 400), lower := (rows 23 11 100 104 16 32 64 128 256), losses := [] }

theorem u1215 : Upper (D 2) (R 2) [22,9,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1215
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1216 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1216 : Upper (D 2) (R 2) [22,9,96,144] 13 := by
  apply FastRouting.sound _ _ [22,9,96,144] 13 (by decide) (choices 1) [32,128,256] r1216 c1216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u523
  · exact u524
  · exact u525

def r1217 : Route 9 := (fun mask => (mask,id))

def c1217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1217 : Upper (D 2) (R 2) [22,9,96,160] 13 := by
  apply FastRouting.sound _ _ [22,9,96,160] 13 (by decide) (choices 1) [64,128,256] r1217 c1217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u526
  · exact u527
  · exact u528

def r1218 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1218 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1218 : Upper (D 2) (R 2) [22,9,96,384] 13 := by
  apply FastRouting.sound _ _ [22,9,96,384] 13 (by decide) (choices 1) [32,128] r1218 c1218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u529
  · exact u530

def b1219 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 482, targets := 16 },{ cop := 0, region := 456, targets := 32 }], pairs := [(1,4),(3,5)], upper := (rows 23 35 44 88 464 480 448 448 448), lower := (rows 23 35 44 88 16 32 64 128 256), losses := [] }

theorem u1219 : Upper (D 2) (R 2) [22,33,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1219
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1220 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1220 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1220 : Upper (D 2) (R 2) [22,33,40,192] 13 := by
  apply FastRouting.sound _ _ [22,33,40,192] 13 (by decide) (choices 1) [64,256] r1220 c1220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u531
  · exact u532

def b1221 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 482, targets := 16 },{ cop := 3, region := 452, targets := 16 }], pairs := [(1,4),(2,4)], upper := (rows 23 35 76 56 464 480 448 448 448), lower := (rows 23 35 76 56 16 32 64 128 256), losses := [] }

theorem u1221 : Upper (D 2) (R 2) [22,33,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1221
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1222 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 4, targets := 160 }], pairs := [(2,5),(2,7)], upper := (rows 23 35 76 88 432 416 480 416 416), lower := (rows 23 35 76 88 16 32 64 128 256), losses := [] }

theorem u1222 : Upper (D 2) (R 2) [22,33,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1222
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1223 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 4, targets := 144 }], pairs := [(2,4),(2,7)], upper := (rows 23 35 76 104 400 432 464 400 400), lower := (rows 23 35 76 104 16 32 64 128 256), losses := [] }

theorem u1223 : Upper (D 2) (R 2) [22,33,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1223
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1224 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 482, targets := 16 },{ cop := 3, region := 356, targets := 16 }], pairs := [(1,4),(2,4)], upper := (rows 23 35 76 152 496 480 480 480 480), lower := (rows 23 35 76 152 16 32 64 128 256), losses := [] }

theorem u1224 : Upper (D 2) (R 2) [22,33,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1224
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1225 : Route 9 := (fun mask => (mask,id))

def c1225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1225 : Upper (D 2) (R 2) [22,33,72,160] 13 := by
  apply FastRouting.sound _ _ [22,33,72,160] 13 (by decide) (choices 1) [64,128,256] r1225 c1225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u533
  · exact u534
  · exact u535

def b1226 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 23 35 76 200 432 432 496 432 432), lower := (rows 23 35 76 200 16 32 64 128 256), losses := [] }

theorem u1226 : Upper (D 2) (R 2) [22,33,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1226
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1227 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1227 : Upper (D 2) (R 2) [22,33,72,384] 13 := by
  apply FastRouting.sound _ _ [22,33,72,384] 13 (by decide) (choices 1) [32,64,128] r1227 c1227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u536
  · exact u537
  · exact u538

def b1228 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 3, region := 420, targets := 16 }], pairs := [(2,4),(3,5)], upper := (rows 23 35 100 88 408 424 456 392 392), lower := (rows 23 35 100 88 16 32 64 128 256), losses := [] }

theorem u1228 : Upper (D 2) (R 2) [22,33,96,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1228
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1229 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 3, region := 356, targets := 16 }], pairs := [(2,4),(3,5)], upper := (rows 23 35 100 152 472 488 456 456 456), lower := (rows 23 35 100 152 16 32 64 128 256), losses := [] }

theorem u1229 : Upper (D 2) (R 2) [22,33,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1229
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1230 : Route 9 := (fun mask => (mask,id))

def c1230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0)

theorem u1230 : Upper (D 2) (R 2) [22,33,96,192] 13 := by
  apply FastRouting.sound _ _ [22,33,96,192] 13 (by decide) (choices 1) [8,128,256] r1230 c1230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u539
  · exact u540
  · exact u541

def r1231 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0)

theorem u1231 : Upper (D 2) (R 2) [22,33,96,384] 13 := by
  apply FastRouting.sound _ _ [22,33,96,384] 13 (by decide) (choices 1) [8,64,128] r1231 c1231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u542
  · exact u543
  · exact u544

def b1232 : PairBound 9 := { available := 456, camps := [{ cop := 3, region := 452, targets := 16 },{ cop := 3, region := 452, targets := 32 }], pairs := [(2,4),(2,5)], upper := (rows 23 35 196 56 472 488 456 456 456), lower := (rows 23 35 196 56 16 32 64 128 256), losses := [] }

theorem u1232 : Upper (D 2) (R 2) [22,33,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1232
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1233 : Route 9 := (fun mask => (mask,id))

def c1233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1233 : Upper (D 2) (R 2) [22,33,192,80] 13 := by
  apply FastRouting.sound _ _ [22,33,192,80] 13 (by decide) (choices 1) [8,32,128,256] r1233 c1233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u545
  · exact u546
  · exact u547
  · exact u548

def r1234 : Route 9 := (fun mask => (mask,id))

def c1234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0)

theorem u1234 : Upper (D 2) (R 2) [22,33,192,96] 13 := by
  apply FastRouting.sound _ _ [22,33,192,96] 13 (by decide) (choices 1) [8,128,256] r1234 c1234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u549
  · exact u550
  · exact u551

def b1235 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 8, targets := 48 }], pairs := [(3,4),(3,5)], upper := (rows 23 35 196 200 312 312 376 440 312), lower := (rows 23 35 196 200 16 32 64 128 256), losses := [] }

theorem u1235 : Upper (D 2) (R 2) [22,33,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1235
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1236 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1236 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0)

theorem u1236 : Upper (D 2) (R 2) [22,33,192,272] 13 := by
  apply FastRouting.sound _ _ [22,33,192,272] 13 (by decide) (choices 1) [8,32,64,256] r1236 c1236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u552
  · exact u553
  · exact u554
  · exact u555

def r1237 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0)

theorem u1237 : Upper (D 2) (R 2) [22,33,192,288] 13 := by
  apply FastRouting.sound _ _ [22,33,192,288] 13 (by decide) (choices 1) [8,64,256] r1237 c1237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u556
  · exact u557
  · exact u558

def r1238 : Route 9 := (fun mask => (mask,id))

def c1238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1238 : Upper (D 2) (R 2) [22,33,192,320] 13 := by
  apply FastRouting.sound _ _ [22,33,192,320] 13 (by decide) (choices 1) [8,32,128,256] r1238 c1238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u559
  · exact u560
  · exact u561
  · exact u562

def b1239 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 23 42 100 25 464 480 448 448 448), lower := (rows 23 42 100 25 16 32 64 128 256), losses := [] }

theorem u1239 : Upper (D 2) (R 2) [22,40,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1239
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1240 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(3,5)], upper := (rows 23 42 100 73 400 432 464 400 400), lower := (rows 23 42 100 73 16 32 64 128 256), losses := [] }

theorem u1240 : Upper (D 2) (R 2) [22,40,96,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1240
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1241 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 484, targets := 16 },{ cop := 0, region := 456, targets := 32 }], pairs := [(2,4),(3,5)], upper := (rows 23 42 100 88 401 417 449 385 385), lower := (rows 23 42 100 88 16 32 64 128 256), losses := [] }

theorem u1241 : Upper (D 2) (R 2) [22,40,96,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1241
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1242 : Route 9 := (fun mask => (mask,id))

def c1242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1242 : Upper (D 2) (R 2) [22,40,96,129] 13 := by
  apply FastRouting.sound _ _ [22,40,96,129] 13 (by decide) (choices 1) [64,128,256] r1242 c1242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u563
  · exact u564
  · exact u565

def b1243 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 484, targets := 16 },{ cop := 0, region := 456, targets := 32 }], pairs := [(2,4),(3,5)], upper := (rows 23 42 100 152 465 481 449 449 449), lower := (rows 23 42 100 152 16 32 64 128 256), losses := [] }

theorem u1243 : Upper (D 2) (R 2) [22,40,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1243
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1244 : Route 9 := (fun mask => (mask,id))

def c1244 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | _ => 0)

theorem u1244 : Upper (D 2) (R 2) [22,40,96,192] 13 := by
  apply FastRouting.sound _ _ [22,40,96,192] 13 (by decide) (choices 1) [1,128,256] r1244 c1244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u566
  · exact u567
  · exact u568

def r1245 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1245 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1245 : Upper (D 2) (R 2) [22,40,96,384] 13 := by
  apply FastRouting.sound _ _ [22,40,96,384] 13 (by decide) (choices 1) [1,64,128] r1245 c1245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u569
  · exact u570
  · exact u571

def b1246 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 23 42 196 25 496 480 480 480 480), lower := (rows 23 42 196 25 16 32 64 128 256), losses := [] }

theorem u1246 : Upper (D 2) (R 2) [22,40,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1246
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1247 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 2, targets := 80 }], pairs := [(1,4),(1,6)], upper := (rows 23 42 196 41 464 496 464 464 464), lower := (rows 23 42 196 41 16 32 64 128 256), losses := [] }

theorem u1247 : Upper (D 2) (R 2) [22,40,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1247
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1248 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 80 }], pairs := [(1,4),(1,6)], upper := (rows 23 42 196 56 465 481 449 449 449), lower := (rows 23 42 196 56 16 32 64 128 256), losses := [] }

theorem u1248 : Upper (D 2) (R 2) [22,40,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1248
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1249 : Route 9 := (fun mask => (mask,id))

def c1249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1249 : Upper (D 2) (R 2) [22,40,192,65] 13 := by
  apply FastRouting.sound _ _ [22,40,192,65] 13 (by decide) (choices 1) [32,128,256] r1249 c1249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u572
  · exact u573
  · exact u574

def r1250 : Route 9 := (fun mask => (mask,id))

def c1250 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1250 : Upper (D 2) (R 2) [22,40,192,80] 13 := by
  apply FastRouting.sound _ _ [22,40,192,80] 13 (by decide) (choices 1) [1,32,128,256] r1250 c1250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u575
  · exact u576
  · exact u577
  · exact u578

def b1251 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 2, targets := 80 }], pairs := [(1,4),(1,6)], upper := (rows 23 42 196 104 401 433 465 401 401), lower := (rows 23 42 196 104 16 32 64 128 256), losses := [] }

theorem u1251 : Upper (D 2) (R 2) [22,40,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1251
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1252 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 8, targets := 48 }], pairs := [(3,4),(3,5)], upper := (rows 23 42 196 200 305 305 369 433 305), lower := (rows 23 42 196 200 16 32 64 128 256), losses := [] }

theorem u1252 : Upper (D 2) (R 2) [22,40,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1252
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1253 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1253 : Upper (D 2) (R 2) [22,40,192,257] 13 := by
  apply FastRouting.sound _ _ [22,40,192,257] 13 (by decide) (choices 1) [32,64,256] r1253 c1253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u579
  · exact u580
  · exact u581

def r1254 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1254 : Upper (D 2) (R 2) [22,40,192,272] 13 := by
  apply FastRouting.sound _ _ [22,40,192,272] 13 (by decide) (choices 1) [1,32,64,256] r1254 c1254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u582
  · exact u583
  · exact u584
  · exact u585

def b1255 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 2, targets := 80 }], pairs := [(1,4),(1,6)], upper := (rows 23 42 196 296 465 497 465 465 465), lower := (rows 23 42 196 296 16 32 64 128 256), losses := [] }

theorem u1255 : Upper (D 2) (R 2) [22,40,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1255
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1256 : Route 9 := (fun mask => (mask,id))

def c1256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1256 : Upper (D 2) (R 2) [22,40,192,320] 13 := by
  apply FastRouting.sound _ _ [22,40,192,320] 13 (by decide) (choices 1) [1,32,128,256] r1256 c1256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u586
  · exact u587
  · exact u588
  · exact u589

def b1257 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 23 98 164 25 472 488 456 456 456), lower := (rows 23 98 164 25 16 32 64 128 256), losses := [] }

theorem u1257 : Upper (D 2) (R 2) [22,96,160,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1257
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1258 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(3,5)], upper := (rows 23 98 164 73 408 440 472 408 408), lower := (rows 23 98 164 73 16 32 64 128 256), losses := [] }

theorem u1258 : Upper (D 2) (R 2) [22,96,160,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1258
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1259 : Route 9 := (fun mask => (mask,id))

def c1259 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0)

theorem u1259 : Upper (D 2) (R 2) [22,96,160,80] 13 := by
  apply FastRouting.sound _ _ [22,96,160,80] 13 (by decide) (choices 1) [1,8,128,256] r1259 c1259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u590
  · exact u591
  · exact u592
  · exact u593

#print axioms u1259
end Delivery.IrregularNine14.P02

import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0009
import IrregularNine14P02C0010
import IrregularNine14P02C0011

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r1260 : Route 9 := (fun mask => (mask,id))

def c1260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1260 : Upper (D 2) (R 2) [22,96,160,192] 13 := by
  apply FastRouting.sound _ _ [22,96,160,192] 13 (by decide) (choices 1) [1,8,256] r1260 c1260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u594
  · exact u595
  · exact u596

theorem m1261_128 : Upper (D 2) (R 2) [22,96,160,257,128] 13 :=
  permutation_upper _ _ _ [22,96,160,257,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u598

def r1261 : Route 9 := (fun mask => (mask,id))

def c1261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0)

theorem u1261 : Upper (D 2) (R 2) [22,96,160,257] 13 := by
  apply FastRouting.sound _ _ [22,96,160,257] 13 (by decide) (choices 1) [8,64,128,256] r1261 c1261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u597
  · exact u598
  · exact m1261_128
  · exact u599

theorem m1262_128 : Upper (D 2) (R 2) [22,96,160,272,128] 13 :=
  permutation_upper _ _ _ [22,96,160,272,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u602

def r1262 : Route 9 := (fun mask => (mask,id))

def c1262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0)

theorem u1262 : Upper (D 2) (R 2) [22,96,160,272] 13 := by
  apply FastRouting.sound _ _ [22,96,160,272] 13 (by decide) (choices 1) [1,8,64,128,256] r1262 c1262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u600
  · exact u601
  · exact u602
  · exact m1262_128
  · exact u603

def r1263 : Route 9 := (fun mask => (mask,id))

def c1263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0)

theorem u1263 : Upper (D 2) (R 2) [22,96,160,320] 13 := by
  apply FastRouting.sound _ _ [22,96,160,320] 13 (by decide) (choices 1) [1,8,128,256] r1263 c1263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u604
  · exact u605
  · exact u606
  · exact u607

def b1264 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 23 98 388 25 504 488 488 488 488), lower := (rows 23 98 388 25 16 32 64 128 256), losses := [] }

theorem u1264 : Upper (D 2) (R 2) [22,96,384,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1264
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1265 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0)

theorem u1265 : Upper (D 2) (R 2) [22,96,384,33] 13 := by
  apply FastRouting.sound _ _ [22,96,384,33] 13 (by decide) (choices 1) [8,64,128] r1265 c1265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u608
  · exact u609
  · exact u610

def r1266 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0)

theorem u1266 : Upper (D 2) (R 2) [22,96,384,48] 13 := by
  apply FastRouting.sound _ _ [22,96,384,48] 13 (by decide) (choices 1) [1,8,64,128] r1266 c1266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u611
  · exact u612
  · exact u613
  · exact u614

def b1267 : PairBound 9 := { available := 409, camps := [{ cop := 1, region := 8, targets := 144 }], pairs := [(3,4),(3,7)], upper := (rows 23 98 388 104 409 441 473 409 409), lower := (rows 23 98 388 104 16 32 64 128 256), losses := [] }

theorem u1267 : Upper (D 2) (R 2) [22,96,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1267
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1268_256 : Upper (D 2) (R 2) [22,96,384,160,256] 13 :=
  permutation_upper _ _ _ [22,96,384,160,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u617

def r1268 : Route 9 := (fun mask => (mask,id))

def c1268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u1268 : Upper (D 2) (R 2) [22,96,384,160] 13 := by
  apply FastRouting.sound _ _ [22,96,384,160] 13 (by decide) (choices 1) [1,8,64,256] r1268 c1268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u615
  · exact u616
  · exact u617
  · exact m1268_256

def b1269 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 3, region := 404, targets := 32 }], pairs := [(2,5),(3,4)], upper := (rows 51 7 28 104 464 480 448 448 448), lower := (rows 51 7 28 104 16 32 64 128 256), losses := [] }

theorem u1269 : Upper (D 2) (R 2) [50,5,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1269
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1270 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1270 : Upper (D 2) (R 2) [50,5,24,192] 13 := by
  apply FastRouting.sound _ _ [50,5,24,192] 13 (by decide) (choices 1) [32,64,256] r1270 c1270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u618
  · exact u619
  · exact u620

def b1271 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 51 7 76 56 464 480 448 448 448), lower := (rows 51 7 76 56 16 32 64 128 256), losses := [] }

theorem u1271 : Upper (D 2) (R 2) [50,5,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1271
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1272 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 4, targets := 160 }], pairs := [(2,5),(2,7)], upper := (rows 51 7 76 88 432 416 480 416 416), lower := (rows 51 7 76 88 16 32 64 128 256), losses := [] }

theorem u1272 : Upper (D 2) (R 2) [50,5,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1272
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1273 : Route 9 := (fun mask => (mask,id))

def c1273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1273 : Upper (D 2) (R 2) [50,5,72,144] 13 := by
  apply FastRouting.sound _ _ [50,5,72,144] 13 (by decide) (choices 1) [32,64,128,256] r1273 c1273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u621
  · exact u622
  · exact u623
  · exact u624

def b1274 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 7 76 200 432 432 496 432 432), lower := (rows 51 7 76 200 16 32 64 128 256), losses := [] }

theorem u1274 : Upper (D 2) (R 2) [50,5,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1274
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1275 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1275 : Upper (D 2) (R 2) [50,5,72,384] 13 := by
  apply FastRouting.sound _ _ [50,5,72,384] 13 (by decide) (choices 1) [32,64,128] r1275 c1275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u625
  · exact u626
  · exact u627

def b1276 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 3, region := 404, targets := 32 }], pairs := [(2,5),(3,4)], upper := (rows 51 7 84 104 408 424 456 392 392), lower := (rows 51 7 84 104 16 32 64 128 256), losses := [] }

theorem u1276 : Upper (D 2) (R 2) [50,5,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1276
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1277 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 3, region := 340, targets := 32 }], pairs := [(2,5),(3,4)], upper := (rows 51 7 84 168 472 488 456 456 456), lower := (rows 51 7 84 168 16 32 64 128 256), losses := [] }

theorem u1277 : Upper (D 2) (R 2) [50,5,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1277
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1278 : Route 9 := (fun mask => (mask,id))

def c1278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1278 : Upper (D 2) (R 2) [50,5,80,192] 13 := by
  apply FastRouting.sound _ _ [50,5,80,192] 13 (by decide) (choices 1) [8,32,128,256] r1278 c1278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u628
  · exact u629
  · exact u630
  · exact u631

def r1279 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0)

theorem u1279 : Upper (D 2) (R 2) [50,5,80,384] 13 := by
  apply FastRouting.sound _ _ [50,5,80,384] 13 (by decide) (choices 1) [8,32,64,128] r1279 c1279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u632
  · exact u633
  · exact u634
  · exact u635

def b1280 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 51 7 196 56 472 488 456 456 456), lower := (rows 51 7 196 56 16 32 64 128 256), losses := [] }

theorem u1280 : Upper (D 2) (R 2) [50,5,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1280
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1281 : Route 9 := (fun mask => (mask,id))

def c1281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1281 : Upper (D 2) (R 2) [50,5,192,80] 13 := by
  apply FastRouting.sound _ _ [50,5,192,80] 13 (by decide) (choices 1) [8,32,128,256] r1281 c1281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u636
  · exact u637
  · exact u638
  · exact u639

def b1282 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 8, targets := 48 }], pairs := [(3,4),(3,5)], upper := (rows 51 7 196 200 312 312 376 440 312), lower := (rows 51 7 196 200 16 32 64 128 256), losses := [] }

theorem u1282 : Upper (D 2) (R 2) [50,5,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1282
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1283 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0)

theorem u1283 : Upper (D 2) (R 2) [50,5,192,272] 13 := by
  apply FastRouting.sound _ _ [50,5,192,272] 13 (by decide) (choices 1) [8,32,64,256] r1283 c1283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u640
  · exact u641
  · exact u642
  · exact u643

def r1284 : Route 9 := (fun mask => (mask,id))

def c1284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1284 : Upper (D 2) (R 2) [50,5,192,320] 13 := by
  apply FastRouting.sound _ _ [50,5,192,320] 13 (by decide) (choices 1) [8,32,128,256] r1284 c1284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u644
  · exact u645
  · exact u646
  · exact u647

def b1285 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 14 21 104 464 480 448 448 448), lower := (rows 51 14 21 104 16 32 64 128 256), losses := [] }

theorem u1285 : Upper (D 2) (R 2) [50,12,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1285
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1286 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 14 21 200 496 480 480 480 480), lower := (rows 51 14 21 200 16 32 64 128 256), losses := [] }

theorem u1286 : Upper (D 2) (R 2) [50,12,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1286
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1287 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 14 52 73 464 480 448 448 448), lower := (rows 51 14 52 73 16 32 64 128 256), losses := [] }

theorem u1287 : Upper (D 2) (R 2) [50,12,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1287
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1288 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 14 52 200 465 481 449 449 449), lower := (rows 51 14 52 200 16 32 64 128 256), losses := [] }

theorem u1288 : Upper (D 2) (R 2) [50,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1288
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1289 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 452, targets := 16 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,4)], upper := (rows 51 14 69 88 432 416 480 416 416), lower := (rows 51 14 69 88 16 32 64 128 256), losses := [] }

theorem u1289 : Upper (D 2) (R 2) [50,12,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1289
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1290 : Route 9 := (fun mask => (mask,id))

def c1290 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1290 : Upper (D 2) (R 2) [50,12,65,144] 13 := by
  apply FastRouting.sound _ _ [50,12,65,144] 13 (by decide) (choices 1) [32,64,128,256] r1290 c1290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u648
  · exact u649
  · exact u650
  · exact u651

def r1291 : Route 9 := (fun mask => (mask,id))

def c1291 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1291 : Upper (D 2) (R 2) [50,12,65,192] 13 := by
  apply FastRouting.sound _ _ [50,12,65,192] 13 (by decide) (choices 1) [32,128,256] r1291 c1291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u652
  · exact u653
  · exact u654

def r1292 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1292 : Upper (D 2) (R 2) [50,12,65,384] 13 := by
  apply FastRouting.sound _ _ [50,12,65,384] 13 (by decide) (choices 1) [32,64,128] r1292 c1292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u655
  · exact u656
  · exact u657

def b1293 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5),(3,4)], upper := (rows 51 14 84 104 401 417 449 385 385), lower := (rows 51 14 84 104 16 32 64 128 256), losses := [] }

theorem u1293 : Upper (D 2) (R 2) [50,12,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1293
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1294 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5),(3,4)], upper := (rows 51 14 84 168 465 481 449 449 449), lower := (rows 51 14 84 168 16 32 64 128 256), losses := [] }

theorem u1294 : Upper (D 2) (R 2) [50,12,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1294
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1295 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,4)], upper := (rows 51 14 84 200 433 417 481 417 417), lower := (rows 51 14 84 200 16 32 64 128 256), losses := [] }

theorem u1295 : Upper (D 2) (R 2) [50,12,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1295
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1296 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1296 : Upper (D 2) (R 2) [50,12,80,384] 13 := by
  apply FastRouting.sound _ _ [50,12,80,384] 13 (by decide) (choices 1) [1,32,64,128] r1296 c1296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u658
  · exact u659
  · exact u660
  · exact u661

def b1297 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 10, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 51 14 196 200 305 305 369 433 305), lower := (rows 51 14 196 200 16 32 64 128 256), losses := [] }

theorem u1297 : Upper (D 2) (R 2) [50,12,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1297
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1298_256 : Upper (D 2) (R 2) [50,12,192,320,256] 13 :=
  permutation_upper _ _ _ [50,12,192,320,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u664

def r1298 : Route 9 := (fun mask => (mask,id))

def c1298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1298 : Upper (D 2) (R 2) [50,12,192,320] 13 := by
  apply FastRouting.sound _ _ [50,12,192,320] 13 (by decide) (choices 1) [1,32,128,256] r1298 c1298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u662
  · exact u663
  · exact u664
  · exact m1298_256

def b1299 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 67 28 44 464 480 448 448 448), lower := (rows 51 67 28 44 16 32 64 128 256), losses := [] }

theorem u1299 : Upper (D 2) (R 2) [50,65,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1299
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1300 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 450, targets := 16 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,4)], upper := (rows 51 67 28 76 432 416 480 416 416), lower := (rows 51 67 28 76 16 32 64 128 256), losses := [] }

theorem u1300 : Upper (D 2) (R 2) [50,65,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1300
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1301 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 488, targets := 16 },{ cop := 3, region := 404, targets := 32 }], pairs := [(2,5),(3,4)], upper := (rows 51 67 28 104 404 420 452 388 388), lower := (rows 51 67 28 104 16 32 64 128 256), losses := [] }

theorem u1301 : Upper (D 2) (R 2) [50,65,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1301
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1302 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 450, targets := 16 },{ cop := 2, region := 488, targets := 16 }], pairs := [(1,4),(3,4)], upper := (rows 51 67 28 140 496 480 480 480 480), lower := (rows 51 67 28 140 16 32 64 128 256), losses := [] }

theorem u1302 : Upper (D 2) (R 2) [50,65,24,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1302
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1303 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 488, targets := 16 },{ cop := 3, region := 340, targets := 32 }], pairs := [(2,5),(3,4)], upper := (rows 51 67 28 168 468 484 452 452 452), lower := (rows 51 67 28 168 16 32 64 128 256), losses := [] }

theorem u1303 : Upper (D 2) (R 2) [50,65,24,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1303
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1304 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 488, targets := 16 },{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(3,4)], upper := (rows 51 67 28 200 436 420 484 420 420), lower := (rows 51 67 28 200 16 32 64 128 256), losses := [] }

theorem u1304 : Upper (D 2) (R 2) [50,65,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1304
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1305 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | _ => 0)

theorem u1305 : Upper (D 2) (R 2) [50,65,24,384] 13 := by
  apply FastRouting.sound _ _ [50,65,24,384] 13 (by decide) (choices 1) [4,32,64,128] r1305 c1305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u665
  · exact u666
  · exact u667
  · exact u668

def b1306 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 67 52 76 408 424 456 392 392), lower := (rows 51 67 52 76 16 32 64 128 256), losses := [] }

theorem u1306 : Upper (D 2) (R 2) [50,65,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1306
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1307 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 67 52 140 472 488 456 456 456), lower := (rows 51 67 52 140 16 32 64 128 256), losses := [] }

theorem u1307 : Upper (D 2) (R 2) [50,65,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1307
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1308 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 67 52 200 412 428 460 396 396), lower := (rows 51 67 52 200 16 32 64 128 256), losses := [] }

theorem u1308 : Upper (D 2) (R 2) [50,65,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1308
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1309 : PairBound 9 := { available := 460, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 67 52 392 476 492 460 460 460), lower := (rows 51 67 52 392 16 32 64 128 256), losses := [] }

theorem u1309 : Upper (D 2) (R 2) [50,65,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1309
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1310 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 440, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 51 67 76 140 432 432 496 432 432), lower := (rows 51 67 76 140 16 32 64 128 256), losses := [] }

theorem u1310 : Upper (D 2) (R 2) [50,65,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1310
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1311 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 440, targets := 64 },{ cop := 3, region := 356, targets := 16 }], pairs := [(2,4),(3,6)], upper := (rows 51 67 76 152 436 420 484 420 420), lower := (rows 51 67 76 152 16 32 64 128 256), losses := [] }

theorem u1311 : Upper (D 2) (R 2) [50,65,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1311
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1312 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1312 : Upper (D 2) (R 2) [50,65,72,384] 13 := by
  apply FastRouting.sound _ _ [50,65,72,384] 13 (by decide) (choices 1) [4,32,128] r1312 c1312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u669
  · exact u670
  · exact u671

def b1313 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 424, targets := 16 },{ cop := 2, region := 424, targets := 64 }], pairs := [(3,4),(3,6)], upper := (rows 51 67 84 140 440 424 488 424 424), lower := (rows 51 67 84 140 16 32 64 128 256), losses := [] }

theorem u1313 : Upper (D 2) (R 2) [50,65,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1313
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1314 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 424, targets := 16 },{ cop := 2, region := 424, targets := 64 }], pairs := [(3,4),(3,6)], upper := (rows 51 67 84 168 412 428 460 396 396), lower := (rows 51 67 84 168 16 32 64 128 256), losses := [] }

theorem u1314 : Upper (D 2) (R 2) [50,65,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1314
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1315 : PairBound 9 := { available := 428, camps := [{ cop := 2, region := 424, targets := 16 },{ cop := 2, region := 424, targets := 64 }], pairs := [(3,4),(3,6)], upper := (rows 51 67 84 392 444 428 492 428 428), lower := (rows 51 67 84 392 16 32 64 128 256), losses := [] }

theorem u1315 : Upper (D 2) (R 2) [50,65,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1315
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1316 : PairBound 9 := { available := 368, camps := [{ cop := 7, region := 12, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 67 140 140 368 368 368 496 368), lower := (rows 51 67 140 140 16 32 64 128 256), losses := [] }

theorem u1316 : Upper (D 2) (R 2) [50,65,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1316
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1317 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 67 140 152 372 356 356 484 356), lower := (rows 51 67 140 152 16 32 64 128 256), losses := [] }

theorem u1317 : Upper (D 2) (R 2) [50,65,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1317
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1318 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 67 140 200 308 308 372 436 308), lower := (rows 51 67 140 200 16 32 64 128 256), losses := [] }

theorem u1318 : Upper (D 2) (R 2) [50,65,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1318
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1319_256 : Upper (D 2) (R 2) [50,65,136,260,256] 13 :=
  permutation_upper _ _ _ [50,65,136,260,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u674

def r1319 : Route 9 := (fun mask => (mask,id))

def c1319 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1319 : Upper (D 2) (R 2) [50,65,136,260] 13 := by
  apply FastRouting.sound _ _ [50,65,136,260] 13 (by decide) (choices 1) [32,64,128,256] r1319 c1319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u672
  · exact u673
  · exact u674
  · exact m1319_256

#print axioms u1319
end Delivery.IrregularNine14.P02

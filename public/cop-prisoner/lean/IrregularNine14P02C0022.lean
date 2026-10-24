import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0011
import IrregularNine14P02C0012
import IrregularNine14P02C0013

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r1320 : Route 9 := (fun mask => (mask,id))

def c1320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | _ => 0)

theorem u1320 : Upper (D 2) (R 2) [50,65,136,272] 13 := by
  apply FastRouting.sound _ _ [50,65,136,272] 13 (by decide) (choices 1) [4,32,64,128,256] r1320 c1320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u675
  · exact u676
  · exact u677
  · exact u678
  · exact u679

def r1321 : Route 9 := (fun mask => (mask,id))

def c1321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1321 : Upper (D 2) (R 2) [50,65,136,320] 13 := by
  apply FastRouting.sound _ _ [50,65,136,320] 13 (by decide) (choices 1) [4,32,128,256] r1321 c1321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u680
  · exact u681
  · exact u682
  · exact u683

def b1322 : PairBound 9 := { available := 372, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 67 140 392 372 372 372 500 372), lower := (rows 51 67 140 392 16 32 64 128 256), losses := [] }

theorem u1322 : Upper (D 2) (R 2) [50,65,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1322
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1323 : PairBound 9 := { available := 332, camps := [{ cop := 2, region := 360, targets := 16 },{ cop := 3, region := 340, targets := 32 }], pairs := [(2,5),(3,4)], upper := (rows 51 67 148 168 348 364 332 460 332), lower := (rows 51 67 148 168 16 32 64 128 256), losses := [] }

theorem u1323 : Upper (D 2) (R 2) [50,65,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1323
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1324 : PairBound 9 := { available := 300, camps := [{ cop := 2, region := 360, targets := 16 },{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(3,4)], upper := (rows 51 67 148 200 316 300 364 428 300), lower := (rows 51 67 148 200 16 32 64 128 256), losses := [] }

theorem u1324 : Upper (D 2) (R 2) [50,65,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1324
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1325 : PairBound 9 := { available := 460, camps := [{ cop := 2, region := 360, targets := 16 },{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5),(3,4)], upper := (rows 51 67 148 296 476 492 460 460 460), lower := (rows 51 67 148 296 16 32 64 128 256), losses := [] }

theorem u1325 : Upper (D 2) (R 2) [50,65,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1325
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1326 : PairBound 9 := { available := 428, camps := [{ cop := 2, region := 360, targets := 16 },{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(3,4)], upper := (rows 51 67 148 328 444 428 492 428 428), lower := (rows 51 67 148 328 16 32 64 128 256), losses := [] }

theorem u1326 : Upper (D 2) (R 2) [50,65,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1326
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1327 : Route 9 := (fun mask => (mask,id))

def c1327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | _ => 0)

theorem u1327 : Upper (D 2) (R 2) [50,65,144,384] 13 := by
  apply FastRouting.sound _ _ [50,65,144,384] 13 (by decide) (choices 1) [4,8,32,64,256] r1327 c1327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u684
  · exact u685
  · exact u686
  · exact u687
  · exact u688

def r1328 : Route 9 := (fun mask => (mask,id))

def c1328 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1328 : Upper (D 2) (R 2) [50,65,192,384] 13 := by
  apply FastRouting.sound _ _ [50,65,192,384] 13 (by decide) (choices 1) [4,8,32,256] r1328 c1328
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u689
  · exact u690
  · exact u691
  · exact u692

def b1329 : PairBound 9 := { available := 124, camps := [{ cop := 2, region := 8, targets := 48 }], pairs := [(3,4),(3,5)], upper := (rows 51 67 388 392 124 124 124 252 380), lower := (rows 51 67 388 392 16 32 64 128 256), losses := [] }

theorem u1329 : Upper (D 2) (R 2) [50,65,384,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1329
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1330 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 70 13 56 464 480 448 448 448), lower := (rows 51 70 13 56 16 32 64 128 256), losses := [] }

theorem u1330 : Upper (D 2) (R 2) [50,68,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1330
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1331 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 482, targets := 16 }], pairs := [(0,6),(1,4)], upper := (rows 51 70 13 88 432 416 480 416 416), lower := (rows 51 70 13 88 16 32 64 128 256), losses := [] }

theorem u1331 : Upper (D 2) (R 2) [50,68,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1331
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1332 : Route 9 := (fun mask => (mask,id))

def c1332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1332 : Upper (D 2) (R 2) [50,68,9,144] 13 := by
  apply FastRouting.sound _ _ [50,68,9,144] 13 (by decide) (choices 1) [32,64,128,256] r1332 c1332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u693
  · exact u694
  · exact u695
  · exact u696

def r1333 : Route 9 := (fun mask => (mask,id))

def c1333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1333 : Upper (D 2) (R 2) [50,68,9,192] 13 := by
  apply FastRouting.sound _ _ [50,68,9,192] 13 (by decide) (choices 1) [32,128,256] r1333 c1333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u697
  · exact u698
  · exact u699

def r1334 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1334 : Upper (D 2) (R 2) [50,68,9,384] 13 := by
  apply FastRouting.sound _ _ [50,68,9,384] 13 (by decide) (choices 1) [32,64,128] r1334 c1334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u700
  · exact u701
  · exact u702

def b1335 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 70 28 41 464 480 448 448 448), lower := (rows 51 70 28 41 16 32 64 128 256), losses := [] }

theorem u1335 : Upper (D 2) (R 2) [50,68,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1335
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1336 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,4)], upper := (rows 51 70 28 73 432 416 480 416 416), lower := (rows 51 70 28 73 16 32 64 128 256), losses := [] }

theorem u1336 : Upper (D 2) (R 2) [50,68,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1336
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1337 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,4)], upper := (rows 51 70 28 104 401 417 449 385 385), lower := (rows 51 70 28 104 16 32 64 128 256), losses := [] }

theorem u1337 : Upper (D 2) (R 2) [50,68,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1337
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1338 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4),(3,4)], upper := (rows 51 70 28 137 496 480 480 480 480), lower := (rows 51 70 28 137 16 32 64 128 256), losses := [] }

theorem u1338 : Upper (D 2) (R 2) [50,68,24,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1338
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1339 : Route 9 := (fun mask => (mask,id))

def c1339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1339 : Upper (D 2) (R 2) [50,68,24,160] 13 := by
  apply FastRouting.sound _ _ [50,68,24,160] 13 (by decide) (choices 1) [1,64,128,256] r1339 c1339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u703
  · exact u704
  · exact u705
  · exact u706

def b1340 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,4)], upper := (rows 51 70 28 200 433 417 481 417 417), lower := (rows 51 70 28 200 16 32 64 128 256), losses := [] }

theorem u1340 : Upper (D 2) (R 2) [50,68,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1340
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1341 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1341 : Upper (D 2) (R 2) [50,68,24,384] 13 := by
  apply FastRouting.sound _ _ [50,68,24,384] 13 (by decide) (choices 1) [1,32,64,128] r1341 c1341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u707
  · exact u708
  · exact u709
  · exact u710

def b1342 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 51 70 133 56 472 488 456 456 456), lower := (rows 51 70 133 56 16 32 64 128 256), losses := [] }

theorem u1342 : Upper (D 2) (R 2) [50,68,129,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1342
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1343 : Route 9 := (fun mask => (mask,id))

def c1343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1343 : Upper (D 2) (R 2) [50,68,129,80] 13 := by
  apply FastRouting.sound _ _ [50,68,129,80] 13 (by decide) (choices 1) [8,32,128,256] r1343 c1343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u711
  · exact u712
  · exact u713
  · exact u714

def r1344 : Route 9 := (fun mask => (mask,id))

def c1344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u1344 : Upper (D 2) (R 2) [50,68,129,144] 13 := by
  apply FastRouting.sound _ _ [50,68,129,144] 13 (by decide) (choices 1) [8,32,64,256] r1344 c1344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u715
  · exact u716
  · exact u717
  · exact u718

def r1345 : Route 9 := (fun mask => (mask,id))

def c1345 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1345 : Upper (D 2) (R 2) [50,68,129,192] 13 := by
  apply FastRouting.sound _ _ [50,68,129,192] 13 (by decide) (choices 1) [8,32,256] r1345 c1345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u719
  · exact u720
  · exact u721

def r1346 : Route 9 := (fun mask => (mask,id))

def c1346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0)

theorem u1346 : Upper (D 2) (R 2) [50,68,129,272] 13 := by
  apply FastRouting.sound _ _ [50,68,129,272] 13 (by decide) (choices 1) [8,32,64,128,256] r1346 c1346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u722
  · exact u723
  · exact u724
  · exact u725
  · exact u726

def r1347 : Route 9 := (fun mask => (mask,id))

def c1347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1347 : Upper (D 2) (R 2) [50,68,129,320] 13 := by
  apply FastRouting.sound _ _ [50,68,129,320] 13 (by decide) (choices 1) [8,32,128,256] r1347 c1347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u727
  · exact u728
  · exact u729
  · exact u730

def r1348 : Route 9 := (fun mask => (mask,id))

def c1348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u1348 : Upper (D 2) (R 2) [50,68,129,384] 13 := by
  apply FastRouting.sound _ _ [50,68,129,384] 13 (by decide) (choices 1) [8,32,64,256] r1348 c1348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u731
  · exact u732
  · exact u733
  · exact u734

def b1349 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 51 70 140 25 496 480 480 480 480), lower := (rows 51 70 140 25 16 32 64 128 256), losses := [] }

theorem u1349 : Upper (D 2) (R 2) [50,68,136,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1349
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1350 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 51 70 140 56 465 481 449 449 449), lower := (rows 51 70 140 56 16 32 64 128 256), losses := [] }

theorem u1350 : Upper (D 2) (R 2) [50,68,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1350
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1351 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 51 70 140 73 432 432 496 432 432), lower := (rows 51 70 140 73 16 32 64 128 256), losses := [] }

theorem u1351 : Upper (D 2) (R 2) [50,68,136,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1351
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1352 : Route 9 := (fun mask => (mask,id))

def c1352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1352 : Upper (D 2) (R 2) [50,68,136,80] 13 := by
  apply FastRouting.sound _ _ [50,68,136,80] 13 (by decide) (choices 1) [1,32,128,256] r1352 c1352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u735
  · exact u736
  · exact u737
  · exact u738

def b1353 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 70 140 137 368 368 368 496 368), lower := (rows 51 70 140 137 16 32 64 128 256), losses := [] }

theorem u1353 : Upper (D 2) (R 2) [50,68,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1353
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1354 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 70 140 152 369 353 353 481 353), lower := (rows 51 70 140 152 16 32 64 128 256), losses := [] }

theorem u1354 : Upper (D 2) (R 2) [50,68,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1354
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1355 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 6, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 51 70 140 200 305 305 369 433 305), lower := (rows 51 70 140 200 16 32 64 128 256), losses := [] }

theorem u1355 : Upper (D 2) (R 2) [50,68,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1355
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1356 : Route 9 := (fun mask => (mask,id))

def c1356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1356 : Upper (D 2) (R 2) [50,68,136,257] 13 := by
  apply FastRouting.sound _ _ [50,68,136,257] 13 (by decide) (choices 1) [32,64,128,256] r1356 c1356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u739
  · exact u740
  · exact u741
  · exact u742

def r1357 : Route 9 := (fun mask => (mask,id))

def c1357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1357 : Upper (D 2) (R 2) [50,68,136,272] 13 := by
  apply FastRouting.sound _ _ [50,68,136,272] 13 (by decide) (choices 1) [1,32,64,128,256] r1357 c1357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u743
  · exact u744
  · exact u745
  · exact u746
  · exact u747

def r1358 : Route 9 := (fun mask => (mask,id))

def c1358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1358 : Upper (D 2) (R 2) [50,68,136,320] 13 := by
  apply FastRouting.sound _ _ [50,68,136,320] 13 (by decide) (choices 1) [1,32,128,256] r1358 c1358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u748
  · exact u749
  · exact u750
  · exact u751

def b1359 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 70 140 392 369 369 369 497 369), lower := (rows 51 70 140 392 16 32 64 128 256), losses := [] }

theorem u1359 : Upper (D 2) (R 2) [50,68,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1359
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1360 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 51 70 148 41 472 488 456 456 456), lower := (rows 51 70 148 41 16 32 64 128 256), losses := [] }

theorem u1360 : Upper (D 2) (R 2) [50,68,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1360
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1361 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 456, targets := 16 },{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(3,4)], upper := (rows 51 70 148 73 440 424 488 424 424), lower := (rows 51 70 148 73 16 32 64 128 256), losses := [] }

theorem u1361 : Upper (D 2) (R 2) [50,68,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1361
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1362 : Route 9 := (fun mask => (mask,id))

def c1362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0)

theorem u1362 : Upper (D 2) (R 2) [50,68,144,96] 13 := by
  apply FastRouting.sound _ _ [50,68,144,96] 13 (by decide) (choices 1) [1,8,128,256] r1362 c1362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u752
  · exact u753
  · exact u754
  · exact u755

def r1363 : Route 9 := (fun mask => (mask,id))

def c1363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u1363 : Upper (D 2) (R 2) [50,68,144,129] 13 := by
  apply FastRouting.sound _ _ [50,68,144,129] 13 (by decide) (choices 1) [8,32,64,256] r1363 c1363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u756
  · exact u757
  · exact u758
  · exact u759

def r1364 : Route 9 := (fun mask => (mask,id))

def c1364 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u1364 : Upper (D 2) (R 2) [50,68,144,160] 13 := by
  apply FastRouting.sound _ _ [50,68,144,160] 13 (by decide) (choices 1) [1,8,64,256] r1364 c1364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u760
  · exact u761
  · exact u762
  · exact u763

def r1365 : Route 9 := (fun mask => (mask,id))

def c1365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1365 : Upper (D 2) (R 2) [50,68,144,192] 13 := by
  apply FastRouting.sound _ _ [50,68,144,192] 13 (by decide) (choices 1) [1,8,32,256] r1365 c1365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u764
  · exact u765
  · exact u766
  · exact u767

def r1366 : Route 9 := (fun mask => (mask,id))

def c1366 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0)

theorem u1366 : Upper (D 2) (R 2) [50,68,144,257] 13 := by
  apply FastRouting.sound _ _ [50,68,144,257] 13 (by decide) (choices 1) [8,32,64,128,256] r1366 c1366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u768
  · exact u769
  · exact u770
  · exact u771
  · exact u772

def r1367 : Route 9 := (fun mask => (mask,id))

def c1367 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0)

theorem u1367 : Upper (D 2) (R 2) [50,68,144,288] 13 := by
  apply FastRouting.sound _ _ [50,68,144,288] 13 (by decide) (choices 1) [1,8,64,128,256] r1367 c1367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u773
  · exact u774
  · exact u775
  · exact u776
  · exact u777

def r1368 : Route 9 := (fun mask => (mask,id))

def c1368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1368 : Upper (D 2) (R 2) [50,68,144,320] 13 := by
  apply FastRouting.sound _ _ [50,68,144,320] 13 (by decide) (choices 1) [1,8,32,128,256] r1368 c1368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u778
  · exact u779
  · exact u780
  · exact u781
  · exact u782

def r1369 : Route 9 := (fun mask => (mask,id))

def c1369 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u1369 : Upper (D 2) (R 2) [50,68,144,384] 13 := by
  apply FastRouting.sound _ _ [50,68,144,384] 13 (by decide) (choices 1) [1,8,32,64,256] r1369 c1369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u783
  · exact u784
  · exact u785
  · exact u786
  · exact u787

def b1370 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 51 70 388 25 504 488 488 488 488), lower := (rows 51 70 388 25 16 32 64 128 256), losses := [] }

theorem u1370 : Upper (D 2) (R 2) [50,68,384,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1370
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1371 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 51 70 388 56 473 489 457 457 457), lower := (rows 51 70 388 56 16 32 64 128 256), losses := [] }

theorem u1371 : Upper (D 2) (R 2) [50,68,384,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1371
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1372 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1372 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1372 : Upper (D 2) (R 2) [50,68,384,65] 13 := by
  apply FastRouting.sound _ _ [50,68,384,65] 13 (by decide) (choices 1) [8,32,128] r1372 c1372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u788
  · exact u789
  · exact u790

def r1373 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1373 : Upper (D 2) (R 2) [50,68,384,80] 13 := by
  apply FastRouting.sound _ _ [50,68,384,80] 13 (by decide) (choices 1) [1,8,32,128] r1373 c1373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u791
  · exact u792
  · exact u793
  · exact u794

def r1374 : Route 9 := (fun mask => (mask,id))

def c1374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u1374 : Upper (D 2) (R 2) [50,68,384,129] 13 := by
  apply FastRouting.sound _ _ [50,68,384,129] 13 (by decide) (choices 1) [8,32,64,256] r1374 c1374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u795
  · exact u796
  · exact u797
  · exact u798

def r1375 : Route 9 := (fun mask => (mask,id))

def c1375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u1375 : Upper (D 2) (R 2) [50,68,384,144] 13 := by
  apply FastRouting.sound _ _ [50,68,384,144] 13 (by decide) (choices 1) [1,8,32,64,256] r1375 c1375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u799
  · exact u800
  · exact u801
  · exact u802
  · exact u803

def r1376 : Route 9 := (fun mask => (mask,id))

def c1376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1376 : Upper (D 2) (R 2) [50,68,384,192] 13 := by
  apply FastRouting.sound _ _ [50,68,384,192] 13 (by decide) (choices 1) [1,8,32,256] r1376 c1376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u804
  · exact u805
  · exact u806
  · exact u807

def b1377 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 48 }], pairs := [(3,4),(3,5)], upper := (rows 51 70 388 392 121 121 121 249 377), lower := (rows 51 70 388 392 16 32 64 128 256), losses := [] }

theorem u1377 : Upper (D 2) (R 2) [50,68,384,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1377
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1378 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 12, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 194 13 28 496 480 480 480 480), lower := (rows 51 194 13 28 16 32 64 128 256), losses := [] }

theorem u1378 : Upper (D 2) (R 2) [50,192,9,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1378
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1379 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 194 13 56 468 484 452 452 452), lower := (rows 51 194 13 56 16 32 64 128 256), losses := [] }

theorem u1379 : Upper (D 2) (R 2) [50,192,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1379
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u1379
end Delivery.IrregularNine14.P02

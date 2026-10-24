import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0013
import IrregularNine14P02C0014
import IrregularNine14P02C0015

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r1380 : Route 9 := (fun mask => (mask,id))

def c1380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1380 : Upper (D 2) (R 2) [50,192,9,68] 13 := by
  apply FastRouting.sound _ _ [50,192,9,68] 13 (by decide) (choices 1) [32,128,256] r1380 c1380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u808
  · exact u809
  · exact u810

def r1381 : Route 9 := (fun mask => (mask,id))

def c1381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1381 : Upper (D 2) (R 2) [50,192,9,80] 13 := by
  apply FastRouting.sound _ _ [50,192,9,80] 13 (by decide) (choices 1) [4,32,128,256] r1381 c1381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u811
  · exact u812
  · exact u813
  · exact u814

def b1382 : PairBound 9 := { available := 308, camps := [{ cop := 1, region := 8, targets := 48 }], pairs := [(3,4),(3,5)], upper := (rows 51 194 13 200 308 308 372 436 308), lower := (rows 51 194 13 200 16 32 64 128 256), losses := [] }

theorem u1382 : Upper (D 2) (R 2) [50,192,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1382
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1383 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1383 : Upper (D 2) (R 2) [50,192,9,260] 13 := by
  apply FastRouting.sound _ _ [50,192,9,260] 13 (by decide) (choices 1) [32,64,256] r1383 c1383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u815
  · exact u816
  · exact u817

def r1384 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | _ => 0)

theorem u1384 : Upper (D 2) (R 2) [50,192,9,272] 13 := by
  apply FastRouting.sound _ _ [50,192,9,272] 13 (by decide) (choices 1) [4,32,64,256] r1384 c1384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u818
  · exact u819
  · exact u820
  · exact u821

def r1385 : Route 9 := (fun mask => (mask,id))

def c1385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1385 : Upper (D 2) (R 2) [50,192,9,320] 13 := by
  apply FastRouting.sound _ _ [50,192,9,320] 13 (by decide) (choices 1) [4,32,128,256] r1385 c1385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u822
  · exact u823
  · exact u824
  · exact u825

def b1386 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 194 21 44 472 488 456 456 456), lower := (rows 51 194 21 44 16 32 64 128 256), losses := [] }

theorem u1386 : Upper (D 2) (R 2) [50,192,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1386
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1387 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 194 21 76 440 424 488 424 424), lower := (rows 51 194 21 76 16 32 64 128 256), losses := [] }

theorem u1387 : Upper (D 2) (R 2) [50,192,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1387
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1388 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 194 21 104 412 428 460 396 396), lower := (rows 51 194 21 104 16 32 64 128 256), losses := [] }

theorem u1388 : Upper (D 2) (R 2) [50,192,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1388
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1389 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 194 21 268 504 488 488 488 488), lower := (rows 51 194 21 268 16 32 64 128 256), losses := [] }

theorem u1389 : Upper (D 2) (R 2) [50,192,17,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1389
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1390 : PairBound 9 := { available := 460, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 194 21 296 476 492 460 460 460), lower := (rows 51 194 21 296 16 32 64 128 256), losses := [] }

theorem u1390 : Upper (D 2) (R 2) [50,192,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1390
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1391 : PairBound 9 := { available := 428, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 51 194 21 328 444 428 492 428 428), lower := (rows 51 194 21 328 16 32 64 128 256), losses := [] }

theorem u1391 : Upper (D 2) (R 2) [50,192,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1391
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1392 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 194 28 44 465 481 449 449 449), lower := (rows 51 194 28 44 16 32 64 128 256), losses := [] }

theorem u1392 : Upper (D 2) (R 2) [50,192,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1392
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1393 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 482, targets := 16 },{ cop := 3, region := 436, targets := 64 }], pairs := [(1,4),(2,6)], upper := (rows 51 194 28 73 436 420 484 420 420), lower := (rows 51 194 28 73 16 32 64 128 256), losses := [] }

theorem u1393 : Upper (D 2) (R 2) [50,192,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1393
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1394 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 450, targets := 16 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(1,4)], upper := (rows 51 194 28 76 433 417 481 417 417), lower := (rows 51 194 28 76 16 32 64 128 256), losses := [] }

theorem u1394 : Upper (D 2) (R 2) [50,192,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1394
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1395 : Route 9 := (fun mask => (mask,id))

def c1395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | _ => 0)

theorem u1395 : Upper (D 2) (R 2) [50,192,24,96] 13 := by
  apply FastRouting.sound _ _ [50,192,24,96] 13 (by decide) (choices 1) [1,4,128,256] r1395 c1395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u826
  · exact u827
  · exact u828
  · exact u829

def b1396 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 8, targets := 48 }], pairs := [(3,4),(3,5)], upper := (rows 51 194 28 200 309 293 357 421 293), lower := (rows 51 194 28 200 16 32 64 128 256), losses := [] }

theorem u1396 : Upper (D 2) (R 2) [50,192,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1396
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1397 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | _ => 0)

theorem u1397 : Upper (D 2) (R 2) [50,192,24,257] 13 := by
  apply FastRouting.sound _ _ [50,192,24,257] 13 (by decide) (choices 1) [4,32,64,256] r1397 c1397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u830
  · exact u831
  · exact u832
  · exact u833

def r1398 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1398 : Upper (D 2) (R 2) [50,192,24,260] 13 := by
  apply FastRouting.sound _ _ [50,192,24,260] 13 (by decide) (choices 1) [1,32,64,256] r1398 c1398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u834
  · exact u835
  · exact u836
  · exact u837

def r1399 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1399 : Upper (D 2) (R 2) [50,192,24,288] 13 := by
  apply FastRouting.sound _ _ [50,192,24,288] 13 (by decide) (choices 1) [1,4,64,256] r1399 c1399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u838
  · exact u839
  · exact u840
  · exact u841

def r1400 : Route 9 := (fun mask => (mask,id))

def c1400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1400 : Upper (D 2) (R 2) [50,192,24,320] 13 := by
  apply FastRouting.sound _ _ [50,192,24,320] 13 (by decide) (choices 1) [1,4,32,128,256] r1400 c1400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u842
  · exact u843
  · exact u844
  · exact u845
  · exact u846

def b1401 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 194 52 73 412 428 460 396 396), lower := (rows 51 194 52 73 16 32 64 128 256), losses := [] }

theorem u1401 : Upper (D 2) (R 2) [50,192,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1401
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1402 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 194 52 76 409 425 457 393 393), lower := (rows 51 194 52 76 16 32 64 128 256), losses := [] }

theorem u1402 : Upper (D 2) (R 2) [50,192,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1402
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1403 : PairBound 9 := { available := 460, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 194 52 265 476 492 460 460 460), lower := (rows 51 194 52 265 16 32 64 128 256), losses := [] }

theorem u1403 : Upper (D 2) (R 2) [50,192,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1403
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1404 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 194 52 268 473 489 457 457 457), lower := (rows 51 194 52 268 16 32 64 128 256), losses := [] }

theorem u1404 : Upper (D 2) (R 2) [50,192,48,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1404
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1405 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 51 194 52 328 413 429 461 397 397), lower := (rows 51 194 52 328 16 32 64 128 256), losses := [] }

theorem u1405 : Upper (D 2) (R 2) [50,192,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1405
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1406 : Route 9 := (fun mask => (mask,id))

def c1406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1406 : Upper (D 2) (R 2) [50,192,65,132] 13 := by
  apply FastRouting.sound _ _ [50,192,65,132] 13 (by decide) (choices 1) [8,32,256] r1406 c1406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u847
  · exact u848
  · exact u849

def r1407 : Route 9 := (fun mask => (mask,id))

def c1407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1407 : Upper (D 2) (R 2) [50,192,65,144] 13 := by
  apply FastRouting.sound _ _ [50,192,65,144] 13 (by decide) (choices 1) [4,8,32,256] r1407 c1407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u850
  · exact u851
  · exact u852
  · exact u853

def r1408 : Route 9 := (fun mask => (mask,id))

def c1408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1408 : Upper (D 2) (R 2) [50,192,65,260] 13 := by
  apply FastRouting.sound _ _ [50,192,65,260] 13 (by decide) (choices 1) [8,32,128,256] r1408 c1408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u854
  · exact u855
  · exact u856
  · exact u857

def r1409 : Route 9 := (fun mask => (mask,id))

def c1409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | _ => 0)

theorem u1409 : Upper (D 2) (R 2) [50,192,65,272] 13 := by
  apply FastRouting.sound _ _ [50,192,65,272] 13 (by decide) (choices 1) [4,8,32,128,256] r1409 c1409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u858
  · exact u859
  · exact u860
  · exact u861
  · exact u862

def r1410 : Route 9 := (fun mask => (mask,id))

def c1410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1410 : Upper (D 2) (R 2) [50,192,65,384] 13 := by
  apply FastRouting.sound _ _ [50,192,65,384] 13 (by decide) (choices 1) [4,8,32,256] r1410 c1410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u863
  · exact u864
  · exact u865
  · exact u866

def b1411 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 12, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 194 76 140 305 305 369 433 305), lower := (rows 51 194 76 140 16 32 64 128 256), losses := [] }

theorem u1411 : Upper (D 2) (R 2) [50,192,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1411
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1412 : Route 9 := (fun mask => (mask,id))

def c1412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1412 : Upper (D 2) (R 2) [50,192,72,144] 13 := by
  apply FastRouting.sound _ _ [50,192,72,144] 13 (by decide) (choices 1) [1,4,32,256] r1412 c1412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u867
  · exact u868
  · exact u869
  · exact u870

def r1413 : Route 9 := (fun mask => (mask,id))

def c1413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1413 : Upper (D 2) (R 2) [50,192,72,257] 13 := by
  apply FastRouting.sound _ _ [50,192,72,257] 13 (by decide) (choices 1) [4,32,128,256] r1413 c1413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u871
  · exact u872
  · exact u873
  · exact u874

def r1414 : Route 9 := (fun mask => (mask,id))

def c1414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1414 : Upper (D 2) (R 2) [50,192,72,260] 13 := by
  apply FastRouting.sound _ _ [50,192,72,260] 13 (by decide) (choices 1) [1,32,128,256] r1414 c1414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u875
  · exact u876
  · exact u877
  · exact u878

def r1415 : Route 9 := (fun mask => (mask,id))

def c1415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1415 : Upper (D 2) (R 2) [50,192,72,272] 13 := by
  apply FastRouting.sound _ _ [50,192,72,272] 13 (by decide) (choices 1) [1,4,32,128,256] r1415 c1415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u879
  · exact u880
  · exact u881
  · exact u882
  · exact u883

def r1416 : Route 9 := (fun mask => (mask,id))

def c1416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1416 : Upper (D 2) (R 2) [50,192,72,384] 13 := by
  apply FastRouting.sound _ _ [50,192,72,384] 13 (by decide) (choices 1) [1,4,32,256] r1416 c1416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u884
  · exact u885
  · exact u886
  · exact u887

def r1417 : Route 9 := (fun mask => (mask,id))

def c1417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1417 : Upper (D 2) (R 2) [50,192,80,160] 13 := by
  apply FastRouting.sound _ _ [50,192,80,160] 13 (by decide) (choices 1) [1,4,8,256] r1417 c1417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u888
  · exact u889
  · exact u890
  · exact u891

def r1418 : Route 9 := (fun mask => (mask,id))

def c1418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | _ => 0)

theorem u1418 : Upper (D 2) (R 2) [50,192,80,257] 13 := by
  apply FastRouting.sound _ _ [50,192,80,257] 13 (by decide) (choices 1) [4,8,32,128,256] r1418 c1418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u892
  · exact u893
  · exact u894
  · exact u895
  · exact u896

def r1419 : Route 9 := (fun mask => (mask,id))

def c1419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1419 : Upper (D 2) (R 2) [50,192,80,260] 13 := by
  apply FastRouting.sound _ _ [50,192,80,260] 13 (by decide) (choices 1) [1,8,32,128,256] r1419 c1419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u897
  · exact u898
  · exact u899
  · exact u900
  · exact u901

def r1420 : Route 9 := (fun mask => (mask,id))

def c1420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | _ => 0)

theorem u1420 : Upper (D 2) (R 2) [50,192,80,288] 13 := by
  apply FastRouting.sound _ _ [50,192,80,288] 13 (by decide) (choices 1) [1,4,8,128,256] r1420 c1420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u902
  · exact u903
  · exact u904
  · exact u905
  · exact u906

def r1421 : Route 9 := (fun mask => (mask,id))

def c1421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1421 : Upper (D 2) (R 2) [50,192,80,384] 13 := by
  apply FastRouting.sound _ _ [50,192,80,384] 13 (by decide) (choices 1) [1,4,8,32,256] r1421 c1421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u907
  · exact u908
  · exact u909
  · exact u910
  · exact u911

def b1422 : PairBound 9 := { available := 316, camps := [{ cop := 1, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 194 196 265 316 316 380 444 316), lower := (rows 51 194 196 265 16 32 64 128 256), losses := [] }

theorem u1422 : Upper (D 2) (R 2) [50,192,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1422
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1423 : PairBound 9 := { available := 313, camps := [{ cop := 1, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 194 196 268 313 313 377 441 313), lower := (rows 51 194 196 268 16 32 64 128 256), losses := [] }

theorem u1423 : Upper (D 2) (R 2) [50,192,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1423
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1424 : PairBound 9 := { available := 301, camps := [{ cop := 1, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 194 196 280 317 301 365 429 301), lower := (rows 51 194 196 280 16 32 64 128 256), losses := [] }

theorem u1424 : Upper (D 2) (R 2) [50,192,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1424
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1425 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 8, targets := 48 }], pairs := [(3,4),(3,5)], upper := (rows 51 194 261 268 248 248 248 248 504), lower := (rows 51 194 261 268 16 32 64 128 256), losses := [] }

theorem u1425 : Upper (D 2) (R 2) [50,192,257,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1425
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1426 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 256 => 8 | _ => 0)

theorem u1426 : Upper (D 2) (R 2) [50,192,257,272] 13 := by
  apply FastRouting.sound _ _ [50,192,257,272] 13 (by decide) (choices 1) [4,8,32,64] r1426 c1426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u912
  · exact u913
  · exact u914
  · exact u915

def r1427 : Route 9 := (fun mask => (mask,id))

def c1427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1427 : Upper (D 2) (R 2) [50,192,257,320] 13 := by
  apply FastRouting.sound _ _ [50,192,257,320] 13 (by decide) (choices 1) [4,8,32,128] r1427 c1427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u916
  · exact u917
  · exact u918
  · exact u919

def b1428 : PairBound 9 := { available := 241, camps := [{ cop := 8, region := 12, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 194 268 268 241 241 241 241 497), lower := (rows 51 194 268 268 16 32 64 128 256), losses := [] }

theorem u1428 : Upper (D 2) (R 2) [50,192,264,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1428
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1429 : PairBound 9 := { available := 229, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 194 268 280 245 229 229 229 485), lower := (rows 51 194 268 280 16 32 64 128 256), losses := [] }

theorem u1429 : Upper (D 2) (R 2) [50,192,264,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1429
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1430 : PairBound 9 := { available := 181, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 51 194 268 328 181 181 245 181 437), lower := (rows 51 194 268 328 16 32 64 128 256), losses := [] }

theorem u1430 : Upper (D 2) (R 2) [50,192,264,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1430
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1431 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1431 : Upper (D 2) (R 2) [50,192,272,288] 13 := by
  apply FastRouting.sound _ _ [50,192,272,288] 13 (by decide) (choices 1) [1,4,8,64] r1431 c1431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u920
  · exact u921
  · exact u922
  · exact u923

def r1432 : Route 9 := (fun mask => (mask,id))

def c1432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1432 : Upper (D 2) (R 2) [50,192,272,320] 13 := by
  apply FastRouting.sound _ _ [50,192,272,320] 13 (by decide) (choices 1) [1,4,8,32,128] r1432 c1432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u924
  · exact u925
  · exact u926
  · exact u927
  · exact u928

theorem m1433_8 : Upper (D 2) (R 2) [50,192,320,384,8] 13 :=
  permutation_upper _ _ _ [50,192,320,384,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u930

def r1433 : Route 9 := (fun mask => (mask,id))

def c1433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1433 : Upper (D 2) (R 2) [50,192,320,384] 13 := by
  apply FastRouting.sound _ _ [50,192,320,384] 13 (by decide) (choices 1) [1,4,8,32] r1433 c1433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u929
  · exact u930
  · exact m1433_8
  · exact u931

def b1434 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 14, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 7 14 56 464 480 448 448 448), lower := (rows 113 7 14 56 16 32 64 128 256), losses := [] }

theorem u1434 : Upper (D 2) (R 2) [112,5,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1434
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1435 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1435 : Upper (D 2) (R 2) [112,5,10,144] 13 := by
  apply FastRouting.sound _ _ [112,5,10,144] 13 (by decide) (choices 1) [32,128,256] r1435 c1435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u932
  · exact u933
  · exact u934

def r1436 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1436 : Upper (D 2) (R 2) [112,5,10,384] 13 := by
  apply FastRouting.sound _ _ [112,5,10,384] 13 (by decide) (choices 1) [32,128] r1436 c1436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u935
  · exact u936

def b1437 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 7 22 168 472 488 456 456 456), lower := (rows 113 7 22 168 16 32 64 128 256), losses := [] }

theorem u1437 : Upper (D 2) (R 2) [112,5,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1437
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1438 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 6, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 7 22 392 504 488 488 488 488), lower := (rows 113 7 22 392 16 32 64 128 256), losses := [] }

theorem u1438 : Upper (D 2) (R 2) [112,5,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1438
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1439 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 14, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 7 28 42 464 480 448 448 448), lower := (rows 113 7 28 42 16 32 64 128 256), losses := [] }

theorem u1439 : Upper (D 2) (R 2) [112,5,24,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1439
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u1439
end Delivery.IrregularNine14.P02

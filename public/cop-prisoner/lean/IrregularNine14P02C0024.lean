import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0015
import IrregularNine14P02C0016
import IrregularNine14P02C0017

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1440 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 113 7 28 104 402 418 450 386 386), lower := (rows 113 7 28 104 16 32 64 128 256), losses := [] }

theorem u1440 : Upper (D 2) (R 2) [112,5,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1440
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1441 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1441 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1441 : Upper (D 2) (R 2) [112,5,24,130] 13 := by
  apply FastRouting.sound _ _ [112,5,24,130] 13 (by decide) (choices 1) [32,128,256] r1441 c1441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u937
  · exact u938
  · exact u939

def r1442 : Route 9 := (fun mask => (mask,id))

def c1442 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1442 : Upper (D 2) (R 2) [112,5,24,160] 13 := by
  apply FastRouting.sound _ _ [112,5,24,160] 13 (by decide) (choices 1) [2,64,128,256] r1442 c1442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u940
  · exact u941
  · exact u942
  · exact u943

def r1443 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1443 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | _ => 0)

theorem u1443 : Upper (D 2) (R 2) [112,5,24,384] 13 := by
  apply FastRouting.sound _ _ [112,5,24,384] 13 (by decide) (choices 1) [2,32,128] r1443 c1443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u944
  · exact u945
  · exact u946

def b1444 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 6, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 113 7 52 74 408 424 456 392 392), lower := (rows 113 7 52 74 16 32 64 128 256), losses := [] }

theorem u1444 : Upper (D 2) (R 2) [112,5,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1444
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1445 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 7 52 138 472 488 456 456 456), lower := (rows 113 7 52 138 16 32 64 128 256), losses := [] }

theorem u1445 : Upper (D 2) (R 2) [112,5,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1445
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1446 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 6, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 7 52 200 410 426 458 394 394), lower := (rows 113 7 52 200 16 32 64 128 256), losses := [] }

theorem u1446 : Upper (D 2) (R 2) [112,5,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1446
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1447 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 6, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 7 52 392 474 490 458 458 458), lower := (rows 113 7 52 392 16 32 64 128 256), losses := [] }

theorem u1447 : Upper (D 2) (R 2) [112,5,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1447
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1448 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 113 7 134 56 472 488 456 456 456), lower := (rows 113 7 134 56 16 32 64 128 256), losses := [] }

theorem u1448 : Upper (D 2) (R 2) [112,5,130,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1448
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1449 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u1449 : Upper (D 2) (R 2) [112,5,130,144] 13 := by
  apply FastRouting.sound _ _ [112,5,130,144] 13 (by decide) (choices 1) [8,32,256] r1449 c1449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u947
  · exact u948
  · exact u949

def r1450 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0)

theorem u1450 : Upper (D 2) (R 2) [112,5,130,272] 13 := by
  apply FastRouting.sound _ _ [112,5,130,272] 13 (by decide) (choices 1) [8,32,128,256] r1450 c1450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u950
  · exact u951
  · exact u952
  · exact u953

def r1451 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u1451 : Upper (D 2) (R 2) [112,5,130,384] 13 := by
  apply FastRouting.sound _ _ [112,5,130,384] 13 (by decide) (choices 1) [8,32,256] r1451 c1451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u954
  · exact u955
  · exact u956

def r1452 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1452 : Upper (D 2) (R 2) [112,5,136,18] 13 := by
  apply FastRouting.sound _ _ [112,5,136,18] 13 (by decide) (choices 1) [32,128,256] r1452 c1452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u957
  · exact u958
  · exact u959

def b1453 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 113 7 140 56 466 482 450 450 450), lower := (rows 113 7 140 56 16 32 64 128 256), losses := [] }

theorem u1453 : Upper (D 2) (R 2) [112,5,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1453
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1454 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 113 7 140 138 368 368 368 496 368), lower := (rows 113 7 140 138 16 32 64 128 256), losses := [] }

theorem u1454 : Upper (D 2) (R 2) [112,5,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1454
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1455 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 113 7 140 152 370 354 354 482 354), lower := (rows 113 7 140 152 16 32 64 128 256), losses := [] }

theorem u1455 : Upper (D 2) (R 2) [112,5,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1455
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1456 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1456 : Upper (D 2) (R 2) [112,5,136,258] 13 := by
  apply FastRouting.sound _ _ [112,5,136,258] 13 (by decide) (choices 1) [32,128,256] r1456 c1456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u960
  · exact u961
  · exact u962

def r1457 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1457 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | _ => 0)

theorem u1457 : Upper (D 2) (R 2) [112,5,136,272] 13 := by
  apply FastRouting.sound _ _ [112,5,136,272] 13 (by decide) (choices 1) [2,32,128,256] r1457 c1457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u963
  · exact u964
  · exact u965
  · exact u966

def b1458 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 113 7 140 392 370 370 370 498 370), lower := (rows 113 7 140 392 16 32 64 128 256), losses := [] }

theorem u1458 : Upper (D 2) (R 2) [112,5,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1458
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1459 : PairBound 9 := { available := 456, camps := [{ cop := 1, region := 488, targets := 16 },{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5),(3,4)], upper := (rows 113 7 148 42 472 488 456 456 456), lower := (rows 113 7 148 42 16 32 64 128 256), losses := [] }

theorem u1459 : Upper (D 2) (R 2) [112,5,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1459
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1460 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 8, targets := 144 }], pairs := [(3,4),(3,7)], upper := (rows 113 7 148 104 410 426 458 394 394), lower := (rows 113 7 148 104 16 32 64 128 256), losses := [] }

theorem u1460 : Upper (D 2) (R 2) [112,5,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1460
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1461 : PairBound 9 := { available := 360, camps := [{ cop := 1, region := 488, targets := 16 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,4)], upper := (rows 113 7 148 138 376 360 360 488 360), lower := (rows 113 7 148 138 16 32 64 128 256), losses := [] }

theorem u1461 : Upper (D 2) (R 2) [112,5,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1461
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1462 : Route 9 := (fun mask => (mask,id))

def c1462 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u1462 : Upper (D 2) (R 2) [112,5,144,160] 13 := by
  apply FastRouting.sound _ _ [112,5,144,160] 13 (by decide) (choices 1) [2,8,64,256] r1462 c1462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u967
  · exact u968
  · exact u969
  · exact u970

def r1463 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0)

theorem u1463 : Upper (D 2) (R 2) [112,5,144,258] 13 := by
  apply FastRouting.sound _ _ [112,5,144,258] 13 (by decide) (choices 1) [8,32,128,256] r1463 c1463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u971
  · exact u972
  · exact u973
  · exact u974

def r1464 : Route 9 := (fun mask => (mask,id))

def c1464 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | _ => 0)

theorem u1464 : Upper (D 2) (R 2) [112,5,144,288] 13 := by
  apply FastRouting.sound _ _ [112,5,144,288] 13 (by decide) (choices 1) [2,8,64,128,256] r1464 c1464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u975
  · exact u976
  · exact u977
  · exact u978
  · exact u979

def r1465 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1465 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | _ => 0)

theorem u1465 : Upper (D 2) (R 2) [112,5,144,384] 13 := by
  apply FastRouting.sound _ _ [112,5,144,384] 13 (by decide) (choices 1) [2,8,32,256] r1465 c1465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u980
  · exact u981
  · exact u982
  · exact u983

def r1466 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0)

theorem u1466 : Upper (D 2) (R 2) [112,5,384,18] 13 := by
  apply FastRouting.sound _ _ [112,5,384,18] 13 (by decide) (choices 1) [8,32,128] r1466 c1466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u984
  · exact u985
  · exact u986

def b1467 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 113 7 388 56 474 490 458 458 458), lower := (rows 113 7 388 56 16 32 64 128 256), losses := [] }

theorem u1467 : Upper (D 2) (R 2) [112,5,384,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1467
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1468 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u1468 : Upper (D 2) (R 2) [112,5,384,130] 13 := by
  apply FastRouting.sound _ _ [112,5,384,130] 13 (by decide) (choices 1) [8,32,256] r1468 c1468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u987
  · exact u988
  · exact u989

def r1469 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | _ => 0)

theorem u1469 : Upper (D 2) (R 2) [112,5,384,144] 13 := by
  apply FastRouting.sound _ _ [112,5,384,144] 13 (by decide) (choices 1) [2,8,32,256] r1469 c1469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u990
  · exact u991
  · exact u992
  · exact u993

def b1470 : PairBound 9 := { available := 122, camps := [{ cop := 2, region := 8, targets := 48 }], pairs := [(3,4),(3,5)], upper := (rows 113 7 388 392 122 122 122 250 378), lower := (rows 113 7 388 392 16 32 64 128 256), losses := [] }

theorem u1470 : Upper (D 2) (R 2) [112,5,384,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1470
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1471 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 14, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 14 21 42 464 480 448 448 448), lower := (rows 113 14 21 42 16 32 64 128 256), losses := [] }

theorem u1471 : Upper (D 2) (R 2) [112,12,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1471
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1472 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 113 14 21 138 496 480 480 480 480), lower := (rows 113 14 21 138 16 32 64 128 256), losses := [] }

theorem u1472 : Upper (D 2) (R 2) [112,12,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1472
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1473 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 113 14 21 168 466 482 450 450 450), lower := (rows 113 14 21 168 16 32 64 128 256), losses := [] }

theorem u1473 : Upper (D 2) (R 2) [112,12,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1473
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1474 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 113 14 21 392 498 482 482 482 482), lower := (rows 113 14 21 392 16 32 64 128 256), losses := [] }

theorem u1474 : Upper (D 2) (R 2) [112,12,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1474
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1475 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 113 14 22 104 401 417 449 385 385), lower := (rows 113 14 22 104 16 32 64 128 256), losses := [] }

theorem u1475 : Upper (D 2) (R 2) [112,12,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1475
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1476 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1476 : Upper (D 2) (R 2) [112,12,18,129] 13 := by
  apply FastRouting.sound _ _ [112,12,18,129] 13 (by decide) (choices 1) [32,128,256] r1476 c1476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u994
  · exact u995
  · exact u996

def r1477 : Route 9 := (fun mask => (mask,id))

def c1477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1477 : Upper (D 2) (R 2) [112,12,18,160] 13 := by
  apply FastRouting.sound _ _ [112,12,18,160] 13 (by decide) (choices 1) [1,64,128,256] r1477 c1477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u997
  · exact u998
  · exact u999
  · exact u1000

def r1478 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1478 : Upper (D 2) (R 2) [112,12,18,384] 13 := by
  apply FastRouting.sound _ _ [112,12,18,384] 13 (by decide) (choices 1) [1,32,128] r1478 c1478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1001
  · exact u1002
  · exact u1003

def b1479 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 113 14 52 137 466 482 450 450 450), lower := (rows 113 14 52 137 16 32 64 128 256), losses := [] }

theorem u1479 : Upper (D 2) (R 2) [112,12,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1479
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1480 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 113 14 52 138 465 481 449 449 449), lower := (rows 113 14 52 138 16 32 64 128 256), losses := [] }

theorem u1480 : Upper (D 2) (R 2) [112,12,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1480
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1481 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 113 14 52 200 403 419 451 387 387), lower := (rows 113 14 52 200 16 32 64 128 256), losses := [] }

theorem u1481 : Upper (D 2) (R 2) [112,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1481
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1482 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 113 14 52 392 467 483 451 451 451), lower := (rows 113 14 52 392 16 32 64 128 256), losses := [] }

theorem u1482 : Upper (D 2) (R 2) [112,12,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1482
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1483 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 10, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 113 14 133 138 368 368 368 496 368), lower := (rows 113 14 133 138 16 32 64 128 256), losses := [] }

theorem u1483 : Upper (D 2) (R 2) [112,12,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1483
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1484 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1484 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1484 : Upper (D 2) (R 2) [112,12,129,144] 13 := by
  apply FastRouting.sound _ _ [112,12,129,144] 13 (by decide) (choices 1) [2,32,256] r1484 c1484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1004
  · exact u1005
  · exact u1006

def r1485 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1485 : Upper (D 2) (R 2) [112,12,129,258] 13 := by
  apply FastRouting.sound _ _ [112,12,129,258] 13 (by decide) (choices 1) [32,128,256] r1485 c1485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1007
  · exact u1008
  · exact u1009

def r1486 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1486 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | _ => 0)

theorem u1486 : Upper (D 2) (R 2) [112,12,129,272] 13 := by
  apply FastRouting.sound _ _ [112,12,129,272] 13 (by decide) (choices 1) [2,32,128,256] r1486 c1486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1010
  · exact u1011
  · exact u1012
  · exact u1013

def r1487 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1487 : Upper (D 2) (R 2) [112,12,129,384] 13 := by
  apply FastRouting.sound _ _ [112,12,129,384] 13 (by decide) (choices 1) [2,32,256] r1487 c1487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1014
  · exact u1015
  · exact u1016

def b1488 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 6, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 113 14 134 152 369 353 353 481 353), lower := (rows 113 14 134 152 16 32 64 128 256), losses := [] }

theorem u1488 : Upper (D 2) (R 2) [112,12,130,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1488
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1489 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1489 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1489 : Upper (D 2) (R 2) [112,12,130,272] 13 := by
  apply FastRouting.sound _ _ [112,12,130,272] 13 (by decide) (choices 1) [1,32,128,256] r1489 c1489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1017
  · exact u1018
  · exact u1019
  · exact u1020

def b1490 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 6, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 113 14 134 392 369 369 369 497 369), lower := (rows 113 14 134 392 16 32 64 128 256), losses := [] }

theorem u1490 : Upper (D 2) (R 2) [112,12,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1490
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1491 : Route 9 := (fun mask => (mask,id))

def c1491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u1491 : Upper (D 2) (R 2) [112,12,144,160] 13 := by
  apply FastRouting.sound _ _ [112,12,144,160] 13 (by decide) (choices 1) [1,2,64,256] r1491 c1491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1021
  · exact u1022
  · exact u1023
  · exact u1024

def r1492 : Route 9 := (fun mask => (mask,id))

def c1492 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1492 : Upper (D 2) (R 2) [112,12,144,288] 13 := by
  apply FastRouting.sound _ _ [112,12,144,288] 13 (by decide) (choices 1) [1,2,64,128,256] r1492 c1492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1025
  · exact u1026
  · exact u1027
  · exact u1028
  · exact u1029

def r1493 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1493 : Upper (D 2) (R 2) [112,12,144,384] 13 := by
  apply FastRouting.sound _ _ [112,12,144,384] 13 (by decide) (choices 1) [1,2,32,256] r1493 c1493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1030
  · exact u1031
  · exact u1032
  · exact u1033

def b1494 : PairBound 9 := { available := 115, camps := [{ cop := 2, region := 10, targets := 48 }], pairs := [(1,4),(1,5)], upper := (rows 113 14 388 392 115 115 115 243 371), lower := (rows 113 14 388 392 16 32 64 128 256), losses := [] }

theorem u1494 : Upper (D 2) (R 2) [112,12,384,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1494
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1495 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 2, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 113 19 38 76 408 424 456 392 392), lower := (rows 113 19 38 76 16 32 64 128 256), losses := [] }

theorem u1495 : Upper (D 2) (R 2) [112,17,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1495
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1496 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 19 38 140 472 488 456 456 456), lower := (rows 113 19 38 140 16 32 64 128 256), losses := [] }

theorem u1496 : Upper (D 2) (R 2) [112,17,34,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1496
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1497 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 19 38 200 412 428 460 396 396), lower := (rows 113 19 38 200 16 32 64 128 256), losses := [] }

theorem u1497 : Upper (D 2) (R 2) [112,17,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1497
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1498 : PairBound 9 := { available := 460, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 19 38 392 476 492 460 460 460), lower := (rows 113 19 38 392 16 32 64 128 256), losses := [] }

theorem u1498 : Upper (D 2) (R 2) [112,17,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1498
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1499 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 44 138 468 484 452 452 452), lower := (rows 113 19 44 138 16 32 64 128 256), losses := [] }

theorem u1499 : Upper (D 2) (R 2) [112,17,40,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1499
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u1499
end Delivery.IrregularNine14.P02

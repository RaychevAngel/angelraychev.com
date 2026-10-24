import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0017
import IrregularNine14P02C0018

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1500 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 19 44 140 466 482 450 450 450), lower := (rows 113 19 44 140 16 32 64 128 256), losses := [] }

theorem u1500 : Upper (D 2) (R 2) [112,17,40,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1500
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1501 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 44 200 406 422 454 390 390), lower := (rows 113 19 44 200 16 32 64 128 256), losses := [] }

theorem u1501 : Upper (D 2) (R 2) [112,17,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1501
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1502 : PairBound 9 := { available := 454, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 44 392 470 486 454 454 454), lower := (rows 113 19 44 392 16 32 64 128 256), losses := [] }

theorem u1502 : Upper (D 2) (R 2) [112,17,40,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1502
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1503 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 134 168 348 364 332 460 332), lower := (rows 113 19 134 168 16 32 64 128 256), losses := [] }

theorem u1503 : Upper (D 2) (R 2) [112,17,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1503
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1504 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 134 268 504 488 488 488 488), lower := (rows 113 19 134 268 16 32 64 128 256), losses := [] }

theorem u1504 : Upper (D 2) (R 2) [112,17,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1504
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1505 : PairBound 9 := { available := 460, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 134 296 476 492 460 460 460), lower := (rows 113 19 134 296 16 32 64 128 256), losses := [] }

theorem u1505 : Upper (D 2) (R 2) [112,17,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1505
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1506 : PairBound 9 := { available := 364, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 134 392 380 364 364 492 364), lower := (rows 113 19 134 392 16 32 64 128 256), losses := [] }

theorem u1506 : Upper (D 2) (R 2) [112,17,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1506
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1507 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 140 268 498 482 482 482 482), lower := (rows 113 19 140 268 16 32 64 128 256), losses := [] }

theorem u1507 : Upper (D 2) (R 2) [112,17,136,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1507
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1508 : PairBound 9 := { available := 454, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 140 296 470 486 454 454 454), lower := (rows 113 19 140 296 16 32 64 128 256), losses := [] }

theorem u1508 : Upper (D 2) (R 2) [112,17,136,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1508
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1509 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 164 200 286 302 334 398 270), lower := (rows 113 19 164 200 16 32 64 128 256), losses := [] }

theorem u1509 : Upper (D 2) (R 2) [112,17,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1509
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1510 : PairBound 9 := { available := 398, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 164 328 414 430 462 398 398), lower := (rows 113 19 164 328 16 32 64 128 256), losses := [] }

theorem u1510 : Upper (D 2) (R 2) [112,17,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1510
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1511 : PairBound 9 := { available := 334, camps := [{ cop := 0, region := 2, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 19 164 392 350 366 334 462 334), lower := (rows 113 19 164 392 16 32 64 128 256), losses := [] }

theorem u1511 : Upper (D 2) (R 2) [112,17,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1511
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1512 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 22 38 137 472 488 456 456 456), lower := (rows 113 22 38 137 16 32 64 128 256), losses := [] }

theorem u1512 : Upper (D 2) (R 2) [112,20,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1512
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1513 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 22 38 200 409 425 457 393 393), lower := (rows 113 22 38 200 16 32 64 128 256), losses := [] }

theorem u1513 : Upper (D 2) (R 2) [112,20,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1513
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1514 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 6, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 22 38 392 473 489 457 457 457), lower := (rows 113 22 38 392 16 32 64 128 256), losses := [] }

theorem u1514 : Upper (D 2) (R 2) [112,20,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1514
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1515 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 113 22 44 74 401 417 449 385 385), lower := (rows 113 22 44 74 16 32 64 128 256), losses := [] }

theorem u1515 : Upper (D 2) (R 2) [112,20,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1515
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1516 : Route 9 := (fun mask => (mask,id))

def c1516 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1516 : Upper (D 2) (R 2) [112,20,40,129] 13 := by
  apply FastRouting.sound _ _ [112,20,40,129] 13 (by decide) (choices 1) [2,64,128,256] r1516 c1516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1034
  · exact u1035
  · exact u1036
  · exact u1037

def r1517 : Route 9 := (fun mask => (mask,id))

def c1517 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1517 : Upper (D 2) (R 2) [112,20,40,130] 13 := by
  apply FastRouting.sound _ _ [112,20,40,130] 13 (by decide) (choices 1) [1,64,128,256] r1517 c1517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1038
  · exact u1039
  · exact u1040
  · exact u1041

def r1518 : Route 9 := (fun mask => (mask,id))

def c1518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | _ => 0)

theorem u1518 : Upper (D 2) (R 2) [112,20,40,192] 13 := by
  apply FastRouting.sound _ _ [112,20,40,192] 13 (by decide) (choices 1) [1,2,128,256] r1518 c1518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1042
  · exact u1043
  · exact u1044
  · exact u1045

def r1519 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1519 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1519 : Upper (D 2) (R 2) [112,20,40,384] 13 := by
  apply FastRouting.sound _ _ [112,20,40,384] 13 (by decide) (choices 1) [1,2,64,128] r1519 c1519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1046
  · exact u1047
  · exact u1048
  · exact u1049

def b1520 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 6, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 113 22 100 137 410 426 458 394 394), lower := (rows 113 22 100 137 16 32 64 128 256), losses := [] }

theorem u1520 : Upper (D 2) (R 2) [112,20,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1520
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1521 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 113 22 100 138 409 425 457 393 393), lower := (rows 113 22 100 138 16 32 64 128 256), losses := [] }

theorem u1521 : Upper (D 2) (R 2) [112,20,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1521
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1522 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 6, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 113 22 100 392 411 427 459 395 395), lower := (rows 113 22 100 392 16 32 64 128 256), losses := [] }

theorem u1522 : Upper (D 2) (R 2) [112,20,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1522
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1523 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 8, targets := 144 }], pairs := [(3,4),(3,7)], upper := (rows 113 22 133 104 410 426 458 394 394), lower := (rows 113 22 133 104 16 32 64 128 256), losses := [] }

theorem u1523 : Upper (D 2) (R 2) [112,20,129,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1523
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1524 : PairBound 9 := { available := 360, camps := [{ cop := 1, region := 488, targets := 16 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,4)], upper := (rows 113 22 133 138 376 360 360 488 360), lower := (rows 113 22 133 138 16 32 64 128 256), losses := [] }

theorem u1524 : Upper (D 2) (R 2) [112,20,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1524
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1525 : Route 9 := (fun mask => (mask,id))

def c1525 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u1525 : Upper (D 2) (R 2) [112,20,129,160] 13 := by
  apply FastRouting.sound _ _ [112,20,129,160] 13 (by decide) (choices 1) [2,8,64,256] r1525 c1525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1050
  · exact u1051
  · exact u1052
  · exact u1053

def r1526 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0)

theorem u1526 : Upper (D 2) (R 2) [112,20,129,258] 13 := by
  apply FastRouting.sound _ _ [112,20,129,258] 13 (by decide) (choices 1) [8,32,128,256] r1526 c1526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1054
  · exact u1055
  · exact u1056
  · exact u1057

def r1527 : Route 9 := (fun mask => (mask,id))

def c1527 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | _ => 0)

theorem u1527 : Upper (D 2) (R 2) [112,20,129,288] 13 := by
  apply FastRouting.sound _ _ [112,20,129,288] 13 (by decide) (choices 1) [2,8,64,128,256] r1527 c1527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1058
  · exact u1059
  · exact u1060
  · exact u1061
  · exact u1062

def r1528 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | _ => 0)

theorem u1528 : Upper (D 2) (R 2) [112,20,129,384] 13 := by
  apply FastRouting.sound _ _ [112,20,129,384] 13 (by decide) (choices 1) [2,8,32,256] r1528 c1528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1063
  · exact u1064
  · exact u1065
  · exact u1066

def b1529 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 113 22 134 104 409 425 457 393 393), lower := (rows 113 22 134 104 16 32 64 128 256), losses := [] }

theorem u1529 : Upper (D 2) (R 2) [112,20,130,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1529
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1530 : PairBound 9 := { available := 360, camps := [{ cop := 0, region := 392, targets := 16 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(3,4)], upper := (rows 113 22 134 137 376 360 360 488 360), lower := (rows 113 22 134 137 16 32 64 128 256), losses := [] }

theorem u1530 : Upper (D 2) (R 2) [112,20,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1530
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1531 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 392, targets := 16 },{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7),(3,4)], upper := (rows 113 22 134 168 345 361 329 457 329), lower := (rows 113 22 134 168 16 32 64 128 256), losses := [] }

theorem u1531 : Upper (D 2) (R 2) [112,20,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1531
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1532 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | _ => 0)

theorem u1532 : Upper (D 2) (R 2) [112,20,130,257] 13 := by
  apply FastRouting.sound _ _ [112,20,130,257] 13 (by decide) (choices 1) [8,32,128,256] r1532 c1532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1067
  · exact u1068
  · exact u1069
  · exact u1070

def r1533 : Route 9 := (fun mask => (mask,id))

def c1533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0)

theorem u1533 : Upper (D 2) (R 2) [112,20,130,288] 13 := by
  apply FastRouting.sound _ _ [112,20,130,288] 13 (by decide) (choices 1) [1,8,64,128,256] r1533 c1533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1071
  · exact u1072
  · exact u1073
  · exact u1074
  · exact u1075

def b1534 : PairBound 9 := { available := 361, camps := [{ cop := 0, region := 392, targets := 16 },{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7),(3,4)], upper := (rows 113 22 134 392 377 361 361 489 361), lower := (rows 113 22 134 392 16 32 64 128 256), losses := [] }

theorem u1534 : Upper (D 2) (R 2) [112,20,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1534
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1535 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 8, targets := 144 }], pairs := [(3,4),(3,7)], upper := (rows 113 22 140 104 403 419 451 387 387), lower := (rows 113 22 140 104 16 32 64 128 256), losses := [] }

theorem u1535 : Upper (D 2) (R 2) [112,20,136,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1535
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1536 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 113 22 140 137 370 354 354 482 354), lower := (rows 113 22 140 137 16 32 64 128 256), losses := [] }

theorem u1536 : Upper (D 2) (R 2) [112,20,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1536
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1537 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 113 22 140 138 369 353 353 481 353), lower := (rows 113 22 140 138 16 32 64 128 256), losses := [] }

theorem u1537 : Upper (D 2) (R 2) [112,20,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1537
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1538 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 113 22 140 168 339 355 323 451 323), lower := (rows 113 22 140 168 16 32 64 128 256), losses := [] }

theorem u1538 : Upper (D 2) (R 2) [112,20,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1538
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1539 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1539 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | _ => 0)

theorem u1539 : Upper (D 2) (R 2) [112,20,136,257] 13 := by
  apply FastRouting.sound _ _ [112,20,136,257] 13 (by decide) (choices 1) [2,32,128,256] r1539 c1539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1076
  · exact u1077
  · exact u1078
  · exact u1079

def r1540 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1540 : Upper (D 2) (R 2) [112,20,136,258] 13 := by
  apply FastRouting.sound _ _ [112,20,136,258] 13 (by decide) (choices 1) [1,32,128,256] r1540 c1540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1080
  · exact u1081
  · exact u1082
  · exact u1083

def r1541 : Route 9 := (fun mask => (mask,id))

def c1541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u1541 : Upper (D 2) (R 2) [112,20,136,288] 13 := by
  apply FastRouting.sound _ _ [112,20,136,288] 13 (by decide) (choices 1) [1,2,64,128,256] r1541 c1541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1084
  · exact u1085
  · exact u1086
  · exact u1087
  · exact u1088

def b1542 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 4, targets := 48 }], pairs := [(2,4),(2,5)], upper := (rows 113 22 140 392 371 355 355 483 355), lower := (rows 113 22 140 392 16 32 64 128 256), losses := [] }

theorem u1542 : Upper (D 2) (R 2) [112,20,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1542
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1543 : Route 9 := (fun mask => (mask,id))

def c1543 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u1543 : Upper (D 2) (R 2) [112,20,160,129] 13 := by
  apply FastRouting.sound _ _ [112,20,160,129] 13 (by decide) (choices 1) [2,8,64,256] r1543 c1543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1089
  · exact u1090
  · exact u1091
  · exact u1092

def r1544 : Route 9 := (fun mask => (mask,id))

def c1544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u1544 : Upper (D 2) (R 2) [112,20,160,130] 13 := by
  apply FastRouting.sound _ _ [112,20,160,130] 13 (by decide) (choices 1) [1,8,64,256] r1544 c1544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1093
  · exact u1094
  · exact u1095
  · exact u1096

def r1545 : Route 9 := (fun mask => (mask,id))

def c1545 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1545 : Upper (D 2) (R 2) [112,20,160,192] 13 := by
  apply FastRouting.sound _ _ [112,20,160,192] 13 (by decide) (choices 1) [1,2,8,256] r1545 c1545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1097
  · exact u1098
  · exact u1099
  · exact u1100

def r1546 : Route 9 := (fun mask => (mask,id))

def c1546 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | _ => 0)

theorem u1546 : Upper (D 2) (R 2) [112,20,160,257] 13 := by
  apply FastRouting.sound _ _ [112,20,160,257] 13 (by decide) (choices 1) [2,8,64,128,256] r1546 c1546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1101
  · exact u1102
  · exact u1103
  · exact u1104
  · exact u1105

def r1547 : Route 9 := (fun mask => (mask,id))

def c1547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | _ => 0)

theorem u1547 : Upper (D 2) (R 2) [112,20,160,258] 13 := by
  apply FastRouting.sound _ _ [112,20,160,258] 13 (by decide) (choices 1) [1,8,64,128,256] r1547 c1547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1106
  · exact u1107
  · exact u1108
  · exact u1109
  · exact u1110

def r1548 : Route 9 := (fun mask => (mask,id))

def c1548 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | _ => 0)

theorem u1548 : Upper (D 2) (R 2) [112,20,160,320] 13 := by
  apply FastRouting.sound _ _ [112,20,160,320] 13 (by decide) (choices 1) [1,2,8,128,256] r1548 c1548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1111
  · exact u1112
  · exact u1113
  · exact u1114
  · exact u1115

def r1549 : Route 9 := (fun mask => (mask,id))

def c1549 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u1549 : Upper (D 2) (R 2) [112,20,160,384] 13 := by
  apply FastRouting.sound _ _ [112,20,160,384] 13 (by decide) (choices 1) [1,2,8,64,256] r1549 c1549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1116
  · exact u1117
  · exact u1118
  · exact u1119
  · exact u1120

def b1550 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 8, targets := 144 }], pairs := [(3,4),(3,7)], upper := (rows 113 22 388 104 411 427 459 395 395), lower := (rows 113 22 388 104 16 32 64 128 256), losses := [] }

theorem u1550 : Upper (D 2) (R 2) [112,20,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1550
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1551 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1551 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | _ => 0)

theorem u1551 : Upper (D 2) (R 2) [112,20,384,129] 13 := by
  apply FastRouting.sound _ _ [112,20,384,129] 13 (by decide) (choices 1) [2,8,32,256] r1551 c1551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1121
  · exact u1122
  · exact u1123
  · exact u1124

def r1552 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c1552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u1552 : Upper (D 2) (R 2) [112,20,384,130] 13 := by
  apply FastRouting.sound _ _ [112,20,384,130] 13 (by decide) (choices 1) [1,8,32,256] r1552 c1552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1125
  · exact u1126
  · exact u1127
  · exact u1128

def r1553 : Route 9 := (fun mask => (mask,id))

def c1553 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | _ => 0)

theorem u1553 : Upper (D 2) (R 2) [112,20,384,160] 13 := by
  apply FastRouting.sound _ _ [112,20,384,160] 13 (by decide) (choices 1) [1,2,8,64,256] r1553 c1553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1129
  · exact u1130
  · exact u1131
  · exact u1132
  · exact u1133

def b1554 : PairBound 9 := { available := 107, camps := [{ cop := 2, region := 8, targets := 48 }], pairs := [(3,4),(3,5)], upper := (rows 113 22 388 392 123 107 107 235 363), lower := (rows 113 22 388 392 16 32 64 128 256), losses := [] }

theorem u1554 : Upper (D 2) (R 2) [112,20,384,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1554
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1555 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 133 138 348 364 332 460 332), lower := (rows 113 50 133 138 16 32 64 128 256), losses := [] }

theorem u1555 : Upper (D 2) (R 2) [112,48,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1555
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1556 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 133 200 286 302 334 398 270), lower := (rows 113 50 133 200 16 32 64 128 256), losses := [] }

theorem u1556 : Upper (D 2) (R 2) [112,48,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1556
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1557 : PairBound 9 := { available := 460, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 133 266 476 492 460 460 460), lower := (rows 113 50 133 266 16 32 64 128 256), losses := [] }

theorem u1557 : Upper (D 2) (R 2) [112,48,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1557
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1558 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 133 268 474 490 458 458 458), lower := (rows 113 50 133 268 16 32 64 128 256), losses := [] }

theorem u1558 : Upper (D 2) (R 2) [112,48,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1558
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1559 : PairBound 9 := { available := 398, camps := [{ cop := 0, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 113 50 133 328 414 430 462 398 398), lower := (rows 113 50 133 328 16 32 64 128 256), losses := [] }

theorem u1559 : Upper (D 2) (R 2) [112,48,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1559
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u1559
end Delivery.IrregularNine14.P02

import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0001

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r420 : Route 9 := (fun mask => (mask,id))

def c420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u420 : Upper (D 2) (R 2) [112,12,144,288,256,128] 13 := by
  apply FastRouting.sound _ _ [112,12,144,288,256,128] 13 (by decide) (choices 1) [1,2] r420 c420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u69
  · exact u70

def b421 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 396, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 44 137 272 34 448 448 448), lower := (rows 113 22 44 137 272 34 64 128 256), losses := [] }

theorem u421 : Upper (D 2) (R 2) [112,20,40,129,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b421
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b422 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 44 137 272 96 450 386 386), lower := (rows 113 22 44 137 272 96 64 128 256), losses := [] }

theorem u422 : Upper (D 2) (R 2) [112,20,40,129,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b422
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b423 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 36, targets := 80 }], pairs := [(2,4),(2,6)], upper := (rows 113 22 44 137 272 160 322 450 322), lower := (rows 113 22 44 137 272 160 64 128 256), losses := [] }

theorem u423 : Upper (D 2) (R 2) [112,20,40,129,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b423
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b424 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 22 44 137 272 288 194 194 450), lower := (rows 113 22 44 137 272 288 64 128 256), losses := [] }

theorem u424 : Upper (D 2) (R 2) [112,20,40,129,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b424
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b425 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 44 138 272 33 448 448 448), lower := (rows 113 22 44 138 272 33 64 128 256), losses := [] }

theorem u425 : Upper (D 2) (R 2) [112,20,40,130,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b425
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b426 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 44 138 272 96 449 385 385), lower := (rows 113 22 44 138 272 96 64 128 256), losses := [] }

theorem u426 : Upper (D 2) (R 2) [112,20,40,130,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b426
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b427 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 36, targets := 80 }], pairs := [(2,4),(2,6)], upper := (rows 113 22 44 138 272 160 321 449 321), lower := (rows 113 22 44 138 272 160 64 128 256), losses := [] }

theorem u427 : Upper (D 2) (R 2) [112,20,40,130,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b427
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b428 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 22 44 138 272 288 193 193 449), lower := (rows 113 22 44 138 272 288 64 128 256), losses := [] }

theorem u428 : Upper (D 2) (R 2) [112,20,40,130,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b428
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b429 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 402, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 44 200 272 33 450 386 386), lower := (rows 113 22 44 200 272 33 64 128 256), losses := [] }

theorem u429 : Upper (D 2) (R 2) [112,20,40,192,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b429
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b430 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 396, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 44 200 272 34 449 385 385), lower := (rows 113 22 44 200 272 34 64 128 256), losses := [] }

theorem u430 : Upper (D 2) (R 2) [112,20,40,192,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b430
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b431 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 36, targets := 80 }], pairs := [(2,4),(2,6)], upper := (rows 113 22 44 200 272 160 323 387 259), lower := (rows 113 22 44 200 272 160 64 128 256), losses := [] }

theorem u431 : Upper (D 2) (R 2) [112,20,40,192,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b431
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b432 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 22 44 200 272 288 195 131 387), lower := (rows 113 22 44 200 272 288 64 128 256), losses := [] }

theorem u432 : Upper (D 2) (R 2) [112,20,40,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b432
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b433 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 396, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 133 168 272 34 328 456 328), lower := (rows 113 22 133 168 272 34 64 128 256), losses := [] }

theorem u433 : Upper (D 2) (R 2) [112,20,129,160,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b433
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b434 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 40, targets := 16 }], pairs := [(3,4)], upper := (rows 113 22 133 168 272 40 322 450 322), lower := (rows 113 22 133 168 272 40 64 128 256), losses := [] }

theorem u434 : Upper (D 2) (R 2) [112,20,129,160,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b434
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b435 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 133 168 272 96 330 394 266), lower := (rows 113 22 133 168 272 96 64 128 256), losses := [] }

theorem u435 : Upper (D 2) (R 2) [112,20,129,160,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b435
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b436 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 22 133 168 272 288 74 202 330), lower := (rows 113 22 133 168 272 288 64 128 256), losses := [] }

theorem u436 : Upper (D 2) (R 2) [112,20,129,160,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b436
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b437 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8)], upper := (rows 113 22 133 266 272 40 224 224 480), lower := (rows 113 22 133 266 272 40 64 128 256), losses := [] }

theorem u437 : Upper (D 2) (R 2) [112,20,129,258,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b437
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b438 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 133 266 272 96 232 168 424), lower := (rows 113 22 133 266 272 96 64 128 256), losses := [] }

theorem u438 : Upper (D 2) (R 2) [112,20,129,258,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b438
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m439_8 : Upper (D 2) (R 2) [112,20,129,258,256,128,8] 13 :=
  permutation_upper _ _ _ [112,20,129,258,256,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u71

theorem m439_32 : Upper (D 2) (R 2) [112,20,129,258,256,128,32] 13 :=
  permutation_upper _ _ _ [112,20,129,258,256,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u72

def r439 : Route 9 := (fun mask => (mask,id))

def c439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u439 : Upper (D 2) (R 2) [112,20,129,258,256,128] 13 := by
  apply FastRouting.sound _ _ [112,20,129,258,256,128] 13 (by decide) (choices 1) [8,32] r439 c439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m439_8
  · exact m439_32

def b440 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 396, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 133 296 272 34 200 200 456), lower := (rows 113 22 133 296 272 34 64 128 256), losses := [] }

theorem u440 : Upper (D 2) (R 2) [112,20,129,288,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b440
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b441 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 134, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 133 296 272 40 194 194 450), lower := (rows 113 22 133 296 272 40 64 128 256), losses := [] }

theorem u441 : Upper (D 2) (R 2) [112,20,129,288,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b441
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b442 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 133 296 272 96 202 138 394), lower := (rows 113 22 133 296 272 96 64 128 256), losses := [] }

theorem u442 : Upper (D 2) (R 2) [112,20,129,288,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b442
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r443 : Route 9 := (fun mask => (mask,id))

def c443 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u443 : Upper (D 2) (R 2) [112,20,129,288,256,128] 13 := by
  apply FastRouting.sound _ _ [112,20,129,288,256,128] 13 (by decide) (choices 1) [2,8] r443 c443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u73
  · exact u74

def b444 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 396, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 133 392 272 34 104 232 360), lower := (rows 113 22 133 392 272 34 64 128 256), losses := [] }

theorem u444 : Upper (D 2) (R 2) [112,20,129,384,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b444
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b445 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8)], upper := (rows 113 22 133 392 272 40 98 226 354), lower := (rows 113 22 133 392 272 40 64 128 256), losses := [] }

theorem u445 : Upper (D 2) (R 2) [112,20,129,384,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b445
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b446 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 133 392 272 96 106 170 298), lower := (rows 113 22 133 392 272 96 64 128 256), losses := [] }

theorem u446 : Upper (D 2) (R 2) [112,20,129,384,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b446
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b447 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8)], upper := (rows 113 22 134 265 272 40 224 224 480), lower := (rows 113 22 134 265 272 40 64 128 256), losses := [] }

theorem u447 : Upper (D 2) (R 2) [112,20,130,257,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b447
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b448 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 134 265 272 96 232 168 424), lower := (rows 113 22 134 265 272 96 64 128 256), losses := [] }

theorem u448 : Upper (D 2) (R 2) [112,20,130,257,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b448
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b449 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 345, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 113 22 134 265 272 160 104 232 360), lower := (rows 113 22 134 265 272 160 64 128 256), losses := [] }

theorem u449 : Upper (D 2) (R 2) [112,20,130,257,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b449
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b450 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 296 272 33 200 200 456), lower := (rows 113 22 134 296 272 33 64 128 256), losses := [] }

theorem u450 : Upper (D 2) (R 2) [112,20,130,288,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b450
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b451 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 134, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 134 296 272 40 193 193 449), lower := (rows 113 22 134 296 272 40 64 128 256), losses := [] }

theorem u451 : Upper (D 2) (R 2) [112,20,130,288,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b451
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b452 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 134 296 272 96 201 137 393), lower := (rows 113 22 134 296 272 96 64 128 256), losses := [] }

theorem u452 : Upper (D 2) (R 2) [112,20,130,288,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b452
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b453 : PairBound 9 := { available := 73, camps := [{ cop := 5, region := 345, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 113 22 134 296 272 160 73 201 329), lower := (rows 113 22 134 296 272 160 64 128 256), losses := [] }

theorem u453 : Upper (D 2) (R 2) [112,20,130,288,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b453
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b454 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 396, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 137 272 34 328 456 328), lower := (rows 113 22 164 137 272 34 64 128 256), losses := [] }

theorem u454 : Upper (D 2) (R 2) [112,20,160,129,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b454
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b455 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 137 272 40 322 450 322), lower := (rows 113 22 164 137 272 40 64 128 256), losses := [] }

theorem u455 : Upper (D 2) (R 2) [112,20,160,129,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b455
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b456 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 164 137 272 96 330 394 266), lower := (rows 113 22 164 137 272 96 64 128 256), losses := [] }

theorem u456 : Upper (D 2) (R 2) [112,20,160,129,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b456
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b457 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 22 164 137 272 288 74 202 330), lower := (rows 113 22 164 137 272 288 64 128 256), losses := [] }

theorem u457 : Upper (D 2) (R 2) [112,20,160,129,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b457
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b458 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 346, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 138 272 33 328 456 328), lower := (rows 113 22 164 138 272 33 64 128 256), losses := [] }

theorem u458 : Upper (D 2) (R 2) [112,20,160,130,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b458
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b459 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 138 272 40 321 449 321), lower := (rows 113 22 164 138 272 40 64 128 256), losses := [] }

theorem u459 : Upper (D 2) (R 2) [112,20,160,130,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b459
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b460 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 164 138 272 96 329 393 265), lower := (rows 113 22 164 138 272 96 64 128 256), losses := [] }

theorem u460 : Upper (D 2) (R 2) [112,20,160,130,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b460
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b461 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 22 164 138 272 288 73 201 329), lower := (rows 113 22 164 138 272 288 64 128 256), losses := [] }

theorem u461 : Upper (D 2) (R 2) [112,20,160,130,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b461
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b462 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 346, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 200 272 33 330 394 266), lower := (rows 113 22 164 200 272 33 64 128 256), losses := [] }

theorem u462 : Upper (D 2) (R 2) [112,20,160,192,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b462
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b463 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 396, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 200 272 34 329 393 265), lower := (rows 113 22 164 200 272 34 64 128 256), losses := [] }

theorem u463 : Upper (D 2) (R 2) [112,20,160,192,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b463
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b464 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 200 272 40 323 387 259), lower := (rows 113 22 164 200 272 40 64 128 256), losses := [] }

theorem u464 : Upper (D 2) (R 2) [112,20,160,192,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b464
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b465 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 142, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 113 22 164 200 272 288 75 139 267), lower := (rows 113 22 164 200 272 288 64 128 256), losses := [] }

theorem u465 : Upper (D 2) (R 2) [112,20,160,192,256,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b465
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b466 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 396, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 265 272 34 200 200 456), lower := (rows 113 22 164 265 272 34 64 128 256), losses := [] }

theorem u466 : Upper (D 2) (R 2) [112,20,160,257,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b466
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b467 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8)], upper := (rows 113 22 164 265 272 40 194 194 450), lower := (rows 113 22 164 265 272 40 64 128 256), losses := [] }

theorem u467 : Upper (D 2) (R 2) [112,20,160,257,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b467
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b468 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 164 265 272 96 202 138 394), lower := (rows 113 22 164 265 272 96 64 128 256), losses := [] }

theorem u468 : Upper (D 2) (R 2) [112,20,160,257,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b468
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b469 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 113 22 164 265 272 160 74 202 330), lower := (rows 113 22 164 265 272 160 64 128 256), losses := [] }

theorem u469 : Upper (D 2) (R 2) [112,20,160,257,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b469
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b470 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 346, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 266 272 33 200 200 456), lower := (rows 113 22 164 266 272 33 64 128 256), losses := [] }

theorem u470 : Upper (D 2) (R 2) [112,20,160,258,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b470
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b471 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 134, targets := 256 }], pairs := [(1,8)], upper := (rows 113 22 164 266 272 40 193 193 449), lower := (rows 113 22 164 266 272 40 64 128 256), losses := [] }

theorem u471 : Upper (D 2) (R 2) [112,20,160,258,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b471
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b472 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 164 266 272 96 201 137 393), lower := (rows 113 22 164 266 272 96 64 128 256), losses := [] }

theorem u472 : Upper (D 2) (R 2) [112,20,160,258,256,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b472
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b473 : PairBound 9 := { available := 73, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 113 22 164 266 272 160 73 201 329), lower := (rows 113 22 164 266 272 160 64 128 256), losses := [] }

theorem u473 : Upper (D 2) (R 2) [112,20,160,258,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b473
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b474 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 346, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 328 272 33 202 138 394), lower := (rows 113 22 164 328 272 33 64 128 256), losses := [] }

theorem u474 : Upper (D 2) (R 2) [112,20,160,320,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b474
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b475 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 396, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 328 272 34 201 137 393), lower := (rows 113 22 164 328 272 34 64 128 256), losses := [] }

theorem u475 : Upper (D 2) (R 2) [112,20,160,320,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b475
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b476 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 328 272 40 195 131 387), lower := (rows 113 22 164 328 272 40 64 128 256), losses := [] }

theorem u476 : Upper (D 2) (R 2) [112,20,160,320,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b476
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b477 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 113 22 164 328 272 160 75 139 267), lower := (rows 113 22 164 328 272 160 64 128 256), losses := [] }

theorem u477 : Upper (D 2) (R 2) [112,20,160,320,256,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b477
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b478 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 346, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 392 272 33 74 202 330), lower := (rows 113 22 164 392 272 33 64 128 256), losses := [] }

theorem u478 : Upper (D 2) (R 2) [112,20,160,384,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b478
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b479 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 396, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 392 272 34 73 201 329), lower := (rows 113 22 164 392 272 34 64 128 256), losses := [] }

theorem u479 : Upper (D 2) (R 2) [112,20,160,384,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b479
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u479
end Delivery.IrregularNine14.P02

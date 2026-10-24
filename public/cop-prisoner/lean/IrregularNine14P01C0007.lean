import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0000

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b420 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 23 98 261 168 144 48 74 202 330), lower := (rows 23 98 261 168 144 48 64 128 256), losses := [] }

theorem u420 : Upper (D 1) (R 1) [22,96,257,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b420
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b421 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 23 98 261 168 144 96 90 154 282), lower := (rows 23 98 261 168 144 96 64 128 256), losses := [] }

theorem u421 : Upper (D 1) (R 1) [22,96,257,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b421
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b422 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 23 259 100 56 144 34 200 200 456), lower := (rows 23 259 100 56 144 34 64 128 256), losses := [] }

theorem u422 : Upper (D 1) (R 1) [22,257,96,48,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b422
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b423 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 23 259 100 56 144 40 194 194 450), lower := (rows 23 259 100 56 144 40 64 128 256), losses := [] }

theorem u423 : Upper (D 1) (R 1) [22,257,96,48,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b423
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b424 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 23 259 100 56 144 96 202 138 394), lower := (rows 23 259 100 56 144 96 64 128 256), losses := [] }

theorem u424 : Upper (D 1) (R 1) [22,257,96,48,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b424
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b425 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 23 259 100 56 144 160 74 202 330), lower := (rows 23 259 100 56 144 160 64 128 256), losses := [] }

theorem u425 : Upper (D 1) (R 1) [22,257,96,48,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b425
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b426 : PairBound 9 := { available := 88, camps := [{ cop := 5, region := 220, targets := 2 }], pairs := [(2,1)], upper := (rows 23 259 100 168 144 34 88 216 344), lower := (rows 23 259 100 168 144 34 64 128 256), losses := [] }

theorem u426 : Upper (D 1) (R 1) [22,257,96,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b426
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b427 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 23 259 100 168 144 40 82 210 338), lower := (rows 23 259 100 168 144 40 64 128 256), losses := [] }

theorem u427 : Upper (D 1) (R 1) [22,257,96,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b427
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b428 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 23 259 100 168 144 48 74 202 330), lower := (rows 23 259 100 168 144 48 64 128 256), losses := [] }

theorem u428 : Upper (D 1) (R 1) [22,257,96,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b428
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b429 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 23 259 100 168 144 96 90 154 282), lower := (rows 23 259 100 168 144 96 64 128 256), losses := [] }

theorem u429 : Upper (D 1) (R 1) [22,257,96,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b429
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b430 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 13 74 144 48 224 224 480), lower := (rows 23 290 13 74 144 48 64 128 256), losses := [] }

theorem u430 : Upper (D 1) (R 1) [22,288,9,66,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b430
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b431 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 402, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 13 74 144 96 240 176 432), lower := (rows 23 290 13 74 144 96 64 128 256), losses := [] }

theorem u431 : Upper (D 1) (R 1) [22,288,9,66,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b431
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r432 : Route 9 := (fun mask => (mask,id))

def c432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u432 : Upper (D 1) (R 1) [22,288,9,66,128,128] 13 := by
  apply FastRouting.sound _ _ [22,288,9,66,128,128] 13 (by decide) (choices 1) [16,32] r432 c432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12
  · exact u13

def b433 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 13 104 144 34 208 208 464), lower := (rows 23 290 13 104 144 34 64 128 256), losses := [] }

theorem u433 : Upper (D 1) (R 1) [22,288,9,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b433
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b434 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 13 104 144 48 194 194 450), lower := (rows 23 290 13 104 144 48 64 128 256), losses := [] }

theorem u434 : Upper (D 1) (R 1) [22,288,9,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b434
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b435 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 23 290 13 104 144 96 210 146 402), lower := (rows 23 290 13 104 144 96 64 128 256), losses := [] }

theorem u435 : Upper (D 1) (R 1) [22,288,9,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b435
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r436 : Route 9 := (fun mask => (mask,id))

def c436 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u436 : Upper (D 1) (R 1) [22,288,9,96,128,128] 13 := by
  apply FastRouting.sound _ _ [22,288,9,96,128,128] 13 (by decide) (choices 1) [2,16] r436 c436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14
  · exact u15

def b437 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 23 290 69 138 144 40 112 240 368), lower := (rows 23 290 69 138 144 40 64 128 256), losses := [] }

theorem u437 : Upper (D 1) (R 1) [22,288,65,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b437
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b438 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 69 138 144 48 104 232 360), lower := (rows 23 290 69 138 144 48 64 128 256), losses := [] }

theorem u438 : Upper (D 1) (R 1) [22,288,65,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b438
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b439 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 69 138 144 96 120 184 312), lower := (rows 23 290 69 138 144 96 64 128 256), losses := [] }

theorem u439 : Upper (D 1) (R 1) [22,288,65,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b439
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b440 : PairBound 9 := { available := 88, camps := [{ cop := 8, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 23 290 69 168 144 34 88 216 344), lower := (rows 23 290 69 168 144 34 64 128 256), losses := [] }

theorem u440 : Upper (D 1) (R 1) [22,288,65,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b440
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b441 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 23 290 69 168 144 40 82 210 338), lower := (rows 23 290 69 168 144 40 64 128 256), losses := [] }

theorem u441 : Upper (D 1) (R 1) [22,288,65,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b441
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b442 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 23 290 69 168 144 48 74 202 330), lower := (rows 23 290 69 168 144 48 64 128 256), losses := [] }

theorem u442 : Upper (D 1) (R 1) [22,288,65,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b442
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b443 : PairBound 9 := { available := 26, camps := [{ cop := 5, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 23 290 69 168 144 96 90 154 282), lower := (rows 23 290 69 168 144 96 64 128 256), losses := [] }

theorem u443 : Upper (D 1) (R 1) [22,288,65,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b443
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b444 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 29 35 70 266 144 48 224 224 480), lower := (rows 29 35 70 266 144 48 64 128 256), losses := [] }

theorem u444 : Upper (D 1) (R 1) [28,33,66,258,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b444
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b445 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 29 35 70 266 144 96 240 176 432), lower := (rows 29 35 70 266 144 96 64 128 256), losses := [] }

theorem u445 : Upper (D 1) (R 1) [28,33,66,258,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b445
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b446 : PairBound 9 := { available := 112, camps := [], pairs := [(1,4)], upper := (rows 29 35 70 266 144 160 112 240 368), lower := (rows 29 35 70 266 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 8 0 176 64 128 256), good := (rows 47 35 70 266 160 160 64 160 256) }] }

theorem u446 : Upper (D 1) (R 1) [28,33,66,258,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b446
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b447 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 29 35 70 392 48 34 208 208 464), lower := (rows 29 35 70 392 48 34 64 128 256), losses := [] }

theorem u447 : Upper (D 1) (R 1) [28,33,66,384,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b447
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b448 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 196, targets := 16 }], pairs := [(2,4)], upper := (rows 29 35 70 392 48 48 194 194 450), lower := (rows 29 35 70 392 48 48 64 128 256), losses := [] }

theorem u448 : Upper (D 1) (R 1) [28,33,66,384,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b448
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b449 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 29 35 70 392 48 96 210 146 402), lower := (rows 29 35 70 392 48 96 64 128 256), losses := [] }

theorem u449 : Upper (D 1) (R 1) [28,33,66,384,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b449
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b450 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 84, targets := 128 }], pairs := [(2,7)], upper := (rows 29 35 70 392 48 160 82 210 338), lower := (rows 29 35 70 392 48 160 64 128 256), losses := [] }

theorem u450 : Upper (D 1) (R 1) [28,33,66,384,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b450
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b451 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1)], upper := (rows 29 35 196 266 48 34 208 208 464), lower := (rows 29 35 196 266 48 34 64 128 256), losses := [] }

theorem u451 : Upper (D 1) (R 1) [28,33,192,258,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b451
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b452 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 196, targets := 16 }], pairs := [(2,4)], upper := (rows 29 35 196 266 48 48 194 194 450), lower := (rows 29 35 196 266 48 48 64 128 256), losses := [] }

theorem u452 : Upper (D 1) (R 1) [28,33,192,258,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b452
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b453 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 29 35 196 266 48 96 210 146 402), lower := (rows 29 35 196 266 48 96 64 128 256), losses := [] }

theorem u453 : Upper (D 1) (R 1) [28,33,192,258,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b453
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b454 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 29 50 70 266 144 33 224 224 480), lower := (rows 29 50 70 266 144 33 64 128 256), losses := [] }

theorem u454 : Upper (D 1) (R 1) [28,48,66,258,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b454
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b455 : PairBound 9 := { available := 161, camps := [], pairs := [(1,7)], upper := (rows 29 50 70 266 144 96 225 161 417), lower := (rows 29 50 70 266 144 96 64 128 256), losses := [{ target := 7, region := (rows 1 3 4 8 16 100 64 0 256), good := (rows 63 50 102 266 16 96 96 0 256) }] }

theorem u455 : Upper (D 1) (R 1) [28,48,66,258,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b455
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b456 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 29 50 70 266 144 160 97 225 353), lower := (rows 29 50 70 266 144 160 64 128 256), losses := [] }

theorem u456 : Upper (D 1) (R 1) [28,48,66,258,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b456
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b457 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 29 50 70 296 144 33 194 194 450), lower := (rows 29 50 70 296 144 33 64 128 256), losses := [] }

theorem u457 : Upper (D 1) (R 1) [28,48,66,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b457
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b458 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 70 296 144 34 193 193 449), lower := (rows 29 50 70 296 144 34 64 128 256), losses := [] }

theorem u458 : Upper (D 1) (R 1) [28,48,66,288,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b458
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b459 : PairBound 9 := { available := 131, camps := [], pairs := [(1,7)], upper := (rows 29 50 70 296 144 96 195 131 387), lower := (rows 29 50 70 296 144 96 64 128 256), losses := [{ target := 7, region := (rows 1 3 4 8 16 100 64 0 256), good := (rows 63 50 102 296 16 96 96 0 256) }] }

theorem u459 : Upper (D 1) (R 1) [28,48,66,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b459
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b460 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 29 50 70 296 144 160 67 195 323), lower := (rows 29 50 70 296 144 160 64 128 256), losses := [] }

theorem u460 : Upper (D 1) (R 1) [28,48,66,288,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b460
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b461 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 29 50 100 266 144 33 194 194 450), lower := (rows 29 50 100 266 144 33 64 128 256), losses := [] }

theorem u461 : Upper (D 1) (R 1) [28,48,96,258,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b461
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b462 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 29 50 100 266 144 34 193 193 449), lower := (rows 29 50 100 266 144 34 64 128 256), losses := [] }

theorem u462 : Upper (D 1) (R 1) [28,48,96,258,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b462
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b463 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 29 50 100 266 144 96 195 131 387), lower := (rows 29 50 100 266 144 96 64 128 256), losses := [] }

theorem u463 : Upper (D 1) (R 1) [28,48,96,258,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b463
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b464 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 29 50 100 266 144 160 67 195 323), lower := (rows 29 50 100 266 144 160 64 128 256), losses := [] }

theorem u464 : Upper (D 1) (R 1) [28,48,96,258,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b464
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b465 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 29 98 7 168 80 34 464 400 400), lower := (rows 29 98 7 168 80 34 64 128 256), losses := [] }

theorem u465 : Upper (D 1) (R 1) [28,96,3,160,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b465
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b466 : PairBound 9 := { available := 386, camps := [{ cop := 5, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 7 168 80 48 450 386 386), lower := (rows 29 98 7 168 80 48 64 128 256), losses := [] }

theorem u466 : Upper (D 1) (R 1) [28,96,3,160,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b466
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b467 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 29 98 7 168 80 160 338 402 274), lower := (rows 29 98 7 168 80 160 64 128 256), losses := [] }

theorem u467 : Upper (D 1) (R 1) [28,96,3,160,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b467
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b468 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 29 98 7 168 80 288 210 146 402), lower := (rows 29 98 7 168 80 288 64 128 256), losses := [] }

theorem u468 : Upper (D 1) (R 1) [28,96,3,160,64,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b468
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b469 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 7 266 144 48 224 224 480), lower := (rows 29 98 7 266 144 48 64 128 256), losses := [] }

theorem u469 : Upper (D 1) (R 1) [28,96,3,258,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b469
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b470 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 29 98 7 266 144 96 240 176 432), lower := (rows 29 98 7 266 144 96 64 128 256), losses := [] }

theorem u470 : Upper (D 1) (R 1) [28,96,3,258,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b470
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m471_16 : Upper (D 1) (R 1) [28,96,3,258,128,128,16] 13 :=
  permutation_upper _ _ _ [28,96,3,258,128,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u16

theorem m471_32 : Upper (D 1) (R 1) [28,96,3,258,128,128,32] 13 :=
  permutation_upper _ _ _ [28,96,3,258,128,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17

def r471 : Route 9 := (fun mask => (mask,id))

def c471 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u471 : Upper (D 1) (R 1) [28,96,3,258,128,128] 13 := by
  apply FastRouting.sound _ _ [28,96,3,258,128,128] 13 (by decide) (choices 1) [16,32] r471 c471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m471_16
  · exact m471_32

def b472 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 29 98 7 296 80 34 208 144 400), lower := (rows 29 98 7 296 80 34 64 128 256), losses := [] }

theorem u472 : Upper (D 1) (R 1) [28,96,3,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b472
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b473 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 7 296 80 48 194 130 386), lower := (rows 29 98 7 296 80 48 64 128 256), losses := [] }

theorem u473 : Upper (D 1) (R 1) [28,96,3,288,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b473
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r474 : Route 9 := (fun mask => (mask,id))

def c474 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u474 : Upper (D 1) (R 1) [28,96,3,288,64,128] 13 := by
  apply FastRouting.sound _ _ [28,96,3,288,64,128] 13 (by decide) (choices 1) [2,16,128] r474 c474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18
  · exact u19
  · exact u20

def b475 : PairBound 9 := { available := 208, camps := [{ cop := 6, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 7 296 144 34 208 208 464), lower := (rows 29 98 7 296 144 34 64 128 256), losses := [] }

theorem u475 : Upper (D 1) (R 1) [28,96,3,288,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b475
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b476 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 29 98 7 296 144 48 194 194 450), lower := (rows 29 98 7 296 144 48 64 128 256), losses := [] }

theorem u476 : Upper (D 1) (R 1) [28,96,3,288,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b476
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b477 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 29 98 7 296 144 96 210 146 402), lower := (rows 29 98 7 296 144 96 64 128 256), losses := [] }

theorem u477 : Upper (D 1) (R 1) [28,96,3,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b477
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r478 : Route 9 := (fun mask => (mask,id))

def c478 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u478 : Upper (D 1) (R 1) [28,96,3,288,128,128] 13 := by
  apply FastRouting.sound _ _ [28,96,3,288,128,128] 13 (by decide) (choices 1) [2,16] r478 c478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21
  · exact u22

def b479 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 29 98 7 392 48 34 208 208 464), lower := (rows 29 98 7 392 48 34 64 128 256), losses := [] }

theorem u479 : Upper (D 1) (R 1) [28,96,3,384,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b479
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u479
end Delivery.IrregularNine14.P01

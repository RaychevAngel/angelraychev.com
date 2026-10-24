import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P04C0001
import IrregularNine14P04C0002

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b420 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 400, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 44 73 400 55 87 151 279), lower := (rows 7 26 44 73 400 32 64 128 256), losses := [] }

theorem u420 : Upper (D 4) (R 4) [6,24,40,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b420
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b421 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 400, targets := 2 }], pairs := [(4,1)], upper := (rows 7 26 44 74 145 309 341 405 277), lower := (rows 7 26 44 74 145 32 64 128 256), losses := [] }

theorem u421 : Upper (D 4) (R 4) [6,24,40,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b421
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b422 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 2 }], pairs := [(4,1)], upper := (rows 7 26 44 74 148 305 337 401 273), lower := (rows 7 26 44 74 148 32 64 128 256), losses := [] }

theorem u422 : Upper (D 4) (R 4) [6,24,40,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b422
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b423 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 400, targets := 2 }], pairs := [(4,1)], upper := (rows 7 26 44 74 400 53 85 149 277), lower := (rows 7 26 44 74 400 32 64 128 256), losses := [] }

theorem u423 : Upper (D 4) (R 4) [6,24,40,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b423
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b424 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 400, targets := 4 }], pairs := [(4,2)], upper := (rows 7 26 44 76 145 307 339 403 275), lower := (rows 7 26 44 76 145 32 64 128 256), losses := [] }

theorem u424 : Upper (D 4) (R 4) [6,24,40,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b424
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b425 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 400, targets := 4 }], pairs := [(4,2)], upper := (rows 7 26 44 76 146 305 337 401 273), lower := (rows 7 26 44 76 146 32 64 128 256), losses := [] }

theorem u425 : Upper (D 4) (R 4) [6,24,40,68,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b425
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b426 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 400, targets := 4 }], pairs := [(4,2)], upper := (rows 7 26 44 76 400 51 83 147 275), lower := (rows 7 26 44 76 400 32 64 128 256), losses := [] }

theorem u426 : Upper (D 4) (R 4) [6,24,40,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b426
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b427 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 293, targets := 16 }], pairs := [(0,4)], upper := (rows 7 26 44 88 145 295 327 391 263), lower := (rows 7 26 44 88 145 32 64 128 256), losses := [] }

theorem u427 : Upper (D 4) (R 4) [6,24,40,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b427
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b428 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 293, targets := 16 }], pairs := [(0,4)], upper := (rows 7 26 44 88 148 291 323 387 259), lower := (rows 7 26 44 88 148 32 64 128 256), losses := [] }

theorem u428 : Upper (D 4) (R 4) [6,24,40,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b428
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b429 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 37, targets := 16 }], pairs := [(0,4)], upper := (rows 7 26 44 88 400 39 71 135 263), lower := (rows 7 26 44 88 400 32 64 128 256), losses := [] }

theorem u429 : Upper (D 4) (R 4) [6,24,40,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b429
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b430 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 44 200 273 55 87 151 279), lower := (rows 7 26 44 200 273 32 64 128 256), losses := [] }

theorem u430 : Upper (D 4) (R 4) [6,24,40,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b430
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b431 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 44 200 274 53 85 149 277), lower := (rows 7 26 44 200 274 32 64 128 256), losses := [] }

theorem u431 : Upper (D 4) (R 4) [6,24,40,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b431
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b432 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 44 200 276 51 83 147 275), lower := (rows 7 26 44 200 276 32 64 128 256), losses := [] }

theorem u432 : Upper (D 4) (R 4) [6,24,40,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b432
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b433 : PairBound 9 := { available := 30, camps := [{ cop := 1, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 137 273 62 94 158 286), lower := (rows 7 26 100 137 273 32 64 128 256), losses := [] }

theorem u433 : Upper (D 4) (R 4) [6,24,96,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b433
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r434 : Route 9 := (fun mask => (mask,id))

def c434 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u434 : Upper (D 4) (R 4) [6,24,96,129,258] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,258] 13 (by decide) (choices 1) [1,4,8,16] r434 c434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u86
  · exact u87
  · exact u88
  · exact u89

def r435 : Route 9 := (fun mask => (mask,id))

def c435 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u435 : Upper (D 4) (R 4) [6,24,96,129,260] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,260] 13 (by decide) (choices 1) [1,2,8,16] r435 c435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u90
  · exact u91
  · exact u92
  · exact u93

def b436 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 101, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 100 137 280 55 87 151 279), lower := (rows 7 26 100 137 280 32 64 128 256), losses := [] }

theorem u436 : Upper (D 4) (R 4) [6,24,96,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b436
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r437 : Route 9 := (fun mask => (mask,id))

def c437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u437 : Upper (D 4) (R 4) [6,24,96,130,260] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130,260] 13 (by decide) (choices 1) [1,8,16] r437 c437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u94
  · exact u95
  · exact u96

def b438 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 101, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 100 138 280 53 85 149 277), lower := (rows 7 26 100 138 280 32 64 128 256), losses := [] }

theorem u438 : Upper (D 4) (R 4) [6,24,96,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b438
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b439 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 101, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 100 140 280 51 83 147 275), lower := (rows 7 26 100 140 280 32 64 128 256), losses := [] }

theorem u439 : Upper (D 4) (R 4) [6,24,96,132,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b439
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b440 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 101, targets := 8 }], pairs := [(0,3)], upper := (rows 7 26 100 152 280 39 71 135 263), lower := (rows 7 26 100 152 280 32 64 128 256), losses := [] }

theorem u440 : Upper (D 4) (R 4) [6,24,96,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b440
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b441 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 26 148 312 344 408 280), lower := (rows 7 35 69 26 148 32 64 128 256), losses := [] }

theorem u441 : Upper (D 4) (R 4) [6,33,65,18,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b441
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b442 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 26 152 316 348 412 284), lower := (rows 7 35 69 26 152 32 64 128 256), losses := [] }

theorem u442 : Upper (D 4) (R 4) [6,33,65,18,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b442
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b443 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 26 400 60 92 156 284), lower := (rows 7 35 69 26 400 32 64 128 256), losses := [] }

theorem u443 : Upper (D 4) (R 4) [6,33,65,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b443
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b444 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 138 280 60 92 156 284), lower := (rows 7 35 69 138 280 32 64 128 256), losses := [] }

theorem u444 : Upper (D 4) (R 4) [6,33,65,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b444
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b445 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 152 280 62 94 158 286), lower := (rows 7 35 69 152 280 32 64 128 256), losses := [] }

theorem u445 : Upper (D 4) (R 4) [6,33,65,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b445
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b446 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 70 28 145 312 344 408 280), lower := (rows 7 35 70 28 145 32 64 128 256), losses := [] }

theorem u446 : Upper (D 4) (R 4) [6,33,66,20,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b446
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b447 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 70 28 152 313 345 409 281), lower := (rows 7 35 70 28 152 32 64 128 256), losses := [] }

theorem u447 : Upper (D 4) (R 4) [6,33,66,20,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b447
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b448 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 70 28 400 57 89 153 281), lower := (rows 7 35 70 28 400 32 64 128 256), losses := [] }

theorem u448 : Upper (D 4) (R 4) [6,33,66,20,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b448
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b449 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 70 137 280 60 92 156 284), lower := (rows 7 35 70 137 280 32 64 128 256), losses := [] }

theorem u449 : Upper (D 4) (R 4) [6,33,66,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b449
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b450 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 70 140 280 57 89 153 281), lower := (rows 7 35 70 140 280 32 64 128 256), losses := [] }

theorem u450 : Upper (D 4) (R 4) [6,33,66,132,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b450
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b451 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 70 152 280 61 93 157 285), lower := (rows 7 35 70 152 280 32 64 128 256), losses := [] }

theorem u451 : Upper (D 4) (R 4) [6,33,66,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b451
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b452 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 14 145 312 344 408 280), lower := (rows 7 35 76 14 145 32 64 128 256), losses := [] }

theorem u452 : Upper (D 4) (R 4) [6,33,72,6,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b452
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b453 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 14 400 57 89 153 281), lower := (rows 7 35 76 14 400 32 64 128 256), losses := [] }

theorem u453 : Upper (D 4) (R 4) [6,33,72,6,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b453
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b454 : PairBound 9 := { available := 284, camps := [{ cop := 3, region := 324, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 26 145 316 348 412 284), lower := (rows 7 35 76 26 145 32 64 128 256), losses := [] }

theorem u454 : Upper (D 4) (R 4) [6,33,72,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b454
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r455 : Route 9 := (fun mask => (mask,id))

def c455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u455 : Upper (D 4) (R 4) [6,33,72,18,132] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18,132] 13 (by decide) (choices 1) [1,8,16,256] r455 c455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u97
  · exact u98
  · exact u99
  · exact u100

def r456 : Route 9 := (fun mask => (mask,id))

def c456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u456 : Upper (D 4) (R 4) [6,33,72,18,136] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18,136] 13 (by decide) (choices 1) [1,4,16,256] r456 c456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u101
  · exact u102
  · exact u103
  · exact u104

def r457 : Route 9 := (fun mask => (mask,id))

def c457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u457 : Upper (D 4) (R 4) [6,33,72,18,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18,384] 13 (by decide) (choices 1) [1,4,8,16] r457 c457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u105
  · exact u106
  · exact u107
  · exact u108

def r458 : Route 9 := (fun mask => (mask,id))

def c458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u458 : Upper (D 4) (R 4) [6,33,72,20,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20,130] 13 (by decide) (choices 1) [1,8,16,256] r458 c458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u109
  · exact u110
  · exact u111
  · exact u112

def r459 : Route 9 := (fun mask => (mask,id))

def c459 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u459 : Upper (D 4) (R 4) [6,33,72,20,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20,384] 13 (by decide) (choices 1) [1,2,8,16] r459 c459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u113
  · exact u114
  · exact u115
  · exact u116

def b460 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 76 137 22 312 344 408 280), lower := (rows 7 35 76 137 22 32 64 128 256), losses := [] }

theorem u460 : Upper (D 4) (R 4) [6,33,72,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b460
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b461 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 324, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 137 26 308 340 404 276), lower := (rows 7 35 76 137 26 32 64 128 256), losses := [] }

theorem u461 : Upper (D 4) (R 4) [6,33,72,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b461
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b462 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 76 137 28 306 338 402 274), lower := (rows 7 35 76 137 28 32 64 128 256), losses := [] }

theorem u462 : Upper (D 4) (R 4) [6,33,72,129,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b462
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r463 : Route 9 := (fun mask => (mask,id))

def c463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u463 : Upper (D 4) (R 4) [6,33,72,129,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,258] 13 (by decide) (choices 1) [4,8,16] r463 c463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u117
  · exact u118
  · exact u119

def r464 : Route 9 := (fun mask => (mask,id))

def c464 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u464 : Upper (D 4) (R 4) [6,33,72,129,260] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,260] 13 (by decide) (choices 1) [2,8,16] r464 c464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u120
  · exact u121
  · exact u122

def r465 : Route 9 := (fun mask => (mask,id))

def c465 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u465 : Upper (D 4) (R 4) [6,33,72,129,264] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,264] 13 (by decide) (choices 1) [2,4,16] r465 c465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u123
  · exact u124
  · exact u125

def b466 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 76 138 28 305 337 401 273), lower := (rows 7 35 76 138 28 32 64 128 256), losses := [] }

theorem u466 : Upper (D 4) (R 4) [6,33,72,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b466
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r467 : Route 9 := (fun mask => (mask,id))

def c467 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u467 : Upper (D 4) (R 4) [6,33,72,130,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,257] 13 (by decide) (choices 1) [4,8,16] r467 c467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u126
  · exact u127
  · exact u128

def r468 : Route 9 := (fun mask => (mask,id))

def c468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u468 : Upper (D 4) (R 4) [6,33,72,130,260] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,260] 13 (by decide) (choices 1) [1,8,16] r468 c468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u129
  · exact u130
  · exact u131

def r469 : Route 9 := (fun mask => (mask,id))

def c469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u469 : Upper (D 4) (R 4) [6,33,72,130,264] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,264] 13 (by decide) (choices 1) [1,4,16] r469 c469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u132
  · exact u133
  · exact u134

def r470 : Route 9 := (fun mask => (mask,id))

def c470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u470 : Upper (D 4) (R 4) [6,33,72,132,10] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,10] 13 (by decide) (choices 1) [1,16,256] r470 c470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u135
  · exact u136
  · exact u137

def r471 : Route 9 := (fun mask => (mask,id))

def c471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u471 : Upper (D 4) (R 4) [6,33,72,132,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,257] 13 (by decide) (choices 1) [2,8,16] r471 c471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u138
  · exact u139
  · exact u140

def r472 : Route 9 := (fun mask => (mask,id))

def c472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u472 : Upper (D 4) (R 4) [6,33,72,132,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,258] 13 (by decide) (choices 1) [1,8,16] r472 c472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u141
  · exact u142
  · exact u143

def r473 : Route 9 := (fun mask => (mask,id))

def c473 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u473 : Upper (D 4) (R 4) [6,33,72,132,264] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132,264] 13 (by decide) (choices 1) [1,2,16] r473 c473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u144
  · exact u145
  · exact u146

def b474 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 76 152 22 313 345 409 281), lower := (rows 7 35 76 152 22 32 64 128 256), losses := [] }

theorem u474 : Upper (D 4) (R 4) [6,33,72,144,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b474
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r475 : Route 9 := (fun mask => (mask,id))

def c475 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u475 : Upper (D 4) (R 4) [6,33,72,144,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,257] 13 (by decide) (choices 1) [2,4,8,16] r475 c475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u147
  · exact u148
  · exact u149
  · exact u150

def r476 : Route 9 := (fun mask => (mask,id))

def c476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u476 : Upper (D 4) (R 4) [6,33,72,144,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,258] 13 (by decide) (choices 1) [1,4,8,16] r476 c476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u151
  · exact u152
  · exact u153
  · exact u154

def r477 : Route 9 := (fun mask => (mask,id))

def c477 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u477 : Upper (D 4) (R 4) [6,33,72,144,260] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,260] 13 (by decide) (choices 1) [1,2,8,16] r477 c477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u155
  · exact u156
  · exact u157
  · exact u158

def r478 : Route 9 := (fun mask => (mask,id))

def c478 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u478 : Upper (D 4) (R 4) [6,33,72,144,264] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,264] 13 (by decide) (choices 1) [1,2,4,16] r478 c478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u159
  · exact u160
  · exact u161
  · exact u162

def b479 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 76 392 22 57 89 153 281), lower := (rows 7 35 76 392 22 32 64 128 256), losses := [] }

theorem u479 : Upper (D 4) (R 4) [6,33,72,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b479
    (constants 4).1 (constants 4).2 (by decide +kernel)

#print axioms u479
end Delivery.IrregularNine14.P04

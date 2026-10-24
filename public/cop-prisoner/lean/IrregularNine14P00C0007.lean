import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0000

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b420 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 84 265 17 160 108 172 300), lower := (rows 51 194 84 265 17 160 64 128 256), losses := [] }

theorem u420 : Upper (D 0) (R 0) [50,192,80,257,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b420
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b421 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 194 84 268 17 33 232 168 424), lower := (rows 51 194 84 268 17 33 64 128 256), losses := [] }

theorem u421 : Upper (D 0) (R 0) [50,192,80,260,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b421
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b422 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 194 84 268 17 40 225 161 417), lower := (rows 51 194 84 268 17 40 64 128 256), losses := [] }

theorem u422 : Upper (D 0) (R 0) [50,192,80,260,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b422
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b423 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 84 268 17 160 105 169 297), lower := (rows 51 194 84 268 17 160 64 128 256), losses := [] }

theorem u423 : Upper (D 0) (R 0) [50,192,80,260,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b423
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b424 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 194 84 296 17 33 204 140 396), lower := (rows 51 194 84 296 17 33 64 128 256), losses := [] }

theorem u424 : Upper (D 0) (R 0) [50,192,80,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b424
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b425 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 51 194 84 296 17 36 201 137 393), lower := (rows 51 194 84 296 17 36 64 128 256), losses := [] }

theorem u425 : Upper (D 0) (R 0) [50,192,80,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b425
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b426 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 194 84 296 17 40 197 133 389), lower := (rows 51 194 84 296 17 40 64 128 256), losses := [] }

theorem u426 : Upper (D 0) (R 0) [50,192,80,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b426
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b427 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 84 296 17 160 77 141 269), lower := (rows 51 194 84 296 17 160 64 128 256), losses := [] }

theorem u427 : Upper (D 0) (R 0) [50,192,80,288,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b427
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b428 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 194 84 392 17 33 108 172 300), lower := (rows 51 194 84 392 17 33 64 128 256), losses := [] }

theorem u428 : Upper (D 0) (R 0) [50,192,80,384,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b428
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b429 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 51 194 84 392 17 36 105 169 297), lower := (rows 51 194 84 392 17 36 64 128 256), losses := [] }

theorem u429 : Upper (D 0) (R 0) [50,192,80,384,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b429
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b430 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 51 194 84 392 17 40 101 165 293), lower := (rows 51 194 84 392 17 40 64 128 256), losses := [] }

theorem u430 : Upper (D 0) (R 0) [50,192,80,384,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b430
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b431 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 28 104 144 33 196 196 452), lower := (rows 51 259 28 104 144 33 64 128 256), losses := [] }

theorem u431 : Upper (D 0) (R 0) [50,257,24,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b431
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b432 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 51 259 28 104 144 36 193 193 449), lower := (rows 51 259 28 104 144 36 64 128 256), losses := [] }

theorem u432 : Upper (D 0) (R 0) [50,257,24,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b432
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b433 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 51 259 28 104 144 96 197 133 389), lower := (rows 51 259 28 104 144 96 64 128 256), losses := [] }

theorem u433 : Upper (D 0) (R 0) [50,257,24,96,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b433
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b434 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 259 28 104 144 160 69 197 325), lower := (rows 51 259 28 104 144 160 64 128 256), losses := [] }

theorem u434 : Upper (D 0) (R 0) [50,257,24,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b434
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b435 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 76 152 80 33 228 164 420), lower := (rows 51 259 76 152 80 33 64 128 256), losses := [] }

theorem u435 : Upper (D 0) (R 0) [50,257,72,144,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b435
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b436 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 259 76 152 80 36 225 161 417), lower := (rows 51 259 76 152 80 36 64 128 256), losses := [] }

theorem u436 : Upper (D 0) (R 0) [50,257,72,144,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b436
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r437 : Route 9 := (fun mask => (mask,id))

def c437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u437 : Upper (D 0) (R 0) [50,257,72,144,64,128] 13 := by
  apply FastRouting.sound _ _ [50,257,72,144,64,128] 13 (by decide) (choices 1) [1,4,32] r437 c437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u31
  · exact u32
  · exact u33

def b438 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 84 104 17 160 204 140 396), lower := (rows 51 259 84 104 17 160 64 128 256), losses := [] }

theorem u438 : Upper (D 0) (R 0) [50,257,80,96,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b438
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b439 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 51 259 84 104 20 160 201 137 393), lower := (rows 51 259 84 104 20 160 64 128 256), losses := [] }

theorem u439 : Upper (D 0) (R 0) [50,257,80,96,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b439
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b440 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 259 84 104 24 160 197 133 389), lower := (rows 51 259 84 104 24 160 64 128 256), losses := [] }

theorem u440 : Upper (D 0) (R 0) [50,257,80,96,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b440
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b441 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 259 84 104 144 160 77 141 269), lower := (rows 51 259 84 104 144 160 64 128 256), losses := [] }

theorem u441 : Upper (D 0) (R 0) [50,257,80,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b441
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b442 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0)], upper := (rows 51 259 84 168 17 96 204 140 396), lower := (rows 51 259 84 168 17 96 64 128 256), losses := [] }

theorem u442 : Upper (D 0) (R 0) [50,257,80,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b442
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b443 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 51 259 84 168 20 96 201 137 393), lower := (rows 51 259 84 168 20 96 64 128 256), losses := [] }

theorem u443 : Upper (D 0) (R 0) [50,257,80,160,4,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b443
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b444 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 259 84 168 24 96 197 133 389), lower := (rows 51 259 84 168 24 96 64 128 256), losses := [] }

theorem u444 : Upper (D 0) (R 0) [50,257,80,160,8,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b444
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r445 : Route 9 := (fun mask => (mask,id))

def c445 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u445 : Upper (D 0) (R 0) [50,257,80,160,128,64] 13 := by
  apply FastRouting.sound _ _ [50,257,80,160,128,64] 13 (by decide) (choices 1) [1,4,8] r445 c445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34
  · exact u35
  · exact u36

def b446 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 51 262 69 88 144 33 232 168 424), lower := (rows 51 262 69 88 144 33 64 128 256), losses := [] }

theorem u446 : Upper (D 0) (R 0) [50,260,65,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b446
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b447 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 262 69 88 144 40 225 161 417), lower := (rows 51 262 69 88 144 40 64 128 256), losses := [] }

theorem u447 : Upper (D 0) (R 0) [50,260,65,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b447
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b448 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 262 69 88 144 160 105 169 297), lower := (rows 51 262 69 88 144 160 64 128 256), losses := [] }

theorem u448 : Upper (D 0) (R 0) [50,260,65,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b448
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b449 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 51 262 69 137 24 160 112 240 368), lower := (rows 51 262 69 137 24 160 64 128 256), losses := [] }

theorem u449 : Upper (D 0) (R 0) [50,260,65,129,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b449
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b450 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 69 137 48 160 88 216 344), lower := (rows 51 262 69 137 48 160 64 128 256), losses := [] }

theorem u450 : Upper (D 0) (R 0) [50,260,65,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b450
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b451 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 262 69 137 80 160 120 184 312), lower := (rows 51 262 69 137 80 160 64 128 256), losses := [] }

theorem u451 : Upper (D 0) (R 0) [50,260,65,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b451
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b452 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 51 262 69 200 17 160 120 184 312), lower := (rows 51 262 69 200 17 160 64 128 256), losses := [] }

theorem u452 : Upper (D 0) (R 0) [50,260,65,192,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b452
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b453 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 262 69 200 24 160 113 177 305), lower := (rows 51 262 69 200 24 160 64 128 256), losses := [] }

theorem u453 : Upper (D 0) (R 0) [50,260,65,192,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b453
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b454 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 262 69 200 48 160 89 153 281), lower := (rows 51 262 69 200 48 160 64 128 256), losses := [] }

theorem u454 : Upper (D 0) (R 0) [50,260,65,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b454
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b455 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 51 262 196 73 17 40 240 176 432), lower := (rows 51 262 196 73 17 40 64 128 256), losses := [] }

theorem u455 : Upper (D 0) (R 0) [50,260,192,65,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b455
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b456 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 462, targets := 16 }], pairs := [(1,4)], upper := (rows 51 262 196 73 17 48 232 168 424), lower := (rows 51 262 196 73 17 48 64 128 256), losses := [] }

theorem u456 : Upper (D 0) (R 0) [50,260,192,65,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b456
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b457 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 51 262 196 73 17 160 120 184 312), lower := (rows 51 262 196 73 17 160 64 128 256), losses := [] }

theorem u457 : Upper (D 0) (R 0) [50,260,192,65,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b457
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b458 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 262 196 88 17 33 232 168 424), lower := (rows 51 262 196 88 17 33 64 128 256), losses := [] }

theorem u458 : Upper (D 0) (R 0) [50,260,192,80,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b458
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b459 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 262 196 88 17 40 225 161 417), lower := (rows 51 262 196 88 17 40 64 128 256), losses := [] }

theorem u459 : Upper (D 0) (R 0) [50,260,192,80,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b459
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b460 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 51 262 196 88 17 160 105 169 297), lower := (rows 51 262 196 88 17 160 64 128 256), losses := [] }

theorem u460 : Upper (D 0) (R 0) [50,260,192,80,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b460
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b461 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 51 322 13 200 17 36 240 176 432), lower := (rows 51 322 13 200 17 36 64 128 256), losses := [] }

theorem u461 : Upper (D 0) (R 0) [50,320,9,192,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b461
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b462 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 462, targets := 16 }], pairs := [(1,4)], upper := (rows 51 322 13 200 17 48 228 164 420), lower := (rows 51 322 13 200 17 48 64 128 256), losses := [] }

theorem u462 : Upper (D 0) (R 0) [50,320,9,192,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b462
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r463 : Route 9 := (fun mask => (mask,id))

def c463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u463 : Upper (D 0) (R 0) [50,320,9,192,1,128] 13 := by
  apply FastRouting.sound _ _ [50,320,9,192,1,128] 13 (by decide) (choices 1) [4,16,32] r463 c463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37
  · exact u38
  · exact u39

def b464 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 322 13 200 20 160 113 177 305), lower := (rows 51 322 13 200 20 160 64 128 256), losses := [] }

theorem u464 : Upper (D 0) (R 0) [50,320,9,192,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b464
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b465 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 13 200 48 160 85 149 277), lower := (rows 51 322 13 200 48 160 64 128 256), losses := [] }

theorem u465 : Upper (D 0) (R 0) [50,320,9,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b465
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b466 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 28 104 17 33 196 132 388), lower := (rows 51 322 28 104 17 33 64 128 256), losses := [] }

theorem u466 : Upper (D 0) (R 0) [50,320,24,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b466
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b467 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 51 322 28 104 17 36 193 129 385), lower := (rows 51 322 28 104 17 36 64 128 256), losses := [] }

theorem u467 : Upper (D 0) (R 0) [50,320,24,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b467
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r468 : Route 9 := (fun mask => (mask,id))

def c468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u468 : Upper (D 0) (R 0) [50,320,24,96,1,128] 13 := by
  apply FastRouting.sound _ _ [50,320,24,96,1,128] 13 (by decide) (choices 1) [1,4,128] r468 c468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u40
  · exact u41
  · exact u42

def r469 : Route 9 := (fun mask => (mask,id))

def c469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u469 : Upper (D 0) (R 0) [50,320,24,96,128,1] 13 := by
  apply FastRouting.sound _ _ [50,320,24,96,128,1] 13 (by decide) (choices 1) [1,4,128] r469 c469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u43
  · exact u44
  · exact u45

def b470 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 51 322 28 104 144 36 193 129 385), lower := (rows 51 322 28 104 144 36 64 128 256), losses := [] }

theorem u470 : Upper (D 0) (R 0) [50,320,24,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b470
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b471 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 322 28 104 144 160 69 133 261), lower := (rows 51 322 28 104 144 160 64 128 256), losses := [] }

theorem u471 : Upper (D 0) (R 0) [50,320,24,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b471
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b472 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 28 168 17 33 196 196 452), lower := (rows 51 322 28 168 17 33 64 128 256), losses := [] }

theorem u472 : Upper (D 0) (R 0) [50,320,24,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b472
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b473 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 51 322 28 168 17 36 193 193 449), lower := (rows 51 322 28 168 17 36 64 128 256), losses := [] }

theorem u473 : Upper (D 0) (R 0) [50,320,24,160,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b473
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b474 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 28 168 17 96 197 133 389), lower := (rows 51 322 28 168 17 96 64 128 256), losses := [] }

theorem u474 : Upper (D 0) (R 0) [50,320,24,160,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b474
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b475 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 51 322 28 168 17 160 69 197 325), lower := (rows 51 322 28 168 17 160 64 128 256), losses := [] }

theorem u475 : Upper (D 0) (R 0) [50,320,24,160,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b475
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b476 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 322 28 200 17 33 228 164 420), lower := (rows 51 322 28 200 17 33 64 128 256), losses := [] }

theorem u476 : Upper (D 0) (R 0) [50,320,24,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b476
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b477 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 322 28 200 17 36 225 161 417), lower := (rows 51 322 28 200 17 36 64 128 256), losses := [] }

theorem u477 : Upper (D 0) (R 0) [50,320,24,192,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b477
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r478 : Route 9 := (fun mask => (mask,id))

def c478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u478 : Upper (D 0) (R 0) [50,320,24,192,1,128] 13 := by
  apply FastRouting.sound _ _ [50,320,24,192,1,128] 13 (by decide) (choices 1) [1,4,32] r478 c478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u46
  · exact u47
  · exact u48

def b479 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 51 322 76 137 17 36 240 176 432), lower := (rows 51 322 76 137 17 36 64 128 256), losses := [] }

theorem u479 : Upper (D 0) (R 0) [50,320,72,129,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b479
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u479
end Delivery.IrregularNine14.P00

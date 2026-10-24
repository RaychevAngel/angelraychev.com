import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0021
import IrregularNine14P06C0022

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r10440 : Route 9 := (fun mask => (mask,id))

def c10440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10440 : Upper (D 6) (R 6) [6,40,144,260,66,64] 13 := by
  apply FastRouting.sound _ _ [6,40,144,260,66,64] 13 (by decide) (choices 1) [1,32] r10440 c10440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1308
  · exact u1309

def b10441 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 148 268 112 33 67 195 323), lower := (rows 7 42 148 268 112 33 64 128 256), losses := [] }

theorem u10441 : Upper (D 6) (R 6) [6,40,144,260,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10441
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10442 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 328, targets := 34 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(3,1),(3,5)], upper := (rows 7 42 148 268 112 34 65 193 321), lower := (rows 7 42 148 268 112 34 64 128 256), losses := [] }

theorem u10442 : Upper (D 6) (R 6) [6,40,144,260,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10442
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10443 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 42 148 268 112 96 67 131 259), lower := (rows 7 42 148 268 112 96 64 128 256), losses := [] }

theorem u10443 : Upper (D 6) (R 6) [6,40,144,260,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10443
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10444 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 7 42 148 328 49 33 70 198 326), lower := (rows 7 42 148 328 49 33 64 128 256), losses := [] }

theorem u10444 : Upper (D 6) (R 6) [6,40,144,320,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10444
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10445 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 42 148 328 49 34 69 197 325), lower := (rows 7 42 148 328 49 34 64 128 256), losses := [] }

theorem u10445 : Upper (D 6) (R 6) [6,40,144,320,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10445
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10446 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 48, targets := 66 },{ cop := 0, region := 328, targets := 4 }], pairs := [(3,2),(4,1),(4,6)], upper := (rows 7 42 148 328 49 36 67 195 323), lower := (rows 7 42 148 328 49 36 64 128 256), losses := [] }

theorem u10446 : Upper (D 6) (R 6) [6,40,144,320,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10446
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10447 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 149, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 148 328 49 96 71 135 263), lower := (rows 7 42 148 328 49 96 64 128 256), losses := [] }

theorem u10447 : Upper (D 6) (R 6) [6,40,144,320,33,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10447
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10448 : Route 9 := (fun mask => (mask,id))

def c10448 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10448 : Upper (D 6) (R 6) [6,40,144,320,65,1] 13 := by
  apply FastRouting.sound _ _ [6,40,144,320,65,1] 13 (by decide) (choices 1) [2,4,32] r10448 c10448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1310
  · exact u1311
  · exact u1312

def b10449 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 148 328 81 34 101 165 293), lower := (rows 7 42 148 328 81 34 64 128 256), losses := [] }

theorem u10449 : Upper (D 6) (R 6) [6,40,144,320,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10449
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10450 : Route 9 := (fun mask => (mask,id))

def c10450 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10450 : Upper (D 6) (R 6) [6,40,144,320,65,4] 13 := by
  apply FastRouting.sound _ _ [6,40,144,320,65,4] 13 (by decide) (choices 1) [1,2,32] r10450 c10450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1313
  · exact u1314
  · exact u1315

def r10451 : Route 9 := (fun mask => (mask,id))

def c10451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10451 : Upper (D 6) (R 6) [6,40,144,320,68,1] 13 := by
  apply FastRouting.sound _ _ [6,40,144,320,68,1] 13 (by decide) (choices 1) [1,2,32] r10451 c10451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1316
  · exact u1317
  · exact u1318

def b10452 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 148 328 84 34 97 161 289), lower := (rows 7 42 148 328 84 34 64 128 256), losses := [] }

theorem u10452 : Upper (D 6) (R 6) [6,40,144,320,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10452
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10453 : Route 9 := (fun mask => (mask,id))

def c10453 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10453 : Upper (D 6) (R 6) [6,40,144,320,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,144,320,96,1] 13 (by decide) (choices 1) [1,2,4] r10453 c10453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1319
  · exact u1320
  · exact u1321

def b10454 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 42 148 328 112 34 69 133 261), lower := (rows 7 42 148 328 112 34 64 128 256), losses := [] }

theorem u10454 : Upper (D 6) (R 6) [6,40,144,320,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10454
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10455 : Route 9 := (fun mask => (mask,id))

def c10455 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10455 : Upper (D 6) (R 6) [6,40,144,320,96,4] 13 := by
  apply FastRouting.sound _ _ [6,40,144,320,96,4] 13 (by decide) (choices 1) [1,2] r10455 c10455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1322
  · exact u1323

def b10456 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 164 25 336 33 70 198 326), lower := (rows 7 42 164 25 336 33 64 128 256), losses := [] }

theorem u10456 : Upper (D 6) (R 6) [6,40,160,17,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10456
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10457 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 25 336 34 69 197 325), lower := (rows 7 42 164 25 336 34 64 128 256), losses := [] }

theorem u10457 : Upper (D 6) (R 6) [6,40,160,17,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10457
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10458 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 164 25 336 36 67 195 323), lower := (rows 7 42 164 25 336 36 64 128 256), losses := [] }

theorem u10458 : Upper (D 6) (R 6) [6,40,160,17,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10458
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10459 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 42 164 25 336 96 71 135 263), lower := (rows 7 42 164 25 336 96 64 128 256), losses := [] }

theorem u10459 : Upper (D 6) (R 6) [6,40,160,17,320,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10459
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10460 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 164 73 84 33 338 402 274), lower := (rows 7 42 164 73 84 33 64 128 256), losses := [] }

theorem u10460 : Upper (D 6) (R 6) [6,40,160,65,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10460
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10461 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 73 84 34 337 401 273), lower := (rows 7 42 164 73 84 34 64 128 256), losses := [] }

theorem u10461 : Upper (D 6) (R 6) [6,40,160,65,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10461
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10462 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 164 73 84 48 323 387 259), lower := (rows 7 42 164 73 84 48 64 128 256), losses := [] }

theorem u10462 : Upper (D 6) (R 6) [6,40,160,65,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10462
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10463 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 88, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 164 73 84 288 83 147 275), lower := (rows 7 42 164 73 84 288 64 128 256), losses := [] }

theorem u10463 : Upper (D 6) (R 6) [6,40,160,65,68,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10463
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10464 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 73 273 34 84 212 340), lower := (rows 7 42 164 73 273 34 64 128 256), losses := [] }

theorem u10464 : Upper (D 6) (R 6) [6,40,160,65,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10464
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10465 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 164 73 273 36 82 210 338), lower := (rows 7 42 164 73 273 36 64 128 256), losses := [] }

theorem u10465 : Upper (D 6) (R 6) [6,40,160,65,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10465
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10466 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 164 73 273 48 70 198 326), lower := (rows 7 42 164 73 273 48 64 128 256), losses := [] }

theorem u10466 : Upper (D 6) (R 6) [6,40,160,65,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10466
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10467 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 164 73 273 96 86 150 278), lower := (rows 7 42 164 73 273 96 64 128 256), losses := [] }

theorem u10467 : Upper (D 6) (R 6) [6,40,160,65,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10467
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10468 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 164 73 274 33 84 212 340), lower := (rows 7 42 164 73 274 33 64 128 256), losses := [] }

theorem u10468 : Upper (D 6) (R 6) [6,40,160,65,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10468
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10469 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 164 73 274 36 81 209 337), lower := (rows 7 42 164 73 274 36 64 128 256), losses := [] }

theorem u10469 : Upper (D 6) (R 6) [6,40,160,65,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10469
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10470 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 164 73 274 48 69 197 325), lower := (rows 7 42 164 73 274 48 64 128 256), losses := [] }

theorem u10470 : Upper (D 6) (R 6) [6,40,160,65,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10470
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10471 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 164 73 274 96 85 149 277), lower := (rows 7 42 164 73 274 96 64 128 256), losses := [] }

theorem u10471 : Upper (D 6) (R 6) [6,40,160,65,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10471
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10472 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 164 73 276 33 82 210 338), lower := (rows 7 42 164 73 276 33 64 128 256), losses := [] }

theorem u10472 : Upper (D 6) (R 6) [6,40,160,65,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10472
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10473 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 73 276 34 81 209 337), lower := (rows 7 42 164 73 276 34 64 128 256), losses := [] }

theorem u10473 : Upper (D 6) (R 6) [6,40,160,65,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10473
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10474 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 164 73 276 48 67 195 323), lower := (rows 7 42 164 73 276 48 64 128 256), losses := [] }

theorem u10474 : Upper (D 6) (R 6) [6,40,160,65,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10474
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10475 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 164 73 276 96 83 147 275), lower := (rows 7 42 164 73 276 96 64 128 256), losses := [] }

theorem u10475 : Upper (D 6) (R 6) [6,40,160,65,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10475
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10476 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 164 73 336 33 86 150 278), lower := (rows 7 42 164 73 336 33 64 128 256), losses := [] }

theorem u10476 : Upper (D 6) (R 6) [6,40,160,65,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10476
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10477 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 73 336 34 85 149 277), lower := (rows 7 42 164 73 336 34 64 128 256), losses := [] }

theorem u10477 : Upper (D 6) (R 6) [6,40,160,65,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10477
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10478 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 164 73 336 36 83 147 275), lower := (rows 7 42 164 73 336 36 64 128 256), losses := [] }

theorem u10478 : Upper (D 6) (R 6) [6,40,160,65,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10478
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10479 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 164 73 336 48 71 135 263), lower := (rows 7 42 164 73 336 48 64 128 256), losses := [] }

theorem u10479 : Upper (D 6) (R 6) [6,40,160,65,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10479
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10480 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 164 88 273 33 70 198 326), lower := (rows 7 42 164 88 273 33 64 128 256), losses := [] }

theorem u10480 : Upper (D 6) (R 6) [6,40,160,80,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10480
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10481 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 88 273 34 69 197 325), lower := (rows 7 42 164 88 273 34 64 128 256), losses := [] }

theorem u10481 : Upper (D 6) (R 6) [6,40,160,80,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10481
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10482 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 164 88 273 36 67 195 323), lower := (rows 7 42 164 88 273 36 64 128 256), losses := [] }

theorem u10482 : Upper (D 6) (R 6) [6,40,160,80,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10482
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10483 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 164 88 273 96 71 135 263), lower := (rows 7 42 164 88 273 96 64 128 256), losses := [] }

theorem u10483 : Upper (D 6) (R 6) [6,40,160,80,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10483
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10484 : Route 9 := (fun mask => (mask,id))

def c10484 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10484 : Upper (D 6) (R 6) [6,40,160,80,260,1] 13 := by
  apply FastRouting.sound _ _ [6,40,160,80,260,1] 13 (by decide) (choices 1) [1,2] r10484 c10484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1324
  · exact u1325

def b10485 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 88 276 34 65 193 321), lower := (rows 7 42 164 88 276 34 64 128 256), losses := [] }

theorem u10485 : Upper (D 6) (R 6) [6,40,160,80,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10485
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10486 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 164 88 276 96 67 131 259), lower := (rows 7 42 164 88 276 96 64 128 256), losses := [] }

theorem u10486 : Upper (D 6) (R 6) [6,40,160,80,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10486
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10487 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 265 81 34 84 212 340), lower := (rows 7 42 164 265 81 34 64 128 256), losses := [] }

theorem u10487 : Upper (D 6) (R 6) [6,40,160,257,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10487
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10488 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 164 265 81 36 82 210 338), lower := (rows 7 42 164 265 81 36 64 128 256), losses := [] }

theorem u10488 : Upper (D 6) (R 6) [6,40,160,257,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10488
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10489 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 164 265 81 48 70 198 326), lower := (rows 7 42 164 265 81 48 64 128 256), losses := [] }

theorem u10489 : Upper (D 6) (R 6) [6,40,160,257,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10489
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10490 : Route 9 := (fun mask => (mask,id))

def c10490 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10490 : Upper (D 6) (R 6) [6,40,160,257,65,64] 13 := by
  apply FastRouting.sound _ _ [6,40,160,257,65,64] 13 (by decide) (choices 1) [2,4,16] r10490 c10490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1326
  · exact u1327
  · exact u1328

def b10491 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 164 265 82 33 84 212 340), lower := (rows 7 42 164 265 82 33 64 128 256), losses := [] }

theorem u10491 : Upper (D 6) (R 6) [6,40,160,257,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10491
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10492 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 7 42 164 265 82 36 81 209 337), lower := (rows 7 42 164 265 82 36 64 128 256), losses := [] }

theorem u10492 : Upper (D 6) (R 6) [6,40,160,257,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10492
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10493 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 164 265 82 48 69 197 325), lower := (rows 7 42 164 265 82 48 64 128 256), losses := [] }

theorem u10493 : Upper (D 6) (R 6) [6,40,160,257,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10493
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10494 : Route 9 := (fun mask => (mask,id))

def c10494 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10494 : Upper (D 6) (R 6) [6,40,160,257,66,64] 13 := by
  apply FastRouting.sound _ _ [6,40,160,257,66,64] 13 (by decide) (choices 1) [1,4,16] r10494 c10494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1329
  · exact u1330
  · exact u1331

def b10495 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 164 265 84 33 82 210 338), lower := (rows 7 42 164 265 84 33 64 128 256), losses := [] }

theorem u10495 : Upper (D 6) (R 6) [6,40,160,257,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10495
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10496 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 7 42 164 265 84 34 81 209 337), lower := (rows 7 42 164 265 84 34 64 128 256), losses := [] }

theorem u10496 : Upper (D 6) (R 6) [6,40,160,257,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10496
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10497 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 164 265 84 48 67 195 323), lower := (rows 7 42 164 265 84 48 64 128 256), losses := [] }

theorem u10497 : Upper (D 6) (R 6) [6,40,160,257,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10497
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10498 : Route 9 := (fun mask => (mask,id))

def c10498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10498 : Upper (D 6) (R 6) [6,40,160,257,68,64] 13 := by
  apply FastRouting.sound _ _ [6,40,160,257,68,64] 13 (by decide) (choices 1) [1,2,16] r10498 c10498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1332
  · exact u1333
  · exact u1334

def b10499 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 344, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 164 280 81 33 70 198 326), lower := (rows 7 42 164 280 81 33 64 128 256), losses := [] }

theorem u10499 : Upper (D 6) (R 6) [6,40,160,272,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10499
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10499
end Delivery.IrregularNine14.P06

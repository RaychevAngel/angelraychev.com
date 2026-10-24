import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0058

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11460 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 41 208 308 372 436 308), lower := (rows 67 162 13 41 208 32 64 128 256), losses := [] }

theorem u11460 : Upper (D 8) (R 8) [66,160,9,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11461 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 41 276 240 240 240 496), lower := (rows 67 162 13 41 276 32 64 128 256), losses := [] }

theorem u11461 : Upper (D 8) (R 8) [66,160,9,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11462 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 41 304 244 212 212 468), lower := (rows 67 162 13 41 304 32 64 128 256), losses := [] }

theorem u11462 : Upper (D 8) (R 8) [66,160,9,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11463 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 41 336 180 244 180 436), lower := (rows 67 162 13 41 336 32 64 128 256), losses := [] }

theorem u11463 : Upper (D 8) (R 8) [66,160,9,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11464 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 41 400 116 116 244 372), lower := (rows 67 162 13 41 400 32 64 128 256), losses := [] }

theorem u11464 : Upper (D 8) (R 8) [66,160,9,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11465 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 162 13 44 49 496 464 464 464), lower := (rows 67 162 13 44 49 32 64 128 256), losses := [] }

theorem u11465 : Upper (D 8) (R 8) [66,160,9,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11466 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 44 81 432 496 432 432), lower := (rows 67 162 13 44 81 32 64 128 256), losses := [] }

theorem u11466 : Upper (D 8) (R 8) [66,160,9,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11467 : Route 9 := (fun mask => (mask,id))

def c11467 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u11467 : Upper (D 8) (R 8) [66,160,9,36,96] 13 := by
  apply FastRouting.sound _ _ [66,160,9,36,96] 13 (by decide) (choices 1) [1,16,128,256] r11467 c11467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3513
  · exact u3514
  · exact u3515
  · exact u3516

def b11468 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 13 44 145 368 368 496 368), lower := (rows 67 162 13 44 145 32 64 128 256), losses := [] }

theorem u11468 : Upper (D 8) (R 8) [66,160,9,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11469 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 162 13 44 176 369 337 465 337), lower := (rows 67 162 13 44 176 32 64 128 256), losses := [] }

theorem u11469 : Upper (D 8) (R 8) [66,160,9,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11470 : Route 9 := (fun mask => (mask,id))

def c11470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u11470 : Upper (D 8) (R 8) [66,160,9,36,192] 13 := by
  apply FastRouting.sound _ _ [66,160,9,36,192] 13 (by decide) (choices 1) [1,16,256] r11470 c11470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3517
  · exact u3518
  · exact u3519

def b11471 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 44 273 240 240 240 496), lower := (rows 67 162 13 44 273 32 64 128 256), losses := [] }

theorem u11471 : Upper (D 8) (R 8) [66,160,9,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11472 : Route 9 := (fun mask => (mask,id))

def c11472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u11472 : Upper (D 8) (R 8) [66,160,9,36,288] 13 := by
  apply FastRouting.sound _ _ [66,160,9,36,288] 13 (by decide) (choices 1) [1,16,64,128] r11472 c11472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3520
  · exact u3521
  · exact u3522
  · exact u3523

def r11473 : Route 9 := (fun mask => (mask,id))

def c11473 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11473 : Upper (D 8) (R 8) [66,160,9,36,320] 13 := by
  apply FastRouting.sound _ _ [66,160,9,36,320] 13 (by decide) (choices 1) [1,16,128] r11473 c11473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3524
  · exact u3525
  · exact u3526

def r11474 : Route 9 := (fun mask => (mask,id))

def c11474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11474 : Upper (D 8) (R 8) [66,160,9,36,384] 13 := by
  apply FastRouting.sound _ _ [66,160,9,36,384] 13 (by decide) (choices 1) [1,16,64] r11474 c11474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3527
  · exact u3528
  · exact u3529

def b11475 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 162 13 56 49 484 452 452 452), lower := (rows 67 162 13 56 49 32 64 128 256), losses := [] }

theorem u11475 : Upper (D 8) (R 8) [66,160,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11476 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 13 56 52 481 449 449 449), lower := (rows 67 162 13 56 52 32 64 128 256), losses := [] }

theorem u11476 : Upper (D 8) (R 8) [66,160,9,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11477 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 56 81 420 484 420 420), lower := (rows 67 162 13 56 81 32 64 128 256), losses := [] }

theorem u11477 : Upper (D 8) (R 8) [66,160,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11478 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 56 84 417 481 417 417), lower := (rows 67 162 13 56 84 32 64 128 256), losses := [] }

theorem u11478 : Upper (D 8) (R 8) [66,160,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11479 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 13 56 112 421 453 389 389), lower := (rows 67 162 13 56 112 32 64 128 256), losses := [] }

theorem u11479 : Upper (D 8) (R 8) [66,160,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11480 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 13 56 145 356 356 484 356), lower := (rows 67 162 13 56 145 32 64 128 256), losses := [] }

theorem u11480 : Upper (D 8) (R 8) [66,160,9,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11481 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 56 148 353 353 481 353), lower := (rows 67 162 13 56 148 32 64 128 256), losses := [] }

theorem u11481 : Upper (D 8) (R 8) [66,160,9,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11482 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 13 56 176 357 325 453 325), lower := (rows 67 162 13 56 176 32 64 128 256), losses := [] }

theorem u11482 : Upper (D 8) (R 8) [66,160,9,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11483 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 56 208 293 357 421 293), lower := (rows 67 162 13 56 208 32 64 128 256), losses := [] }

theorem u11483 : Upper (D 8) (R 8) [66,160,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11484 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 56 273 228 228 228 484), lower := (rows 67 162 13 56 273 32 64 128 256), losses := [] }

theorem u11484 : Upper (D 8) (R 8) [66,160,9,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11485 : Route 9 := (fun mask => (mask,id))

def c11485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11485 : Upper (D 8) (R 8) [66,160,9,48,260] 13 := by
  apply FastRouting.sound _ _ [66,160,9,48,260] 13 (by decide) (choices 1) [1,64,128] r11485 c11485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3530
  · exact u3531
  · exact u3532

def b11486 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 162 13 56 304 229 197 197 453), lower := (rows 67 162 13 56 304 32 64 128 256), losses := [] }

theorem u11486 : Upper (D 8) (R 8) [66,160,9,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11487 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 56 336 165 229 165 421), lower := (rows 67 162 13 56 336 32 64 128 256), losses := [] }

theorem u11487 : Upper (D 8) (R 8) [66,160,9,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r11488 : Route 9 := (fun mask => (mask,id))

def c11488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11488 : Upper (D 8) (R 8) [66,160,9,48,384] 13 := by
  apply FastRouting.sound _ _ [66,160,9,48,384] 13 (by decide) (choices 1) [1,4,64] r11488 c11488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3533
  · exact u3534
  · exact u3535

def b11489 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 73 52 432 496 432 432), lower := (rows 67 162 13 73 52 32 64 128 256), losses := [] }

theorem u11489 : Upper (D 8) (R 8) [66,160,9,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11490 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 73 148 304 368 432 304), lower := (rows 67 162 13 73 148 32 64 128 256), losses := [] }

theorem u11490 : Upper (D 8) (R 8) [66,160,9,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11491 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 73 276 176 240 176 432), lower := (rows 67 162 13 73 276 32 64 128 256), losses := [] }

theorem u11491 : Upper (D 8) (R 8) [66,160,9,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11492 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 73 304 180 244 180 436), lower := (rows 67 162 13 73 304 32 64 128 256), losses := [] }

theorem u11492 : Upper (D 8) (R 8) [66,160,9,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11493 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 73 400 52 116 180 308), lower := (rows 67 162 13 73 400 32 64 128 256), losses := [] }

theorem u11493 : Upper (D 8) (R 8) [66,160,9,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11494 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 76 49 432 496 432 432), lower := (rows 67 162 13 76 49 32 64 128 256), losses := [] }

theorem u11494 : Upper (D 8) (R 8) [66,160,9,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11495 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 76 273 176 240 176 432), lower := (rows 67 162 13 76 273 32 64 128 256), losses := [] }

theorem u11495 : Upper (D 8) (R 8) [66,160,9,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11496 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 76 304 177 241 177 433), lower := (rows 67 162 13 76 304 32 64 128 256), losses := [] }

theorem u11496 : Upper (D 8) (R 8) [66,160,9,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11497 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 162 13 76 400 49 113 177 305), lower := (rows 67 162 13 76 400 32 64 128 256), losses := [] }

theorem u11497 : Upper (D 8) (R 8) [66,160,9,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11498 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 88 49 420 484 420 420), lower := (rows 67 162 13 88 49 32 64 128 256), losses := [] }

theorem u11498 : Upper (D 8) (R 8) [66,160,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11499 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 88 52 417 481 417 417), lower := (rows 67 162 13 88 52 32 64 128 256), losses := [] }

theorem u11499 : Upper (D 8) (R 8) [66,160,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11500 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 88 148 289 353 417 289), lower := (rows 67 162 13 88 148 32 64 128 256), losses := [] }

theorem u11500 : Upper (D 8) (R 8) [66,160,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11501 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 88 273 164 228 164 420), lower := (rows 67 162 13 88 273 32 64 128 256), losses := [] }

theorem u11501 : Upper (D 8) (R 8) [66,160,9,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11502 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 88 276 161 225 161 417), lower := (rows 67 162 13 88 276 32 64 128 256), losses := [] }

theorem u11502 : Upper (D 8) (R 8) [66,160,9,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11503 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 88 304 165 229 165 421), lower := (rows 67 162 13 88 304 32 64 128 256), losses := [] }

theorem u11503 : Upper (D 8) (R 8) [66,160,9,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11504 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 88 400 37 101 165 293), lower := (rows 67 162 13 88 400 32 64 128 256), losses := [] }

theorem u11504 : Upper (D 8) (R 8) [66,160,9,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11505 : PairBound 9 := { available := 404, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 104 49 436 468 404 404), lower := (rows 67 162 13 104 49 32 64 128 256), losses := [] }

theorem u11505 : Upper (D 8) (R 8) [66,160,9,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11506 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 104 52 433 465 401 401), lower := (rows 67 162 13 104 52 32 64 128 256), losses := [] }

theorem u11506 : Upper (D 8) (R 8) [66,160,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11507 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 104 148 305 369 433 305), lower := (rows 67 162 13 104 148 32 64 128 256), losses := [] }

theorem u11507 : Upper (D 8) (R 8) [66,160,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11508 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 104 273 180 244 180 436), lower := (rows 67 162 13 104 273 32 64 128 256), losses := [] }

theorem u11508 : Upper (D 8) (R 8) [66,160,9,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11509 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 104 276 177 241 177 433), lower := (rows 67 162 13 104 276 32 64 128 256), losses := [] }

theorem u11509 : Upper (D 8) (R 8) [66,160,9,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11510 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 104 304 181 213 149 405), lower := (rows 67 162 13 104 304 32 64 128 256), losses := [] }

theorem u11510 : Upper (D 8) (R 8) [66,160,9,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11511 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 104 400 53 117 181 309), lower := (rows 67 162 13 104 400 32 64 128 256), losses := [] }

theorem u11511 : Upper (D 8) (R 8) [66,160,9,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11512 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 137 52 368 368 496 368), lower := (rows 67 162 13 137 52 32 64 128 256), losses := [] }

theorem u11512 : Upper (D 8) (R 8) [66,160,9,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11513 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 137 84 304 368 432 304), lower := (rows 67 162 13 137 84 32 64 128 256), losses := [] }

theorem u11513 : Upper (D 8) (R 8) [66,160,9,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11514 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 137 112 308 372 436 308), lower := (rows 67 162 13 137 112 32 64 128 256), losses := [] }

theorem u11514 : Upper (D 8) (R 8) [66,160,9,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11515 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 137 276 112 112 240 368), lower := (rows 67 162 13 137 276 32 64 128 256), losses := [] }

theorem u11515 : Upper (D 8) (R 8) [66,160,9,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11516 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 137 304 116 116 244 372), lower := (rows 67 162 13 137 304 32 64 128 256), losses := [] }

theorem u11516 : Upper (D 8) (R 8) [66,160,9,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11517 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 13 137 336 52 116 180 308), lower := (rows 67 162 13 137 336 32 64 128 256), losses := [] }

theorem u11517 : Upper (D 8) (R 8) [66,160,9,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11518 : PairBound 9 := { available := 368, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 140 49 368 368 496 368), lower := (rows 67 162 13 140 49 32 64 128 256), losses := [] }

theorem u11518 : Upper (D 8) (R 8) [66,160,9,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11519 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 140 112 305 369 433 305), lower := (rows 67 162 13 140 112 32 64 128 256), losses := [] }

theorem u11519 : Upper (D 8) (R 8) [66,160,9,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u11519
end Delivery.IrregularNine14.P08

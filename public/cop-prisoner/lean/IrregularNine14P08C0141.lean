import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0030

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8460 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 196 265 81 176 240 176 432), lower := (rows 35 14 196 265 81 32 64 128 256), losses := [] }

theorem u8460 : Upper (D 8) (R 8) [34,12,192,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8461 : Route 9 := (fun mask => (mask,id))

def c8461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8461 : Upper (D 8) (R 8) [34,12,192,257,96] 13 := by
  apply FastRouting.sound _ _ [34,12,192,257,96] 13 (by decide) (choices 1) [1,16,128] r8461 c8461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1837
  · exact u1838
  · exact u1839

def b8462 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 196 265 208 49 113 177 305), lower := (rows 35 14 196 265 208 32 64 128 256), losses := [] }

theorem u8462 : Upper (D 8) (R 8) [34,12,192,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8463 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 196 280 49 225 225 225 481), lower := (rows 35 14 196 280 49 32 64 128 256), losses := [] }

theorem u8463 : Upper (D 8) (R 8) [34,12,192,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8464 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 196 280 81 161 225 161 417), lower := (rows 35 14 196 280 81 32 64 128 256), losses := [] }

theorem u8464 : Upper (D 8) (R 8) [34,12,192,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8465 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 196 280 112 161 225 161 417), lower := (rows 35 14 196 280 112 32 64 128 256), losses := [] }

theorem u8465 : Upper (D 8) (R 8) [34,12,192,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8466 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 196 280 208 33 97 161 289), lower := (rows 35 14 196 280 208 32 64 128 256), losses := [] }

theorem u8466 : Upper (D 8) (R 8) [34,12,192,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8467 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 14 196 296 49 241 209 209 465), lower := (rows 35 14 196 296 49 32 64 128 256), losses := [] }

theorem u8467 : Upper (D 8) (R 8) [34,12,192,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8468 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 196 296 81 177 241 177 433), lower := (rows 35 14 196 296 81 32 64 128 256), losses := [] }

theorem u8468 : Upper (D 8) (R 8) [34,12,192,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8469 : Route 9 := (fun mask => (mask,id))

def c8469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8469 : Upper (D 8) (R 8) [34,12,192,288,96] 13 := by
  apply FastRouting.sound _ _ [34,12,192,288,96] 13 (by decide) (choices 1) [1,16,128] r8469 c8469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1840
  · exact u1841
  · exact u1842

def b8470 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 14 196 296 208 49 113 177 305), lower := (rows 35 14 196 296 208 32 64 128 256), losses := [] }

theorem u8470 : Upper (D 8) (R 8) [34,12,192,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8471 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 28 176 480 480 480 480), lower := (rows 35 67 13 28 176 32 64 128 256), losses := [] }

theorem u8471 : Upper (D 8) (R 8) [34,65,9,20,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8472 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 28 208 416 480 416 416), lower := (rows 35 67 13 28 208 32 64 128 256), losses := [] }

theorem u8472 : Upper (D 8) (R 8) [34,65,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8473 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 28 304 224 224 224 480), lower := (rows 35 67 13 28 304 32 64 128 256), losses := [] }

theorem u8473 : Upper (D 8) (R 8) [34,65,9,20,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8474 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 28 336 160 224 160 416), lower := (rows 35 67 13 28 336 32 64 128 256), losses := [] }

theorem u8474 : Upper (D 8) (R 8) [34,65,9,20,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8475 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 28 400 224 224 224 480), lower := (rows 35 67 13 28 400 32 64 128 256), losses := [] }

theorem u8475 : Upper (D 8) (R 8) [34,65,9,20,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8476 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 44 176 496 464 464 464), lower := (rows 35 67 13 44 176 32 64 128 256), losses := [] }

theorem u8476 : Upper (D 8) (R 8) [34,65,9,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8477 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 44 208 432 496 432 432), lower := (rows 35 67 13 44 208 32 64 128 256), losses := [] }

theorem u8477 : Upper (D 8) (R 8) [34,65,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8478 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 44 304 240 208 208 464), lower := (rows 35 67 13 44 304 32 64 128 256), losses := [] }

theorem u8478 : Upper (D 8) (R 8) [34,65,9,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8479 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 44 336 176 240 176 432), lower := (rows 35 67 13 44 336 32 64 128 256), losses := [] }

theorem u8479 : Upper (D 8) (R 8) [34,65,9,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8480 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 44 400 240 240 240 496), lower := (rows 35 67 13 44 400 32 64 128 256), losses := [] }

theorem u8480 : Upper (D 8) (R 8) [34,65,9,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8481 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 56 84 416 480 416 416), lower := (rows 35 67 13 56 84 32 64 128 256), losses := [] }

theorem u8481 : Upper (D 8) (R 8) [34,65,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8482 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 56 148 480 480 480 480), lower := (rows 35 67 13 56 148 32 64 128 256), losses := [] }

theorem u8482 : Upper (D 8) (R 8) [34,65,9,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8483 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 56 208 420 484 420 420), lower := (rows 35 67 13 56 208 32 64 128 256), losses := [] }

theorem u8483 : Upper (D 8) (R 8) [34,65,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8484 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 56 276 224 224 224 480), lower := (rows 35 67 13 56 276 32 64 128 256), losses := [] }

theorem u8484 : Upper (D 8) (R 8) [34,65,9,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8485 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 56 336 164 228 164 420), lower := (rows 35 67 13 56 336 32 64 128 256), losses := [] }

theorem u8485 : Upper (D 8) (R 8) [34,65,9,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8486 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 56 400 228 228 228 484), lower := (rows 35 67 13 56 400 32 64 128 256), losses := [] }

theorem u8486 : Upper (D 8) (R 8) [34,65,9,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8487 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 76 176 432 496 432 432), lower := (rows 35 67 13 76 176 32 64 128 256), losses := [] }

theorem u8487 : Upper (D 8) (R 8) [34,65,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8488 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 76 304 176 240 176 432), lower := (rows 35 67 13 76 304 32 64 128 256), losses := [] }

theorem u8488 : Upper (D 8) (R 8) [34,65,9,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8489 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 76 400 176 240 176 432), lower := (rows 35 67 13 76 400 32 64 128 256), losses := [] }

theorem u8489 : Upper (D 8) (R 8) [34,65,9,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8490 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 88 52 416 480 416 416), lower := (rows 35 67 13 88 52 32 64 128 256), losses := [] }

theorem u8490 : Upper (D 8) (R 8) [34,65,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8491 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 88 148 416 480 416 416), lower := (rows 35 67 13 88 148 32 64 128 256), losses := [] }

theorem u8491 : Upper (D 8) (R 8) [34,65,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8492 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 88 176 420 484 420 420), lower := (rows 35 67 13 88 176 32 64 128 256), losses := [] }

theorem u8492 : Upper (D 8) (R 8) [34,65,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8493 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 88 276 160 224 160 416), lower := (rows 35 67 13 88 276 32 64 128 256), losses := [] }

theorem u8493 : Upper (D 8) (R 8) [34,65,9,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8494 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 88 304 164 228 164 420), lower := (rows 35 67 13 88 304 32 64 128 256), losses := [] }

theorem u8494 : Upper (D 8) (R 8) [34,65,9,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8495 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 88 400 164 228 164 420), lower := (rows 35 67 13 88 400 32 64 128 256), losses := [] }

theorem u8495 : Upper (D 8) (R 8) [34,65,9,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8496 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 140 176 368 368 496 368), lower := (rows 35 67 13 140 176 32 64 128 256), losses := [] }

theorem u8496 : Upper (D 8) (R 8) [34,65,9,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8497 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 140 208 304 368 432 304), lower := (rows 35 67 13 140 208 32 64 128 256), losses := [] }

theorem u8497 : Upper (D 8) (R 8) [34,65,9,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8498 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 140 304 240 240 240 496), lower := (rows 35 67 13 140 304 32 64 128 256), losses := [] }

theorem u8498 : Upper (D 8) (R 8) [34,65,9,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8499 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 140 336 176 240 176 432), lower := (rows 35 67 13 140 336 32 64 128 256), losses := [] }

theorem u8499 : Upper (D 8) (R 8) [34,65,9,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8500 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 140 400 112 112 240 368), lower := (rows 35 67 13 140 400 32 64 128 256), losses := [] }

theorem u8500 : Upper (D 8) (R 8) [34,65,9,132,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8501 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 152 52 480 480 480 480), lower := (rows 35 67 13 152 52 32 64 128 256), losses := [] }

theorem u8501 : Upper (D 8) (R 8) [34,65,9,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8502 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 152 84 416 480 416 416), lower := (rows 35 67 13 152 84 32 64 128 256), losses := [] }

theorem u8502 : Upper (D 8) (R 8) [34,65,9,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8503 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 152 276 224 224 224 480), lower := (rows 35 67 13 152 276 32 64 128 256), losses := [] }

theorem u8503 : Upper (D 8) (R 8) [34,65,9,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8504 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 152 304 228 228 228 484), lower := (rows 35 67 13 152 304 32 64 128 256), losses := [] }

theorem u8504 : Upper (D 8) (R 8) [34,65,9,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8505 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 152 336 164 228 164 420), lower := (rows 35 67 13 152 336 32 64 128 256), losses := [] }

theorem u8505 : Upper (D 8) (R 8) [34,65,9,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8506 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 168 52 496 464 464 464), lower := (rows 35 67 13 168 52 32 64 128 256), losses := [] }

theorem u8506 : Upper (D 8) (R 8) [34,65,9,160,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8507 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 168 84 432 496 432 432), lower := (rows 35 67 13 168 84 32 64 128 256), losses := [] }

theorem u8507 : Upper (D 8) (R 8) [34,65,9,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8508 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 168 148 368 368 496 368), lower := (rows 35 67 13 168 148 32 64 128 256), losses := [] }

theorem u8508 : Upper (D 8) (R 8) [34,65,9,160,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8509 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 168 208 308 372 436 308), lower := (rows 35 67 13 168 208 32 64 128 256), losses := [] }

theorem u8509 : Upper (D 8) (R 8) [34,65,9,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8510 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 168 276 240 240 240 496), lower := (rows 35 67 13 168 276 32 64 128 256), losses := [] }

theorem u8510 : Upper (D 8) (R 8) [34,65,9,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8511 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 168 304 244 212 212 468), lower := (rows 35 67 13 168 304 32 64 128 256), losses := [] }

theorem u8511 : Upper (D 8) (R 8) [34,65,9,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8512 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 168 336 180 244 180 436), lower := (rows 35 67 13 168 336 32 64 128 256), losses := [] }

theorem u8512 : Upper (D 8) (R 8) [34,65,9,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8513 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 168 400 116 116 244 372), lower := (rows 35 67 13 168 400 32 64 128 256), losses := [] }

theorem u8513 : Upper (D 8) (R 8) [34,65,9,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8514 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 200 52 432 496 432 432), lower := (rows 35 67 13 200 52 32 64 128 256), losses := [] }

theorem u8514 : Upper (D 8) (R 8) [34,65,9,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8515 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 200 148 304 368 432 304), lower := (rows 35 67 13 200 148 32 64 128 256), losses := [] }

theorem u8515 : Upper (D 8) (R 8) [34,65,9,192,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8516 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 200 176 308 372 436 308), lower := (rows 35 67 13 200 176 32 64 128 256), losses := [] }

theorem u8516 : Upper (D 8) (R 8) [34,65,9,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8517 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 200 276 176 240 176 432), lower := (rows 35 67 13 200 276 32 64 128 256), losses := [] }

theorem u8517 : Upper (D 8) (R 8) [34,65,9,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8518 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 200 304 180 244 180 436), lower := (rows 35 67 13 200 304 32 64 128 256), losses := [] }

theorem u8518 : Upper (D 8) (R 8) [34,65,9,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8519 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 200 400 52 116 180 308), lower := (rows 35 67 13 200 400 32 64 128 256), losses := [] }

theorem u8519 : Upper (D 8) (R 8) [34,65,9,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u8519
end Delivery.IrregularNine14.P08

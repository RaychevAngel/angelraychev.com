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

def b8520 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 268 176 240 240 240 496), lower := (rows 35 67 13 268 176 32 64 128 256), losses := [] }

theorem u8520 : Upper (D 8) (R 8) [34,65,9,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8521 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 268 208 176 240 176 432), lower := (rows 35 67 13 268 208 32 64 128 256), losses := [] }

theorem u8521 : Upper (D 8) (R 8) [34,65,9,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8522 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 280 52 224 224 224 480), lower := (rows 35 67 13 280 52 32 64 128 256), losses := [] }

theorem u8522 : Upper (D 8) (R 8) [34,65,9,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8523 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 280 84 160 224 160 416), lower := (rows 35 67 13 280 84 32 64 128 256), losses := [] }

theorem u8523 : Upper (D 8) (R 8) [34,65,9,272,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8524 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 280 148 224 224 224 480), lower := (rows 35 67 13 280 148 32 64 128 256), losses := [] }

theorem u8524 : Upper (D 8) (R 8) [34,65,9,272,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8525 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 280 176 228 228 228 484), lower := (rows 35 67 13 280 176 32 64 128 256), losses := [] }

theorem u8525 : Upper (D 8) (R 8) [34,65,9,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8525 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8526 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 280 208 164 228 164 420), lower := (rows 35 67 13 280 208 32 64 128 256), losses := [] }

theorem u8526 : Upper (D 8) (R 8) [34,65,9,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8527 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 296 52 240 208 208 464), lower := (rows 35 67 13 296 52 32 64 128 256), losses := [] }

theorem u8527 : Upper (D 8) (R 8) [34,65,9,288,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8528 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 296 84 176 240 176 432), lower := (rows 35 67 13 296 84 32 64 128 256), losses := [] }

theorem u8528 : Upper (D 8) (R 8) [34,65,9,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8529 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 296 148 240 240 240 496), lower := (rows 35 67 13 296 148 32 64 128 256), losses := [] }

theorem u8529 : Upper (D 8) (R 8) [34,65,9,288,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8530 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 296 176 244 212 212 468), lower := (rows 35 67 13 296 176 32 64 128 256), losses := [] }

theorem u8530 : Upper (D 8) (R 8) [34,65,9,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8531 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 296 208 180 244 180 436), lower := (rows 35 67 13 296 208 32 64 128 256), losses := [] }

theorem u8531 : Upper (D 8) (R 8) [34,65,9,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8532 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 328 52 176 240 176 432), lower := (rows 35 67 13 328 52 32 64 128 256), losses := [] }

theorem u8532 : Upper (D 8) (R 8) [34,65,9,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8533 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 328 148 176 240 176 432), lower := (rows 35 67 13 328 148 32 64 128 256), losses := [] }

theorem u8533 : Upper (D 8) (R 8) [34,65,9,320,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8534 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 328 176 180 244 180 436), lower := (rows 35 67 13 328 176 32 64 128 256), losses := [] }

theorem u8534 : Upper (D 8) (R 8) [34,65,9,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8535 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 392 52 240 240 240 496), lower := (rows 35 67 13 392 52 32 64 128 256), losses := [] }

theorem u8535 : Upper (D 8) (R 8) [34,65,9,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8536 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 392 84 176 240 176 432), lower := (rows 35 67 13 392 84 32 64 128 256), losses := [] }

theorem u8536 : Upper (D 8) (R 8) [34,65,9,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8537 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 392 148 112 112 240 368), lower := (rows 35 67 13 392 148 32 64 128 256), losses := [] }

theorem u8537 : Upper (D 8) (R 8) [34,65,9,384,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8538 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 392 176 116 116 244 372), lower := (rows 35 67 13 392 176 32 64 128 256), losses := [] }

theorem u8538 : Upper (D 8) (R 8) [34,65,9,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8539 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 13 392 208 52 116 180 308), lower := (rows 35 67 13 392 208 32 64 128 256), losses := [] }

theorem u8539 : Upper (D 8) (R 8) [34,65,9,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8540 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 28 41 52 480 448 448 448), lower := (rows 35 67 28 41 52 32 64 128 256), losses := [] }

theorem u8540 : Upper (D 8) (R 8) [34,65,24,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8541 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 67 28 41 148 480 480 480 480), lower := (rows 35 67 28 41 148 32 64 128 256), losses := [] }

theorem u8541 : Upper (D 8) (R 8) [34,65,24,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8542 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 67 28 41 176 484 452 452 452), lower := (rows 35 67 28 41 176 32 64 128 256), losses := [] }

theorem u8542 : Upper (D 8) (R 8) [34,65,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8543 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 67 28 41 208 420 484 420 420), lower := (rows 35 67 28 41 208 32 64 128 256), losses := [] }

theorem u8543 : Upper (D 8) (R 8) [34,65,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8544 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 67 28 41 276 224 224 224 480), lower := (rows 35 67 28 41 276 32 64 128 256), losses := [] }

theorem u8544 : Upper (D 8) (R 8) [34,65,24,33,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8545 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 67 28 41 304 228 196 196 452), lower := (rows 35 67 28 41 304 32 64 128 256), losses := [] }

theorem u8545 : Upper (D 8) (R 8) [34,65,24,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8546 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 67 28 41 336 164 228 164 420), lower := (rows 35 67 28 41 336 32 64 128 256), losses := [] }

theorem u8546 : Upper (D 8) (R 8) [34,65,24,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8547 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 67 28 41 400 228 228 228 484), lower := (rows 35 67 28 41 400 32 64 128 256), losses := [] }

theorem u8547 : Upper (D 8) (R 8) [34,65,24,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8548 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 28 44 81 416 480 416 416), lower := (rows 35 67 28 44 81 32 64 128 256), losses := [] }

theorem u8548 : Upper (D 8) (R 8) [34,65,24,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8549 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 44 112 417 449 385 385), lower := (rows 35 67 28 44 112 32 64 128 256), losses := [] }

theorem u8549 : Upper (D 8) (R 8) [34,65,24,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8550 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 44 145 480 480 480 480), lower := (rows 35 67 28 44 145 32 64 128 256), losses := [] }

theorem u8550 : Upper (D 8) (R 8) [34,65,24,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8551 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 44 176 481 449 449 449), lower := (rows 35 67 28 44 176 32 64 128 256), losses := [] }

theorem u8551 : Upper (D 8) (R 8) [34,65,24,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8552 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 44 208 417 481 417 417), lower := (rows 35 67 28 44 208 32 64 128 256), losses := [] }

theorem u8552 : Upper (D 8) (R 8) [34,65,24,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8553 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 44 273 224 224 224 480), lower := (rows 35 67 28 44 273 32 64 128 256), losses := [] }

theorem u8553 : Upper (D 8) (R 8) [34,65,24,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8554 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 44 304 225 193 193 449), lower := (rows 35 67 28 44 304 32 64 128 256), losses := [] }

theorem u8554 : Upper (D 8) (R 8) [34,65,24,36,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8555 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 44 336 161 225 161 417), lower := (rows 35 67 28 44 336 32 64 128 256), losses := [] }

theorem u8555 : Upper (D 8) (R 8) [34,65,24,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8556 : Route 9 := (fun mask => (mask,id))

def c8556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8556 : Upper (D 8) (R 8) [34,65,24,36,384] 13 := by
  apply FastRouting.sound _ _ [34,65,24,36,384] 13 (by decide) (choices 1) [1,64,128] r8556 c8556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1843
  · exact u1844
  · exact u1845

def b8557 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 148 416 480 416 416), lower := (rows 35 67 28 73 148 32 64 128 256), losses := [] }

theorem u8557 : Upper (D 8) (R 8) [34,65,24,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8558 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 176 420 484 420 420), lower := (rows 35 67 28 73 176 32 64 128 256), losses := [] }

theorem u8558 : Upper (D 8) (R 8) [34,65,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8559 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 276 160 224 160 416), lower := (rows 35 67 28 73 276 32 64 128 256), losses := [] }

theorem u8559 : Upper (D 8) (R 8) [34,65,24,65,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8560 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 304 164 228 164 420), lower := (rows 35 67 28 73 304 32 64 128 256), losses := [] }

theorem u8560 : Upper (D 8) (R 8) [34,65,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8561 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 400 164 228 164 420), lower := (rows 35 67 28 73 400 32 64 128 256), losses := [] }

theorem u8561 : Upper (D 8) (R 8) [34,65,24,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8562 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 76 176 417 481 417 417), lower := (rows 35 67 28 76 176 32 64 128 256), losses := [] }

theorem u8562 : Upper (D 8) (R 8) [34,65,24,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8563 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 76 304 161 225 161 417), lower := (rows 35 67 28 76 304 32 64 128 256), losses := [] }

theorem u8563 : Upper (D 8) (R 8) [34,65,24,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8563 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8564 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 76 400 161 225 161 417), lower := (rows 35 67 28 76 400 32 64 128 256), losses := [] }

theorem u8564 : Upper (D 8) (R 8) [34,65,24,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8565 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 104 148 417 481 417 417), lower := (rows 35 67 28 104 148 32 64 128 256), losses := [] }

theorem u8565 : Upper (D 8) (R 8) [34,65,24,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8566 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 104 176 421 453 389 389), lower := (rows 35 67 28 104 176 32 64 128 256), losses := [] }

theorem u8566 : Upper (D 8) (R 8) [34,65,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8567 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 104 276 161 225 161 417), lower := (rows 35 67 28 104 276 32 64 128 256), losses := [] }

theorem u8567 : Upper (D 8) (R 8) [34,65,24,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8568 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 104 304 165 197 133 389), lower := (rows 35 67 28 104 304 32 64 128 256), losses := [] }

theorem u8568 : Upper (D 8) (R 8) [34,65,24,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8569 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 104 400 165 229 165 421), lower := (rows 35 67 28 104 400 32 64 128 256), losses := [] }

theorem u8569 : Upper (D 8) (R 8) [34,65,24,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8570 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 28 137 148 352 352 480 352), lower := (rows 35 67 28 137 148 32 64 128 256), losses := [] }

theorem u8570 : Upper (D 8) (R 8) [34,65,24,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8570 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8571 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 137 176 356 356 484 356), lower := (rows 35 67 28 137 176 32 64 128 256), losses := [] }

theorem u8571 : Upper (D 8) (R 8) [34,65,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8572 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 137 208 292 356 420 292), lower := (rows 35 67 28 137 208 32 64 128 256), losses := [] }

theorem u8572 : Upper (D 8) (R 8) [34,65,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8572 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8573 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 137 276 224 224 224 480), lower := (rows 35 67 28 137 276 32 64 128 256), losses := [] }

theorem u8573 : Upper (D 8) (R 8) [34,65,24,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8574 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 137 304 228 228 228 484), lower := (rows 35 67 28 137 304 32 64 128 256), losses := [] }

theorem u8574 : Upper (D 8) (R 8) [34,65,24,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8575 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 137 336 164 228 164 420), lower := (rows 35 67 28 137 336 32 64 128 256), losses := [] }

theorem u8575 : Upper (D 8) (R 8) [34,65,24,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8576 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 137 400 100 100 228 356), lower := (rows 35 67 28 137 400 32 64 128 256), losses := [] }

theorem u8576 : Upper (D 8) (R 8) [34,65,24,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8577 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 140 176 353 353 481 353), lower := (rows 35 67 28 140 176 32 64 128 256), losses := [] }

theorem u8577 : Upper (D 8) (R 8) [34,65,24,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8578 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 140 208 289 353 417 289), lower := (rows 35 67 28 140 208 32 64 128 256), losses := [] }

theorem u8578 : Upper (D 8) (R 8) [34,65,24,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8579 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 140 273 224 224 224 480), lower := (rows 35 67 28 140 273 32 64 128 256), losses := [] }

theorem u8579 : Upper (D 8) (R 8) [34,65,24,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u8579
end Delivery.IrregularNine14.P08

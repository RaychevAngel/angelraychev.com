import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0069

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12480 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 116, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 44 137 84 49 113 177 305), lower := (rows 67 386 44 137 84 32 64 128 256), losses := [] }

theorem u12480 : Upper (D 8) (R 8) [66,384,40,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12481 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 116, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 44 137 112 53 117 181 309), lower := (rows 67 386 44 137 112 32 64 128 256), losses := [] }

theorem u12481 : Upper (D 8) (R 8) [66,384,40,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12482 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 67 386 44 140 112 49 113 177 305), lower := (rows 67 386 44 140 112 32 64 128 256), losses := [] }

theorem u12482 : Upper (D 8) (R 8) [66,384,40,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12483 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 44 152 81 37 101 165 293), lower := (rows 67 386 44 152 81 32 64 128 256), losses := [] }

theorem u12483 : Upper (D 8) (R 8) [66,384,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12484 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 44 152 84 33 97 161 289), lower := (rows 67 386 44 152 84 32 64 128 256), losses := [] }

theorem u12484 : Upper (D 8) (R 8) [66,384,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12485 : Route 9 := (fun mask => (mask,id))

def c12485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12485 : Upper (D 8) (R 8) [66,384,40,144,96] 13 := by
  apply FastRouting.sound _ _ [66,384,40,144,96] 13 (by decide) (choices 1) [1,4] r12485 c12485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4143
  · exact u4144

def b12486 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 168 84 49 113 177 305), lower := (rows 67 386 44 168 84 32 64 128 256), losses := [] }

theorem u12486 : Upper (D 8) (R 8) [66,384,40,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12487 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 386 44 168 112 53 85 149 277), lower := (rows 67 386 44 168 112 32 64 128 256), losses := [] }

theorem u12487 : Upper (D 8) (R 8) [66,384,40,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12488 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 56 152 480 480 480 480), lower := (rows 97 7 7 56 152 32 64 128 256), losses := [] }

theorem u12488 : Upper (D 8) (R 8) [96,5,3,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12489 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 56 208 424 488 424 424), lower := (rows 97 7 7 56 208 32 64 128 256), losses := [] }

theorem u12489 : Upper (D 8) (R 8) [96,5,3,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12490 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 56 280 224 224 224 480), lower := (rows 97 7 7 56 280 32 64 128 256), losses := [] }

theorem u12490 : Upper (D 8) (R 8) [96,5,3,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12491 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 56 336 168 232 168 424), lower := (rows 97 7 7 56 336 32 64 128 256), losses := [] }

theorem u12491 : Upper (D 8) (R 8) [96,5,3,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12492 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 56 400 232 232 232 488), lower := (rows 97 7 7 56 400 32 64 128 256), losses := [] }

theorem u12492 : Upper (D 8) (R 8) [96,5,3,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12493 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 88 176 424 488 424 424), lower := (rows 97 7 7 88 176 32 64 128 256), losses := [] }

theorem u12493 : Upper (D 8) (R 8) [96,5,3,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12494 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 88 304 168 232 168 424), lower := (rows 97 7 7 88 304 32 64 128 256), losses := [] }

theorem u12494 : Upper (D 8) (R 8) [96,5,3,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12495 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 88 400 168 232 168 424), lower := (rows 97 7 7 88 400 32 64 128 256), losses := [] }

theorem u12495 : Upper (D 8) (R 8) [96,5,3,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12496 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 152 280 224 224 224 480), lower := (rows 97 7 7 152 280 32 64 128 256), losses := [] }

theorem u12496 : Upper (D 8) (R 8) [96,5,3,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12497 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 152 304 232 232 232 488), lower := (rows 97 7 7 152 304 32 64 128 256), losses := [] }

theorem u12497 : Upper (D 8) (R 8) [96,5,3,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12498 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 152 336 168 232 168 424), lower := (rows 97 7 7 152 336 32 64 128 256), losses := [] }

theorem u12498 : Upper (D 8) (R 8) [96,5,3,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12499 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 168 208 312 376 440 312), lower := (rows 97 7 7 168 208 32 64 128 256), losses := [] }

theorem u12499 : Upper (D 8) (R 8) [96,5,3,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12500 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 168 280 240 240 240 496), lower := (rows 97 7 7 168 280 32 64 128 256), losses := [] }

theorem u12500 : Upper (D 8) (R 8) [96,5,3,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12501 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 168 304 248 216 216 472), lower := (rows 97 7 7 168 304 32 64 128 256), losses := [] }

theorem u12501 : Upper (D 8) (R 8) [96,5,3,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12502 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 168 336 184 248 184 440), lower := (rows 97 7 7 168 336 32 64 128 256), losses := [] }

theorem u12502 : Upper (D 8) (R 8) [96,5,3,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12503 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 168 400 120 120 248 376), lower := (rows 97 7 7 168 400 32 64 128 256), losses := [] }

theorem u12503 : Upper (D 8) (R 8) [96,5,3,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12504 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 200 280 176 240 176 432), lower := (rows 97 7 7 200 280 32 64 128 256), losses := [] }

theorem u12504 : Upper (D 8) (R 8) [96,5,3,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12505 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 200 304 184 248 184 440), lower := (rows 97 7 7 200 304 32 64 128 256), losses := [] }

theorem u12505 : Upper (D 8) (R 8) [96,5,3,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12506 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 7 200 400 56 120 184 312), lower := (rows 97 7 7 200 400 32 64 128 256), losses := [] }

theorem u12506 : Upper (D 8) (R 8) [96,5,3,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12507 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 26 176 480 480 480 480), lower := (rows 97 7 13 26 176 32 64 128 256), losses := [] }

theorem u12507 : Upper (D 8) (R 8) [96,5,9,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12508 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 26 208 416 480 416 416), lower := (rows 97 7 13 26 208 32 64 128 256), losses := [] }

theorem u12508 : Upper (D 8) (R 8) [96,5,9,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12509 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 26 304 224 224 224 480), lower := (rows 97 7 13 26 304 32 64 128 256), losses := [] }

theorem u12509 : Upper (D 8) (R 8) [96,5,9,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12510 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 26 336 160 224 160 416), lower := (rows 97 7 13 26 336 32 64 128 256), losses := [] }

theorem u12510 : Upper (D 8) (R 8) [96,5,9,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12511 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 26 400 224 224 224 480), lower := (rows 97 7 13 26 400 32 64 128 256), losses := [] }

theorem u12511 : Upper (D 8) (R 8) [96,5,9,18,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12512 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 42 176 496 464 464 464), lower := (rows 97 7 13 42 176 32 64 128 256), losses := [] }

theorem u12512 : Upper (D 8) (R 8) [96,5,9,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12513 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 42 208 432 496 432 432), lower := (rows 97 7 13 42 208 32 64 128 256), losses := [] }

theorem u12513 : Upper (D 8) (R 8) [96,5,9,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12514 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 42 304 240 208 208 464), lower := (rows 97 7 13 42 304 32 64 128 256), losses := [] }

theorem u12514 : Upper (D 8) (R 8) [96,5,9,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12515 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 42 336 176 240 176 432), lower := (rows 97 7 13 42 336 32 64 128 256), losses := [] }

theorem u12515 : Upper (D 8) (R 8) [96,5,9,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12516 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 13 42 400 240 240 240 496), lower := (rows 97 7 13 42 400 32 64 128 256), losses := [] }

theorem u12516 : Upper (D 8) (R 8) [96,5,9,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12517 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 30, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 13 56 82 416 480 416 416), lower := (rows 97 7 13 56 82 32 64 128 256), losses := [] }

theorem u12517 : Upper (D 8) (R 8) [96,5,9,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12518 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 56 146 480 480 480 480), lower := (rows 97 7 13 56 146 32 64 128 256), losses := [] }

theorem u12518 : Upper (D 8) (R 8) [96,5,9,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12519 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 56 208 418 482 418 418), lower := (rows 97 7 13 56 208 32 64 128 256), losses := [] }

theorem u12519 : Upper (D 8) (R 8) [96,5,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12520 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 56 274 224 224 224 480), lower := (rows 97 7 13 56 274 32 64 128 256), losses := [] }

theorem u12520 : Upper (D 8) (R 8) [96,5,9,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12521 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 56 336 162 226 162 418), lower := (rows 97 7 13 56 336 32 64 128 256), losses := [] }

theorem u12521 : Upper (D 8) (R 8) [96,5,9,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12522 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 56 400 226 226 226 482), lower := (rows 97 7 13 56 400 32 64 128 256), losses := [] }

theorem u12522 : Upper (D 8) (R 8) [96,5,9,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12523 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 74 176 432 496 432 432), lower := (rows 97 7 13 74 176 32 64 128 256), losses := [] }

theorem u12523 : Upper (D 8) (R 8) [96,5,9,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12524 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 74 304 176 240 176 432), lower := (rows 97 7 13 74 304 32 64 128 256), losses := [] }

theorem u12524 : Upper (D 8) (R 8) [96,5,9,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12525 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 74 400 176 240 176 432), lower := (rows 97 7 13 74 400 32 64 128 256), losses := [] }

theorem u12525 : Upper (D 8) (R 8) [96,5,9,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12525 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12526 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 30, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 13 88 50 416 480 416 416), lower := (rows 97 7 13 88 50 32 64 128 256), losses := [] }

theorem u12526 : Upper (D 8) (R 8) [96,5,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12527 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 88 146 416 480 416 416), lower := (rows 97 7 13 88 146 32 64 128 256), losses := [] }

theorem u12527 : Upper (D 8) (R 8) [96,5,9,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12528 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 88 176 418 482 418 418), lower := (rows 97 7 13 88 176 32 64 128 256), losses := [] }

theorem u12528 : Upper (D 8) (R 8) [96,5,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12529 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 88 274 160 224 160 416), lower := (rows 97 7 13 88 274 32 64 128 256), losses := [] }

theorem u12529 : Upper (D 8) (R 8) [96,5,9,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12530 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 88 304 162 226 162 418), lower := (rows 97 7 13 88 304 32 64 128 256), losses := [] }

theorem u12530 : Upper (D 8) (R 8) [96,5,9,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12531 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 88 400 162 226 162 418), lower := (rows 97 7 13 88 400 32 64 128 256), losses := [] }

theorem u12531 : Upper (D 8) (R 8) [96,5,9,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12532 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 138 176 368 368 496 368), lower := (rows 97 7 13 138 176 32 64 128 256), losses := [] }

theorem u12532 : Upper (D 8) (R 8) [96,5,9,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12533 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 138 208 304 368 432 304), lower := (rows 97 7 13 138 208 32 64 128 256), losses := [] }

theorem u12533 : Upper (D 8) (R 8) [96,5,9,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12534 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 138 304 240 240 240 496), lower := (rows 97 7 13 138 304 32 64 128 256), losses := [] }

theorem u12534 : Upper (D 8) (R 8) [96,5,9,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12535 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 138 336 176 240 176 432), lower := (rows 97 7 13 138 336 32 64 128 256), losses := [] }

theorem u12535 : Upper (D 8) (R 8) [96,5,9,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12536 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 138 400 112 112 240 368), lower := (rows 97 7 13 138 400 32 64 128 256), losses := [] }

theorem u12536 : Upper (D 8) (R 8) [96,5,9,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12537 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 152 50 480 480 480 480), lower := (rows 97 7 13 152 50 32 64 128 256), losses := [] }

theorem u12537 : Upper (D 8) (R 8) [96,5,9,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12538 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 13 152 82 416 480 416 416), lower := (rows 97 7 13 152 82 32 64 128 256), losses := [] }

theorem u12538 : Upper (D 8) (R 8) [96,5,9,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12539 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 152 274 224 224 224 480), lower := (rows 97 7 13 152 274 32 64 128 256), losses := [] }

theorem u12539 : Upper (D 8) (R 8) [96,5,9,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12539
end Delivery.IrregularNine14.P08

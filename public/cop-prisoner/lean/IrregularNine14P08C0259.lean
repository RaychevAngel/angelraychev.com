import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0090
import IrregularNine14P08C0091

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15540 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 22 104 176 289 353 417 289), lower := (rows 193 14 22 104 176 32 64 128 256), losses := [] }

theorem u15540 : Upper (D 8) (R 8) [192,12,18,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15541 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 22 104 273 161 225 161 417), lower := (rows 193 14 22 104 273 32 64 128 256), losses := [] }

theorem u15541 : Upper (D 8) (R 8) [192,12,18,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15542 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 22 104 304 161 225 161 417), lower := (rows 193 14 22 104 304 32 64 128 256), losses := [] }

theorem u15542 : Upper (D 8) (R 8) [192,12,18,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15543 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 22 104 400 33 97 161 289), lower := (rows 193 14 22 104 400 32 64 128 256), losses := [] }

theorem u15543 : Upper (D 8) (R 8) [192,12,18,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15544 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 22 200 273 33 97 161 289), lower := (rows 193 14 22 200 273 32 64 128 256), losses := [] }

theorem u15544 : Upper (D 8) (R 8) [192,12,18,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15545 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 22 200 304 33 97 161 289), lower := (rows 193 14 22 200 304 32 64 128 256), losses := [] }

theorem u15545 : Upper (D 8) (R 8) [192,12,18,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15546 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 41 50 496 464 464 464), lower := (rows 193 14 37 41 50 32 64 128 256), losses := [] }

theorem u15546 : Upper (D 8) (R 8) [192,12,33,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15547 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 41 82 432 496 432 432), lower := (rows 193 14 37 41 82 32 64 128 256), losses := [] }

theorem u15547 : Upper (D 8) (R 8) [192,12,33,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15548 : PairBound 9 := { available := 402, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 41 112 434 466 402 402), lower := (rows 193 14 37 41 112 32 64 128 256), losses := [] }

theorem u15548 : Upper (D 8) (R 8) [192,12,33,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15549 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 41 274 240 240 240 496), lower := (rows 193 14 37 41 274 32 64 128 256), losses := [] }

theorem u15549 : Upper (D 8) (R 8) [192,12,33,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15550 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 41 304 242 210 210 466), lower := (rows 193 14 37 41 304 32 64 128 256), losses := [] }

theorem u15550 : Upper (D 8) (R 8) [192,12,33,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15551 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 41 336 178 242 178 434), lower := (rows 193 14 37 41 336 32 64 128 256), losses := [] }

theorem u15551 : Upper (D 8) (R 8) [192,12,33,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15552 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 42 49 496 464 464 464), lower := (rows 193 14 37 42 49 32 64 128 256), losses := [] }

theorem u15552 : Upper (D 8) (R 8) [192,12,33,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15553 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 42 112 433 465 401 401), lower := (rows 193 14 37 42 112 32 64 128 256), losses := [] }

theorem u15553 : Upper (D 8) (R 8) [192,12,33,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15554 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 42 273 240 240 240 496), lower := (rows 193 14 37 42 273 32 64 128 256), losses := [] }

theorem u15554 : Upper (D 8) (R 8) [192,12,33,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15555 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 42 304 241 209 209 465), lower := (rows 193 14 37 42 304 32 64 128 256), losses := [] }

theorem u15555 : Upper (D 8) (R 8) [192,12,33,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15556 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 42 336 177 241 177 433), lower := (rows 193 14 37 42 336 32 64 128 256), losses := [] }

theorem u15556 : Upper (D 8) (R 8) [192,12,33,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15556 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15557 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 26, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 56 49 482 450 450 450), lower := (rows 193 14 37 56 49 32 64 128 256), losses := [] }

theorem u15557 : Upper (D 8) (R 8) [192,12,33,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15558 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 26, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 56 50 481 449 449 449), lower := (rows 193 14 37 56 50 32 64 128 256), losses := [] }

theorem u15558 : Upper (D 8) (R 8) [192,12,33,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15559 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 56 81 418 482 418 418), lower := (rows 193 14 37 56 81 32 64 128 256), losses := [] }

theorem u15559 : Upper (D 8) (R 8) [192,12,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15560 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 292, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 37 56 82 417 481 417 417), lower := (rows 193 14 37 56 82 32 64 128 256), losses := [] }

theorem u15560 : Upper (D 8) (R 8) [192,12,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15561 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 37 56 112 419 451 387 387), lower := (rows 193 14 37 56 112 32 64 128 256), losses := [] }

theorem u15561 : Upper (D 8) (R 8) [192,12,33,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15562 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 37 56 208 291 355 419 291), lower := (rows 193 14 37 56 208 32 64 128 256), losses := [] }

theorem u15562 : Upper (D 8) (R 8) [192,12,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15563 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15563 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15563 : Upper (D 8) (R 8) [192,12,33,48,257] 13 := by
  apply FastRouting.sound _ _ [192,12,33,48,257] 13 (by decide) (choices 1) [2,64] r15563 c15563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5428
  · exact u5429

def r15564 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c15564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u15564 : Upper (D 8) (R 8) [192,12,33,48,258] 13 := by
  apply FastRouting.sound _ _ [192,12,33,48,258] 13 (by decide) (choices 1) [1,64] r15564 c15564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5430
  · exact u5431

def b15565 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 37 56 304 227 195 195 451), lower := (rows 193 14 37 56 304 32 64 128 256), losses := [] }

theorem u15565 : Upper (D 8) (R 8) [192,12,33,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15566 : Route 9 := (fun mask => (mask,id))

def c15566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15566 : Upper (D 8) (R 8) [192,12,33,48,320] 13 := by
  apply FastRouting.sound _ _ [192,12,33,48,320] 13 (by decide) (choices 1) [1,2,128] r15566 c15566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5432
  · exact u5433
  · exact u5434

def b15567 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 73 50 432 496 432 432), lower := (rows 193 14 37 73 50 32 64 128 256), losses := [] }

theorem u15567 : Upper (D 8) (R 8) [192,12,33,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15568 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 73 146 304 368 432 304), lower := (rows 193 14 37 73 146 32 64 128 256), losses := [] }

theorem u15568 : Upper (D 8) (R 8) [192,12,33,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15569 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 73 176 306 370 434 306), lower := (rows 193 14 37 73 176 32 64 128 256), losses := [] }

theorem u15569 : Upper (D 8) (R 8) [192,12,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15570 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 73 274 176 240 176 432), lower := (rows 193 14 37 73 274 32 64 128 256), losses := [] }

theorem u15570 : Upper (D 8) (R 8) [192,12,33,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15570 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15571 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 73 304 178 242 178 434), lower := (rows 193 14 37 73 304 32 64 128 256), losses := [] }

theorem u15571 : Upper (D 8) (R 8) [192,12,33,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15572 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 73 400 50 114 178 306), lower := (rows 193 14 37 73 400 32 64 128 256), losses := [] }

theorem u15572 : Upper (D 8) (R 8) [192,12,33,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15572 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15573 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 37 74 176 305 369 433 305), lower := (rows 193 14 37 74 176 32 64 128 256), losses := [] }

theorem u15573 : Upper (D 8) (R 8) [192,12,33,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15574 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 37 74 273 176 240 176 432), lower := (rows 193 14 37 74 273 32 64 128 256), losses := [] }

theorem u15574 : Upper (D 8) (R 8) [192,12,33,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15575 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 37 74 304 177 241 177 433), lower := (rows 193 14 37 74 304 32 64 128 256), losses := [] }

theorem u15575 : Upper (D 8) (R 8) [192,12,33,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15576 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 37 74 400 49 113 177 305), lower := (rows 193 14 37 74 400 32 64 128 256), losses := [] }

theorem u15576 : Upper (D 8) (R 8) [192,12,33,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15576 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15577 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 37 88 49 418 482 418 418), lower := (rows 193 14 37 88 49 32 64 128 256), losses := [] }

theorem u15577 : Upper (D 8) (R 8) [192,12,33,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15578 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 292, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 37 88 50 417 481 417 417), lower := (rows 193 14 37 88 50 32 64 128 256), losses := [] }

theorem u15578 : Upper (D 8) (R 8) [192,12,33,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15579 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 88 145 290 354 418 290), lower := (rows 193 14 37 88 145 32 64 128 256), losses := [] }

theorem u15579 : Upper (D 8) (R 8) [192,12,33,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15580 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 292, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 37 88 146 289 353 417 289), lower := (rows 193 14 37 88 146 32 64 128 256), losses := [] }

theorem u15580 : Upper (D 8) (R 8) [192,12,33,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15581 : Route 9 := (fun mask => (mask,id))

def c15581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u15581 : Upper (D 8) (R 8) [192,12,33,80,160] 13 := by
  apply FastRouting.sound _ _ [192,12,33,80,160] 13 (by decide) (choices 1) [1,2,256] r15581 c15581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5435
  · exact u5436
  · exact u5437

def r15582 : Route 9 := (fun mask => (mask,id))

def c15582 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15582 : Upper (D 8) (R 8) [192,12,33,80,257] 13 := by
  apply FastRouting.sound _ _ [192,12,33,80,257] 13 (by decide) (choices 1) [2,128] r15582 c15582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5438
  · exact u5439

def b15583 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 37 88 274 161 225 161 417), lower := (rows 193 14 37 88 274 32 64 128 256), losses := [] }

theorem u15583 : Upper (D 8) (R 8) [192,12,33,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15584 : Route 9 := (fun mask => (mask,id))

def c15584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15584 : Upper (D 8) (R 8) [192,12,33,80,288] 13 := by
  apply FastRouting.sound _ _ [192,12,33,80,288] 13 (by decide) (choices 1) [1,2,128] r15584 c15584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5440
  · exact u5441
  · exact u5442

def r15585 : Route 9 := (fun mask => (mask,id))

def c15585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15585 : Upper (D 8) (R 8) [192,12,33,80,384] 13 := by
  apply FastRouting.sound _ _ [192,12,33,80,384] 13 (by decide) (choices 1) [1,2] r15585 c15585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5443
  · exact u5444

def b15586 : PairBound 9 := { available := 402, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 37 104 49 434 466 402 402), lower := (rows 193 14 37 104 49 32 64 128 256), losses := [] }

theorem u15586 : Upper (D 8) (R 8) [192,12,33,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15587 : PairBound 9 := { available := 401, camps := [{ cop := 4, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 193 14 37 104 50 433 465 401 401), lower := (rows 193 14 37 104 50 32 64 128 256), losses := [] }

theorem u15587 : Upper (D 8) (R 8) [192,12,33,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15587 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15588 : PairBound 9 := { available := 306, camps := [{ cop := 4, region := 366, targets := 128 }], pairs := [(1,7)], upper := (rows 193 14 37 104 145 306 370 434 306), lower := (rows 193 14 37 104 145 32 64 128 256), losses := [] }

theorem u15588 : Upper (D 8) (R 8) [192,12,33,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15588 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r15589 : Route 9 := (fun mask => (mask,id))

def c15589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u15589 : Upper (D 8) (R 8) [192,12,33,96,130] 13 := by
  apply FastRouting.sound _ _ [192,12,33,96,130] 13 (by decide) (choices 1) [1,16,256] r15589 c15589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5445
  · exact u5446
  · exact u5447

def r15590 : Route 9 := (fun mask => (mask,id))

def c15590 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u15590 : Upper (D 8) (R 8) [192,12,33,96,160] 13 := by
  apply FastRouting.sound _ _ [192,12,33,96,160] 13 (by decide) (choices 1) [1,2,16,256] r15590 c15590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5448
  · exact u5449
  · exact u5450
  · exact u5451

def r15591 : Route 9 := (fun mask => (mask,id))

def c15591 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15591 : Upper (D 8) (R 8) [192,12,33,96,257] 13 := by
  apply FastRouting.sound _ _ [192,12,33,96,257] 13 (by decide) (choices 1) [2,16,128] r15591 c15591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5452
  · exact u5453
  · exact u5454

def r15592 : Route 9 := (fun mask => (mask,id))

def c15592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15592 : Upper (D 8) (R 8) [192,12,33,96,258] 13 := by
  apply FastRouting.sound _ _ [192,12,33,96,258] 13 (by decide) (choices 1) [1,16,128] r15592 c15592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5455
  · exact u5456
  · exact u5457

def r15593 : Route 9 := (fun mask => (mask,id))

def c15593 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u15593 : Upper (D 8) (R 8) [192,12,33,96,288] 13 := by
  apply FastRouting.sound _ _ [192,12,33,96,288] 13 (by decide) (choices 1) [1,2,16,128] r15593 c15593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5458
  · exact u5459
  · exact u5460
  · exact u5461

def r15594 : Route 9 := (fun mask => (mask,id))

def c15594 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15594 : Upper (D 8) (R 8) [192,12,33,96,384] 13 := by
  apply FastRouting.sound _ _ [192,12,33,96,384] 13 (by decide) (choices 1) [1,2,16] r15594 c15594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5462
  · exact u5463
  · exact u5464

def b15595 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 37 200 50 305 369 433 305), lower := (rows 193 14 37 200 50 32 64 128 256), losses := [] }

theorem u15595 : Upper (D 8) (R 8) [192,12,33,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15595 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15596 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 37 200 273 50 114 178 306), lower := (rows 193 14 37 200 273 32 64 128 256), losses := [] }

theorem u15596 : Upper (D 8) (R 8) [192,12,33,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15597 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 37 200 274 49 113 177 305), lower := (rows 193 14 37 200 274 32 64 128 256), losses := [] }

theorem u15597 : Upper (D 8) (R 8) [192,12,33,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15597 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15598 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 37 200 304 51 115 179 307), lower := (rows 193 14 37 200 304 32 64 128 256), losses := [] }

theorem u15598 : Upper (D 8) (R 8) [192,12,33,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15599 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 37 265 50 240 240 240 496), lower := (rows 193 14 37 265 50 32 64 128 256), losses := [] }

theorem u15599 : Upper (D 8) (R 8) [192,12,33,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15599 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u15599
end Delivery.IrregularNine14.P08

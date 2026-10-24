import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0004

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3540 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 4, region := 296, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 11 131 37 296 84 96 66 148 276), lower := (rows 11 131 37 296 84 96 66 128 256), losses := [] }

theorem u3540 : Upper (D 6) (R 6) [10,129,33,288,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3541 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 131 37 296 84 96 68 146 274), lower := (rows 11 131 37 296 84 96 68 128 256), losses := [] }

theorem u3541 : Upper (D 6) (R 6) [10,129,33,288,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3542 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 37 296 84 96 80 134 262), lower := (rows 11 131 37 296 84 96 80 128 256), losses := [] }

theorem u3542 : Upper (D 6) (R 6) [10,129,33,288,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3542 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3543 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 4, region := 296, targets := 1 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 11 131 37 328 84 36 66 176 304), lower := (rows 11 131 37 328 84 36 66 128 256), losses := [] }

theorem u3543 : Upper (D 6) (R 6) [10,129,33,320,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3544 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 37 328 84 36 80 162 290), lower := (rows 11 131 37 328 84 36 80 128 256), losses := [] }

theorem u3544 : Upper (D 6) (R 6) [10,129,33,320,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3544 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3545 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 395, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 37 328 84 36 96 146 274), lower := (rows 11 131 37 328 84 36 96 128 256), losses := [] }

theorem u3545 : Upper (D 6) (R 6) [10,129,33,320,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3546 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 37 328 84 48 66 164 292), lower := (rows 11 131 37 328 84 48 66 128 256), losses := [] }

theorem u3546 : Upper (D 6) (R 6) [10,129,33,320,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3546 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3547 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 37 328 84 48 68 162 290), lower := (rows 11 131 37 328 84 48 68 128 256), losses := [] }

theorem u3547 : Upper (D 6) (R 6) [10,129,33,320,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3547 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3548 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 395, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 37 328 84 48 96 134 262), lower := (rows 11 131 37 328 84 48 96 128 256), losses := [] }

theorem u3548 : Upper (D 6) (R 6) [10,129,33,320,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3548 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3549 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 11 131 37 328 112 36 66 148 276), lower := (rows 11 131 37 328 112 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 20 36 67 164 292), good := (rows 74 194 508 328 504 444 66 128 256) }] }

theorem u3549 : Upper (D 6) (R 6) [10,129,33,320,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3550 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 395, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 37 328 112 36 68 146 274), lower := (rows 11 131 37 328 112 36 68 128 256), losses := [] }

theorem u3550 : Upper (D 6) (R 6) [10,129,33,320,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3551 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 37 328 112 36 80 134 262), lower := (rows 11 131 37 328 112 36 80 128 256), losses := [] }

theorem u3551 : Upper (D 6) (R 6) [10,129,33,320,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3551 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3552 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5),(3,1)], upper := (rows 11 131 38 28 304 96 65 196 324), lower := (rows 11 131 38 28 304 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 28 103 67 132 260), good := (rows 121 225 508 444 304 96 97 128 256) }] }

theorem u3552 : Upper (D 6) (R 6) [10,129,34,20,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3553 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 100, targets := 1 }], pairs := [(0,5),(1,5),(2,0)], upper := (rows 11 131 38 28 304 96 68 193 321), lower := (rows 11 131 38 28 304 96 68 128 256), losses := [] }

theorem u3553 : Upper (D 6) (R 6) [10,129,34,20,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3554 : PairBound 9 := { available := 36, camps := [], pairs := [(0,6),(3,1),(4,1)], upper := (rows 11 131 38 28 336 96 65 164 292), lower := (rows 11 131 38 28 336 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 21 119 67 140 268), good := (rows 505 241 508 444 368 96 113 128 256) },{ target := 6, region := (rows 9 10 4 8 16 32 0 132 260), good := (rows 11 131 422 415 272 32 1 128 256) }] }

theorem u3554 : Upper (D 6) (R 6) [10,129,34,20,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3555 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 100, targets := 1 }], pairs := [(2,0),(3,1),(4,1)], upper := (rows 11 131 38 28 336 96 68 161 289), lower := (rows 11 131 38 28 336 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 76 21 125 76 131 259), good := (rows 505 433 508 124 376 104 124 128 256) }] }

theorem u3555 : Upper (D 6) (R 6) [10,129,34,20,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3556 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 38 28 336 96 96 133 261), lower := (rows 11 131 38 28 336 96 96 128 256), losses := [] }

theorem u3556 : Upper (D 6) (R 6) [10,129,34,20,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3557 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 56 84 288 65 196 324), lower := (rows 11 131 38 56 84 288 65 128 256), losses := [] }

theorem u3557 : Upper (D 6) (R 6) [10,129,34,48,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3557 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3558 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 56 84 288 68 193 321), lower := (rows 11 131 38 56 84 288 68 128 256), losses := [] }

theorem u3558 : Upper (D 6) (R 6) [10,129,34,48,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3558 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3559 : Route 9 := (fun mask => (mask,id))

def c3559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3559 : Upper (D 6) (R 6) [10,129,34,48,257,64,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,48,257,64,4] 13 (by decide) (choices 1) [4,64] r3559 c3559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u254
  · exact u255

def b3560 : PairBound 9 := { available := 68, camps := [], pairs := [(3,1),(3,2),(4,1)], upper := (rows 11 131 38 56 276 96 65 196 324), lower := (rows 11 131 38 56 276 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 20 103 67 132 260), good := (rows 105 225 508 56 444 96 97 128 256) },{ target := 2, region := (rows 1 2 0 24 16 103 67 128 256), good := (rows 107 227 98 56 312 96 97 128 256) }] }

theorem u3560 : Upper (D 6) (R 6) [10,129,34,48,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3561 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 0, region := 100, targets := 1 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 131 38 56 276 96 68 193 321), lower := (rows 11 131 38 56 276 96 68 128 256), losses := [] }

theorem u3561 : Upper (D 6) (R 6) [10,129,34,48,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3562 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 56 336 36 65 196 324), lower := (rows 11 131 38 56 336 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 7 88 80 103 64 192 320), good := (rows 46 166 38 56 504 36 508 128 256) }] }

theorem u3562 : Upper (D 6) (R 6) [10,129,34,48,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3563 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 36, targets := 1 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 56 336 36 68 193 321), lower := (rows 11 131 38 56 336 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 103 103 128 256), good := (rows 110 230 102 120 376 100 100 128 256) }] }

theorem u3563 : Upper (D 6) (R 6) [10,129,34,48,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3564 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 435, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 38 76 49 288 68 208 336), lower := (rows 11 131 38 76 49 288 68 128 256), losses := [] }

theorem u3564 : Upper (D 6) (R 6) [10,129,34,68,33,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3564 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3565 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 131, targets := 32 }], pairs := [(0,5)], upper := (rows 11 131 38 76 49 288 80 196 324), lower := (rows 11 131 38 76 49 288 80 128 256), losses := [] }

theorem u3565 : Upper (D 6) (R 6) [10,129,34,68,33,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3565 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3566 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 131 38 76 112 288 65 148 276), lower := (rows 11 131 38 76 112 288 65 128 256), losses := [] }

theorem u3566 : Upper (D 6) (R 6) [10,129,34,68,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3566 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3567 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 76 112 288 68 145 273), lower := (rows 11 131 38 76 112 288 68 128 256), losses := [] }

theorem u3567 : Upper (D 6) (R 6) [10,129,34,68,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3567 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3568 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 11 131 38 76 112 288 80 133 261), lower := (rows 11 131 38 76 112 288 80 128 256), losses := [] }

theorem u3568 : Upper (D 6) (R 6) [10,129,34,68,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3568 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3569 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 435, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 38 76 273 96 68 176 304), lower := (rows 11 131 38 76 273 96 68 128 256), losses := [] }

theorem u3569 : Upper (D 6) (R 6) [10,129,34,68,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3570 : PairBound 9 := { available := 36, camps := [], pairs := [(2,0),(3,0)], upper := (rows 11 131 38 76 273 96 80 164 292), lower := (rows 11 131 38 76 273 96 80 128 256), losses := [{ target := 0, region := (rows 0 2 5 24 16 120 80 157 285), good := (rows 430 390 422 492 508 96 504 128 256) }] }

theorem u3570 : Upper (D 6) (R 6) [10,129,34,68,257,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3570 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3571 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 403, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 38 76 273 96 96 148 276), lower := (rows 11 131 38 76 273 96 96 128 256), losses := [] }

theorem u3571 : Upper (D 6) (R 6) [10,129,34,68,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3572 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 131 38 76 276 48 65 224 352), lower := (rows 11 131 38 76 276 48 65 128 256), losses := [] }

theorem u3572 : Upper (D 6) (R 6) [10,129,34,68,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3572 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3573 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 38 76 276 48 96 193 321), lower := (rows 11 131 38 76 276 48 96 128 256), losses := [] }

theorem u3573 : Upper (D 6) (R 6) [10,129,34,68,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3573 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3574 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 272, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 38 76 276 96 65 176 304), lower := (rows 11 131 38 76 276 96 65 128 256), losses := [] }

theorem u3574 : Upper (D 6) (R 6) [10,129,34,68,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3575 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 38 76 276 96 80 161 289), lower := (rows 11 131 38 76 276 96 80 128 256), losses := [] }

theorem u3575 : Upper (D 6) (R 6) [10,129,34,68,260,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3575 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3576 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 403, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 131 38 76 276 96 96 145 273), lower := (rows 11 131 38 76 276 96 96 128 256), losses := [] }

theorem u3576 : Upper (D 6) (R 6) [10,129,34,68,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3577 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 272, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 38 76 304 96 65 148 276), lower := (rows 11 131 38 76 304 96 65 128 256), losses := [] }

theorem u3577 : Upper (D 6) (R 6) [10,129,34,68,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3578 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 435, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 131 38 76 304 96 68 145 273), lower := (rows 11 131 38 76 304 96 68 128 256), losses := [] }

theorem u3578 : Upper (D 6) (R 6) [10,129,34,68,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3579 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 131, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 11 131 38 76 304 96 80 133 261), lower := (rows 11 131 38 76 304 96 80 128 256), losses := [] }

theorem u3579 : Upper (D 6) (R 6) [10,129,34,68,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3579 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3580 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 131 38 76 336 48 65 164 292), lower := (rows 11 131 38 76 336 48 65 128 256), losses := [] }

theorem u3580 : Upper (D 6) (R 6) [10,129,34,68,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3580 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3581 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 435, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 131 38 76 336 48 68 161 289), lower := (rows 11 131 38 76 336 48 68 128 256), losses := [] }

theorem u3581 : Upper (D 6) (R 6) [10,129,34,68,320,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3581 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3582 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 131, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 38 76 336 48 96 133 261), lower := (rows 11 131 38 76 336 48 96 128 256), losses := [] }

theorem u3582 : Upper (D 6) (R 6) [10,129,34,68,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3582 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3583 : Route 9 := (fun mask => (mask,id))

def c3583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3583 : Upper (D 6) (R 6) [10,129,34,80,257,64,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,80,257,64,4] 13 (by decide) (choices 1) [4,32] r3583 c3583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u256
  · exact u257

def b3584 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 38 88 273 96 96 132 260), lower := (rows 11 131 38 88 273 96 96 128 256), losses := [] }

theorem u3584 : Upper (D 6) (R 6) [10,129,34,80,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3585 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 88 276 36 65 224 352), lower := (rows 11 131 38 88 276 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 7 72 81 119 64 200 328), good := (rows 446 182 38 504 308 36 508 128 256) }] }

theorem u3585 : Upper (D 6) (R 6) [10,129,34,80,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3586 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 131, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 38 88 276 36 96 193 321), lower := (rows 11 131 38 88 276 36 96 128 256), losses := [] }

theorem u3586 : Upper (D 6) (R 6) [10,129,34,80,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3587 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 272, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 38 88 276 96 65 164 292), lower := (rows 11 131 38 88 276 96 65 128 256), losses := [] }

theorem u3587 : Upper (D 6) (R 6) [10,129,34,80,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3588 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 131 38 88 276 96 68 161 289), lower := (rows 11 131 38 88 276 96 68 128 256), losses := [] }

theorem u3588 : Upper (D 6) (R 6) [10,129,34,80,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3589 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 131 38 88 276 96 96 133 261), lower := (rows 11 131 38 88 276 96 96 128 256), losses := [] }

theorem u3589 : Upper (D 6) (R 6) [10,129,34,80,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3590 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 88 304 36 65 196 324), lower := (rows 11 131 38 88 304 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 7 72 88 103 64 192 320), good := (rows 62 166 38 504 304 36 508 128 256) }] }

theorem u3590 : Upper (D 6) (R 6) [10,129,34,80,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3591 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 131, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 38 88 304 36 68 193 321), lower := (rows 11 131 38 88 304 36 68 128 256), losses := [] }

theorem u3591 : Upper (D 6) (R 6) [10,129,34,80,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3592 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 272, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 131 38 88 304 96 65 132 260), lower := (rows 11 131 38 88 304 96 65 128 256), losses := [] }

theorem u3592 : Upper (D 6) (R 6) [10,129,34,80,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3593 : Route 9 := (fun mask => (mask,id))

def c3593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3593 : Upper (D 6) (R 6) [10,129,34,80,288,64,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,80,288,64,4] 13 (by decide) (choices 1) [1,4] r3593 c3593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u258
  · exact u259

def b3594 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 131 38 104 84 288 65 148 276), lower := (rows 11 131 38 104 84 288 65 128 256), losses := [] }

theorem u3594 : Upper (D 6) (R 6) [10,129,34,96,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3594 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3595 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 104 84 288 68 145 273), lower := (rows 11 131 38 104 84 288 68 128 256), losses := [] }

theorem u3595 : Upper (D 6) (R 6) [10,129,34,96,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3595 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3596 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 11 131 38 104 84 288 80 133 261), lower := (rows 11 131 38 104 84 288 80 128 256), losses := [] }

theorem u3596 : Upper (D 6) (R 6) [10,129,34,96,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3596 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3597 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 11 131 38 104 276 36 65 208 336), lower := (rows 11 131 38 104 276 36 65 128 256), losses := [] }

theorem u3597 : Upper (D 6) (R 6) [10,129,34,96,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3598 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 131, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 131 38 104 276 36 80 193 321), lower := (rows 11 131 38 104 276 36 80 128 256), losses := [] }

theorem u3598 : Upper (D 6) (R 6) [10,129,34,96,260,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3598 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3599 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 131 38 104 276 48 65 196 324), lower := (rows 11 131 38 104 276 48 65 128 256), losses := [] }

theorem u3599 : Upper (D 6) (R 6) [10,129,34,96,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3599 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3599
end Delivery.IrregularNine14.P06

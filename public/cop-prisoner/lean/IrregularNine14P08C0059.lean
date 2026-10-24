import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0007
import IrregularNine14P08C0008

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3540 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 13 268 208 48 97 161 289), lower := (rows 67 162 13 268 208 48 64 128 256), losses := [] }

theorem u3540 : Upper (D 8) (R 8) [66,160,9,260,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3540 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3541 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 67 162 13 280 52 33 224 224 480), lower := (rows 67 162 13 280 52 33 64 128 256), losses := [] }

theorem u3541 : Upper (D 8) (R 8) [66,160,9,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3542 : PairBound 9 := { available := 161, camps := [], pairs := [(4,0)], upper := (rows 67 162 13 280 52 96 225 161 417), lower := (rows 67 162 13 280 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 97 64 128 256), good := (rows 98 162 60 280 52 96 96 128 256) }] }

theorem u3542 : Upper (D 8) (R 8) [66,160,9,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3543 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 280 52 160 97 225 353), lower := (rows 67 162 13 280 52 160 64 128 256), losses := [] }

theorem u3543 : Upper (D 8) (R 8) [66,160,9,272,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3544 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 67 162 13 296 49 36 208 208 464), lower := (rows 67 162 13 296 49 36 64 128 256), losses := [] }

theorem u3544 : Upper (D 8) (R 8) [66,160,9,288,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3544 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3545 : PairBound 9 := { available := 196, camps := [], pairs := [], upper := (rows 67 162 13 296 49 48 196 196 452), lower := (rows 67 162 13 296 49 48 64 128 256), losses := [] }

theorem u3545 : Upper (D 8) (R 8) [66,160,9,288,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3545 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3546 : PairBound 9 := { available := 148, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 13 296 49 96 212 148 404), lower := (rows 67 162 13 296 49 96 64 128 256), losses := [] }

theorem u3546 : Upper (D 8) (R 8) [66,160,9,288,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3547 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 296 49 160 84 212 340), lower := (rows 67 162 13 296 49 160 64 128 256), losses := [] }

theorem u3547 : Upper (D 8) (R 8) [66,160,9,288,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3548 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 67 162 13 296 52 33 208 208 464), lower := (rows 67 162 13 296 52 33 64 128 256), losses := [] }

theorem u3548 : Upper (D 8) (R 8) [66,160,9,288,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3549 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 162 13 296 52 48 193 193 449), lower := (rows 67 162 13 296 52 48 64 128 256), losses := [] }

theorem u3549 : Upper (D 8) (R 8) [66,160,9,288,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3549 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3550 : PairBound 9 := { available := 145, camps := [], pairs := [(4,0)], upper := (rows 67 162 13 296 52 96 209 145 401), lower := (rows 67 162 13 296 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 97 64 128 256), good := (rows 98 162 60 296 52 96 96 128 256) }] }

theorem u3550 : Upper (D 8) (R 8) [66,160,9,288,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3551 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 296 52 160 81 209 337), lower := (rows 67 162 13 296 52 160 64 128 256), losses := [] }

theorem u3551 : Upper (D 8) (R 8) [66,160,9,288,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3552 : PairBound 9 := { available := 176, camps := [], pairs := [(1,6)], upper := (rows 67 162 13 296 84 33 240 176 432), lower := (rows 67 162 13 296 84 33 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 37 0 144 272), good := (rows 35 162 45 296 446 33 0 128 256) }] }

theorem u3552 : Upper (D 8) (R 8) [66,160,9,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3553 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 162 13 296 84 48 225 161 417), lower := (rows 67 162 13 296 84 48 64 128 256), losses := [] }

theorem u3553 : Upper (D 8) (R 8) [66,160,9,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3553 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3554 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 296 84 160 113 177 305), lower := (rows 67 162 13 296 84 160 64 128 256), losses := [] }

theorem u3554 : Upper (D 8) (R 8) [66,160,9,288,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3555 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 162 13 296 112 33 212 148 404), lower := (rows 67 162 13 296 112 33 64 128 256), losses := [] }

theorem u3555 : Upper (D 8) (R 8) [66,160,9,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3556 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 162 13 296 112 36 209 145 401), lower := (rows 67 162 13 296 112 36 64 128 256), losses := [] }

theorem u3556 : Upper (D 8) (R 8) [66,160,9,288,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3556 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3557 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 162 13 296 112 48 197 133 389), lower := (rows 67 162 13 296 112 48 64 128 256), losses := [] }

theorem u3557 : Upper (D 8) (R 8) [66,160,9,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3557 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3558 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 13 296 112 160 85 149 277), lower := (rows 67 162 13 296 112 160 64 128 256), losses := [] }

theorem u3558 : Upper (D 8) (R 8) [66,160,9,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3559 : PairBound 9 := { available := 112, camps := [], pairs := [(1,6)], upper := (rows 67 162 13 296 148 33 112 240 368), lower := (rows 67 162 13 296 148 33 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 8 16 37 0 128 256), good := (rows 35 162 45 296 182 33 0 128 256) }] }

theorem u3559 : Upper (D 8) (R 8) [66,160,9,288,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3560 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 162 13 296 148 48 97 225 353), lower := (rows 67 162 13 296 148 48 64 128 256), losses := [] }

theorem u3560 : Upper (D 8) (R 8) [66,160,9,288,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3560 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3561 : Route 9 := (fun mask => (mask,id))

def c3561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3561 : Upper (D 8) (R 8) [66,160,9,288,132,64] 13 := by
  apply FastRouting.sound _ _ [66,160,9,288,132,64] 13 (by decide) (choices 1) [1,16,32] r3561 c3561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u472
  · exact u473
  · exact u474

def r3562 : Route 9 := (fun mask => (mask,id))

def c3562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3562 : Upper (D 8) (R 8) [66,160,9,288,192,1] 13 := by
  apply FastRouting.sound _ _ [66,160,9,288,192,1] 13 (by decide) (choices 1) [4,16,32] r3562 c3562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u475
  · exact u476
  · exact u477

def b3563 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 162 13 296 208 36 113 177 305), lower := (rows 67 162 13 296 208 36 64 128 256), losses := [] }

theorem u3563 : Upper (D 8) (R 8) [66,160,9,288,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3563 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3564 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 162 13 296 208 48 101 165 293), lower := (rows 67 162 13 296 208 48 64 128 256), losses := [] }

theorem u3564 : Upper (D 8) (R 8) [66,160,9,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3564 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3565 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 60, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 28 41 112 33 452 388 388), lower := (rows 67 162 28 41 112 33 64 128 256), losses := [] }

theorem u3565 : Upper (D 8) (R 8) [66,160,24,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3565 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3566 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 67 162 28 41 112 36 449 385 385), lower := (rows 67 162 28 41 112 36 64 128 256), losses := [] }

theorem u3566 : Upper (D 8) (R 8) [66,160,24,33,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3566 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3567 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 41 112 160 325 389 261), lower := (rows 67 162 28 41 112 160 64 128 256), losses := [] }

theorem u3567 : Upper (D 8) (R 8) [66,160,24,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3568 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 162 28 41 112 288 197 133 389), lower := (rows 67 162 28 41 112 288 64 128 256), losses := [] }

theorem u3568 : Upper (D 8) (R 8) [66,160,24,33,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3568 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3569 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 28 41 208 33 356 420 292), lower := (rows 67 162 28 41 208 33 64 128 256), losses := [] }

theorem u3569 : Upper (D 8) (R 8) [66,160,24,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3569 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3570 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 162 28 41 208 36 353 417 289), lower := (rows 67 162 28 41 208 36 64 128 256), losses := [] }

theorem u3570 : Upper (D 8) (R 8) [66,160,24,33,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3570 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3571 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 162 28 41 208 288 101 165 293), lower := (rows 67 162 28 41 208 288 64 128 256), losses := [] }

theorem u3571 : Upper (D 8) (R 8) [66,160,24,33,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3571 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3572 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 28 41 276 33 224 224 480), lower := (rows 67 162 28 41 276 33 64 128 256), losses := [] }

theorem u3572 : Upper (D 8) (R 8) [66,160,24,33,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3572 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3573 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 130, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 41 276 96 225 161 417), lower := (rows 67 162 28 41 276 96 64 128 256), losses := [] }

theorem u3573 : Upper (D 8) (R 8) [66,160,24,33,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3573 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3574 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 41 276 160 97 225 353), lower := (rows 67 162 28 41 276 160 64 128 256), losses := [] }

theorem u3574 : Upper (D 8) (R 8) [66,160,24,33,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3575 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 28 41 304 33 196 196 452), lower := (rows 67 162 28 41 304 33 64 128 256), losses := [] }

theorem u3575 : Upper (D 8) (R 8) [66,160,24,33,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3575 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3576 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 162 28 41 304 36 193 193 449), lower := (rows 67 162 28 41 304 36 64 128 256), losses := [] }

theorem u3576 : Upper (D 8) (R 8) [66,160,24,33,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3576 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3577 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 41 304 96 197 133 389), lower := (rows 67 162 28 41 304 96 64 128 256), losses := [] }

theorem u3577 : Upper (D 8) (R 8) [66,160,24,33,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3578 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 41 304 160 69 197 325), lower := (rows 67 162 28 41 304 160 64 128 256), losses := [] }

theorem u3578 : Upper (D 8) (R 8) [66,160,24,33,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3579 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 28 41 336 33 228 164 420), lower := (rows 67 162 28 41 336 33 64 128 256), losses := [] }

theorem u3579 : Upper (D 8) (R 8) [66,160,24,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3580 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 162 28 41 336 36 225 161 417), lower := (rows 67 162 28 41 336 36 64 128 256), losses := [] }

theorem u3580 : Upper (D 8) (R 8) [66,160,24,33,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3580 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3581 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 41 336 160 101 165 293), lower := (rows 67 162 28 41 336 160 64 128 256), losses := [] }

theorem u3581 : Upper (D 8) (R 8) [66,160,24,33,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3581 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3582 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 28 41 400 33 100 228 356), lower := (rows 67 162 28 41 400 33 64 128 256), losses := [] }

theorem u3582 : Upper (D 8) (R 8) [66,160,24,33,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3583 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 162 28 41 400 36 97 225 353), lower := (rows 67 162 28 41 400 36 64 128 256), losses := [] }

theorem u3583 : Upper (D 8) (R 8) [66,160,24,33,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3583 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3584 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 28 41 400 96 101 165 293), lower := (rows 67 162 28 41 400 96 64 128 256), losses := [] }

theorem u3584 : Upper (D 8) (R 8) [66,160,24,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3585 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 67 162 28 44 273 33 224 224 480), lower := (rows 67 162 28 44 273 33 64 128 256), losses := [] }

theorem u3585 : Upper (D 8) (R 8) [66,160,24,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3585 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3586 : PairBound 9 := { available := 161, camps := [], pairs := [(2,0)], upper := (rows 67 162 28 44 273 96 225 161 417), lower := (rows 67 162 28 44 273 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 97 64 128 256), good := (rows 98 162 28 44 316 96 96 128 256) }] }

theorem u3586 : Upper (D 8) (R 8) [66,160,24,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3587 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 44 273 160 97 225 353), lower := (rows 67 162 28 44 273 160 64 128 256), losses := [] }

theorem u3587 : Upper (D 8) (R 8) [66,160,24,36,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3587 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3588 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 162 28 104 273 33 228 164 420), lower := (rows 67 162 28 104 273 33 64 128 256), losses := [] }

theorem u3588 : Upper (D 8) (R 8) [66,160,24,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3588 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3589 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 162 28 104 273 36 225 161 417), lower := (rows 67 162 28 104 273 36 64 128 256), losses := [] }

theorem u3589 : Upper (D 8) (R 8) [66,160,24,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3589 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3590 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 104 273 160 101 165 293), lower := (rows 67 162 28 104 273 160 64 128 256), losses := [] }

theorem u3590 : Upper (D 8) (R 8) [66,160,24,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3591 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 162 28 104 304 33 197 133 389), lower := (rows 67 162 28 104 304 33 64 128 256), losses := [] }

theorem u3591 : Upper (D 8) (R 8) [66,160,24,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3591 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3592 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 67 162 28 104 304 36 193 129 385), lower := (rows 67 162 28 104 304 36 64 128 256), losses := [] }

theorem u3592 : Upper (D 8) (R 8) [66,160,24,96,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3592 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3593 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 28 104 304 160 69 133 261), lower := (rows 67 162 28 104 304 160 64 128 256), losses := [] }

theorem u3593 : Upper (D 8) (R 8) [66,160,24,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3594 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 162 28 104 400 33 101 165 293), lower := (rows 67 162 28 104 400 33 64 128 256), losses := [] }

theorem u3594 : Upper (D 8) (R 8) [66,160,24,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3594 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3595 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 28 104 400 36 97 161 289), lower := (rows 67 162 28 104 400 36 64 128 256), losses := [] }

theorem u3595 : Upper (D 8) (R 8) [66,160,24,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3595 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3596 : PairBound 9 := { available := 36, camps := [], pairs := [(1,6)], upper := (rows 67 162 28 200 273 33 100 164 292), lower := (rows 67 162 28 200 273 33 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 49 0 132 260), good := (rows 35 162 446 136 305 33 0 128 256) }] }

theorem u3596 : Upper (D 8) (R 8) [66,160,24,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3597 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 28 200 273 36 97 161 289), lower := (rows 67 162 28 200 273 36 64 128 256), losses := [] }

theorem u3597 : Upper (D 8) (R 8) [66,160,24,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3597 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3598 : Route 9 := (fun mask => (mask,id))

def c3598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3598 : Upper (D 8) (R 8) [66,160,24,192,288,1] 13 := by
  apply FastRouting.sound _ _ [66,160,24,192,288,1] 13 (by decide) (choices 1) [1,4,32] r3598 c3598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u478
  · exact u479
  · exact u480

def b3599 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 28 200 304 36 97 161 289), lower := (rows 67 162 28 200 304 36 64 128 256), losses := [] }

theorem u3599 : Upper (D 8) (R 8) [66,160,24,192,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3599 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3599
end Delivery.IrregularNine14.P08

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0007

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3420 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 134 37 104 304 48 201 137 393), lower := (rows 67 134 37 104 304 48 64 128 256), losses := [] }

theorem u3420 : Upper (D 8) (R 8) [66,132,33,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3420 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3421 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 67 134 37 104 304 160 89 153 281), lower := (rows 67 134 37 104 304 160 64 128 256), losses := [] }

theorem u3421 : Upper (D 8) (R 8) [66,132,33,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3422 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 104 400 33 120 184 312), lower := (rows 67 134 37 104 400 33 64 128 256), losses := [] }

theorem u3422 : Upper (D 8) (R 8) [66,132,33,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3423 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 134 37 104 400 40 113 177 305), lower := (rows 67 134 37 104 400 40 64 128 256), losses := [] }

theorem u3423 : Upper (D 8) (R 8) [66,132,33,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3423 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3424 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 134 37 104 400 48 105 169 297), lower := (rows 67 134 37 104 400 48 64 128 256), losses := [] }

theorem u3424 : Upper (D 8) (R 8) [66,132,33,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3424 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3425 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 152 304 33 104 232 360), lower := (rows 67 134 37 152 304 33 64 128 256), losses := [] }

theorem u3425 : Upper (D 8) (R 8) [66,132,33,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3426 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 134 37 152 304 40 97 225 353), lower := (rows 67 134 37 152 304 40 64 128 256), losses := [] }

theorem u3426 : Upper (D 8) (R 8) [66,132,33,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3426 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3427 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 152 304 96 105 169 297), lower := (rows 67 134 37 152 304 96 64 128 256), losses := [] }

theorem u3427 : Upper (D 8) (R 8) [66,132,33,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3428 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 152 336 33 104 168 296), lower := (rows 67 134 37 152 336 33 64 128 256), losses := [] }

theorem u3428 : Upper (D 8) (R 8) [66,132,33,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3429 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 37 152 336 40 97 161 289), lower := (rows 67 134 37 152 336 40 64 128 256), losses := [] }

theorem u3429 : Upper (D 8) (R 8) [66,132,33,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3429 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3430 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 168 280 33 112 240 368), lower := (rows 67 134 37 168 280 33 64 128 256), losses := [] }

theorem u3430 : Upper (D 8) (R 8) [66,132,33,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3431 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 134 37 168 280 48 97 225 353), lower := (rows 67 134 37 168 280 48 64 128 256), losses := [] }

theorem u3431 : Upper (D 8) (R 8) [66,132,33,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3431 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3432 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 168 280 96 113 177 305), lower := (rows 67 134 37 168 280 96 64 128 256), losses := [] }

theorem u3432 : Upper (D 8) (R 8) [66,132,33,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3433 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 168 304 33 88 216 344), lower := (rows 67 134 37 168 304 33 64 128 256), losses := [] }

theorem u3433 : Upper (D 8) (R 8) [66,132,33,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3433 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3434 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 67 134 37 168 304 40 81 209 337), lower := (rows 67 134 37 168 304 40 64 128 256), losses := [] }

theorem u3434 : Upper (D 8) (R 8) [66,132,33,160,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3434 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3435 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 67 134 37 168 304 48 73 201 329), lower := (rows 67 134 37 168 304 48 64 128 256), losses := [] }

theorem u3435 : Upper (D 8) (R 8) [66,132,33,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3435 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3436 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 37 168 304 96 89 153 281), lower := (rows 67 134 37 168 304 96 64 128 256), losses := [] }

theorem u3436 : Upper (D 8) (R 8) [66,132,33,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3436 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3437 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 168 336 33 120 184 312), lower := (rows 67 134 37 168 336 33 64 128 256), losses := [] }

theorem u3437 : Upper (D 8) (R 8) [66,132,33,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3438 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 134 37 168 336 40 113 177 305), lower := (rows 67 134 37 168 336 40 64 128 256), losses := [] }

theorem u3438 : Upper (D 8) (R 8) [66,132,33,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3438 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3439 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 134 37 168 336 48 105 169 297), lower := (rows 67 134 37 168 336 48 64 128 256), losses := [] }

theorem u3439 : Upper (D 8) (R 8) [66,132,33,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3439 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3440 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 200 280 33 112 176 304), lower := (rows 67 134 37 200 280 33 64 128 256), losses := [] }

theorem u3440 : Upper (D 8) (R 8) [66,132,33,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3441 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 37 200 280 48 97 161 289), lower := (rows 67 134 37 200 280 48 64 128 256), losses := [] }

theorem u3441 : Upper (D 8) (R 8) [66,132,33,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3441 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3442 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 37 200 304 33 120 184 312), lower := (rows 67 134 37 200 304 33 64 128 256), losses := [] }

theorem u3442 : Upper (D 8) (R 8) [66,132,33,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3443 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 134 37 200 304 40 113 177 305), lower := (rows 67 134 37 200 304 40 64 128 256), losses := [] }

theorem u3443 : Upper (D 8) (R 8) [66,132,33,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3443 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3444 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 134 37 200 304 48 105 169 297), lower := (rows 67 134 37 200 304 48 64 128 256), losses := [] }

theorem u3444 : Upper (D 8) (R 8) [66,132,33,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3444 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3445 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 44 25 304 33 224 224 480), lower := (rows 67 134 44 25 304 33 64 128 256), losses := [] }

theorem u3445 : Upper (D 8) (R 8) [66,132,40,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3446 : PairBound 9 := { available := 161, camps := [], pairs := [(2,0)], upper := (rows 67 134 44 25 304 96 225 161 417), lower := (rows 67 134 44 25 304 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 97 64 128 256), good := (rows 98 134 44 60 304 96 96 128 256) }] }

theorem u3446 : Upper (D 8) (R 8) [66,132,40,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3447 : Route 9 := (fun mask => (mask,id))

def c3447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3447 : Upper (D 8) (R 8) [66,132,40,17,288,128] 13 := by
  apply FastRouting.sound _ _ [66,132,40,17,288,128] 13 (by decide) (choices 1) [1,32] r3447 c3447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u453
  · exact u454

def b3448 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 67 134 44 265 49 48 224 224 480), lower := (rows 67 134 44 265 49 48 64 128 256), losses := [] }

theorem u3448 : Upper (D 8) (R 8) [66,132,40,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3448 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3449 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 44 265 49 96 240 176 432), lower := (rows 67 134 44 265 49 96 64 128 256), losses := [] }

theorem u3449 : Upper (D 8) (R 8) [66,132,40,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3450 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 44 265 49 160 112 240 368), lower := (rows 67 134 44 265 49 160 64 128 256), losses := [] }

theorem u3450 : Upper (D 8) (R 8) [66,132,40,257,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3451 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 44 265 112 33 240 176 432), lower := (rows 67 134 44 265 112 33 64 128 256), losses := [] }

theorem u3451 : Upper (D 8) (R 8) [66,132,40,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3452 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 134 44 265 112 48 225 161 417), lower := (rows 67 134 44 265 112 48 64 128 256), losses := [] }

theorem u3452 : Upper (D 8) (R 8) [66,132,40,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3452 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3453 : PairBound 9 := { available := 49, camps := [], pairs := [(4,0)], upper := (rows 67 134 44 265 112 160 113 177 305), lower := (rows 67 134 44 265 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 162 64 128 256), good := (rows 114 166 44 280 112 160 64 160 256) }] }

theorem u3453 : Upper (D 8) (R 8) [66,132,40,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3454 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 44 265 176 33 112 240 368), lower := (rows 67 134 44 265 176 33 64 128 256), losses := [] }

theorem u3454 : Upper (D 8) (R 8) [66,132,40,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3455 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 134 44 265 176 48 97 225 353), lower := (rows 67 134 44 265 176 48 64 128 256), losses := [] }

theorem u3455 : Upper (D 8) (R 8) [66,132,40,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3455 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3456 : PairBound 9 := { available := 49, camps := [], pairs := [(2,0)], upper := (rows 67 134 44 265 176 96 113 177 305), lower := (rows 67 134 44 265 176 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 97 64 128 256), good := (rows 98 134 44 300 176 96 96 128 256) }] }

theorem u3456 : Upper (D 8) (R 8) [66,132,40,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3457 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 44 265 208 33 112 176 304), lower := (rows 67 134 44 265 208 33 64 128 256), losses := [] }

theorem u3457 : Upper (D 8) (R 8) [66,132,40,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3458 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 44 265 208 48 97 161 289), lower := (rows 67 134 44 265 208 48 64 128 256), losses := [] }

theorem u3458 : Upper (D 8) (R 8) [66,132,40,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3458 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3459 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 44 280 49 33 224 224 480), lower := (rows 67 134 44 280 49 33 64 128 256), losses := [] }

theorem u3459 : Upper (D 8) (R 8) [66,132,40,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3460 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 44 280 49 96 225 161 417), lower := (rows 67 134 44 280 49 96 64 128 256), losses := [] }

theorem u3460 : Upper (D 8) (R 8) [66,132,40,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3461 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 44 280 49 160 97 225 353), lower := (rows 67 134 44 280 49 160 64 128 256), losses := [] }

theorem u3461 : Upper (D 8) (R 8) [66,132,40,272,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3462 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 134 44 280 112 33 225 161 417), lower := (rows 67 134 44 280 112 33 64 128 256), losses := [] }

theorem u3462 : Upper (D 8) (R 8) [66,132,40,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3463 : PairBound 9 := { available := 33, camps := [], pairs := [(4,0)], upper := (rows 67 134 44 280 112 160 97 161 289), lower := (rows 67 134 44 280 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 162 64 128 256), good := (rows 114 166 44 280 112 160 64 160 256) }] }

theorem u3463 : Upper (D 8) (R 8) [66,132,40,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3464 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 261 56 208 33 104 168 296), lower := (rows 67 134 261 56 208 33 64 128 256), losses := [] }

theorem u3464 : Upper (D 8) (R 8) [66,132,257,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3465 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 261 56 208 40 97 161 289), lower := (rows 67 134 261 56 208 40 64 128 256), losses := [] }

theorem u3465 : Upper (D 8) (R 8) [66,132,257,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3465 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3466 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 261 88 176 33 104 168 296), lower := (rows 67 134 261 88 176 33 64 128 256), losses := [] }

theorem u3466 : Upper (D 8) (R 8) [66,132,257,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3467 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 261 88 176 40 97 161 289), lower := (rows 67 134 261 88 176 40 64 128 256), losses := [] }

theorem u3467 : Upper (D 8) (R 8) [66,132,257,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3467 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3468 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 261 104 152 33 112 176 304), lower := (rows 67 134 261 104 152 33 64 128 256), losses := [] }

theorem u3468 : Upper (D 8) (R 8) [66,132,257,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3469 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 134 261 104 152 48 97 161 289), lower := (rows 67 134 261 104 152 48 64 128 256), losses := [] }

theorem u3469 : Upper (D 8) (R 8) [66,132,257,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3469 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3470 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 134 261 104 176 33 120 184 312), lower := (rows 67 134 261 104 176 33 64 128 256), losses := [] }

theorem u3470 : Upper (D 8) (R 8) [66,132,257,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3471 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 134 261 104 176 40 113 177 305), lower := (rows 67 134 261 104 176 40 64 128 256), losses := [] }

theorem u3471 : Upper (D 8) (R 8) [66,132,257,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3471 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3472 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 134 261 104 176 48 105 169 297), lower := (rows 67 134 261 104 176 48 64 128 256), losses := [] }

theorem u3472 : Upper (D 8) (R 8) [66,132,257,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3472 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3473 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 268 41 112 33 240 176 432), lower := (rows 67 134 268 41 112 33 64 128 256), losses := [] }

theorem u3473 : Upper (D 8) (R 8) [66,132,264,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3474 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 134 268 41 112 48 225 161 417), lower := (rows 67 134 268 41 112 48 64 128 256), losses := [] }

theorem u3474 : Upper (D 8) (R 8) [66,132,264,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3474 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3475 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 340, targets := 128 }], pairs := [(2,7)], upper := (rows 67 134 268 41 112 160 113 177 305), lower := (rows 67 134 268 41 112 160 64 128 256), losses := [] }

theorem u3475 : Upper (D 8) (R 8) [66,132,264,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3476 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 268 41 176 33 112 240 368), lower := (rows 67 134 268 41 176 33 64 128 256), losses := [] }

theorem u3476 : Upper (D 8) (R 8) [66,132,264,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3477 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 134 268 41 176 48 97 225 353), lower := (rows 67 134 268 41 176 48 64 128 256), losses := [] }

theorem u3477 : Upper (D 8) (R 8) [66,132,264,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3477 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3478 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 134 268 41 176 96 113 177 305), lower := (rows 67 134 268 41 176 96 64 128 256), losses := [] }

theorem u3478 : Upper (D 8) (R 8) [66,132,264,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3479 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 134 268 41 208 33 112 176 304), lower := (rows 67 134 268 41 208 33 64 128 256), losses := [] }

theorem u3479 : Upper (D 8) (R 8) [66,132,264,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3479
end Delivery.IrregularNine14.P08
